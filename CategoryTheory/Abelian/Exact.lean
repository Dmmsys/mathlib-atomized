/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer
-/
module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Tactic.TFAE

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* A short complex `S` is exact iff `imageSubobject S.f = kernelSubobject S.g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `Exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π f = 0` iff `Exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* A functor `F` such that for all `S`, we have `S.Exact → (S.map F).Exact` preserves both
  finite limits and colimits.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex C)

attribute [local instance] hasEqualizers_of_hasKernels

/-
**CategoryTheory.ShortComplex.exact_iff_epi_imageToKernel'** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_epi_imageToKernel' : S.Exact ↔ Epi (imageToKernel' S.f S.g S.zer
o)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift`：exact_iff_epi_ker
nel_lift [S.HasHomology] [HasKernel S.g] : S.Exact ↔ Epi (kernel.lift S.g S.f S.
zero)
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.instEpiFactorThruImageOfHasLimitWalkingParallelPai
rParallelPair`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C
} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasImage f]   [∀ {Z : C} (g…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Preadditive.hasEqualizers_of_hasKernels`：hasEqualizers_of
_hasKernels [HasKernels C] : HasEqualizers C
-/
theorem exact_iff_epi_imageToKernel' : S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero) := by
  rw [S.exact_iff_epi_kernel_lift]
  have : factorThruImage S.f ≫ imageToKernel' S.f S.g S.zero = kernel.lift S.g S.f S.zero := by
    simp only [← cancel_mono (kernel.ι _), kernel.lift_ι, imageToKernel',
      Category.assoc, image.fac]
  constructor
  · intro
    exact epi_of_epi_fac this
  · intro
    rw [← this]
    apply epi_comp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.exact_iff_epi_imageToKernel** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_epi_imageToKernel : S.Exact ↔ Epi (imageToKernel S.f S.g S.zero)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_epi_imageToKernel'`：exact_iff_epi_
imageToKernel' : S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `imageToKernel'_kernelSubobjectIso`：∀ {V : Type u} [inst : CategoryTheory
.Category.{v, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {A B C :
 V}   (f : A ⟶ B) (g : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exact_iff_epi_imageToKernel : S.Exact ↔ Epi (imageToKernel S.f S.g S.zero) := by
  rw [S.exact_iff_epi_imageToKernel']
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (imageSubobjectIso S.f).symm (kernelSubobjectIso S.g).symm
/-
**CategoryTheory.ShortComplex.exact_iff_isIso_imageToKernel'** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_isIso_imageToKernel' : S.Exact ↔ IsIso (imageToKernel' S.f S.g S
.zero)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_epi_imageToKernel'`：exact_iff_epi_
imageToKernel' : S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero)
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Limits.kernel.lift_mono`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
-/
lemma exact_iff_isIso_imageToKernel' : S.Exact ↔ IsIso (imageToKernel' S.f S.g S.zero) := by
  simp only [S.exact_iff_epi_imageToKernel', isIso_iff_mono_and_epi, iff_and_self]
  intro
  apply Limits.kernel.lift_mono
/-
**CategoryTheory.ShortComplex.exact_iff_isIso_imageToKernel** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_isIso_imageToKernel : S.Exact ↔ IsIso (imageToKernel S.f S.g S.z
ero)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_epi_imageToKernel`：exact_iff_epi_i
mageToKernel : S.Exact ↔ Epi (imageToKernel S.f S.g S.zero)
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `instMonoImageToKernel`：∀ {V : Type u} [inst : CategoryTheory.Category.{v
, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {A B C : V}   (f : A
 ⟶ B) [inst…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
theorem exact_iff_isIso_imageToKernel : S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero) := by
  rw [S.exact_iff_epi_imageToKernel]
  constructor
  · intro
    apply isIso_of_mono_of_epi
  · intro
    infer_instance
/-
**CategoryTheory.ShortComplex.Exact.isIso_imageToKernel** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Abelian C]   (S : CategoryTheory.ShortComplex C), S.Exact → CategoryT
heory.IsIso (imageToKernel S.f S.g ⋯)
参数：S : CategoryTheory.ShortComplex C；imageToKernel S.f S.g ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_isIso_imageToKernel`：exact_iff_isI
so_imageToKernel : S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero)
-/
lemma Exact.isIso_imageToKernel (hS : S.Exact) : IsIso (imageToKernel S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel.1 hS
/-
**CategoryTheory.ShortComplex.Exact.isIso_imageToKernel'** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Abelian C]   (S : CategoryTheory.ShortComplex C), S.Exact → CategoryT
heory.IsIso (imageToKernel' S.f S.g ⋯)
参数：S : CategoryTheory.ShortComplex C；imageToKernel' S.f S.g ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_isIso_imageToKernel'`：exact_iff_is
Iso_imageToKernel' : S.Exact ↔ IsIso (imageToKernel' S.f S.g S.zero)
-/
lemma Exact.isIso_imageToKernel' (hS : S.Exact) : IsIso (imageToKernel' S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel'.1 hS

/-- In an abelian category, a short complex `S` is exact
iff `imageSubobject S.f = kernelSubobject S.g`.
-/
/-
**CategoryTheory.ShortComplex.exact_iff_image_eq_kernel** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_image_eq_kernel : S.Exact ↔ imageSubobject S.f = kernelSubobject
 S.g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_isIso_imageToKernel`：exact_iff_isI
so_imageToKernel : S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero)
· 使用定理 `CategoryTheory.Subobject.eq_of_comm`：eq_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ≅ (Y : C)) (w : f.hom ≫ Y.arrow = X.arrow) : X = Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
In an abelian category, a short complex `S` is exact
iff `imageSubobject S.f = kernelSubobject S.g`.
-/
theorem exact_iff_image_eq_kernel : S.Exact ↔ imageSubobject S.f = kernelSubobject S.g := by
  rw [exact_iff_isIso_imageToKernel]
  constructor
  · intro
    exact Subobject.eq_of_comm (asIso (imageToKernel _ _ S.zero)) (by simp)
  · intro h
    exact ⟨Subobject.ofLE _ _ h.ge, by ext; simp, by ext; simp⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.exact_iff_of_forks** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：exact_iff_of_forks {cg : KernelFork S.g} (hg : IsLimit cg) {cf : CokernelC
ofork S.f} (hf : IsColimit cf) : S.Exact ↔ cg.ι ≫ cf.π = 0
参数：hg : IsLimit cg；hf : IsColimit cf。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero`：exa
ct_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology] [HasKernel S.g] [HasCokerne
l S.f] : S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Preadditive.IsIso.comp_left_eq_zero`：comp_left_eq_zero [I
sIso f] : f ≫ g = 0 ↔ g = 0
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Preadditive.IsIso.comp_right_eq_zero`：comp_right_eq_zero 
[IsIso g] : f ≫ g = 0 ↔ f = 0
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exact_iff_of_forks {cg : KernelFork S.g} (hg : IsLimit cg) {cf : CokernelCofork S.f}
    (hf : IsColimit cf) : S.Exact ↔ cg.ι ≫ cf.π = 0 := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero]
  let e₁ := IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hg
  let e₂ := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hf
  have : cg.ι ≫ cf.π = e₁.inv ≫ kernel.ι S.g ≫ cokernel.π S.f ≫ e₂.hom := by
    have eq₁ := IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) hg (.zero)
    have eq₂ := IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f) hf (.one)
    dsimp at eq₁ eq₂
    rw [← eq₁, ← eq₂, Category.assoc]
  rw [this, IsIso.comp_left_eq_zero e₁.inv, ← Category.assoc,
    IsIso.comp_right_eq_zero _ e₂.hom]

variable {S}

/-- If `(f, g)` is exact, then `Abelian.image.ι S.f` is a kernel of `S.g`. -/
/-
**CategoryTheory.ShortComplex.Exact.isLimitImage** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Abelian C] →       {S : CategoryTheory.ShortComplex C} →     
    S.Exact →           CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Ker
nelFork.ofι (CategoryTheory.Abelian.image.ι S.f) ⋯)
参数：CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Abelian.image.ι S.f) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(f, g)` is exact, then `Abelian.image.ι S.f` is a kernel of `S.g`.
-/
def Exact.isLimitImage (h : S.Exact) :
    IsLimit (KernelFork.ofι (Abelian.image.ι S.f)
      (Abelian.image_ι_comp_eq_zero S.zero) : KernelFork S.g) := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  exact KernelFork.IsLimit.ofι _ _
    (fun u hu ↦ kernel.lift (cokernel.π S.f) u
      (by rw [← kernel.lift_ι S.g u hu, Category.assoc, h, comp_zero])) (by simp)
    (fun _ _ _ hm => by rw [← cancel_mono (Abelian.image.ι S.f), hm, kernel.lift_ι])

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
/-
**CategoryTheory.ShortComplex.Exact.isLimitImage'** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Abelian C] →       {S : CategoryTheory.ShortComplex C} →     
    S.Exact →           CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Ker
nelFork.ofι (CategoryTheory.Limits.image.ι S.f) ⋯)
参数：CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limits.image.ι S.f) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(f, g)` is exact, then `image.ι f` is a kernel of `g`.
-/
def Exact.isLimitImage' (h : S.Exact) :
    IsLimit (KernelFork.ofι (Limits.image.ι S.f)
      (image_ι_comp_eq_zero S.zero) : KernelFork S.g) :=
  IsKernel.isoKernel _ _ h.isLimitImage (Abelian.imageIsoImage S.f).symm <| IsImage.lift_fac _ _

/-- If `(f, g)` is exact, then `Abelian.coimage.π g` is a cokernel of `f`. -/
/-
**CategoryTheory.ShortComplex.Exact.isColimitCoimage** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Abelian C] →       {S : CategoryTheory.ShortComplex C} →     
    S.Exact →           CategoryTheory.Limits.IsColimit             (CategoryThe
ory.Limits.CokernelCofork.ofπ (CategoryTheory.Abelian.coimage.π S.g) ⋯)
参数：CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Abelian.coimage.π S.
g) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(f, g)` is exact, then `Abelian.coimage.π g` is a cokernel of `f`.
-/
def Exact.isColimitCoimage (h : S.Exact) :
    IsColimit
      (CokernelCofork.ofπ (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero) :
        CokernelCofork S.f) := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun u hu => cokernel.desc (kernel.ι S.g) u
      (by rw [← cokernel.π_desc S.f u hu, ← Category.assoc, h, zero_comp]))
    (by simp) ?_
  intro _ _ _ _ hm
  ext
  rw [hm, cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
/-- If `(f, g)` is exact, then `factorThruImage g` is a cokernel of `f`. -/
/-
**CategoryTheory.ShortComplex.Exact.isColimitImage** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Abelian C] →       {S : CategoryTheory.ShortComplex C} →     
    S.Exact →           CategoryTheory.Limits.IsColimit             (CategoryThe
ory.Limits.CokernelCofork.ofπ (CategoryTheory.Limits.factorThruImage S.g) ⋯)
参数：CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Limits.factorThruIma
ge S.g) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(f, g)` is exact, then `factorThruImage g` is a cokernel of `f`.
-/
def Exact.isColimitImage (h : S.Exact) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage S.g)
        (comp_factorThruImage_eq_zero S.zero)) :=
  IsCokernel.cokernelIso _ _ h.isColimitCoimage (Abelian.coimageIsoImage' S.g) <|
    (cancel_mono (Limits.image.ι S.g)).1 <| by simp
/-
**CategoryTheory.ShortComplex.exact_kernel** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：exact_kernel {X Y : C} (f : X ⟶ Y) : (ShortComplex.mk (kernel.ι f) f (by s
imp)).Exact
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
theorem exact_kernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (kernel.ι f) f (by simp)).Exact :=
  exact_of_f_is_kernel _ (kernelIsKernel f)
/-
**CategoryTheory.ShortComplex.exact_cokernel** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：exact_cokernel {X Y : C} (f : X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (
by simp)).Exact
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
theorem exact_cokernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (cokernel.π f) (by simp)).Exact :=
  exact_of_g_is_cokernel _ (cokernelIsCokernel f)

variable (S)
/-
**CategoryTheory.ShortComplex.exact_iff_exact_image_** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exact_iff_exact_image_ι :
    S.Exact ↔ (ShortComplex.mk (Abelian.image.ι S.f) S.g
      (Abelian.image_ι_comp_eq_zero S.zero)).Exact :=
  ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := Abelian.factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
/-
**CategoryTheory.ShortComplex.exact_iff_exact_coimage_** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exact_iff_exact_coimage_π :
    S.Exact ↔ (ShortComplex.mk S.f (Abelian.coimage.π S.g)
      (Abelian.comp_coimage_π_eq_zero S.zero)).Exact := by
  symm
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.factorThruCoimage S.g }

end ShortComplex

section

open List in
/-
**CategoryTheory.Abelian.tfae_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abe
lian`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Abelian C] {X Y : C} (f : X ⟶ Y)   (Z : C),   [CategoryTheory.Mono f,
 CategoryTheory.Limits.kernel.ι f = 0,       { X₁ := Z, X₂ := X, X₃ := Y, f := 0
, g := f, zero := ⋯ }.Exact].TFAE
参数：f : X ⟶ Y；Z : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Abelian.mono_of_kernel_ι_eq_zero`：mono_of_kernel_ι_eq_zer
o (h : kernel.ι f = 0) : Mono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono`：exact_iff_mono [HasZeroObjec
t C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Abelian.tfae_mono {X Y : C} (f : X ⟶ Y) (Z : C) :
    TFAE [Mono f, kernel.ι f = 0, (ShortComplex.mk (0 : Z ⟶ X) f zero_comp).Exact] := by
  tfae_have 2 → 1 := mono_of_kernel_ι_eq_zero _
  tfae_have 1 → 2
  | _ => by rw [← cancel_mono f, kernel.condition, zero_comp]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_mono _ (by simp)
  tfae_finish

open List in
/-
**CategoryTheory.Abelian.tfae_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abel
ian`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Abelian C] {X Y : C} (f : X ⟶ Y)   (Z : C),   [CategoryTheory.Epi f, 
CategoryTheory.Limits.cokernel.π f = 0,       { X₁ := X, X₂ := Y, X₃ := Z, f := 
f, g := 0, zero := ⋯ }.Exact].TFAE
参数：f : X ⟶ Y；Z : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Abelian.epi_of_cokernel_π_eq_zero`：epi_of_cokernel_π_eq_z
ero (h : cokernel.π f = 0) : Epi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi`：exact_iff_epi [HasZeroObject 
C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Abelian.tfae_epi {X Y : C} (f : X ⟶ Y) (Z : C) :
    TFAE [Epi f, cokernel.π f = 0, (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).Exact] := by
  tfae_have 2 → 1 := epi_of_cokernel_π_eq_zero _
  tfae_have 1 → 2
  | _ => by rw [← cancel_epi f, cokernel.condition, comp_zero]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_epi _ (by simp)
  tfae_finish

end

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.reflects_exact_of_faithful** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：reflects_exact_of_faithful [F.Faithful] (S : ShortComplex C) (hS : (S.map 
F).Exact) : S.Exact
参数：S : ShortComplex C；hS : (S.map F).Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero`：exa
ct_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology] [HasKernel S.g] [HasCokerne
l S.f] : S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.zero_of_map_zero`：zero_of_map_zero (F : C ⥤ D) [P
reservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y) (h : F.map f = 0) : 
f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma reflects_exact_of_faithful [F.Faithful] (S : ShortComplex C) (hS : (S.map F).Exact) :
    S.Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hS ⊢
  dsimp at hS
  apply F.zero_of_map_zero
  obtain ⟨k, hk⟩ :=
    kernel.lift' (F.map S.g) (F.map (kernel.ι S.g))
      (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
  obtain ⟨l, hl⟩ :=
    cokernel.desc' (F.map S.f) (F.map (cokernel.π S.f))
      (by simp only [← F.map_comp, cokernel.condition, CategoryTheory.Functor.map_zero])
  rw [F.map_comp, ← hl, ← hk, Category.assoc, reassoc_of% hS, zero_comp, comp_zero]

end

end Functor

namespace Functor

open Limits Abelian

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [Abelian A] [Abelian B]
variable (L : A ⥤ B)

section

variable [L.PreservesZeroMorphisms]
variable (hL : ∀ (S : ShortComplex A), S.Exact → (S.map L).Exact)
include hL

open ZeroObject

set_option backward.defeqAttrib.useBackward true in
/-- A functor which preserves exactness preserves monomorphisms. -/
/-
**CategoryTheory.Functor.preservesMonomorphisms_of_map_exact** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesMonomorphisms_of_map_exact : L.PreservesMonomorphisms where prese
rves f hf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Abelian.tfae_mono`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Abelian C] {X Y : C} (f : X ⟶ Y) 
  (Z : C),   [Category…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
A functor which preserves exactness preserves monomorphisms.
-/
theorem preservesMonomorphisms_of_map_exact : L.PreservesMonomorphisms where
  preserves f hf := by
    apply ((Abelian.tfae_mono (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_mono f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- A functor which preserves exactness preserves epimorphisms. -/
/-
**CategoryTheory.Functor.preservesEpimorphisms_of_map_exact** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesEpimorphisms_of_map_exact : L.PreservesEpimorphisms where preserv
es f hf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Abelian.tfae_epi`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Abelian C] {X Y : C} (f : X ⟶ Y)  
 (Z : C),   [Category…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…

--- 原说明 ---
A functor which preserves exactness preserves epimorphisms.
-/
theorem preservesEpimorphisms_of_map_exact : L.PreservesEpimorphisms where
  preserves f hf := by
    apply ((Abelian.tfae_epi (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_epi f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- A functor which preserves the exactness of short complexes preserves homology. -/
/-
**CategoryTheory.Functor.preservesHomology_of_map_exact** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：preservesHomology_of_map_exact : L.PreservesHomology where preservesCokern
els X Y f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_map_exact`：preservesMon
omorphisms_of_map_exact : L.PreservesMonomorphisms where preserves f hf
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_map_exact`：preservesEpim
orphisms_of_map_exact : L.PreservesEpimorphisms where preserves f hf
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact

--- 原说明 ---
A functor which preserves the exactness of short complexes preserves homology.
-/
lemma preservesHomology_of_map_exact : L.PreservesHomology where
  preservesCokernels X Y f := by
    have := preservesEpimorphisms_of_map_exact _ hL
    apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    apply (CokernelCofork.isColimitMapCoconeEquiv _ L).2
    have : Epi ((ShortComplex.mk _ _ (cokernel.condition f)).map L).g := by
      dsimp
      infer_instance
    exact (hL (ShortComplex.mk _ _ (cokernel.condition f))
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))).gIsCokernel
  preservesKernels X Y f := by
    have := preservesMonomorphisms_of_map_exact _ hL
    apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    apply (KernelFork.isLimitMapConeEquiv _ L).2
    have : Mono ((ShortComplex.mk _ _ (kernel.condition f)).map L).f := by
      dsimp
      infer_instance
    exact (hL (ShortComplex.mk _ _ (kernel.condition f))
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f))).fIsKernel

end

section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A functor preserving zero morphisms, monos, and cokernels preserves homology. -/
/-
**CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesHomology_of_preservesMonos_and_cokernels [PreservesZeroMorphisms 
L] [PreservesMonomorphisms L] [forall {X Y} (f : X ⟶ Y), PreservesColimit (paral
lelPair f 0) L] : PreservesHomology L
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesHomology_of_map_exact`：preservesHomology
_of_map_exact : L.PreservesHomology where preservesCokernels X Y f
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…
· 使用定理 `CategoryTheory.Abelian.comp_coimage_π_eq_zero`：comp_coimage_π_eq_zero {R
 : C} {g : Q ⟶ R} (h : f ≫ g = 0) : f ≫ Abelian.coimage.π g = 0
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`：exact_iff
_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : S₁.
Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Abelian.instMonoFactorThruCoimage`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C}
 (f : P ⟶ Q),   CategoryTheory.Mono (C…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A functor preserving zero morphisms, monos, and cokernels preserves homology.
-/
lemma preservesHomology_of_preservesMonos_and_cokernels [PreservesZeroMorphisms L]
    [PreservesMonomorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) L] :
    PreservesHomology L := by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : (ShortComplex.mk _ _ (Abelian.comp_coimage_π_eq_zero S.zero)).map L ⟶ S.map L :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := L.map (Abelian.factorThruCoimage S.g)
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, ← L.map_comp, cokernel.π_desc] }
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
  apply ShortComplex.exact_of_g_is_cokernel
  exact CokernelCofork.mapIsColimit _ ((S.exact_iff_exact_coimage_π).1 hS).gIsCokernel L

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A functor preserving zero morphisms, epis, and kernels preserves homology. -/
/-
**CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L] 
[PreservesEpimorphisms L] [forall {X Y} (f : X ⟶ Y), PreservesLimit (parallelPai
r f 0) L] : PreservesHomology L
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesHomology_of_map_exact`：preservesHomology
_of_map_exact : L.PreservesHomology where preservesCokernels X Y f
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
· 使用定理 `CategoryTheory.Abelian.image_ι_comp_eq_zero`：image_ι_comp_eq_zero {R : C
} {g : Q ⟶ R} (h : f ≫ g = 0) : Abelian.image.ι f ≫ g = 0
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`：exact_iff
_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : S₁.
Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.Abelian.instEpiFactorThruImage`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C} (f
 : P ⟶ Q),   CategoryTheory.Epi (Ca…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A functor preserving zero morphisms, epis, and kernels preserves homology.
-/
lemma preservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L]
    [PreservesEpimorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) L] :
    PreservesHomology L := by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : S.map L ⟶ (ShortComplex.mk _ _ (Abelian.image_ι_comp_eq_zero S.zero)).map L :=
    { τ₁ := L.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id, ← L.map_comp, kernel.lift_ι] }
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.mapIsLimit _ ((S.exact_iff_exact_image_ι).1 hS).fIsKernel L

end

end Functor

end CategoryTheory

