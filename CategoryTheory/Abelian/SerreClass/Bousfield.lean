/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Bousfield localizations with respect to Serre classes

If `G : D ⥤ C` is an exact functor between abelian categories,
with a fully faithful right adjoint `F`, then `G` identifies
`C` to the localization of `D` with respect to the
class of morphisms `G.kernel.isoModSerre`, i.e. `D`
is the localization of `C` with respect to the Serre class
`G.kernel` consisting of the objects in `D`
that are sent to a zero object by `G`.
(We also translate this in terms of a left Bousfield localization.)

-/

public section

namespace CategoryTheory

open Localization Limits MorphismProperty

variable {C D : Type*} [Category* C] [Category* D]
  [Abelian C] [Abelian D] (G : D ⥤ C)
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

namespace Abelian

/-
**CategoryTheory.Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：isoModSerre_kernel_eq_inverseImage_isomorphisms : G.kernel.isoModSerre = (
isomorphisms C).inverseImage G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `CategoryTheory.ObjectProperty.instIsSerreClassInverseImageOfPreservesFin
iteLimitsOfPreservesFiniteColimits`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectPro
perty C) {D : Ty…
· 使用定理 `CategoryTheory.ObjectProperty.instIsSerreClassIsZero`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Ca
tegoryTheory.ObjectProperty.IsSerreClass C…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_isInvertedBy_iff`：isoModSerre_
isInvertedBy_iff (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits 
F] : P.isoModSerre.IsInvertedBy F ↔ P <= F.kerne…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Limits.KernelFork.IsLimit.isZero_of_mono`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : Ca…
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
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Limits.CokernelCofork.IsColimit.isZero_of_epi`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : Ca…
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
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
lemma isoModSerre_kernel_eq_inverseImage_isomorphisms :
    G.kernel.isoModSerre = (isomorphisms C).inverseImage G := by
  ext X Y f
  refine ⟨(G.kernel.isoModSerre_isInvertedBy_iff G).2 (by rfl) _, fun hf ↦ ?_⟩
  simp only [inverseImage_iff, isomorphisms.iff] at hf
  constructor
  · exact KernelFork.IsLimit.isZero_of_mono
      (KernelFork.mapIsLimit _ (kernelIsKernel f) G)
  · exact CokernelCofork.IsColimit.isZero_of_epi
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) G)

variable {G}
/-
**CategoryTheory.Abelian.isoModSerre_kernel_eq_isLocal_of_rightAdjoint** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：isoModSerre_kernel_eq_isLocal_of_rightAdjoint {F : C ⥤ D} (adj : G ⊣ F) [F
.Full] [F.Faithful] : G.kernel.isoModSerre = ObjectProperty.isLocal (· in Set.ra
nge F.obj)
参数：adj : G ⊣ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instIsSerreClassInverseImageOfPreservesFin
iteLimitsOfPreservesFiniteColimits`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectPro
perty C) {D : Ty…
· 使用定理 `CategoryTheory.ObjectProperty.instIsSerreClassIsZero`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Ca
tegoryTheory.ObjectProperty.IsSerreClass C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_eq_inverseImage_isomorphisms`：isLo
cal_eq_inverseImage_isomorphisms : isLocal (· in Set.range F.obj) = (MorphismPro
perty.isomorphisms _).inverseImage G
· 使用引理 `CategoryTheory.Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms`：
isoModSerre_kernel_eq_inverseImage_isomorphisms : G.kernel.isoModSerre = (isomor
phisms C).inverseImage G
-/
lemma isoModSerre_kernel_eq_isLocal_of_rightAdjoint
    {F : C ⥤ D} (adj : G ⊣ F) [F.Full] [F.Faithful] :
    G.kernel.isoModSerre = ObjectProperty.isLocal (· ∈ Set.range F.obj) := by
  rw [ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj,
    isoModSerre_kernel_eq_inverseImage_isomorphisms]
/-
**CategoryTheory.Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：isLocalization_isoModSerre_kernel_of_leftAdjoint {F : C ⥤ D} (adj : G ⊣ F)
 [F.Full] [F.Faithful] : G.IsLocalization G.kernel.isoModSerre
参数：adj : G ⊣ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instIsSerreClassInverseImageOfPreservesFin
iteLimitsOfPreservesFiniteColimits`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectPro
perty C) {D : Ty…
· 使用定理 `CategoryTheory.ObjectProperty.instIsSerreClassIsZero`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Ca
tegoryTheory.ObjectProperty.IsSerreClass C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms`：
isoModSerre_kernel_eq_inverseImage_isomorphisms : G.kernel.isoModSerre = (isomor
phisms C).inverseImage G
· 使用引理 `CategoryTheory.Adjunction.isLocalization`：isLocalization [F.Full] [F.Fai
thful] : G.IsLocalization ((MorphismProperty.isomorphisms C₂).inverseImage G)
-/
lemma isLocalization_isoModSerre_kernel_of_leftAdjoint
    {F : C ⥤ D} (adj : G ⊣ F) [F.Full] [F.Faithful] :
    G.IsLocalization G.kernel.isoModSerre := by
  rw [isoModSerre_kernel_eq_inverseImage_isomorphisms G]
  exact adj.isLocalization

end Abelian

end CategoryTheory

