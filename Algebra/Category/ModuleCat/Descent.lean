/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Christian Merten, Joël Riou, Adam Topaz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithfully flat descent for modules

In this file we show that extension of scalars by a faithfully flat ring homomorphism is comonadic.
Then the general theory of descent implies that the pseudofunctor to `Cat` given by extension
of scalars has effective descent relative to faithfully flat maps (TODO).

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Comonad ModuleCat Limits MonoidalCategory

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}

/-
**ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat (hf : f.Flat) : 
PreservesFiniteLimits tensorLeft ((restrictScalars f).obj (ModuleCat.of B B))
参数：hf : f.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.instPreservesFiniteLimitsModuleCatTensorLeftOfCarrier`：∀ {R 
: Type u} [inst : CommRing R] (M : ModuleCat R) [Module.Flat R ↑M],   CategoryTh
eory.Limits.PreservesFiniteLimits (CategoryTheory.Monoi…
-/
lemma ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat (hf : f.Flat) :
    PreservesFiniteLimits <| tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)) := by
  algebraize [f]
  change PreservesFiniteLimits <| tensorLeft (ModuleCat.of A B)
  infer_instance
/-
**ModuleCat.preservesFiniteLimits_extendScalars_of_flat** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf : f.Flat) : Pres
ervesFiniteLimits (extendScalars.{_, _, u} f)
参数：hf : f.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat`：ModuleCat.pre
servesFiniteLimits_tensorLeft_of_ringHomFlat (hf : f.Flat) : PreservesFiniteLimi
ts tensorLeft ((restrictScalars f).obj (ModuleC…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves`：pr
eservesFiniteLimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E) [PreservesF
initeLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesF…
· 使用定理 `ModuleCat.instReflectsIsomorphismsRestrictScalars`：∀ {R : Type u_1} {S :
 Type u_2} [inst : Ring R] [inst_1 : Ring S] (f : R →+* S),   (ModuleCat.restric
tScalars f).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `ModuleCat.instIsRightAdjointRestrictScalars`：∀ {R : Type u₁} {S : Type u
₂} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S),   (ModuleCat.restric
tScalars f).IsRightAdjoint
-/
lemma ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf : f.Flat) :
    PreservesFiniteLimits (extendScalars.{_, _, u} f) := by
  have : PreservesFiniteLimits (extendScalars.{_, _, u} f ⋙ restrictScalars.{_, _, u} f) :=
    ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat hf
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars f) (restrictScalars f)

/-- Extension of scalars along faithfully flat ring maps reflects isomorphisms. -/
/-
**ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat** 是 Mathlib 中的一
个引理，位于命名空间 ``。
形式化陈述：ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat (hf : f.Fai
thfullyFlat) : (extendScalars.{_, _, u} f).ReflectsIsomorphisms
参数：hf : f.FaithfullyFlat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用引理 `Module.FaithfullyFlat.lTensor_bijective_iff_bijective`：lTensor_bijective
_iff_bijective [Module.FaithfullyFlat R M] : Function.Bijective (f.lTensor M) ↔ 
Function.Bijective f

--- 原说明 ---
Extension of scalars along faithfully flat ring maps reflects isomorphisms.
-/
lemma ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat
    (hf : f.FaithfullyFlat) : (extendScalars.{_, _, u} f).ReflectsIsomorphisms := by
  refine ⟨fun {M N} g h ↦ ?_⟩
  algebraize [f]
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  replace h : Function.Bijective (LinearMap.lTensor B g.hom) := h
  rwa [Module.FaithfullyFlat.lTensor_bijective_iff_bijective] at h

/-- Extension of scalars by a faithfully flat ring map is comonadic. -/
@[instance_reducible]
/-
**comonadicExtendScalars** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：comonadicExtendScalars (hf : f.FaithfullyFlat) : ComonadicLeftAdjoint (ext
endScalars f)
参数：hf : f.FaithfullyFlat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat`：ModuleCa
t.reflectsIsomorphisms_extendScalars_of_faithfullyFlat (hf : f.FaithfullyFlat) :
 (extendScalars.{_, _, u} f).ReflectsIsomorphisms

--- 原说明 ---
Extension of scalars by a faithfully flat ring map is comonadic.
-/
def comonadicExtendScalars (hf : f.FaithfullyFlat) :
    ComonadicLeftAdjoint (extendScalars f) := by
  have := preservesFiniteLimits_extendScalars_of_flat hf.flat
  have := reflectsIsomorphisms_extendScalars_of_faithfullyFlat hf
  convert!
    Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
      (extendRestrictScalarsAdj f)
  · exact ⟨inferInstance⟩
  · exact ⟨inferInstance⟩
