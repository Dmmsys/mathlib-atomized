/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Effective epimorphisms in `CompHausLike`

In any category of compact Hausdorff spaces, continuous surjections are effective epimorphisms.

We deduce that if the converse holds and explicit pullbacks exist, then `CompHausLike P` is
preregular.

If furthermore explicit finite coproducts exist, then `CompHausLike P` is precoherent.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace CompHausLike

variable {P : TopCat.{u} → Prop}

/--
If `π` is a surjective morphism in `CompHausLike P`, then it is an effective epi.
-/
noncomputable
/-
**CompHausLike.effectiveEpiStruct** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：effectiveEpiStruct {B X : CompHausLike P} (π : X ⟶ B) (hπ : Function.Surje
ctive π) : EffectiveEpiStruct π where desc e h
参数：π : X ⟶ B；hπ : Function.Surjective π。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop
-/
def effectiveEpiStruct {B X : CompHausLike P} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h :=
    ofHom _ ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).lift e.hom.hom
      fun a b hab ↦
        CategoryTheory.congr_fun (h
          (ofHom _ ⟨fun _ ↦ a, continuous_const⟩)
          (ofHom _ ⟨fun _ ↦ b, continuous_const⟩)
        (by ext; exact hab)) a)
  fac e h :=
    InducedCategory.hom_ext (TopCat.hom_ext
      ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).lift_comp _ _))
  uniq e h g hm := by
    suffices g = ofHom _
        ((IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).liftEquiv ⟨e.hom.hom,
      fun a b hab ↦ CategoryTheory.congr_fun
        (h
          (ofHom _ ⟨fun _ ↦ a, continuous_const⟩)
          (ofHom _ ⟨fun _ ↦ b, continuous_const⟩)
          (by ext; exact hab))
        a⟩) by assumption
    apply ConcreteCategory.ext
    rw [hom_ofHom, ← Equiv.symm_apply_eq
      (IsQuotientMap.of_surjective_continuous hπ π.hom.hom.continuous).liftEquiv]
    ext
    simp only [IsQuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl
/-
**CompHausLike.preregular** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：preregular [HasExplicitPullbacks P] (hs : forall ⦃X Y : CompHausLike P⦄ (f
 : X ⟶ Y), EffectiveEpi f -> Function.Surjective f) : Preregular (CompHausLike P
) where exists_fac
参数：hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Su
rjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.HasExplicitPullbacks.hasProp`：∀ {P : TopCat → Prop} [self :
 CompHausLike.HasExplicitPullbacks P] {X Y B : CompHausLike P} (f : X ⟶ B) (g : 
Y ⟶ B),   CompHausLike.HasExpli…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CompHausLike.pullback.condition`：∀ {P : TopCat → Prop} {X Y B : CompHaus
Like P} (f : X ⟶ B) (g : Y ⟶ B) [inst : CompHausLike.HasExplicitPullback f g],  
 CategoryTheory.Categ…
-/
theorem preregular [HasExplicitPullbacks P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f) :
    Preregular (CompHausLike P) where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ⟨⟨effectiveEpiStruct _ ?_⟩⟩, pullback.snd f π,
      (pullback.condition _ _).symm⟩
    intro y
    obtain ⟨z, hz⟩ := hs π hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩
/-
**CompHausLike.precoherent** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：precoherent [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P] (
hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Surje
ctive f) : Precoherent (CompHausLike P)
参数：hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Su
rjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.preregular`：preregular [HasExplicitPullbacks P] (hs : foral
l ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Surjective f) :
 Preregular (…
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
-/
theorem precoherent [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f) :
    Precoherent (CompHausLike P) := by
  have : Preregular (CompHausLike P) := preregular hs
  infer_instance

end CompHausLike

