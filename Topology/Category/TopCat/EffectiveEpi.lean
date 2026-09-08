/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
/-!

# Effective epimorphisms in `TopCat`

This file proves the result `TopCat.effectiveEpi_iff_isQuotientMap`:
The effective epimorphisms in `TopCat` are precisely the quotient maps.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

/--
Implementation: If `π` is a morphism in `TopCat` which is a quotient map, then it is an effective
epimorphism. The theorem `TopCat.effectiveEpi_iff_isQuotientMap` should be used instead of
this definition.
-/
noncomputable
/-
**TopCat.effectiveEpiStructOfQuotientMap** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：effectiveEpiStructOfQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) (hπ : IsQuo
tientMap π) : EffectiveEpiStruct π where /- `IsQuotientMap.lift` gives the requi
red morphism -/ desc e h
参数：π : X ⟶ B；hπ : IsQuotientMap π。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiStructOfQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) (hπ : IsQuotientMap π) :
    EffectiveEpiStruct π where
  /- `IsQuotientMap.lift` gives the required morphism -/
  desc e h := ofHom <| hπ.lift e.hom fun a b hab ↦
    CategoryTheory.congr_fun (h
      (ofHom ⟨fun _ ↦ a, continuous_const⟩)
      (ofHom ⟨fun _ ↦ b, continuous_const⟩)
    (by ext; exact hab)) a
  /- `IsQuotientMap.lift_comp` gives the factorisation -/
  fac e h := hom_ext (hπ.lift_comp e.hom
    fun a b hab ↦ CategoryTheory.congr_fun (h
      (ofHom ⟨fun _ ↦ a, continuous_const⟩)
      (ofHom ⟨fun _ ↦ b, continuous_const⟩)
    (by ext; exact hab)) a)
  /- Uniqueness follows from the fact that `IsQuotientMap.lift` is an equivalence (given by
  `IsQuotientMap.liftEquiv`). -/
  uniq e h g hm := by
    suffices g = ofHom (hπ.liftEquiv ⟨e.hom,
      fun a b hab ↦ CategoryTheory.congr_fun (h
          (ofHom ⟨fun _ ↦ a, continuous_const⟩)
          (ofHom ⟨fun _ ↦ b, continuous_const⟩)
          (by ext; exact hab))
        a⟩) by assumption
    apply hom_ext
    rw [hom_ofHom, ← Equiv.symm_apply_eq hπ.liftEquiv]
    ext
    simp only [IsQuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

/-- The effective epimorphisms in `TopCat` are precisely the quotient maps. -/
/-
**TopCat.effectiveEpi_iff_isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：effectiveEpi_iff_isQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) : EffectiveE
pi π ↔ IsQuotientMap π
参数：π : X ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.isQuotientMap_of_isColimit_cofork`：isQuotientMap_of_isColimit_cof
ork (c : Cofork f g) (hc : IsColimit c) : IsQuotientMap c.π
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.IsRegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularEpi
 f],   CategoryTheo…

--- 原说明 ---
The effective epimorphisms in `TopCat` are precisely the quotient maps.
-/
theorem effectiveEpi_iff_isQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) :
    EffectiveEpi π ↔ IsQuotientMap π := by
  /- The backward direction is given by `effectiveEpiStructOfQuotientMap` above. -/
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨effectiveEpiStructOfQuotientMap π hπ⟩⟩⟩
  /- Since `TopCat` has pullbacks, `π` is in fact a `RegularEpi`. This means that it exhibits `B` as
    a coequalizer of two maps into `X`. It suffices to prove that `π` followed by the isomorphism to
    an arbitrary coequalizer is a quotient map. -/
  exact isQuotientMap_of_isColimit_cofork _ (IsRegularEpi.isColimit π)

end TopCat

