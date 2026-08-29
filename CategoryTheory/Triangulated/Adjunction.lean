/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-!
# The adjoint functor is triangulated

If a functor `F : C ⥤ D` between pretriangulated categories is triangulated, and if we
have an adjunction `F ⊣ G`, then `G` is also a triangulated functor. We deduce the
symmetric statement (if `G` is a triangulated functor, then so is `F`) using opposite
categories.

We then introduce a class `IsTriangulated` for adjunctions: an adjunction `F ⊣ G`
is called triangulated if both `F` and `G` are triangulated, and if the adjunction
is compatible with the shifts by `ℤ` on `F` and `G` (in the sense of `Adjunction.CommShift`);
we prove that this is compatible with composition and that the identity adjunction is
triangulated.
Thanks to the results above, an adjunction carrying an `Adjunction.CommShift` instance
is triangulated as soon as one of the adjoint functors is triangulated.

We finally specialize these structures to equivalences of categories, and prove that,
if `E : C ≌ D` is an equivalence of pretriangulated categories, then
`E.functor` is triangulated if and only if `E.inverse` is triangulated.

-/

public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive Pretriangulated Adjunction

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C Int] [HasShift D Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [forall (n : Int), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.CommShift Int] [G.CommShift Int]
  [adj.CommShift Int]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include adj in
/--
lemma `isTriangulated_rightAdjoint` / 引理 `isTriangulated_rightAdjoint`

English:
lemma isTriangulated_rightAdjoint
  given: [F.IsTriangulated]
  statement: G.IsTriangulated where
  proof: by
    have : G.Additive := adj.right_adjoint_additive
    obtain ⟨Z, f, g, mem⟩ := distinguished_cocone_triangle (G.map T.mor₁)
    obtain ⟨h, ⟨h₁, h₂⟩⟩ := complete_distinguished_triangle_morphism _ _
      (F.map_distinguished _ mem) hT (adj.counit.app T.obj₁) (adj.counit.app T.obj₂) (by simp)
   

中文:
引理 isTriangulated_rightAdjoint
  条件: [F.是三角]
  结论: G.是三角 where
  证明: by
    have : G.Additive := adj.right_adjoint_additive
    obtain ⟨Z, f, g, mem⟩ := distinguished_cocone_triangle (G.map T.mor₁)
    obtain ⟨h, ⟨h₁, h₂⟩⟩ := complete_distinguished_triangle_morphism _ _
      (F.map_distinguished _ mem) hT (adj.counit.app T.obj₁) (adj.counit.app T.obj₂) (by simp)
   

Depends on / 依赖: Additive, DFunLike, DFunLike.congr_arg, F.map_distinguished, G.Additive, G.commShiftIso, G.map, T.mor, T.obj, adj.counit.app, adj.homEquiv, adj.right_adjoint_additive, adj.unit.app, commShiftIso, complete_distinguished_triangle_morphism, congr_arg, counit, distinguished_cocone_triangle, homEquiv, homEquiv_apply
-/
lemma isTriangulated_rightAdjoint [F.IsTriangulated] : G.IsTriangulated where
  map_distinguished T hT := by
    have : G.Additive := adj.right_adjoint_additive
    obtain ⟨Z, f, g, mem⟩ := distinguished_cocone_triangle (G.map T.mor₁)
    obtain ⟨h, ⟨h₁, h₂⟩⟩ := complete_distinguished_triangle_morphism _ _
      (F.map_distinguished _ mem) hT (adj.counit.app T.obj₁) (adj.counit.app T.obj₂) (by simp)
    dsimp at h h₁ h₂ ⊢
    have h₁' : f ≫ adj.unit.app Z ≫ G.map h = G.map T.mor₂ := by
      simpa [homEquiv_apply] using DFunLike.congr_arg (adj.homEquiv _ _) h₁
    have h₂' : g ≫ (G.commShiftIso (1 : Int)).inv.app T.obj₁ =
        adj.homEquiv _ _ h ≫ G.map T.mor₃ := by
      apply (adj.homEquiv _ _).symm.injective
      simp only [Functor.comp_obj, homEquiv_counit, Functor.id_obj, Functor.map_comp, assoc,
        homEquiv_unit, counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
        ← h₂, adj.shift_counit_app, Iso.hom_inv_id_app_assoc]
    rw [assoc] at h₂
    have : Mono (adj.homEquiv _ _ h) := by
      rw [mono_iff_cancel_zero]
      intro _ φ hφ
      obtain ⟨ψ, rfl⟩ := Triangle.coyoneda_exact₃ _ mem φ (by
        dsimp
        simp only [homEquiv_unit, Functor.comp_obj] at hφ
        rw [← cancel_mono ((G.commShiftIso (1 : Int)).inv.app T.obj₁)]; rw [assoc]; rw [h₂']; rw [zero_comp]; rw [homEquiv_unit]; rw [assoc]; rw [reassoc_of% hφ]; rw [zero_comp])
      dsimp at ψ hφ ⊢
      obtain ⟨α, hα⟩ := T.coyoneda_exact₂ hT ((adj.homEquiv _ _).symm ψ)
        ((adj.homEquiv _ _).injective (by simpa [homEquiv_counit, homEquiv_unit, ← h₁'] using hφ))
      have eq := DFunLike.congr_arg (adj.homEquiv _ _) hα
      simp only [homEquiv_counit, homEquiv_unit, comp_id,
        Functor.map_comp, unit_naturality_assoc, right_triangle_components] at eq
      have eq' := comp_distTriang_mor_zero₁₂ _ mem
      dsimp at eq eq'
      rw [eq]; rw [assoc]; rw [assoc]; rw [eq']; rw [comp_zero]; rw [comp_zero]
    have := isIso_of_yoneda_map_bijective (adj.homEquiv _ _ h) (fun Y => by
      constructor
      · intro φ₁ φ₂ hφ
        rw [← cancel_mono (adj.homEquiv _ _ h)]
        exact hφ
      · intro φ
        obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₁ _ mem (φ ≫ G.map T.mor₃ ≫
          (G.commShiftIso (1 : Int)).hom.app T.obj₁) (by
            dsimp
            rw [assoc]; rw [assoc]; rw [← G.commShiftIso_hom_naturality]; rw [← G.map_comp_assoc]; rw [comp_distTriang_mor_zero₃₁ _ hT]; rw [G.map_zero]; rw [zero_comp]; rw [comp_zero])
        dsimp at ψ hψ
        obtain ⟨α, hα⟩ : exists α, α = φ - ψ ≫ adj.homEquiv _ _ h := ⟨_, rfl⟩
        have hα₀ : α ≫ G.map T.mor₃ = 0 := by
          rw [hα]; rw [sub_comp]; rw [← cancel_mono ((Functor.commShiftIso G (1 : Int)).hom.app T.obj₁)]; rw [assoc]; rw [sub_comp]; rw [assoc]; rw [assoc]; rw [hψ]; rw [zero_comp]; rw [sub_eq_zero]; rw [← cancel_mono ((Functor.commShiftIso G (1 : Int)).inv.app T.obj₁)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [h₂']; rw [Iso.hom_inv_id_app]; rw [comp_id]
        suffices exists (β : Y ⟶ Z), β ≫ adj.homEquiv _ _ h = α by
          obtain ⟨β, hβ⟩ := this
          refine ⟨ψ + β, ?_⟩
          dsimp
          rw [add_comp]; rw [hβ]; rw [hα]; rw [add_sub_cancel]
        obtain ⟨β, hβ⟩ := T.coyoneda_exact₃ hT ((adj.homEquiv _ _).symm α)
          ((adj.homEquiv _ _).injective (by simpa [homEquiv_unit, homEquiv_counit] using hα₀))
        refine ⟨adj.homEquiv _ _ β ≫ f, ?_⟩
        simpa [homEquiv_unit, h₁'] using congr_arg (adj.homEquiv _ _).toFun hβ.symm)
    refine isomorphic_distinguished _ mem _ (Iso.symm ?_)
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (adj.homEquiv Z T.obj₃ h)) ?_ ?_ ?_
    · simp
    · apply (adj.homEquiv _ _).symm.injective
      dsimp
      simp only [homEquiv_unit, homEquiv_counit, Functor.map_comp, assoc,
        counit_naturality, left_triangle_components_assoc, h₁, id_comp]
    · dsimp
      rw [Functor.map_id]; rw [comp_id]; rw [homEquiv_unit]; rw [assoc]; rw [← G.map_comp_assoc]; rw [← h₂]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]; rw [unit_naturality_assoc]; rw [assoc]; rw [Functor.commShiftIso_hom_naturality]; rw [← adj.shift_unit_app_assoc]; rw [← Functor.map_comp]; rw [right_triangle_components]; rw [Functor.map_id]; rw [comp_id]

include adj in
open Pretriangulated.Opposite in
/--
lemma `isTriangulated_leftAdjoint` / 引理 `isTriangulated_leftAdjoint`

English:
lemma isTriangulated_leftAdjoint
  given: [G.IsTriangulated]
  statement: F.IsTriangulated
  proof: by
  have := isTriangulated_rightAdjoint adj.op
  exact F.isTriangulated_of_op

中文:
引理 isTriangulated_leftAdjoint
  条件: [G.是三角]
  结论: F.是三角
  证明: by
  have := isTriangulated_rightAdjoint adj.op
  exact F.isTriangulated_of_op

Depends on / 依赖: F.isTriangulated_of_op, adj.op, isTriangulated_of_op, isTriangulated_rightAdjoint
-/
lemma isTriangulated_leftAdjoint [G.IsTriangulated] : F.IsTriangulated := by
  have := isTriangulated_rightAdjoint adj.op
  exact F.isTriangulated_of_op

/--
Definition of `IsTriangulated` / `IsTriangulated` 的定义

English:
class IsTriangulated
  parameters: : Prop where
  axioms and operations (3):
    - commShift : adj.CommShift Int  [default: by infer_instance]
    - leftAdjoint_isTriangulated : F.IsTriangulated  [default: by infer_instance]
    - rightAdjoint_isTriangulated : G.IsTriangulated  [default: by infer_instance]

中文:
类 是三角
  参数: : 命题 where
  公理与运算 (3 个):
    - commShift : adj.交换Shift 整数  [默认: by infer_instance]
    - leftAdjoint_isTriangulated : F.是三角  [默认: by infer_instance]
    - rightAdjoint_isTriangulated : G.是三角  [默认: by infer_instance]

Depends on / 依赖: F.IsTriangulated, G.IsTriangulated, IsTriangulated, infer_instance, leftAdjoint_isTriangulated, rightAdjoint_isTriangulated
-/
class IsTriangulated : Prop where
  commShift : adj.CommShift Int := by infer_instance
  leftAdjoint_isTriangulated : F.IsTriangulated := by infer_instance
  rightAdjoint_isTriangulated : G.IsTriangulated := by infer_instance

namespace IsTriangulated

attribute [instance] commShift leftAdjoint_isTriangulated rightAdjoint_isTriangulated

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: [F.IsTriangulated]
  statement: adj.IsTriangulated where
  proof: adj.isTriangulated_rightAdjoint

中文:
引理 mk'
  条件: [F.是三角]
  结论: adj.是三角 where
  证明: adj.isTriangulated_rightAdjoint

Depends on / 依赖: adj.isTriangulated_rightAdjoint, isTriangulated_rightAdjoint
-/
lemma mk' [F.IsTriangulated] : adj.IsTriangulated where
  rightAdjoint_isTriangulated := adj.isTriangulated_rightAdjoint

/--
lemma `mk''` / 引理 `mk''`

English:
lemma mk''
  given: [G.IsTriangulated]
  statement: adj.IsTriangulated where
  proof: adj.isTriangulated_leftAdjoint

中文:
引理 mk''
  条件: [G.是三角]
  结论: adj.是三角 where
  证明: adj.isTriangulated_leftAdjoint

Depends on / 依赖: adj.isTriangulated_leftAdjoint, isTriangulated_leftAdjoint
-/
lemma mk'' [G.IsTriangulated] : adj.IsTriangulated where
  leftAdjoint_isTriangulated := adj.isTriangulated_leftAdjoint

/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : (Adjunction.id (C := C)).IsTriangulated where

中文:
实例 id
  签名: : (伴随.id (C := C)).是三角 where

Depends on / 依赖: IsTriangulated
-/
instance id : (Adjunction.id (C := C)).IsTriangulated where

variable {E : Type*} [Category* E] {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G') [HasZeroObject E]
  [Preadditive E] [HasShift E Int] [forall (n : Int), (shiftFunctor E n).Additive] [Pretriangulated E]
  [F'.CommShift Int] [G'.CommShift Int] [adj'.CommShift Int]

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: [adj.IsTriangulated] [adj'.IsTriangulated]

中文:
实例 comp
  签名: [adj.是三角] [adj'.是三角]
-/
instance comp [adj.IsTriangulated] [adj'.IsTriangulated] : (adj.comp adj').IsTriangulated where

end IsTriangulated

end Adjunction

namespace Equivalence

variable (E : C ≌ D) [E.functor.CommShift Int] [E.inverse.CommShift Int] [E.CommShift Int]

/--
Definition of `IsTriangulated` / `IsTriangulated` 的定义

English:
abbreviation IsTriangulated
  signature: : Prop
  body: E.toAdjunction.IsTriangulated

中文:
缩写 是三角
  签名: : 命题
  定义体: E.toAdjunction.IsTriangulated

Depends on / 依赖: E.toAdjunction.IsTriangulated, IsTriangulated, toAdjunction
-/
abbrev IsTriangulated : Prop := E.toAdjunction.IsTriangulated

namespace IsTriangulated

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [E.IsTriangulated]
  signature: : E.functor.IsTriangulated
  body: inferInstance

中文:
实例 [E.是三角]
  签名: : E.functor.是三角
  定义体: inferInstance
-/
instance [E.IsTriangulated] : E.functor.IsTriangulated := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [E.IsTriangulated]
  signature: : E.inverse.IsTriangulated
  body: inferInstance

中文:
实例 [E.是三角]
  签名: : E.inverse.是三角
  定义体: inferInstance
-/
instance [E.IsTriangulated] : E.inverse.IsTriangulated := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : E.functor.IsTriangulated] : E.symm.inverse.IsTriangulated
  body: h

中文:
实例 [h
  签名: : E.functor.是三角] : E.symm.inverse.是三角
  定义体: h
-/
instance [h : E.functor.IsTriangulated] : E.symm.inverse.IsTriangulated := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : E.inverse.IsTriangulated] : E.symm.functor.IsTriangulated
  body: h

中文:
实例 [h
  签名: : E.inverse.是三角] : E.symm.functor.是三角
  定义体: h
-/
instance [h : E.inverse.IsTriangulated] : E.symm.functor.IsTriangulated := h


/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (h : E.functor.IsTriangulated)
  statement: E.IsTriangulated where
  proof: E.toAdjunction.isTriangulated_rightAdjoint

中文:
引理 mk'
  条件: (h : E.functor.是三角)
  结论: E.是三角 where
  证明: E.toAdjunction.isTriangulated_rightAdjoint

Depends on / 依赖: E.toAdjunction.isTriangulated_rightAdjoint, isTriangulated_rightAdjoint, toAdjunction
-/
lemma mk' (h : E.functor.IsTriangulated) : E.IsTriangulated where
  rightAdjoint_isTriangulated := E.toAdjunction.isTriangulated_rightAdjoint

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mk''` / 引理 `mk''`

English:
lemma mk''
  given: (h : E.inverse.IsTriangulated)
  statement: E.IsTriangulated where
  proof: (mk' E.symm h).rightAdjoint_isTriangulated

中文:
引理 mk''
  条件: (h : E.inverse.是三角)
  结论: E.是三角 where
  证明: (mk' E.symm h).rightAdjoint_isTriangulated

Depends on / 依赖: E.symm, rightAdjoint_isTriangulated
-/
lemma mk'' (h : E.inverse.IsTriangulated) : E.IsTriangulated where
  leftAdjoint_isTriangulated := (mk' E.symm h).rightAdjoint_isTriangulated

set_option backward.isDefEq.respectTransparency false in
/--
Instance `refl` / 实例 `refl`

English:
instance refl
  signature: : (Equivalence.refl (C := C)).IsTriangulated
  body: by
  dsimp [Equivalence.IsTriangulated]
  rw [refl_toAdjunction]
  infer_instance

中文:
实例 refl
  签名: : (等价.refl (C := C)).是三角
  定义体: by
  dsimp [Equivalence.IsTriangulated]
  rw [refl_toAdjunction]
  infer_instance

Depends on / 依赖: Equivalence, Equivalence.IsTriangulated, IsTriangulated, infer_instance, refl_toAdjunction
-/
instance refl : (Equivalence.refl (C := C)).IsTriangulated := by
  dsimp [Equivalence.IsTriangulated]
  rw [refl_toAdjunction]
  infer_instance

/--
Instance `symm` / 实例 `symm`

English:
instance symm
  signature: [E.IsTriangulated]

中文:
实例 symm
  签名: [E.是三角]
-/
instance symm [E.IsTriangulated] : E.symm.IsTriangulated where

variable {D' : Type*} [Category* D'] [HasZeroObject D'] [Preadditive D'] [HasShift D' Int]
  [forall (n : Int), (shiftFunctor D' n).Additive] [Pretriangulated D'] {E' : D ≌ D'}
  [E'.functor.CommShift Int] [E'.inverse.CommShift Int] [E'.CommShift Int]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `trans` / 实例 `trans`

English:
instance trans
  signature: [E.IsTriangulated] [E'.IsTriangulated]
  body: by
  dsimp [Equivalence.IsTriangulated]
  rw [trans_toAdjunction]
  infer_instance

中文:
实例 trans
  签名: [E.是三角] [E'.是三角]
  定义体: by
  dsimp [Equivalence.IsTriangulated]
  rw [trans_toAdjunction]
  infer_instance

Depends on / 依赖: Equivalence, Equivalence.IsTriangulated, IsTriangulated, infer_instance, trans_toAdjunction
-/
instance trans [E.IsTriangulated] [E'.IsTriangulated] : (E.trans E').IsTriangulated := by
  dsimp [Equivalence.IsTriangulated]
  rw [trans_toAdjunction]
  infer_instance

end IsTriangulated

end Equivalence

end CategoryTheory
