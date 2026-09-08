/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Finality on Costructured Arrow categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8(i)
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open Limits CostructuredArrow

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

attribute [local instance] Grothendieck.final_map

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The version of `final_of_final_costructuredArrowToOver` on small categories used to prove the
full statement. -/
/-
**CategoryTheory.Functor.final_of_final_costructuredArrowToOver_small** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The version of `final_of_final_costructuredArrowToOver` on small categories used
 to prove the
full statement.
-/
private lemma final_of_final_costructuredArrowToOver_small (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [∀ b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L := by
  rw [final_iff_isIso_colimit_pre]
  intro G
  have : ∀ (b : B), Final ((whiskerLeft R (preFunctor L (𝟭 T))).app b).toFunctor := fun b =>
    inferInstanceAs (Final (CostructuredArrow.toOver L (R.obj b)))
  let i : colimit (L ⋙ G) ≅ colimit G :=
    calc colimit (L ⋙ G) ≅ colimit <| grothendieckProj L ⋙ L ⋙ G :=
            colimitIsoColimitGrothendieck L (L ⋙ G)
      _ ≅ colimit <| Grothendieck.pre (functor L) R ⋙ grothendieckProj L ⋙ L ⋙ G :=
            (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ L ⋙ G)).symm
      _ ≅ colimit <| Grothendieck.map (whiskerLeft _ (preFunctor L (𝟭 T))) ⋙
            grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
              HasColimit.isoOfNatIso (NatIso.ofComponents (fun _ => Iso.refl _))
      _ ≅ colimit <| grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
            Final.colimitIso _ _
      _ ≅ colimit <| Grothendieck.pre (functor (𝟭 T)) R ⋙ grothendieckProj (𝟭 T) ⋙ G :=
            HasColimit.isoOfNatIso (Iso.refl _)
      _ ≅ colimit <| grothendieckProj (𝟭 T) ⋙ G :=
            Final.colimitIso _ _
      _ ≅ colimit G := (colimitIsoColimitGrothendieck (𝟭 T) G).symm
  convert! Iso.isIso_hom i
  simp only [Iso.trans_def, comp_obj, grothendieckProj_obj, Grothendieck.pre_obj_base,
    Grothendieck.pre_obj_fiber, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, i]
  rw [← Iso.inv_comp_eq, Iso.eq_inv_comp]
  apply colimit.hom_ext (fun _ => by simp)

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A functor `L : A ⥤ T` is final if there is a final functor `R : B ⥤ T` such that for all
`b : B`, the canonical functor `CostructuredArrow L (R.obj b) ⥤ Over (R.obj b)` is final. -/
/-
**CategoryTheory.Functor.final_of_final_costructuredArrowToOver** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：final_of_final_costructuredArrowToOver (L : A ⥤ T) (R : B ⥤ T) [Final R] [
hB : forall b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L
参数：L : A ⥤ T；R : B ⥤ T；CostructuredArrow.toOver L (R.obj b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Equivalence.functor_unit_comp_assoc`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.CategoryTheory.Comma.StructuredArrow.Final.0.CategoryTh
eory.Functor.final_of_final_costructuredArrowToOver_small`：∀ {A : Type u₁} [inst
 : CategoryTheory.SmallCategory A] {B : Type u₁} [inst_1 : CategoryTheory.SmallC
ategory B]   {T : Type u₁} [inst_2 : Ca…

--- 原说明 ---
A functor `L : A ⥤ T` is final if there is a final functor `R : B ⥤ T` such that
 for all
`b : B`, the canonical functor `CostructuredArrow L (R.obj b) ⥤ Over (R.obj b)` 
is final.
-/
theorem final_of_final_costructuredArrowToOver (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [hB : ∀ b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let L' := sA.inverse ⋙ L ⋙ sT.functor
  let R' := sB.inverse ⋙ R ⋙ sT.functor
  have (b : _) : (CostructuredArrow.toOver L' (R'.obj b)).Final := by
    dsimp only [L', R', CostructuredArrow.toOver] at hB ⊢
    let x := (sB.inverse ⋙ R ⋙ sT.functor).obj b
    let F'' : CostructuredArrow (sA.inverse ⋙ L ⋙ sT.functor) x ⥤ CostructuredArrow (𝟭 _) x :=
      map₂ (F := sA.inverse) (G := sT.inverse) (whiskerLeft (sA.inverse ⋙ L) sT.unit) (𝟙 _) ⋙
      pre L (𝟭 T) (R.obj _) ⋙ map₂ (F := sT.functor) (G := sT.functor) (𝟙 _) (𝟙 _)
    apply final_of_natIso (F := F'')
    have hsT (X) : sT.counitInv.app X = 𝟙 _ := rfl
    exact NatIso.ofComponents (fun X => CostructuredArrow.isoMk (Iso.refl _) (by simp [F'', hsT]))
  have := final_of_final_costructuredArrowToOver_small L' R'
  apply final_of_natIso (F := (sA.functor ⋙ L' ⋙ sT.inverse))
  exact (sA.functor.associator (sA.inverse ⋙ L ⋙ sT.functor) sT.inverse).symm ≪≫
    ((sA.functor.associator sA.inverse (L ⋙ sT.functor)).symm ≪≫
      isoWhiskerRight sA.unitIso.symm _ ≪≫ (L ⋙ sT.functor).leftUnitor).compInverseIso

end Functor

end CategoryTheory

