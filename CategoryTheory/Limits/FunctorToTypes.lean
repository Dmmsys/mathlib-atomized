/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Concrete description of (co)limits in functor categories

Some of the concrete descriptions of (co)limits in `Type v` extend to (co)limits in the functor
category `K ⥤ Type v`.
-/

public section

namespace CategoryTheory.FunctorToTypes

open CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (F : J ⥤ K ⥤ Type w)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.FunctorToTypes.jointly_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.FunctorToTypes`。
形式化陈述：jointly_surjective (k : K) {t : Cocone F} (h : IsColimit t) (x : t.pt.obj 
k) [forall k, HasColimit (F.flip.obj k)] : exists j y, x = (t.ι.app j).app k y
参数：k : K；h : IsColimit t；x : t.pt.obj k；F.flip.obj k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective`：jointly_surjective (F : 
J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) : exists (j : J) (y : F.
obj j), t.ι.app j y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem jointly_surjective (k : K) {t : Cocone F} (h : IsColimit t) (x : t.pt.obj k)
    [∀ k, HasColimit (F.flip.obj k)] : ∃ j y, x = (t.ι.app j).app k y := by
  let hev := isColimitOfPreserves ((evaluation _ _).obj k) h
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective _ hev x
  exact ⟨j, y, by simp⟩
/-
**CategoryTheory.FunctorToTypes.jointly_surjective'** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.FunctorToTypes`。
形式化陈述：jointly_surjective' [forall k, HasColimit (F.flip.obj k)] (k : K) (x : (co
limit F).obj k) : exists j y, x = (colimit.ι F j).app k y
参数：F.flip.obj k；k : K；x : (colimit F).obj k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FunctorToTypes.jointly_surjective`：jointly_surjective (k 
: K) {t : Cocone F} (h : IsColimit t) (x : t.pt.obj k) [forall k, HasColimit (F.
flip.obj k)] : exists j y, x = (t.ι.ap…
-/
theorem jointly_surjective' [∀ k, HasColimit (F.flip.obj k)] (k : K) (x : (colimit F).obj k) :
    ∃ j y, x = (colimit.ι F j).app k y :=
  jointly_surjective _ _ (colimit.isColimit _) x
/-
**CategoryTheory.FunctorToTypes.colimit.map_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.FunctorToTypes`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit.map_ι_apply [HasColimit F] (j : J) {k k' : K} {f : k ⟶ k'} {x} :
    (colimit F).map f ((colimit.ι F j).app _ x) = (colimit.ι F j).app _ ((F.obj j).map f x) :=
  ConcreteCategory.congr_hom ((colimit.ι F j).naturality _).symm _

end CategoryTheory.FunctorToTypes

