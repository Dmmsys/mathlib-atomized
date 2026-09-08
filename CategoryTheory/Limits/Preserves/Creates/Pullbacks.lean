/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Creation of limits and pullbacks

We show some lemmas relating creation of (co)limits and pullbacks (resp. pushouts).
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-
**CategoryTheory.Limits.HasPullback.of_createsLimit** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.HasPullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)   [CategoryTheory.CreatesLimit (Categ
oryTheory.Limits.cospan f g) F]   [CategoryTheory.Limits.HasPullback (F.map f) (
F.map g)], CategoryTheory.Limits.HasPullback f g
参数：F : CategoryTheory.Functor C D；f : X ⟶ S；g : Y ⟶ S；CategoryTheory.Limits.cosp
an f g；F.map f；F.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
lemma HasPullback.of_createsLimit (F : C ⥤ D) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)
    [CreatesLimit (cospan f g) F] [HasPullback (F.map f) (F.map g)] :
    HasPullback f g :=
  have : HasLimit (cospan f g ⋙ F) := hasLimit_of_iso (cospanCompIso F f g).symm
  hasLimit_of_created _ F
/-
**CategoryTheory.Limits.HasPushout.of_createsColimit** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.HasPushout`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y)   [CategoryTheory.CreatesColimit (Cat
egoryTheory.Limits.span f g) F]   [CategoryTheory.Limits.HasPushout (F.map f) (F
.map g)], CategoryTheory.Limits.HasPushout f g
参数：F : CategoryTheory.Functor C D；f : S ⟶ X；g : S ⟶ Y；CategoryTheory.Limits.span
 f g；F.map f；F.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K
-/
lemma HasPushout.of_createsColimit (F : C ⥤ D) {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y)
    [CreatesColimit (span f g) F] [HasPushout (F.map f) (F.map g)] :
    HasPushout f g :=
  have : HasColimit (span f g ⋙ F) := hasColimit_of_iso (spanCompIso F f g)
  hasColimit_of_created _ F

end CategoryTheory.Limits

