/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Filtered colimits in concrete categories

In this file, we provide analogues to some of the API in the
`CategoryTheory.Limits.Types.FilteredColimit` namespace, for concrete categories for which the
forgetful functor preserves filtered colimits.
-/

public section

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* J] [Category* C]
  {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC] [PreservesColimitsOfShape J (forget C)]
  (F : J ⥤ C) [IsFilteredOrEmpty J]

/-
**CategoryTheory.Limits.IsColimit.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.IsColimit`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C] {FC : C → C → Type u_3} {C
C : C → Type u_4}   [inst_2 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [inst_
3 : CategoryTheory.ConcreteCategory C FC]   [CategoryTheory.Limits.PreservesColi
mitsOfShape J (CategoryTheory.forget C)] (F : CategoryTheory.Functor J C)   [Cat
egoryTheory.IsFilteredOrEmpty J] {t : CategoryTheory.Limits.Cocone F} (ht : Cate
goryTheory.Limits.IsColimit t)   {i j : J} {xi : CategoryTheory.ToType (F.obj i)
} {xj : CategoryTheory.ToType (F.obj j)},   (CategoryTheory.ConcreteCategory.hom
 (t.ι.app i)) xi = (CategoryTheory.ConcreteCategory.hom (t.ι.app j)) xj ↔     ∃ 
k f g, (CategoryTheory.ConcreteCategory.hom (F.map f)) xi = (CategoryTheory.Conc
reteCategory.hom (F.map g)) xj
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget C；F : CategoryTheory.Functor J
 C；ht : CategoryTheory.Limits.IsColimit t；F.obj i；F.obj j；CategoryTheory.Concret
eCategory.hom (t.ι.app i)；CategoryTheory.ConcreteCategory.hom (t.ι.app j)；Catego
ryTheory.ConcreteCategory.hom (F.map f)；CategoryTheory.ConcreteCategory.hom (F.m
ap g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`：isColimit_
eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j}
 : t.ι.app i xi = t.ι.app j xj ↔ exists (k : _) (f…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma IsColimit.eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : ToType <| F.obj i}
    {xj : ToType <| F.obj j} : t.ι.app i xi = t.ι.app j xj ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k),
    F.map f xi = F.map g xj :=
  Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (forget C) ht)

variable {F} in
/-
**CategoryTheory.Limits.IsColimit.eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.IsColimit`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C] {FC : C → C → Type u_3} {C
C : C → Type u_4}   [inst_2 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [inst_
3 : CategoryTheory.ConcreteCategory C FC]   [CategoryTheory.Limits.PreservesColi
mitsOfShape J (CategoryTheory.forget C)] {F : CategoryTheory.Functor J C}   [Cat
egoryTheory.IsFilteredOrEmpty J] {t : CategoryTheory.Limits.Cocone F} (ht : Cate
goryTheory.Limits.IsColimit t)   {i : J} (x y : CategoryTheory.ToType (F.obj i))
,   (CategoryTheory.ConcreteCategory.hom (t.ι.app i)) x = (CategoryTheory.Concre
teCategory.hom (t.ι.app i)) y ↔     ∃ j f, (CategoryTheory.ConcreteCategory.hom 
(F.map f)) x = (CategoryTheory.ConcreteCategory.hom (F.map f)) y
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget C；ht : CategoryTheory.Limits.I
sColimit t；x y : CategoryTheory.ToType (F.obj i)；CategoryTheory.ConcreteCategory
.hom (t.ι.app i)；CategoryTheory.ConcreteCategory.hom (t.ι.app i)；CategoryTheory.
ConcreteCategory.hom (F.map f)；CategoryTheory.ConcreteCategory.hom (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma IsColimit.eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : ToType <| F.obj i) :
    t.ι.app i x = t.ι.app i y ↔ ∃ (j : _) (f : i ⟶ j), F.map f x = F.map f y :=
  Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget C) ht) x y
/-
**CategoryTheory.Limits.colimit_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：colimit_eq_iff [HasColimit F] {i j : J} {xi : ToType <| F.obj i} {xj : ToT
ype <| F.obj j} : colimit.ι F i xi = colimit.ι F j xj ↔ exists (k : _) (f : i ⟶ 
k) (g : j ⟶ k), F.map f xi = F.map g xj
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.eq_iff`：∀ {J : Type u_1} {C : Type u_2} 
[inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_2} C] {FC : C → C …
-/
lemma colimit_eq_iff [HasColimit F] {i j : J} {xi : ToType <| F.obj i} {xj : ToType <| F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
  (colimit.isColimit F).eq_iff _

end CategoryTheory.Limits

