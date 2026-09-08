/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotence of the Karoubi envelope

In this file, we construct the equivalence of categories
`KaroubiKaroubi.equivalence C : Karoubi C ≌ Karoubi (Karoubi C)` for any category `C`.

-/

@[expose] public section


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

namespace KaroubiKaroubi

variable (C : Type*) [Category* C]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.idem_f** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Idempotents.KaroubiKaroubi`。
形式化陈述：idem_f (P : Karoubi (Karoubi C)) : P.p.f ≫ P.p.f = P.p.f
参数：P : Karoubi (Karoubi C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi C),  
 CategoryTheory.CategoryStruc…
-/
lemma idem_f (P : Karoubi (Karoubi C)) : P.p.f ≫ P.p.f = P.p.f := by
  simpa only [hom_ext_iff, comp_f] using P.idem

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.p_comm_f** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Idempotents.KaroubiKaroubi`。
形式化陈述：p_comm_f {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q) : P.p.f ≫ f.f.f = f.f.f ≫
 Q.p.f
参数：Karoubi C；f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comm`：p_comm {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p
-/
lemma p_comm_f {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q) : P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f := by
  simpa only [hom_ext_iff, comp_f] using p_comm f

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical functor `Karoubi (Karoubi C) ⥤ Karoubi C` -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.inverse** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Idempotents.KaroubiKaroubi`。
形式化陈述：inverse : Karoubi (Karoubi C) ⥤ Karoubi C where obj P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor `Karoubi (Karoubi C) ⥤ Karoubi C`
-/
def inverse : Karoubi (Karoubi C) ⥤ Karoubi C where
  obj P := ⟨P.X.X, P.p.f, by simpa only [hom_ext_iff] using! P.idem⟩
  map f := ⟨f.f.f, by simpa only [hom_ext_iff] using! f.comm⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Idempotents.KaroubiKaroubi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] : Functor.Additive (inverse C) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit isomorphism of the equivalence -/
@[simps!]
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.unitIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Idempotents.KaroubiKaroubi`。
形式化陈述：unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit isomorphism of the equivalence
-/
def unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C :=
  eqToIso (Functor.ext (by cat_disch) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] p_comm_f in
/-- The counit isomorphism of the equivalence -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.counitIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Idempotents.KaroubiKaroubi`。
形式化陈述：counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) wh
ere hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism of the equivalence
-/
def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  hom := { app := fun P => { f := { f := P.p.1 } } }
  inv := { app := fun P => { f := { f := P.p.1 } } }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Karoubi C ≌ Karoubi (Karoubi C)` -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.equivalence** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Idempotents.KaroubiKaroubi`。
形式化陈述：equivalence : Karoubi C ≌ Karoubi (Karoubi C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `Karoubi C ≌ Karoubi (Karoubi C)`
-/
def equivalence : Karoubi C ≌ Karoubi (Karoubi C) where
  functor := toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_functor** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Idempotents.KaroubiKaroubi.equivalence`。
形式化陈述：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C],   (CategoryTheory.Idempotents.KaroubiKaroubi.equiv
alence C).functor.Additive
参数：C : Type u_1；CategoryTheory.Idempotents.KaroubiKaroubi.equivalence C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equivalence.additive_functor [Preadditive C] :
    Functor.Additive (equivalence C).functor where

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_inverse** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Idempotents.KaroubiKaroubi.equivalence`。
形式化陈述：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C],   (CategoryTheory.Idempotents.KaroubiKaroubi.equiv
alence C).inverse.Additive
参数：C : Type u_1；CategoryTheory.Idempotents.KaroubiKaroubi.equivalence C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equivalence.additive_inverse [Preadditive C] :
    Functor.Additive (equivalence C).inverse where

end KaroubiKaroubi

end Idempotents

end CategoryTheory

