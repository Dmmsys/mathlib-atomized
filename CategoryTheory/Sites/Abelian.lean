/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Jujian Zhang
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Category of sheaves is abelian

Let `C, D` be categories and `J` be a Grothendieck topology on `C`, when `D` is abelian and
sheafification is possible in `C`, `Sheaf J D` is abelian as well (`sheafIsAbelian`).

Hence, `presheafToSheaf` is an additive functor (`presheafToSheaf_additive`).

-/

public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

section Abelian

universe w' w v u

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{w'} D] [Abelian D]
variable {J : GrothendieckTopology C}
variable [HasSheafify J D]

/-
**CategoryTheory.sheafIsAbelian** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：sheafIsAbelian : Abelian (Sheaf J D)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instPreservesFiniteLimitsFunctorOppositeSheafPresheafToSh
eaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTh
eory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTh…
-/
instance sheafIsAbelian : Abelian (Sheaf J D) :=
  let adj := sheafificationAdjunction J D
  abelianOfAdjunction _ _ (asIso adj.counit) adj

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
/-
**CategoryTheory.presheafToSheaf_additive** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：presheafToSheaf_additive : (presheafToSheaf J D).Additive
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesFiniteLimitsFunctorOppositeSheafPresheafToSh
eaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTh
eory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTh…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProduc
ts`：preservesBinaryBiproducts_of_preservesBinaryProducts [PreservesLimitsOfShape
 (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where p…
-/
instance presheafToSheaf_additive : (presheafToSheaf J D).Additive :=
  (presheafToSheaf J D).additive_of_preservesBinaryBiproducts
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (constantSheaf J D).Additive :=
  inferInstanceAs (Functor.const _ ⋙ presheafToSheaf _ _).Additive

end Abelian

end CategoryTheory

