/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Sites.Equivalence
/-!

# Coherence and equivalence of categories

This file proves that the coherent and regular topologies transfer nicely along equivalences of
categories.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

open GrothendieckTopology

namespace Equivalence

variable {D : Type*} [Category* D]

section Coherent

variable [Precoherent C]

/-- `Precoherent` is preserved by equivalence of categories. -/
/-
**CategoryTheory.Equivalence.precoherent** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Equivalence`。
形式化陈述：precoherent (e : C ≌ D) : Precoherent D
参数：e : C ≌ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.reflects_precoherent`：∀ {C : Type u_1} {D : Type 
u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instPreservesFiniteEffectiveEpiFamiliesOfPreserve
sEffectiveEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_
1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Cate
gor…
· 使用定理 `CategoryTheory.Functor.instPreservesEffectiveEpiFamiliesOfIsEquivalence`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.instReflectsFiniteEffectiveEpiFamiliesOfReflectsE
ffectiveEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1}
 C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Catego
r…
· 使用定理 `CategoryTheory.Functor.instReflectsEffectiveEpiFamiliesOfIsEquivalence`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instEffectivelyEnoughOfIsEquivalence`：∀ {C : Type
 u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] (F : Categor…

--- 原说明 ---
`Precoherent` is preserved by equivalence of categories.
-/
theorem precoherent (e : C ≌ D) : Precoherent D := e.inverse.reflects_precoherent
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssentiallySmall C] :
    Precoherent (SmallModel C) := (equivSmallModel C).precoherent
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : C ≌ D) : haveI := precoherent e
    e.inverse.IsDenseSubsite (coherentTopology D) (coherentTopology C) where
  functorPushforward_mem_iff := by
    simp [coherentTopology.eq_induced e.inverse]

variable (A : Type*) [Category* A]

/--
Equivalent precoherent categories give equivalent coherent toposes.
-/
@[simps!]
/-
**CategoryTheory.Equivalence.sheafCongrPrecoherent** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：sheafCongrPrecoherent (e : C ≌ D) : haveI
参数：e : C ≌ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.precoherent`：precoherent (e : C ≌ D) : Precoh
erent D
· 使用定理 `CategoryTheory.Equivalence.instIsDenseSubsiteCoherentTopologyInverse`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [i
nst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
Equivalent precoherent categories give equivalent coherent toposes.
-/
def sheafCongrPrecoherent (e : C ≌ D) : haveI := e.precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The coherent sheaf condition can be checked after precomposing with the equivalence.
-/
/-
**CategoryTheory.Equivalence.precoherent_isSheaf_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Equivalence`。
形式化陈述：precoherent_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI
参数：e : C ≌ D；F : Cᵒᵖ ⥤ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.precoherent`：precoherent (e : C ≌ D) : Precoh
erent D
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'

--- 原说明 ---
The coherent sheaf condition can be checked after precomposing with the equivale
nce.
-/
theorem precoherent_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI := e.precoherent
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPrecoherent A).functor.obj ⟨F, hF⟩).property, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPrecoherent A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.property
  · exact Functor.isoWhiskerRight e.op.unitIso F

/--
The coherent sheaf condition on an essentially small site can be checked after precomposing with
the equivalence with a small category.
-/
/-
**CategoryTheory.Equivalence.precoherent_isSheaf_iff_of_essentiallySmall** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：precoherent_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ 
⥤ A) : IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology (SmallModel C)
) ((equivSmallModel C).inverse.op ⋙ F)
参数：F : Cᵒᵖ ⥤ A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.precoherent_isSheaf_iff`：precoherent_isSheaf_
iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI

--- 原说明 ---
The coherent sheaf condition on an essentially small site can be checked after p
recomposing with
the equivalence with a small category.
-/
theorem precoherent_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology C) F ↔
      IsSheaf (coherentTopology (SmallModel C)) ((equivSmallModel C).inverse.op ⋙ F) :=
  precoherent_isSheaf_iff _ _ _

end Coherent

section Regular

variable [Preregular C]

/-- `Preregular` is preserved by equivalence of categories. -/
/-
**CategoryTheory.Equivalence.preregular** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：preregular (e : C ≌ D) : Preregular D
参数：e : C ≌ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.reflects_preregular`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instPreservesEffectiveEpisOfPreservesFiniteEffect
iveEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {
D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instPreservesFiniteEffectiveEpiFamiliesOfPreserve
sEffectiveEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_
1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Cate
gor…
· 使用定理 `CategoryTheory.Functor.instPreservesEffectiveEpiFamiliesOfIsEquivalence`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.instReflectsEffectiveEpisOfReflectsFiniteEffectiv
eEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instReflectsFiniteEffectiveEpiFamiliesOfReflectsE
ffectiveEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1}
 C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Catego
r…
· 使用定理 `CategoryTheory.Functor.instReflectsEffectiveEpiFamiliesOfIsEquivalence`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instEffectivelyEnoughOfIsEquivalence`：∀ {C : Type
 u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] (F : Categor…

--- 原说明 ---
`Preregular` is preserved by equivalence of categories.
-/
theorem preregular (e : C ≌ D) : Preregular D := e.inverse.reflects_preregular
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssentiallySmall C] :
    Preregular (SmallModel C) := (equivSmallModel C).preregular
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : C ≌ D) : haveI := preregular e
    e.inverse.IsDenseSubsite (regularTopology D) (regularTopology C) where
  functorPushforward_mem_iff := by
    simp [regularTopology.eq_induced e.inverse]

variable (A : Type*) [Category* A]

/--
Equivalent preregular categories give equivalent regular toposes.
-/
@[simps!]
/-
**CategoryTheory.Equivalence.sheafCongrPreregular** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：sheafCongrPreregular (e : C ≌ D) : haveI
参数：e : C ≌ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.preregular`：preregular (e : C ≌ D) : Preregul
ar D
· 使用定理 `CategoryTheory.Equivalence.instIsDenseSubsiteRegularTopologyInverse`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [in
st_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
Equivalent preregular categories give equivalent regular toposes.
-/
def sheafCongrPreregular (e : C ≌ D) : haveI := e.preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The regular sheaf condition can be checked after precomposing with the equivalence.
-/
/-
**CategoryTheory.Equivalence.preregular_isSheaf_iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Equivalence`。
形式化陈述：preregular_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI
参数：e : C ≌ D；F : Cᵒᵖ ⥤ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.preregular`：preregular (e : C ≌ D) : Preregul
ar D
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'

--- 原说明 ---
The regular sheaf condition can be checked after precomposing with the equivalen
ce.
-/
theorem preregular_isSheaf_iff (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI := e.preregular
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPreregular A).functor.obj ⟨F, hF⟩).property, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPreregular A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.property
  · exact Functor.isoWhiskerRight e.op.unitIso F

/--
The regular sheaf condition on an essentially small site can be checked after precomposing with
the equivalence with a small category.
-/
/-
**CategoryTheory.Equivalence.preregular_isSheaf_iff_of_essentiallySmall** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：preregular_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤
 A) : IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology (SmallModel C)) (
(equivSmallModel C).inverse.op ⋙ F)
参数：F : Cᵒᵖ ⥤ A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.preregular_isSheaf_iff`：preregular_isSheaf_if
f (e : C ≌ D) (F : Cᵒᵖ ⥤ A) : haveI

--- 原说明 ---
The regular sheaf condition on an essentially small site can be checked after pr
ecomposing with
the equivalence with a small category.
-/
theorem preregular_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology (SmallModel C))
    ((equivSmallModel C).inverse.op ⋙ F) := preregular_isSheaf_iff _ _ _

end Regular

end Equivalence

end CategoryTheory

