/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.Yoneda
public import Mathlib.CategoryTheory.Generator.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Embedding opposites of Grothendieck categories

If `C` is Grothendieck abelian and `F : D ⥤ Cᵒᵖ` is a functor from a small category, we construct
an object `G : Cᵒᵖ` such that `preadditiveCoyonedaObj G : Cᵒᵖ ⥤ ModuleCat (End G)ᵐᵒᵖ` is faithful
and exact and its precomposition with `F` is full if `F` is.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite ZeroObject

namespace CategoryTheory.Abelian.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] {D : Type v} [SmallCategory D] (F : D ⥤ Cᵒᵖ)

namespace OppositeModuleEmbedding

variable [Abelian C] [IsGrothendieckAbelian.{v} C]

variable (C) in
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.projectiv
eSeparator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbeli
an.OppositeModuleEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def projectiveSeparator : Cᵒᵖ :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEm
bedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : Projective (projectiveSeparator C) :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.1
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.isSeparat
or_projectiveSeparator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abelian.IsGroth
endieckAbelian.OppositeModuleEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isSeparator_projectiveSeparator : IsSeparator (projectiveSeparator C) :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.2

set_option backward.privateInPublic true in
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.generator
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.Opposit
eModuleEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def generator : Cᵒᵖ :=
  ∐ (fun (X : D) => ∐ fun (_ : projectiveSeparator C ⟶ F.obj X) => projectiveSeparator C)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.exists_ep
i** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.Opposi
teModuleEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_epi (X : D) : ∃ f : generator F ⟶ F.obj X, Epi f := by
  classical
  refine ⟨Sigma.desc (Pi.single X (𝟙 _)) ≫ Sigma.desc (fun f => f), ?_⟩
  have h := (isSeparator_iff_epi (projectiveSeparator C)).1
    isSeparator_projectiveSeparator (F.obj X)
  suffices Epi (Sigma.desc (Pi.single X (𝟙 _))) from epi_comp' this h
  exact SplitEpi.epi ⟨Sigma.ι (fun (X : D) => ∐ fun _ => projectiveSeparator C) X, by simp⟩
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEm
bedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : Projective (generator F) := by
  rw [generator]
  infer_instance
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.isSeparat
or** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.Oppos
iteModuleEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isSeparator [Nonempty D] : IsSeparator (generator F) := by
  apply isSeparator_sigma_of_isSeparator _ Classical.ofNonempty
  apply isSeparator_sigma_of_isSeparator _ 0
  exact isSeparator_projectiveSeparator

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given a functor `F : D ⥤ Cᵒᵖ`, where `C` is Grothendieck abelian, this is a ring `R` such that
`Cᵒᵖ` has a nice embedding into `ModuleCat (EmbeddingRing F)`; see
`OppositeModuleEmbedding.embedding`. -/
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.Embedding
Ring** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.Opp
ositeModuleEmbedding`。
形式化陈述：EmbeddingRing : Type v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : D ⥤ Cᵒᵖ`, where `C` is Grothendieck abelian, this is a ring
 `R` such that
`Cᵒᵖ` has a nice embedding into `ModuleCat (EmbeddingRing F)`; see
`OppositeModuleEmbedding.embedding`.
-/
def EmbeddingRing : Type v := (End (generator F))ᵐᵒᵖ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEm
bedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Ring (EmbeddingRing F) :=
  inferInstanceAs <| Ring (End (generator F))ᵐᵒᵖ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- This is a functor `embedding F : Cᵒᵖ ⥤ ModuleCat (EmbeddingRing F)`. We have that `embedding F`
is faithful and preserves finite limits and colimits. Furthermore, `F ⋙ embedding F` is full. -/
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.embedding
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.Opposit
eModuleEmbedding`。
形式化陈述：embedding : Cᵒᵖ ⥤ ModuleCat.{v} (EmbeddingRing F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a functor `embedding F : Cᵒᵖ ⥤ ModuleCat (EmbeddingRing F)`. We have tha
t `embedding F`
is faithful and preserves finite limits and colimits. Furthermore, `F ⋙ embeddin
g F` is full.
-/
noncomputable def embedding : Cᵒᵖ ⥤ ModuleCat.{v} (EmbeddingRing F) :=
  preadditiveCoyonedaObj (generator F)
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.faithful_
embedding** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelia
n.OppositeModuleEmbedding`。
形式化陈述：faithful_embedding [Nonempty D] : (embedding F).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObj`：isSepara
tor_iff_faithful_preadditiveCoyonedaObj (G : C) : IsSeparator G ↔ (preadditiveCo
yonedaObj G).Faithful
· 使用定理 `_private.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbed
ding.Opposite.0.CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbed
ding.isSeparator`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : 
Type v} [inst_1 : CategoryTheory.SmallCategory D]   (F : CategoryTheory.Functo…
-/
instance faithful_embedding [Nonempty D] : (embedding F).Faithful :=
  (isSeparator_iff_faithful_preadditiveCoyonedaObj _).1 (isSeparator F)
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.full_embe
dding** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.IsGrothendieckAbelian.Op
positeModuleEmbedding`。
形式化陈述：full_embedding [Nonempty D] [F.Full] : (F ⋙ embedding F).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.full_comp_preadditiveCoyonedaObj`：full_comp_pread
ditiveCoyonedaObj [F.Full] {G : C} [Projective G] (hG : IsSeparator G) (hG₂ : fo
rall X, exists (p : G ⟶ F.obj X), Epi p) : (F…
· 使用定理 `_private.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbed
ding.Opposite.0.CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbed
ding.instProjectiveOppositeGenerator`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {D : Type v} [inst_1 : CategoryTheory.SmallCategory D]   (F : Cat
egoryTheory.Functo…
· 使用定理 `_private.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbed
ding.Opposite.0.CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbed
ding.isSeparator`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : 
Type v} [inst_1 : CategoryTheory.SmallCategory D]   (F : CategoryTheory.Functo…
· 使用定理 `_private.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbed
ding.Opposite.0.CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbed
ding.exists_epi`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : T
ype v} [inst_1 : CategoryTheory.SmallCategory D]   (F : CategoryTheory.Functo…
-/
instance full_embedding [Nonempty D] [F.Full] : (F ⋙ embedding F).Full :=
  full_comp_preadditiveCoyonedaObj _ (isSeparator F) (exists_epi F)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.preserves
FiniteLimits_embedding** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.IsGroth
endieckAbelian.OppositeModuleEmbedding`。
形式化陈述：preservesFiniteLimits_embedding : PreservesFiniteLimits (embedding F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.emb
edding.eq_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type 
v} [inst_1 : CategoryTheory.SmallCategory D]   (F : CategoryTheory.Functo…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance preservesFiniteLimits_embedding : PreservesFiniteLimits (embedding F) := by
  rw [embedding]
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  infer_instance
/-
**CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.preserves
FiniteColimits_embedding** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.IsGro
thendieckAbelian.OppositeModuleEmbedding`。
形式化陈述：preservesFiniteColimits_embedding : PreservesFiniteColimits (embedding F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbed
ding.Opposite.0.CategoryTheory.Abelian.IsGrothendieckAbelian.OppositeModuleEmbed
ding.instProjectiveOppositeGenerator`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {D : Type v} [inst_1 : CategoryTheory.SmallCategory D]   (F : Cat
egoryTheory.Functo…
-/
instance preservesFiniteColimits_embedding : PreservesFiniteColimits (embedding F) := by
  apply preservesFiniteColimits_preadditiveCoyonedaObj_of_projective

end OppositeModuleEmbedding

end CategoryTheory.Abelian.IsGrothendieckAbelian

