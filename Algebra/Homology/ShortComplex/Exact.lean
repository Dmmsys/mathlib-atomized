/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Exact short complexes

When `S : ShortComplex C`, this file defines a structure
`S.Exact` which expresses the exactness of `S`, i.e. there
exists a homology data `h : S.HomologyData` such that
`h.left.H` is zero. When `[S.HasHomology]`, it is equivalent
to the assertion `IsZero S.homology`.

Almost by construction, this notion of exactness is self dual,
see `Exact.op` and `Exact.unop`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C D : Type*} [Category* C] [Category* D]

namespace ShortComplex

section

variable
  [HasZeroMorphisms C] [HasZeroMorphisms D] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/-- The assertion that the short complex `S : ShortComplex C` is exact. -/
/-
**CategoryTheory.ShortComplex.Exact** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ShortComplex C
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The assertion that the short complex `S : ShortComplex C` is exact.
-/
structure Exact : Prop where
  /-- the condition that there exists a homology data whose `left.H` field is zero -/
  condition : ∃ (h : S.HomologyData), IsZero h.left.H

variable {S}
/-
**CategoryTheory.ShortComplex.Exact.hasHomology** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
S.Exact → S.HasHomology
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.Exact.condition`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {S : CategoryTheory.Sho…
-/
lemma Exact.hasHomology (h : S.Exact) : S.HasHomology :=
  HasHomology.mk' h.condition.choose
/-
**CategoryTheory.ShortComplex.Exact.hasZeroObject** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
S.Exact → CategoryTheory.Limits.HasZeroObject C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.condition`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {S : CategoryTheory.Sho…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Exact.hasZeroObject (h : S.Exact) : HasZeroObject C :=
  ⟨h.condition.choose.left.H, h.condition.choose_spec⟩

variable (S)
/-
**CategoryTheory.ShortComplex.exact_iff_isZero_homology** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_isZero_homology [S.HasHomology] : S.Exact ↔ IsZero S.homology
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
-/
lemma exact_iff_isZero_homology [S.HasHomology] :
    S.Exact ↔ IsZero S.homology := by
  constructor
  · rintro ⟨⟨h', z⟩⟩
    exact IsZero.of_iso z h'.left.homologyIso
  · intro h
    exact ⟨⟨_, h⟩⟩

variable {S}
/-
**CategoryTheory.ShortComplex.LeftHomologyData.exact_iff** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} [
S.HasHomology] (h : S.LeftHomologyData),   S.Exact ↔ CategoryTheory.Limits.IsZer
o h.H
参数：h : S.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_isZero_homology`：exact_iff_isZero_
homology [S.HasHomology] : S.Exact ↔ IsZero S.homology
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
-/
lemma LeftHomologyData.exact_iff [S.HasHomology]
    (h : S.LeftHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso
/-
**CategoryTheory.ShortComplex.RightHomologyData.exact_iff** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} [
S.HasHomology] (h : S.RightHomologyData),   S.Exact ↔ CategoryTheory.Limits.IsZe
ro h.H
参数：h : S.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_isZero_homology`：exact_iff_isZero_
homology [S.HasHomology] : S.Exact ↔ IsZero S.homology
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
-/
lemma RightHomologyData.exact_iff [S.HasHomology]
    (h : S.RightHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

variable (S)
/-
**CategoryTheory.ShortComplex.exact_iff_isZero_leftHomology** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_isZero_leftHomology [S.HasHomology] : S.Exact ↔ IsZero S.leftHom
ology
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma exact_iff_isZero_leftHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.leftHomology :=
  LeftHomologyData.exact_iff _
/-
**CategoryTheory.ShortComplex.exact_iff_isZero_rightHomology** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_isZero_rightHomology [S.HasHomology] : S.Exact ↔ IsZero S.rightH
omology
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma exact_iff_isZero_rightHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.rightHomology :=
  RightHomologyData.exact_iff _

variable {S}
/-
**CategoryTheory.ShortComplex.HomologyData.exact_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.HomologyData), S.Exact ↔ CategoryTheory.Limits.IsZero h.left.H
参数：h : S.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma HomologyData.exact_iff (h : S.HomologyData) :
    S.Exact ↔ IsZero h.left.H := by
  have := HasHomology.mk' h
  exact LeftHomologyData.exact_iff h.left
/-
**CategoryTheory.ShortComplex.HomologyData.exact_iff'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.HomologyData), S.Exact ↔ CategoryTheory.Limits.IsZero h.right.H
参数：h : S.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma HomologyData.exact_iff' (h : S.HomologyData) :
    S.Exact ↔ IsZero h.right.H := by
  have := HasHomology.mk' h
  exact RightHomologyData.exact_iff h.right

variable (S)
/-
**CategoryTheory.ShortComplex.exact_iff_homology_iso_zero** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_homology_iso_zero [S.HasHomology] [HasZeroObject C] : S.Exact ↔ 
Nonempty (S.homology ≅ 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_isZero_homology`：exact_iff_isZero_
homology [S.HasHomology] : S.Exact ↔ IsZero S.homology
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
lemma exact_iff_homology_iso_zero [S.HasHomology] [HasZeroObject C] :
    S.Exact ↔ Nonempty (S.homology ≅ 0) := by
  rw [exact_iff_isZero_homology]
  constructor
  · intro h
    exact ⟨h.isoZero⟩
  · rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e
/-
**CategoryTheory.ShortComplex.exact_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：exact_of_iso (e : S₁ ≅ S₂) (h : S₁.Exact) : S₂.Exact
参数：e : S₁ ≅ S₂；h : S₁.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_of_iso (e : S₁ ≅ S₂) (h : S₁.Exact) : S₂.Exact := by
  obtain ⟨⟨h, z⟩⟩ := h
  exact ⟨⟨HomologyData.ofIso e h, z⟩⟩
/-
**CategoryTheory.ShortComplex.exact_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ↔ S₂.Exact
参数：e : S₁ ≅ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
-/
lemma exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩
/-
**CategoryTheory.ShortComplex.exact_and_mono_f_iff_of_iso** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_and_mono_f_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ∧ Mono S₁.f ↔ S₂.Exac
t ∧ Mono S₂.f
参数：e : S₁ ≅ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_iso`：exact_iff_of_iso (e : S₁ ≅
 S₂) : S₁.Exact ↔ S₂.Exact
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exact_and_mono_f_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Mono S₁.f ↔ S₂.Exact ∧ Mono S₂.f := by
  have : Mono S₁.f ↔ Mono S₂.f :=
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e, this]
/-
**CategoryTheory.ShortComplex.exact_and_epi_g_iff_of_iso** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_and_epi_g_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ∧ Epi S₁.g ↔ S₂.Exact 
∧ Epi S₂.g
参数：e : S₁ ≅ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_iso`：exact_iff_of_iso (e : S₁ ≅
 S₂) : S₁.Exact ↔ S₂.Exact
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exact_and_epi_g_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Epi S₁.g ↔ S₂.Exact ∧ Epi S₂.g := by
  have : Epi S₁.g ↔ Epi S₂.g :=
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e, this]
/-
**CategoryTheory.ShortComplex.exact_of_isZero_X** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_of_isZero_X₂ (h : IsZero S.X₂) : S.Exact := by
  rw [(HomologyData.ofZeros S (IsZero.eq_of_tgt h _ _) (IsZero.eq_of_src h _ _)).exact_iff]
  exact h
/-
**CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [M
ono φ.τ₃] : S₁.Exact ↔ S₂.Exact
参数：φ : S₁ ⟶ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_iff_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    S₁.Exact ↔ S₂.Exact := by
  constructor
  · rintro ⟨h₁, z₁⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono φ h₁, z₁⟩
  · rintro ⟨h₂, z₂⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono' φ h₂, z₂⟩

variable {S}
/-
**CategoryTheory.ShortComplex.HomologyData.exact_iff_i_p_zero** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.HomologyData),   S.Exact ↔ CategoryTheory.CategoryStruct.comp h.left.i h.r
ight.p = 0
参数：h : S.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.comm`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instMonoι`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instEpiπ`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HomologyData.exact_iff_i_p_zero (h : S.HomologyData) :
    S.Exact ↔ h.left.i ≫ h.right.p = 0 := by
  have := HasHomology.mk' h
  rw [h.left.exact_iff, ← h.comm]
  constructor
  · intro z
    rw [IsZero.eq_of_src z h.iso.hom 0, zero_comp, comp_zero]
  · intro eq
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp, ← cancel_mono h.right.ι,
      ← cancel_epi h.left.π, eq, zero_comp, comp_zero]

variable (S)
/-
**CategoryTheory.ShortComplex.exact_iff_i_p_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：exact_iff_i_p_zero [S.HasHomology] (h₁ : S.LeftHomologyData) (h₂ : S.Right
HomologyData) : S.Exact ↔ h₁.i ≫ h₂.p = 0
参数：h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.exact_iff_i_p_zero`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma exact_iff_i_p_zero [S.HasHomology] (h₁ : S.LeftHomologyData)
    (h₂ : S.RightHomologyData) :
    S.Exact ↔ h₁.i ≫ h₂.p = 0 :=
  (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero
/-
**CategoryTheory.ShortComplex.exact_iff_iCycles_pOpcycles_zero** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_iCycles_pOpcycles_zero [S.HasHomology] : S.Exact ↔ S.iCycles ≫ S
.pOpcycles = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_i_p_zero`：exact_iff_i_p_zero [S.Ha
sHomology] (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) : S.Exact ↔ h₁.i
 ≫ h₂.p = 0
-/
lemma exact_iff_iCycles_pOpcycles_zero [S.HasHomology] :
    S.Exact ↔ S.iCycles ≫ S.pOpcycles = 0 :=
  S.exact_iff_i_p_zero _ _
/-
**CategoryTheory.ShortComplex.exact_iff_kernel_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology]
    [HasKernel S.g] [HasCokernel S.f] :
    S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  have := HasLeftHomology.hasCokernel S
  have := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofHasKernelOfHasCokernel S)
    (RightHomologyData.ofHasCokernelOfHasKernel S)

variable {S}
/-
**CategoryTheory.ShortComplex.Exact.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
S.Exact → S.op.Exact
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.op`：op (h : IsZero X) : IsZero (Opposite.op
 X)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
-/
lemma Exact.op (h : S.Exact) : S.op.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.op, (IsZero.of_iso z h.iso.symm).op⟩⟩
/-
**CategoryTheory.ShortComplex.Exact.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex Cᵒᵖ}
, S.Exact → S.unop.Exact
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unop`：unop {X : Cᵒᵖ} (h : IsZero X) : IsZer
o (Opposite.unop X)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
-/
lemma Exact.unop {S : ShortComplex Cᵒᵖ} (h : S.Exact) : S.unop.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.unop, (IsZero.of_iso z h.iso.symm).unop⟩⟩

variable (S)

@[simp]
/-
**CategoryTheory.ShortComplex.exact_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：exact_op_iff : S.op.Exact ↔ S.Exact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.unop`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.op`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {S : CategoryTheory.Sho…
-/
lemma exact_op_iff : S.op.Exact ↔ S.Exact :=
  ⟨Exact.unop, Exact.op⟩

@[simp]
/-
**CategoryTheory.ShortComplex.exact_unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：exact_unop_iff (S : ShortComplex Cᵒᵖ) : S.unop.Exact ↔ S.Exact
参数：S : ShortComplex Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ShortComplex.exact_op_iff`：exact_op_iff : S.op.Exact ↔ S.
Exact
-/
lemma exact_unop_iff (S : ShortComplex Cᵒᵖ) : S.unop.Exact ↔ S.Exact :=
  S.unop.exact_op_iff.symm

variable {S}
/-
**CategoryTheory.ShortComplex.LeftHomologyData.exact_map_iff** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h : S.LeftHomologyData)   (F : CategoryTheo
ry.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map 
F).HasHomology],   (S.map F).Exact ↔ CategoryTheory.Limits.IsZero (F.obj h.H)
参数：h : S.LeftHomologyData；F : CategoryTheory.Functor C D；S.map F；S.map F；F.obj h
.H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma LeftHomologyData.exact_map_iff (h : S.LeftHomologyData) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map F).HasHomology] :
    (S.map F).Exact ↔ IsZero (F.obj h.H) :=
  (h.map F).exact_iff
/-
**CategoryTheory.ShortComplex.RightHomologyData.exact_map_iff** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C} (h : S.RightHomologyData)   (F : CategoryThe
ory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map
 F).HasHomology],   (S.map F).Exact ↔ CategoryTheory.Limits.IsZero (F.obj h.H)
参数：h : S.RightHomologyData；F : CategoryTheory.Functor C D；S.map F；S.map F；F.obj 
h.H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma RightHomologyData.exact_map_iff (h : S.RightHomologyData) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map F).HasHomology] :
    (S.map F).Exact ↔ IsZero (F.obj h.H) :=
  (h.map F).exact_iff
/-
**CategoryTheory.ShortComplex.Exact.map_of_preservesLeftHomologyOf** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C},   S.Exact →     ∀ (F : CategoryTheory.Funct
or C D) [inst_4 : F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]       
[(S.map F).HasHomology], (S.map F).Exact
参数：F : CategoryTheory.Functor C D；S.map F；S.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_map_iff`：∀ {C : Type 
u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
lemma Exact.map_of_preservesLeftHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
  have := h.hasHomology
  rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero] at h
  rw [S.leftHomologyData.exact_map_iff F, IsZero.iff_id_eq_zero,
    ← F.map_id, h, F.map_zero]
/-
**CategoryTheory.ShortComplex.Exact.map_of_preservesRightHomologyOf** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C},   S.Exact →     ∀ (F : CategoryTheory.Funct
or C D) [inst_4 : F.PreservesZeroMorphisms] [F.PreservesRightHomologyOf S]      
 [(S.map F).HasHomology], (S.map F).Exact
参数：F : CategoryTheory.Functor C D；S.map F；S.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_map_iff`：∀ {C : Type
 u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.isPreservedBy_of_preserves
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
lemma Exact.map_of_preservesRightHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesRightHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
  have : S.HasHomology := h.hasHomology
  rw [S.rightHomologyData.exact_iff, IsZero.iff_id_eq_zero] at h
  rw [S.rightHomologyData.exact_map_iff F, IsZero.iff_id_eq_zero,
    ← F.map_id, h, F.map_zero]
/-
**CategoryTheory.ShortComplex.Exact.map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C},   S.Exact →     ∀ (F : CategoryTheory.Funct
or C D) [inst_4 : F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]       
[F.PreservesRightHomologyOf S], (S.map F).Exact
参数：F : CategoryTheory.Functor C D；S.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.map_of_preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma Exact.map (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] : (S.map F).Exact := by
  have := h.hasHomology
  exact h.map_of_preservesLeftHomologyOf F

variable (S)
/-
**CategoryTheory.ShortComplex.exact_map_iff_of_faithful** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_map_iff_of_faithful [S.HasHomology] (F : C ⥤ D) [F.PreservesZeroMorp
hisms] [F.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S] [F.Faithful]
 : (S.map F).Exact ↔ S.Exact
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_preserves`
：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.map_H`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma exact_map_iff_of_faithful [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [F.Faithful] :
    (S.map F).Exact ↔ S.Exact := by
  constructor
  · intro h
    rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
    rw [(S.leftHomologyData.map F).exact_iff, IsZero.iff_id_eq_zero,
      LeftHomologyData.map_H] at h
    apply F.map_injective
    rw [F.map_id, F.map_zero, h]
  · intro h
    exact h.map F

variable {S}

@[reassoc]
/-
**CategoryTheory.ShortComplex.Exact.comp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
  S.Exact →     ∀ {X Y : C} {a : X ⟶ S.X₂},       CategoryTheory.CategoryStruct.
comp a S.g = 0 →         ∀ {b : S.X₂ ⟶ Y}, CategoryTheory.CategoryStruct.comp S.
f b = 0 → CategoryTheory.CategoryStruct.comp a b = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用引理 `CategoryTheory.ShortComplex.p_descOpcycles`：p_descOpcycles : S.pOpcycles
 ≫ S.descOpcycles k hk = k
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_iCycles_pOpcycles_zero`：exact_iff_
iCycles_pOpcycles_zero [S.HasHomology] : S.Exact ↔ S.iCycles ≫ S.pOpcycles = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma Exact.comp_eq_zero (h : S.Exact) {X Y : C} {a : X ⟶ S.X₂} (ha : a ≫ S.g = 0)
    {b : S.X₂ ⟶ Y} (hb : S.f ≫ b = 0) : a ≫ b = 0 := by
  have := h.hasHomology
  have eq := h
  rw [exact_iff_iCycles_pOpcycles_zero] at eq
  rw [← S.liftCycles_i a ha, ← S.p_descOpcycles b hb, assoc, reassoc_of% eq,
    zero_comp, comp_zero]
/-
**CategoryTheory.ShortComplex.Exact.isZero_of_both_zeros** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
S.Exact → S.f = 0 → S.g = 0 → CategoryTheory.Limits.IsZero S.X₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.exact_iff`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma Exact.isZero_of_both_zeros (ex : S.Exact) (hf : S.f = 0) (hg : S.g = 0) :
    IsZero S.X₂ :=
  (ShortComplex.HomologyData.ofZeros S hf hg).exact_iff.1 ex

/-- In an exact short complex, if the two outer objects are zero objects, then so is the
middle object. -/
/-
**CategoryTheory.ShortComplex.Exact.isZero_of_both_isZero** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
  S.Exact → CategoryTheory.Limits.IsZero S.X₁ → CategoryTheory.Limits.IsZero S.X
₃ → CategoryTheory.Limits.IsZero S.X₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.isZero_of_both_zeros`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_src`：eq_zero_of_src {X Y : C} (o
 : IsZero X) (f : X ⟶ Y) : f = 0
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_tgt`：eq_zero_of_tgt {X Y : C} (o
 : IsZero Y) (f : X ⟶ Y) : f = 0

--- 原说明 ---
In an exact short complex, if the two outer objects are zero objects, then so is
 the
middle object.
-/
lemma Exact.isZero_of_both_isZero (ex : S.Exact) (hX₁ : IsZero S.X₁) (hX₃ : IsZero S.X₃) :
    IsZero S.X₂ :=
  ex.isZero_of_both_zeros (hX₁.eq_zero_of_src _) (hX₃.eq_zero_of_tgt _)

end

section Preadditive

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

/-
**CategoryTheory.ShortComplex.exact_iff_mono** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：exact_iff_mono [HasZeroObject C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
参数：hf : S.f = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.isIso_pOpcycles`：isIso_pOpcycles (hf : S.f =
 0) : IsIso S.pOpcycles
· 使用引理 `CategoryTheory.Preadditive.mono_of_isZero_kernel'`：mono_of_isZero_kernel
' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) (h : IsZero c.pt) : 
Mono f
· 使用引理 `CategoryTheory.ShortComplex.homologyι_comp_fromOpcycles`：homologyι_comp_
fromOpcycles : S.homologyι ≫ S.fromOpcycles = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.p_fromOpcycles`：p_fromOpcycles : S.pOpcycles
 ≫ S.fromOpcycles = S.g
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.exact_iff`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma exact_iff_mono [HasZeroObject C] (hf : S.f = 0) :
    S.Exact ↔ Mono S.g := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_pOpcycles hf
    have := mono_of_isZero_kernel' _ S.homologyIsKernel h
    rw [← S.p_fromOpcycles]
    apply mono_comp
  · intro
    rw [(HomologyData.ofIsLimitKernelFork S hf _
      (KernelFork.IsLimit.ofMonoOfIsZero (KernelFork.ofι (0 : 0 ⟶ S.X₂) zero_comp)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C
/-
**CategoryTheory.ShortComplex.exact_iff_epi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：exact_iff_epi [HasZeroObject C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
参数：hg : S.g = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.isIso_iCycles`：isIso_iCycles (hg : S.g = 0) 
: IsIso S.iCycles
· 使用引理 `CategoryTheory.Preadditive.epi_of_isZero_cokernel'`：epi_of_isZero_cokern
el' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c) (h : IsZero 
c.pt) : Epi f
· 使用引理 `CategoryTheory.ShortComplex.toCycles_comp_homologyπ`：toCycles_comp_homol
ogyπ : S.toCycles ≫ S.homologyπ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.exact_iff`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma exact_iff_epi [HasZeroObject C] (hg : S.g = 0) :
    S.Exact ↔ Epi S.f := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_iCycles hg
    have : Epi S.toCycles := epi_of_isZero_cokernel' _ S.homologyIsCokernel h
    rw [← S.toCycles_i]
    apply epi_comp
  · intro
    rw [(HomologyData.ofIsColimitCokernelCofork S hg _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

variable {S}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.Exact.epi_f'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → ∀ 
(h : S.LeftHomologyData), CategoryTheory.Epi h.f'
参数：h : S.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Preadditive.epi_of_isZero_cokernel'`：epi_of_isZero_cokern
el' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c) (h : IsZero 
c.pt) : Epi f
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wπ`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma Exact.epi_f' (hS : S.Exact) (h : LeftHomologyData S) : Epi h.f' :=
  epi_of_isZero_cokernel' _ h.hπ (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.Exact.mono_g'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → ∀ 
(h : S.RightHomologyData), CategoryTheory.Mono h.g'
参数：h : S.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Preadditive.mono_of_isZero_kernel'`：mono_of_isZero_kernel
' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) (h : IsZero c.pt) : 
Mono f
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.wp`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.wι`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma Exact.mono_g' (hS : S.Exact) (h : RightHomologyData S) : Mono h.g' :=
  mono_of_isZero_kernel' _ h.hι (by
    have := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)
/-
**CategoryTheory.ShortComplex.Exact.epi_toCycles** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → ∀ 
[inst_2 : S.HasLeftHomology], CategoryTheory.Epi S.toCycles
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f'`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
-/
lemma Exact.epi_toCycles (hS : S.Exact) [S.HasLeftHomology] : Epi S.toCycles :=
  hS.epi_f' _
/-
**CategoryTheory.ShortComplex.Exact.mono_fromOpcycles** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → ∀ 
[inst_2 : S.HasRightHomology], CategoryTheory.Mono S.fromOpcycles
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g'`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
-/
lemma Exact.mono_fromOpcycles (hS : S.Exact) [S.HasRightHomology] : Mono S.fromOpcycles :=
  hS.mono_g' _
/-
**CategoryTheory.ShortComplex.LeftHomologyData.exact_iff_epi_f'** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C} [S.HasHomolog
y] (h : S.LeftHomologyData), S.Exact ↔ CategoryTheory.Epi h.f'
参数：h : S.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f'`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instEpiπ`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_π`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.exact_iff_epi_f' [S.HasHomology] (h : LeftHomologyData S) :
    S.Exact ↔ Epi h.f' := by
  constructor
  · intro hS
    exact hS.epi_f' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_epi h.π, ← cancel_epi h.f',
      comp_id, h.f'_π, comp_zero]
/-
**CategoryTheory.ShortComplex.RightHomologyData.exact_iff_mono_g'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C} [S.HasHomolog
y] (h : S.RightHomologyData), S.Exact ↔ CategoryTheory.Mono h.g'
参数：h : S.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g'`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instMonoι`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.ι_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.exact_iff_mono_g' [S.HasHomology] (h : RightHomologyData S) :
    S.Exact ↔ Mono h.g' := by
  constructor
  · intro hS
    exact hS.mono_g' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_mono h.ι, ← cancel_mono h.g',
      id_comp, h.ι_g', zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Given an exact short complex `S` and a limit kernel fork `kf` for `S.g`, this is the
left homology data for `S` with `K := kf.pt` and `H := 0`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {S : CategoryTheory.ShortComplex C}
 →         S.Exact →           [CategoryTheory.Limits.HasZeroObject C] →        
     (kf : CategoryTheory.Limits.KernelFork S.g) → CategoryTheory.Limits.IsLimit
 kf → S.LeftHomologyData
参数：kf : CategoryTheory.Limits.KernelFork S.g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
Given an exact short complex `S` and a limit kernel fork `kf` for `S.g`, this is
 the
left homology data for `S` with `K := kf.pt` and `H := 0`.
-/
noncomputable def Exact.leftHomologyDataOfIsLimitKernelFork
    (hS : S.Exact) [HasZeroObject C] (kf : KernelFork S.g) (hkf : IsLimit kf) :
    S.LeftHomologyData where
  K := kf.pt
  H := 0
  i := kf.ι
  π := 0
  wi := kf.condition
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := comp_zero
  hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff ?_).1
      hS.epi_toCycles
    refine Arrow.isoMk (Iso.refl _)
      (IsLimit.conePointUniqueUpToIso S.cyclesIsKernel hkf) ?_
    apply Fork.IsLimit.hom_ext hkf
    simp [IsLimit.conePointUniqueUpToIso]) (isZero_zero C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an exact short complex `S` and a colimit cokernel cofork `cc` for `S.f`, this is the
right homology data for `S` with `Q := cc.pt` and `H := 0`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {S : CategoryTheory.ShortComplex C}
 →         S.Exact →           [CategoryTheory.Limits.HasZeroObject C] →        
     (cc : CategoryTheory.Limits.CokernelCofork S.f) → CategoryTheory.Limits.IsC
olimit cc → S.RightHomologyData
参数：cc : CategoryTheory.Limits.CokernelCofork S.f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
Given an exact short complex `S` and a colimit cokernel cofork `cc` for `S.f`, t
his is the
right homology data for `S` with `Q := cc.pt` and `H := 0`.
-/
noncomputable def Exact.rightHomologyDataOfIsColimitCokernelCofork
    (hS : S.Exact) [HasZeroObject C] (cc : CokernelCofork S.f) (hcc : IsColimit cc) :
    S.RightHomologyData where
  Q := cc.pt
  H := 0
  p := cc.π
  ι := 0
  wp := cc.condition
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := zero_comp
  hι := KernelFork.IsLimit.ofMonoOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
      hS.mono_fromOpcycles
    refine Arrow.isoMk (IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel)
      (Iso.refl _) ?_
    apply Cofork.IsColimit.hom_ext hcc
    simp [IsColimit.coconePointUniqueUpToIso]) (isZero_zero C)

variable (S)
/-
**CategoryTheory.ShortComplex.exact_iff_epi_toCycles** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_epi_toCycles [S.HasHomology] : S.Exact ↔ Epi S.toCycles
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff_epi_f'`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.P
readditive C]   {S : CategoryTheory.ShortComplex C}…
-/
lemma exact_iff_epi_toCycles [S.HasHomology] : S.Exact ↔ Epi S.toCycles :=
  S.leftHomologyData.exact_iff_epi_f'
/-
**CategoryTheory.ShortComplex.exact_iff_mono_fromOpcycles** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_mono_fromOpcycles [S.HasHomology] : S.Exact ↔ Mono S.fromOpcycle
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff_mono_g'`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory
.Preadditive C]   {S : CategoryTheory.ShortComplex C}…
-/
lemma exact_iff_mono_fromOpcycles [S.HasHomology] : S.Exact ↔ Mono S.fromOpcycles :=
  S.rightHomologyData.exact_iff_mono_g'

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_epi_kernel_lift [S.HasHomology] [HasKernel S.g] : S.Exact ↔ Epi 
(kernel.lift S.g S.f S.zero)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi_toCycles`：exact_iff_epi_toCycl
es [S.HasHomology] : S.Exact ↔ Epi S.toCycles
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exact_iff_epi_kernel_lift [S.HasHomology] [HasKernel S.g] :
    S.Exact ↔ Epi (kernel.lift S.g S.f S.zero) := by
  rw [exact_iff_epi_toCycles]
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) S.cyclesIsoKernel (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.exact_iff_mono_cokernel_desc** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_mono_cokernel_desc [S.HasHomology] [HasCokernel S.f] : S.Exact ↔
 Mono (cokernel.desc S.f S.g S.zero)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono_fromOpcycles`：exact_iff_mono_
fromOpcycles [S.HasHomology] : S.Exact ↔ Mono S.fromOpcycles
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用引理 `CategoryTheory.ShortComplex.p_fromOpcycles`：p_fromOpcycles : S.pOpcycles
 ≫ S.fromOpcycles = S.g
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exact_iff_mono_cokernel_desc [S.HasHomology] [HasCokernel S.f] :
    S.Exact ↔ Mono (cokernel.desc S.f S.g S.zero) := by
  rw [exact_iff_mono_fromOpcycles]
  refine (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (Iso.symm ?_)
  exact Arrow.isoMk S.opcyclesIsoCokernel.symm (Iso.refl _) (by cat_disch)

variable {S} in
/-
**CategoryTheory.ShortComplex.Exact.mono_cokernelDesc** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C} [S.HasHomolog
y] [inst_3 : CategoryTheory.Limits.HasCokernel S.f],   S.Exact → CategoryTheory.
Mono (CategoryTheory.Limits.cokernel.desc S.f S.g ⋯)
参数：CategoryTheory.Limits.cokernel.desc S.f S.g ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono_cokernel_desc`：exact_iff_mono
_cokernel_desc [S.HasHomology] [HasCokernel S.f] : S.Exact ↔ Mono (cokernel.desc
 S.f S.g S.zero)
-/
lemma Exact.mono_cokernelDesc [S.HasHomology] [HasCokernel S.f] (hS : S.Exact) :
    Mono (Limits.cokernel.desc S.f S.g S.zero) :=
  S.exact_iff_mono_cokernel_desc.1 hS

variable {S} in
/-
**CategoryTheory.ShortComplex.Exact.epi_kernelLift** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C} [S.HasHomolog
y] [inst_3 : CategoryTheory.Limits.HasKernel S.g],   S.Exact → CategoryTheory.Ep
i (CategoryTheory.Limits.kernel.lift S.g S.f ⋯)
参数：CategoryTheory.Limits.kernel.lift S.g S.f ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift`：exact_iff_epi_ker
nel_lift [S.HasHomology] [HasKernel S.g] : S.Exact ↔ Epi (kernel.lift S.g S.f S.
zero)
-/
lemma Exact.epi_kernelLift [S.HasHomology] [HasKernel S.g] (hS : S.Exact) :
    Epi (Limits.kernel.lift S.g S.f S.zero) :=
  S.exact_iff_epi_kernel_lift.1 hS
/-
**CategoryTheory.ShortComplex.QuasiIso.exact_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ShortComplex.QuasiIso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶
 S₂) [inst_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology]   [CategoryTheory.Short
Complex.QuasiIso φ], S₁.Exact ↔ S₂.Exact
参数：φ : S₁ ⟶ S₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
· 使用定理 `CategoryTheory.ShortComplex.QuasiIso.isIso`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {S₁ S₂ : CategoryTheory…
-/
lemma QuasiIso.exact_iff {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [QuasiIso φ] : S₁.Exact ↔ S₂.Exact := by
  simp only [exact_iff_isZero_homology]
  exact Iso.isZero_iff (asIso (homologyMap φ))
/-
**CategoryTheory.ShortComplex.exact_of_f_is_kernel** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：exact_of_f_is_kernel (hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomo
logy] : S.Exact
参数：hS : IsLimit (KernelFork.ofι S.f S.zero)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi_toCycles`：exact_iff_epi_toCycl
es [S.HasHomology] : S.Exact ↔ Epi S.toCycles
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.lift_ι`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s t : CategoryTheory.Limits
.Fork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…
· 使用定理 `CategoryTheory.instIsRegularEpiOfIsSplitEpi`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplitEp
i f],   CategoryTheory.IsRegularE…
-/
lemma exact_of_f_is_kernel (hS : IsLimit (KernelFork.ofι S.f S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles :=
    ⟨⟨{ section_ := hS.lift (KernelFork.ofι S.iCycles S.iCycles_g)
        id := by
          rw [← cancel_mono S.iCycles, assoc, toCycles_i, id_comp]
          exact Fork.IsLimit.lift_ι hS }⟩⟩
  infer_instance
/-
**CategoryTheory.ShortComplex.exact_of_g_is_cokernel** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：exact_of_g_is_cokernel (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S
.HasHomology] : S.Exact
参数：hS : IsColimit (CokernelCofork.ofπ S.g S.zero)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono_fromOpcycles`：exact_iff_mono_
fromOpcycles [S.HasHomology] : S.Exact ↔ Mono S.fromOpcycles
· 使用引理 `CategoryTheory.ShortComplex.f_pOpcycles`：f_pOpcycles : S.f ≫ S.pOpcycles
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.p_fromOpcycles_assoc`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.π_desc`：∀ {C : Type u} {X Y : C} 
[inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   {s t : CategoryTheory.
Limits.Cofork f g} (hs : CategoryTh…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
-/
lemma exact_of_g_is_cokernel (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_mono_fromOpcycles]
  have : IsSplitMono S.fromOpcycles :=
    ⟨⟨{ retraction := hS.desc (CokernelCofork.ofπ S.pOpcycles S.f_pOpcycles)
        id := by
          rw [← cancel_epi S.pOpcycles, p_fromOpcycles_assoc, comp_id]
          exact Cofork.IsColimit.π_desc hS }⟩⟩
  infer_instance

variable {S}
/-
**CategoryTheory.ShortComplex.Exact.mono_g** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → S.
f = 0 → CategoryTheory.Mono S.g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_toCycles`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]  
 {S : CategoryTheory.ShortComplex C}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `CategoryTheory.Preadditive.mono_of_cancel_zero`：mono_of_cancel_zero {Q R
 : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) : Mono f 
where right_cancellation
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
-/
lemma Exact.mono_g (hS : S.Exact) (hf : S.f = 0) : Mono S.g := by
  have := hS.hasHomology
  have := hS.epi_toCycles
  have : S.iCycles = 0 := by rw [← cancel_epi S.toCycles, comp_zero, toCycles_i, hf]
  apply Preadditive.mono_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.liftCycles_i x₂ hx₂, this, comp_zero]
/-
**CategoryTheory.ShortComplex.Exact.epi_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → S.
g = 0 → CategoryTheory.Epi S.f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_fromOpcycles`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive
 C]   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ShortComplex.p_fromOpcycles`：p_fromOpcycles : S.pOpcycles
 ≫ S.fromOpcycles = S.g
· 使用定理 `CategoryTheory.Preadditive.epi_of_cancel_zero`：epi_of_cancel_zero {P Q :
 C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0) : Epi f
· 使用引理 `CategoryTheory.ShortComplex.p_descOpcycles`：p_descOpcycles : S.pOpcycles
 ≫ S.descOpcycles k hk = k
-/
lemma Exact.epi_f (hS : S.Exact) (hg : S.g = 0) : Epi S.f := by
  have := hS.hasHomology
  have := hS.mono_fromOpcycles
  have : S.pOpcycles = 0 := by rw [← cancel_mono S.fromOpcycles, zero_comp, p_fromOpcycles, hg]
  apply Preadditive.epi_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.p_descOpcycles x₂ hx₂, this, zero_comp]
/-
**CategoryTheory.ShortComplex.Exact.mono_g_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → (C
ategoryTheory.Mono S.g ↔ S.f = 0)
参数：CategoryTheory.Mono S.g ↔ S.f = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
-/
lemma Exact.mono_g_iff (hS : S.Exact) : Mono S.g ↔ S.f = 0 := by
  constructor
  · intro
    rw [← cancel_mono S.g, zero, zero_comp]
  · exact hS.mono_g
/-
**CategoryTheory.ShortComplex.Exact.epi_f_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}, S.Exact → (C
ategoryTheory.Epi S.f ↔ S.g = 0)
参数：CategoryTheory.Epi S.f ↔ S.g = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : C
ategoryTheory.ShortComplex C}…
-/
lemma Exact.epi_f_iff (hS : S.Exact) : Epi S.f ↔ S.g = 0 := by
  constructor
  · intro
    rw [← cancel_epi S.f, zero, comp_zero]
  · exact hS.epi_f
/-
**CategoryTheory.ShortComplex.Exact.isZero_X** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Exact.isZero_X₂ (hS : S.Exact) (hf : S.f = 0) (hg : S.g = 0) : IsZero S.X₂ := by
  have := hS.mono_g hf
  rw [IsZero.iff_id_eq_zero, ← cancel_mono S.g, hg, comp_zero, comp_zero]
/-
**CategoryTheory.ShortComplex.Exact.isZero_X** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Exact.isZero_X₂_iff (hS : S.Exact) : IsZero S.X₂ ↔ S.f = 0 ∧ S.g = 0 := by
  constructor
  · intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩
  · rintro ⟨hf, hg⟩
    exact hS.isZero_X₂ hf hg

variable (S)

/-- A splitting for a short complex `S` consists of the data of a retraction `r : X₂ ⟶ X₁`
of `S.f` and section `s : X₃ ⟶ X₂` of `S.g` which satisfy `r ≫ S.f + S.g ≫ s = 𝟙 _` -/
/-
**CategoryTheory.ShortComplex.Splitting** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheor
y.ShortComplex`。
形式化陈述：Splitting (S : ShortComplex C) where /-- a retraction of `S.f` -/ r : S.X₂
 ⟶ S.X₁ /-- a section of `S.g` -/ s : S.X₃ ⟶ S.X₂ /-- the condition that `r` is 
a retraction of `S.f` -/ f_r : S.f ≫ r = 𝟙 _
参数：S : ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A splitting for a short complex `S` consists of the data of a retraction `r : X₂
 ⟶ X₁`
of `S.f` and section `s : X₃ ⟶ X₂` of `S.g` which satisfy `r ≫ S.f + S.g ≫ s = 𝟙
 _`
-/
structure Splitting (S : ShortComplex C) where
  /-- a retraction of `S.f` -/
  r : S.X₂ ⟶ S.X₁
  /-- a section of `S.g` -/
  s : S.X₃ ⟶ S.X₂
  /-- the condition that `r` is a retraction of `S.f` -/
  f_r : S.f ≫ r = 𝟙 _ := by cat_disch
  /-- the condition that `s` is a section of `S.g` -/
  s_g : s ≫ S.g = 𝟙 _ := by cat_disch
  /-- the compatibility between the given section and retraction -/
  id : r ≫ S.f + S.g ≫ s = 𝟙 _ := by cat_disch

namespace Splitting

attribute [reassoc (attr := simp)] f_r s_g

variable {S}

@[reassoc]
/-
**CategoryTheory.ShortComplex.Splitting.r_f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex.Splitting`。
形式化陈述：r_f (s : S.Splitting) : s.r ≫ S.f = 𝟙 _ - S.g ≫ s.s
参数：s : S.Splitting。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.Splitting.id`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
lemma r_f (s : S.Splitting) : s.r ≫ S.f = 𝟙 _ - S.g ≫ s.s := by rw [← s.id, add_sub_cancel_right]

@[reassoc]
/-
**CategoryTheory.ShortComplex.Splitting.g_s** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex.Splitting`。
形式化陈述：g_s (s : S.Splitting) : S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f
参数：s : S.Splitting。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.Splitting.id`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
lemma g_s (s : S.Splitting) : S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f := by rw [← s.id, add_sub_cancel_left]

/-- Given a splitting of a short complex `S`, this shows that `S.f` is a split monomorphism. -/
/-
**CategoryTheory.ShortComplex.Splitting.splitMono_f** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex.Splitting`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {S : CategoryTheory.ShortComplex C}
 → S.Splitting → CategoryTheory.SplitMono S.f
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Splitting.f_r`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…

--- 原说明 ---
Given a splitting of a short complex `S`, this shows that `S.f` is a split monom
orphism.
-/
@[simps] def splitMono_f (s : S.Splitting) : SplitMono S.f := ⟨s.r, s.f_r⟩
/-
**CategoryTheory.ShortComplex.Splitting.isSplitMono_f** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex.Splitting`。
形式化陈述：isSplitMono_f (s : S.Splitting) : IsSplitMono S.f
参数：s : S.Splitting。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a splitting of a short complex `S`, this shows that `S.f` is a split monom
orphism.
-/
lemma isSplitMono_f (s : S.Splitting) : IsSplitMono S.f := ⟨⟨s.splitMono_f⟩⟩
/-
**CategoryTheory.ShortComplex.Splitting.mono_f** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex.Splitting`。
形式化陈述：mono_f (s : S.Splitting) : Mono S.f
参数：s : S.Splitting。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Splitting.isSplitMono_f`：isSplitMono_f (s : 
S.Splitting) : IsSplitMono S.f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
-/
lemma mono_f (s : S.Splitting) : Mono S.f := by
  have := s.isSplitMono_f
  infer_instance

/-- Given a splitting of a short complex `S`, this shows that `S.g` is a split epimorphism. -/
/-
**CategoryTheory.ShortComplex.Splitting.splitEpi_g** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.Splitting`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {S : CategoryTheory.ShortComplex C}
 → S.Splitting → CategoryTheory.SplitEpi S.g
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Splitting.s_g`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…

--- 原说明 ---
Given a splitting of a short complex `S`, this shows that `S.g` is a split epimo
rphism.
-/
@[simps] def splitEpi_g (s : S.Splitting) : SplitEpi S.g := ⟨s.s, s.s_g⟩
/-
**CategoryTheory.ShortComplex.Splitting.isSplitEpi_g** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex.Splitting`。
形式化陈述：isSplitEpi_g (s : S.Splitting) : IsSplitEpi S.g
参数：s : S.Splitting。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a splitting of a short complex `S`, this shows that `S.g` is a split epimo
rphism.
-/
lemma isSplitEpi_g (s : S.Splitting) : IsSplitEpi S.g := ⟨⟨s.splitEpi_g⟩⟩
/-
**CategoryTheory.ShortComplex.Splitting.epi_g** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex.Splitting`。
形式化陈述：epi_g (s : S.Splitting) : Epi S.g
参数：s : S.Splitting。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Splitting.isSplitEpi_g`：isSplitEpi_g (s : S.
Splitting) : IsSplitEpi S.g
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…
· 使用定理 `CategoryTheory.instIsRegularEpiOfIsSplitEpi`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplitEp
i f],   CategoryTheory.IsRegularE…
-/
lemma epi_g (s : S.Splitting) : Epi S.g := by
  have := s.isSplitEpi_g
  infer_instance

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.Splitting.s_r** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex.Splitting`。
形式化陈述：s_r (s : S.Splitting) : s.s ≫ s.r = 0
参数：s : S.Splitting。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Splitting.epi_g`：epi_g (s : S.Splitting) : E
pi S.g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.Splitting.g_s_assoc`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  {S : CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.Splitting.f_r`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma s_r (s : S.Splitting) : s.s ≫ s.r = 0 := by
  have := s.epi_g
  simp only [← cancel_epi S.g, comp_zero, g_s_assoc, sub_comp, id_comp,
    assoc, f_r, comp_id, sub_self]
/-
**CategoryTheory.ShortComplex.Splitting.ext_r** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex.Splitting`。
形式化陈述：ext_r (s s' : S.Splitting) (h : s.r = s'.r) : s = s'
参数：s s' : S.Splitting；h : s.r = s'.r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Splitting.epi_g`：epi_g (s : S.Splitting) : E
pi S.g
· 使用定理 `CategoryTheory.ShortComplex.Splitting.id`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma ext_r (s s' : S.Splitting) (h : s.r = s'.r) : s = s' := by
  have := s.epi_g
  have eq := s.id
  rw [← s'.id, h, add_right_inj, cancel_epi S.g] at eq
  cases s
  congr
/-
**CategoryTheory.ShortComplex.Splitting.ext_s** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex.Splitting`。
形式化陈述：ext_s (s s' : S.Splitting) (h : s.s = s'.s) : s = s'
参数：s s' : S.Splitting；h : s.s = s'.s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Splitting.mono_f`：mono_f (s : S.Splitting) :
 Mono S.f
· 使用定理 `CategoryTheory.ShortComplex.Splitting.id`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma ext_s (s s' : S.Splitting) (h : s.s = s'.s) : s = s' := by
  have := s.mono_f
  have eq := s.id
  rw [← s'.id, h, add_left_inj, cancel_mono S.f] at eq
  cases s
  congr

/-- The left homology data on a short complex equipped with a splitting. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.leftHomologyData** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：leftHomologyData [HasZeroObject C] (s : S.Splitting) : LeftHomologyData S
参数：s : S.Splitting。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
The left homology data on a short complex equipped with a splitting.
-/
noncomputable def leftHomologyData [HasZeroObject C] (s : S.Splitting) :
    LeftHomologyData S := by
  have hi := KernelFork.IsLimit.ofι S.f S.zero
    (fun x _ => x ≫ s.r)
    (fun x hx => by simp only [assoc, s.r_f, comp_sub, comp_id,
      sub_eq_self, reassoc_of% hx, zero_comp])
    (fun x _ b hb => by simp only [← hb, assoc, f_r, comp_id])
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 _ := by simp [f']
  have wπ : f' ≫ (0 : S.X₁ ⟶ 0) = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ 0 wπ) := CokernelCofork.IsColimit.ofEpiOfIsZero _
      (by rw [hf']; infer_instance) (isZero_zero _)
  exact
    { K := S.X₁
      H := 0
      i := S.f
      wi := S.zero
      hi := hi
      π := 0
      wπ := wπ
      hπ := hπ }

set_option backward.defeqAttrib.useBackward true in
/-- The right homology data on a short complex equipped with a splitting. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.rightHomologyData** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：rightHomologyData [HasZeroObject C] (s : S.Splitting) : RightHomologyData 
S
参数：s : S.Splitting。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
The right homology data on a short complex equipped with a splitting.
-/
noncomputable def rightHomologyData [HasZeroObject C] (s : S.Splitting) :
    RightHomologyData S := by
  have hp := CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun x _ => s.s ≫ x)
    (fun x hx => by simp only [s.g_s_assoc, sub_comp, id_comp, sub_eq_self, assoc, hx, comp_zero])
    (fun x _ b hb => by simp only [← hb, s.s_g_assoc])
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 _ := by simp [g']
  have wι : (0 : 0 ⟶ S.X₃) ≫ g' = 0 := zero_comp
  have hι : IsLimit (KernelFork.ofι 0 wι) := KernelFork.IsLimit.ofMonoOfIsZero _
      (by rw [hg']; dsimp; infer_instance) (isZero_zero _)
  exact
    { Q := S.X₃
      H := 0
      p := S.g
      wp := S.zero
      hp := hp
      ι := 0
      wι := wι
      hι := hι }

set_option backward.defeqAttrib.useBackward true in
/-- The homology data on a short complex equipped with a splitting. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.homologyData** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.Splitting`。
形式化陈述：homologyData [HasZeroObject C] (s : S.Splitting) : S.HomologyData where le
ft
参数：s : S.Splitting。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology data on a short complex equipped with a splitting.
-/
noncomputable def homologyData [HasZeroObject C] (s : S.Splitting) : S.HomologyData where
  left := s.leftHomologyData
  right := s.rightHomologyData
  iso := Iso.refl 0

/-- A short complex equipped with a splitting is exact. -/
/-
**CategoryTheory.ShortComplex.Splitting.exact** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex.Splitting`。
形式化陈述：exact [HasZeroObject C] (s : S.Splitting) : S.Exact
参数：s : S.Splitting。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
A short complex equipped with a splitting is exact.
-/
lemma exact [HasZeroObject C] (s : S.Splitting) : S.Exact :=
  ⟨s.homologyData, isZero_zero _⟩

/-- If a short complex `S` is equipped with a splitting, then `S.X₁` is the kernel of `S.g`. -/
/-
**CategoryTheory.ShortComplex.Splitting.fIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.Splitting`。
形式化陈述：fIsKernel [HasZeroObject C] (s : S.Splitting) : IsLimit (KernelFork.ofι S.
f S.zero)
参数：s : S.Splitting。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a short complex `S` is equipped with a splitting, then `S.X₁` is the kernel o
f `S.g`.
-/
noncomputable def fIsKernel [HasZeroObject C] (s : S.Splitting) :
    IsLimit (KernelFork.ofι S.f S.zero) :=
  s.homologyData.left.hi

/-- If a short complex `S` is equipped with a splitting, then `S.X₃` is the cokernel of `S.f`. -/
/-
**CategoryTheory.ShortComplex.Splitting.gIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex.Splitting`。
形式化陈述：gIsCokernel [HasZeroObject C] (s : S.Splitting) : IsColimit (CokernelCofor
k.ofπ S.g S.zero)
参数：s : S.Splitting。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a short complex `S` is equipped with a splitting, then `S.X₃` is the cokernel
 of `S.f`.
-/
noncomputable def gIsCokernel [HasZeroObject C] (s : S.Splitting) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  s.homologyData.right.hp

set_option backward.isDefEq.respectTransparency false in
/-- If a short complex `S` has a splitting and `F` is an additive functor, then
`S.map F` also has a splitting. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex.Splitting`。
形式化陈述：map (s : S.Splitting) (F : C ⥤ D) [F.Additive] : (S.map F).Splitting where
 r
参数：s : S.Splitting；F : C ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If a short complex `S` has a splitting and `F` is an additive functor, then
`S.map F` also has a splitting.
-/
def map (s : S.Splitting) (F : C ⥤ D) [F.Additive] : (S.map F).Splitting where
  r := F.map s.r
  s := F.map s.s
  f_r := by
    dsimp [ShortComplex.map]
    rw [← F.map_comp, f_r, F.map_id]
  s_g := by
    dsimp [ShortComplex.map]
    simp only [← F.map_comp, s_g, F.map_id]
  id := by
    dsimp [ShortComplex.map]
    simp only [← F.map_id, ← s.id, Functor.map_comp, Functor.map_add]

/-- A splitting on a short complex induces splittings on isomorphic short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex.Splitting`。
形式化陈述：ofIso {S₁ S₂ : ShortComplex C} (s : S₁.Splitting) (e : S₁ ≅ S₂) : S₂.Split
ting where r
参数：s : S₁.Splitting；e : S₁ ≅ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A splitting on a short complex induces splittings on isomorphic short complexes.
-/
def ofIso {S₁ S₂ : ShortComplex C} (s : S₁.Splitting) (e : S₁ ≅ S₂) : S₂.Splitting where
  r := e.inv.τ₂ ≫ s.r ≫ e.hom.τ₁
  s := e.inv.τ₃ ≫ s.s ≫ e.hom.τ₂
  f_r := by rw [← e.inv.comm₁₂_assoc, s.f_r_assoc, ← comp_τ₁, e.inv_hom_id, id_τ₁]
  s_g := by rw [assoc, assoc, e.hom.comm₂₃, s.s_g_assoc, ← comp_τ₃, e.inv_hom_id, id_τ₃]
  id := by
    have eq := e.inv.τ₂ ≫= s.id =≫ e.hom.τ₂
    rw [id_comp, ← comp_τ₂, e.inv_hom_id, id_τ₂] at eq
    rw [← eq, assoc, assoc, add_comp, assoc, assoc, comp_add,
      e.hom.comm₁₂, e.inv.comm₂₃_assoc]

/-- The obvious splitting of the short complex `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂`. -/
/-
**CategoryTheory.ShortComplex.Splitting.ofHasBinaryBiproduct** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：ofHasBinaryBiproduct (X₁ X₂ : C) [HasBinaryBiproduct X₁ X₂] : Splitting (S
hortComplex.mk (biprod.inl : X₁ ⟶ _) (biprod.snd : _ ⟶ X₂) (by simp)) where r
参数：X₁ X₂ : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious splitting of the short complex `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂`.
-/
noncomputable def ofHasBinaryBiproduct (X₁ X₂ : C) [HasBinaryBiproduct X₁ X₂] :
    Splitting (ShortComplex.mk (biprod.inl : X₁ ⟶ _) (biprod.snd : _ ⟶ X₂) (by simp)) where
  r := biprod.fst
  s := biprod.inr

variable (S)

/-- The obvious splitting of a short complex when `S.X₁` is zero and `S.g` is an isomorphism. -/
/-
**CategoryTheory.ShortComplex.Splitting.ofIsZeroOfIsIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：ofIsZeroOfIsIso (hf : IsZero S.X₁) (hg : IsIso S.g) : Splitting S where r
参数：hf : IsZero S.X₁；hg : IsIso S.g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious splitting of a short complex when `S.X₁` is zero and `S.g` is an iso
morphism.
-/
noncomputable def ofIsZeroOfIsIso (hf : IsZero S.X₁) (hg : IsIso S.g) : Splitting S where
  r := 0
  s := inv S.g
  f_r := hf.eq_of_src _ _

/-- The obvious splitting of a short complex when `S.f` is an isomorphism and `S.X₃` is zero. -/
/-
**CategoryTheory.ShortComplex.Splitting.ofIsIsoOfIsZero** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：ofIsIsoOfIsZero (hf : IsIso S.f) (hg : IsZero S.X₃) : Splitting S where r
参数：hf : IsIso S.f；hg : IsZero S.X₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious splitting of a short complex when `S.f` is an isomorphism and `S.X₃`
 is zero.
-/
noncomputable def ofIsIsoOfIsZero (hf : IsIso S.f) (hg : IsZero S.X₃) : Splitting S where
  r := inv S.f
  s := 0
  s_g := hg.eq_of_src _ _

variable {S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The splitting of the short complex `S.op` deduced from a splitting of `S`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex.Splitting`。
形式化陈述：op (h : Splitting S) : Splitting S.op where r
参数：h : Splitting S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The splitting of the short complex `S.op` deduced from a splitting of `S`.
-/
def op (h : Splitting S) : Splitting S.op where
  r := h.s.op
  s := h.r.op
  f_r := Quiver.Hom.unop_inj (by simp)
  s_g := Quiver.Hom.unop_inj (by simp)
  id := Quiver.Hom.unop_inj (by
    simp only [op_X₂, Opposite.unop_op, op_X₁, op_f, op_X₃, op_g, unop_add, unop_comp,
      Quiver.Hom.unop_op, unop_id, ← h.id]
    abel)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The splitting of the short complex `S.unop` deduced from a splitting of `S`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.unop** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ShortComplex.Splitting`。
形式化陈述：unop {S : ShortComplex Cᵒᵖ} (h : Splitting S) : Splitting S.unop where r
参数：h : Splitting S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The splitting of the short complex `S.unop` deduced from a splitting of `S`.
-/
def unop {S : ShortComplex Cᵒᵖ} (h : Splitting S) : Splitting S.unop where
  r := h.s.unop
  s := h.r.unop
  f_r := Quiver.Hom.op_inj (by simp)
  s_g := Quiver.Hom.op_inj (by simp)
  id := Quiver.Hom.op_inj (by
    simp only [unop_X₂, Opposite.op_unop, unop_X₁, unop_f, unop_X₃, unop_g, op_add,
      op_comp, Quiver.Hom.op_unop, op_id, ← h.id]
    abel)

/-- The isomorphism `S.X₂ ≅ S.X₁ ⊞ S.X₃` induced by a splitting of the short complex `S`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：isoBinaryBiproduct (h : Splitting S) [HasBinaryBiproduct S.X₁ S.X₃] : S.X₂
 ≅ S.X₁ ⊞ S.X₃ where hom
参数：h : Splitting S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S.X₂ ≅ S.X₁ ⊞ S.X₃` induced by a splitting of the short complex
 `S`.
-/
noncomputable def isoBinaryBiproduct (h : Splitting S) [HasBinaryBiproduct S.X₁ S.X₃] :
    S.X₂ ≅ S.X₁ ⊞ S.X₃ where
  hom := biprod.lift h.r S.g
  inv := biprod.desc S.f h.s
  hom_inv_id := by simp [h.id]

end Splitting

section Balanced

variable {S}
variable [Balanced C]

namespace Exact

/-
**CategoryTheory.ShortComplex.Exact.isIso_f'** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex.Exact`。
形式化陈述：isIso_f' (hS : S.Exact) (h : S.LeftHomologyData) [Mono S.f] : IsIso h.f'
参数：hS : S.Exact；h : S.LeftHomologyData。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f'`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
-/
lemma isIso_f' (hS : S.Exact) (h : S.LeftHomologyData) [Mono S.f] :
    IsIso h.f' := by
  have := hS.epi_f' h
  have := mono_of_mono_fac h.f'_i
  exact isIso_of_mono_of_epi h.f'
/-
**CategoryTheory.ShortComplex.Exact.isIso_toCycles** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex.Exact`。
形式化陈述：isIso_toCycles (hS : S.Exact) [Mono S.f] [S.HasLeftHomology] : IsIso S.toC
ycles
参数：hS : S.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Exact.isIso_f'`：isIso_f' (hS : S.Exact) (h :
 S.LeftHomologyData) [Mono S.f] : IsIso h.f'
-/
lemma isIso_toCycles (hS : S.Exact) [Mono S.f] [S.HasLeftHomology] :
    IsIso S.toCycles :=
  hS.isIso_f' _
/-
**CategoryTheory.ShortComplex.Exact.isIso_g'** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex.Exact`。
形式化陈述：isIso_g' (hS : S.Exact) (h : S.RightHomologyData) [Epi S.g] : IsIso h.g'
参数：hS : S.Exact；h : S.RightHomologyData。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g'`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
-/
lemma isIso_g' (hS : S.Exact) (h : S.RightHomologyData) [Epi S.g] :
    IsIso h.g' := by
  have := hS.mono_g' h
  have := epi_of_epi_fac h.p_g'
  exact isIso_of_mono_of_epi h.g'
/-
**CategoryTheory.ShortComplex.Exact.isIso_fromOpcycles** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：isIso_fromOpcycles (hS : S.Exact) [Epi S.g] [S.HasRightHomology] : IsIso S
.fromOpcycles
参数：hS : S.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Exact.isIso_g'`：isIso_g' (hS : S.Exact) (h :
 S.RightHomologyData) [Epi S.g] : IsIso h.g'
-/
lemma isIso_fromOpcycles (hS : S.Exact) [Epi S.g] [S.HasRightHomology] :
    IsIso S.fromOpcycles :=
  hS.isIso_g' _

set_option backward.defeqAttrib.useBackward true in
/-- In a balanced category, if a short complex `S` is exact and `S.f` is a mono, then
`S.X₁` is the kernel of `S.g`. -/
/-
**CategoryTheory.ShortComplex.Exact.fIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex.Exact`。
形式化陈述：fIsKernel (hS : S.Exact) [Mono S.f] : IsLimit (KernelFork.ofι S.f S.zero)
参数：hS : S.Exact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a balanced category, if a short complex `S` is exact and `S.f` is a mono, the
n
`S.X₁` is the kernel of `S.g`.
-/
noncomputable def fIsKernel (hS : S.Exact) [Mono S.f] : IsLimit (KernelFork.ofι S.f S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_toCycles
  exact IsLimit.ofIsoLimit S.cyclesIsKernel
    (Fork.ext (asIso S.toCycles).symm (by simp))
/-
**CategoryTheory.ShortComplex.Exact.map_of_mono_of_preservesKernel** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：map_of_mono_of_preservesKernel (hS : S.Exact) (F : C ⥤ D) [F.PreservesZero
Morphisms] [(S.map F).HasHomology] (_ : Mono S.f) (_ : PreservesLimit (parallelP
air S.g 0) F) : (S.map F).Exact
参数：hS : S.Exact；F : C ⥤ D；S.map F；_ : Mono S.f；_ : PreservesLimit (parallelPair 
S.g 0) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
-/
lemma map_of_mono_of_preservesKernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Mono S.f)
    (_ : PreservesLimit (parallelPair S.g 0) F) :
    (S.map F).Exact :=
  exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel F)

set_option backward.isDefEq.respectTransparency false in
/-- In a balanced category, if a short complex `S` is exact and `S.g` is an epi, then
`S.X₃` is the cokernel of `S.g`. -/
/-
**CategoryTheory.ShortComplex.Exact.gIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ShortComplex.Exact`。
形式化陈述：gIsCokernel (hS : S.Exact) [Epi S.g] : IsColimit (CokernelCofork.ofπ S.g S
.zero)
参数：hS : S.Exact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a balanced category, if a short complex `S` is exact and `S.g` is an epi, the
n
`S.X₃` is the cokernel of `S.g`.
-/
noncomputable def gIsCokernel (hS : S.Exact) [Epi S.g] :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_fromOpcycles
  exact IsColimit.ofIsoColimit S.opcyclesIsCokernel
    (Cofork.ext (asIso S.fromOpcycles) (by simp))
/-
**CategoryTheory.ShortComplex.Exact.map_of_epi_of_preservesCokernel** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：map_of_epi_of_preservesCokernel (hS : S.Exact) (F : C ⥤ D) [F.PreservesZer
oMorphisms] [(S.map F).HasHomology] (_ : Epi S.g) (_ : PreservesColimit (paralle
lPair S.f 0) F) : (S.map F).Exact
参数：hS : S.Exact；F : C ⥤ D；S.map F；_ : Epi S.g；_ : PreservesColimit (parallelPair
 S.f 0) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
-/
lemma map_of_epi_of_preservesCokernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Epi S.g)
    (_ : PreservesColimit (parallelPair S.f 0) F) :
    (S.map F).Exact :=
  exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hS.gIsCokernel F)

/-- If a short complex `S` in a balanced category is exact and such that `S.f` is a mono,
then a morphism `k : A ⟶ S.X₂` such that `k ≫ S.g = 0` lifts to a morphism `A ⟶ S.X₁`. -/
/-
**CategoryTheory.ShortComplex.Exact.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ShortComplex.Exact`。
形式化陈述：lift (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
 A ⟶ S.X₁
参数：hS : S.Exact；k : A ⟶ S.X₂；hk : k ≫ S.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a short complex `S` in a balanced category is exact and such that `S.f` is a 
mono,
then a morphism `k : A ⟶ S.X₂` such that `k ≫ S.g = 0` lifts to a morphism `A ⟶ 
S.X₁`.
-/
noncomputable def lift (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    A ⟶ S.X₁ := hS.fIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.Exact.lift_f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex.Exact`。
形式化陈述：lift_f (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f]
 : hS.lift k hk ≫ S.f = k
参数：hS : S.Exact；k : A ⟶ S.X₂；hk : k ≫ S.g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.lift_ι`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s t : CategoryTheory.Limits
.Fork f g}   (hs : CategoryTheo…
-/
lemma lift_f (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    hS.lift k hk ≫ S.f = k :=
  Fork.IsLimit.lift_ι _
/-
**CategoryTheory.ShortComplex.Exact.lift'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.Exact`。
形式化陈述：lift' (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] 
: exists (l : A ⟶ S.X₁), l ≫ S.f = k
参数：hS : S.Exact；k : A ⟶ S.X₂；hk : k ≫ S.g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.Exact.lift_f`：lift_f (hS : S.Exact) {A : C} 
(k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] : hS.lift k hk ≫ S.f = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift' (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    ∃ (l : A ⟶ S.X₁), l ≫ S.f = k :=
  ⟨hS.lift k hk, by simp⟩

/-- If a short complex `S` in a balanced category is exact and such that `S.g` is an epi,
then a morphism `k : S.X₂ ⟶ A` such that `S.f ≫ k = 0` descends to a morphism `S.X₃ ⟶ A`. -/
/-
**CategoryTheory.ShortComplex.Exact.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ShortComplex.Exact`。
形式化陈述：desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] : 
S.X₃ ⟶ A
参数：hS : S.Exact；k : S.X₂ ⟶ A；hk : S.f ≫ k = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a short complex `S` in a balanced category is exact and such that `S.g` is an
 epi,
then a morphism `k : S.X₂ ⟶ A` such that `S.f ≫ k = 0` descends to a morphism `S
.X₃ ⟶ A`.
-/
noncomputable def desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.X₃ ⟶ A := hS.gIsCokernel.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.Exact.g_desc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex.Exact`。
形式化陈述：g_desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] 
: S.g ≫ hS.desc k hk = k
参数：hS : S.Exact；k : S.X₂ ⟶ A；hk : S.f ≫ k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.π_desc`：∀ {C : Type u} {X Y : C} 
[inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   {s t : CategoryTheory.
Limits.Cofork f g} (hs : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
-/
lemma g_desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.g ≫ hS.desc k hk = k :=
  Cofork.IsColimit.π_desc (hS.gIsCokernel)
/-
**CategoryTheory.ShortComplex.Exact.desc'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.Exact`。
形式化陈述：desc' (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
 exists (l : S.X₃ ⟶ A), S.g ≫ l = k
参数：hS : S.Exact；k : S.X₂ ⟶ A；hk : S.f ≫ k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.Exact.g_desc`：g_desc (hS : S.Exact) {A : C} 
(k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] : S.g ≫ hS.desc k hk = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma desc' (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    ∃ (l : S.X₃ ⟶ A), S.g ≫ l = k :=
  ⟨hS.desc k hk, by simp⟩

end Exact

/-
**CategoryTheory.ShortComplex.mono_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_τ₂_of_exact_of_mono {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.Exact) [Mono S₁.f] [Mono S₂.f] [Mono φ.τ₁] [Mono φ.τ₃] : Mono φ.τ₂ := by
  rw [mono_iff_cancel_zero]
  intro A x₂ hx₂
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ≫ S₁.f = x₂ := ⟨_, h₁.lift_f x₂
    (by simp only [← cancel_mono φ.τ₃, assoc, zero_comp, ← φ.comm₂₃, reassoc_of% hx₂])⟩
  suffices x₁ = 0 by rw [← hx₁, this, zero_comp]
  simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.f, assoc, φ.comm₁₂, zero_comp,
    reassoc_of% hx₁, hx₂]

attribute [local instance] balanced_opposite

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.epi_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epi_τ₂_of_exact_of_epi {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] [Epi φ.τ₁] [Epi φ.τ₃] : Epi φ.τ₂ := by
  have : Mono S₁.op.f := by dsimp; infer_instance
  have : Mono S₂.op.f := by dsimp; infer_instance
  have : Mono (opMap φ).τ₁ := by dsimp; infer_instance
  have : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  have := mono_τ₂_of_exact_of_mono (opMap φ) h₂.op
  exact unop_epi_of_mono (opMap φ).τ₂

variable (S)
/-
**CategoryTheory.ShortComplex.exact_and_mono_f_iff_f_is_kernel** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_and_mono_f_iff_f_is_kernel [S.HasHomology] : S.Exact ∧ Mono S.f ↔ No
nempty (IsLimit (KernelFork.ofι S.f S.zero))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.mono_of_isLimit_fork`：mono_of_isLimit_fork {c : Fo
rk f g} (i : IsLimit c) : Mono (Fork.ι c)
-/
lemma exact_and_mono_f_iff_f_is_kernel [S.HasHomology] :
    S.Exact ∧ Mono S.f ↔ Nonempty (IsLimit (KernelFork.ofι S.f S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.fIsKernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_f_is_kernel hS, mono_of_isLimit_fork hS⟩
/-
**CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_and_epi_g_iff_g_is_cokernel [S.HasHomology] : S.Exact ∧ Epi S.g ↔ No
nempty (IsColimit (CokernelCofork.ofπ S.g S.zero))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.epi_of_isColimit_cofork`：epi_of_isColimit_cofork {
c : Cofork f g} (i : IsColimit c) : Epi c.π
-/
lemma exact_and_epi_g_iff_g_is_cokernel [S.HasHomology] :
    S.Exact ∧ Epi S.g ↔ Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_g_is_cokernel hS, epi_of_isColimit_cofork hS⟩

end Balanced

end Preadditive

section Abelian

variable [Abelian C]

section

variable {X Y : C} (f : X ⟶ Y)

/-- The exact short complex `kernel f ⟶ X ⟶ Y` for any morphism `f : X ⟶ Y`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.kernelSequence** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：kernelSequence : ShortComplex C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exact short complex `kernel f ⟶ X ⟶ Y` for any morphism `f : X ⟶ Y`.
-/
noncomputable def kernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (kernel.condition f)

/-- The exact short complex `X ⟶ Y ⟶ cokernel f` for any morphism `f : X ⟶ Y`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.cokernelSequence** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：cokernelSequence : ShortComplex C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exact short complex `X ⟶ Y ⟶ cokernel f` for any morphism `f : X ⟶ Y`.
-/
noncomputable def cokernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (cokernel.condition f)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (kernelSequence f).f := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (cokernelSequence f).g := by
  dsimp
  infer_instance
/-
**CategoryTheory.ShortComplex.kernelSequence_exact** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：kernelSequence_exact : (kernelSequence f).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma kernelSequence_exact : (kernelSequence f).Exact :=
  exact_of_f_is_kernel _ (kernelIsKernel f)
/-
**CategoryTheory.ShortComplex.cokernelSequence_exact** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：cokernelSequence_exact : (cokernelSequence f).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma cokernelSequence_exact : (cokernelSequence f).Exact :=
  exact_of_g_is_cokernel _ (cokernelIsCokernel f)

end

set_option backward.defeqAttrib.useBackward true in
/-- Given a morphism of short complexes `φ : S₁ ⟶ S₂` in an abelian category, if `S₁.f`
and `S₁.g` are zero (e.g. when `S₁` is of the form `0 ⟶ S₁.X₂ ⟶ 0`) and `S₂.f = 0`
(e.g when `S₂` is of the form `0 ⟶ S₂.X₂ ⟶ S₂.X₃`), then `φ` is a quasi-isomorphism iff
the obvious short complex `S₁.X₂ ⟶ S₂.X₂ ⟶ S₂.X₃` is exact and `φ.τ₂` is a mono. -/
/-
**CategoryTheory.ShortComplex.quasiIso_iff_of_zeros** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_of_zeros {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hf₁ : S₁.f =
 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) : QuasiIso φ ↔ (ShortComplex.mk φ.τ₂ S₂.g 
(by rw [φ.comm₂₃, hg₁, zero_comp])).Exact ∧ Mono φ.τ₂
参数：φ : S₁ ⟶ S₂；hf₁ : S₁.f = 0；hg₁ : S₁.g = 0；hf₂ : S₂.f = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_isIso_liftCycles`：quasiIso_iff_
isIso_liftCycles (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0
) : QuasiIso φ ↔ IsIso (S₂.liftCycles φ.τ₂ (by …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.Exact.lift_f`：lift_f (hS : S.Exact) {A : C} 
(k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] : hS.lift k hk ≫ S.f = k
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
Given a morphism of short complexes `φ : S₁ ⟶ S₂` in an abelian category, if `S₁
.f`
and `S₁.g` are zero (e.g. when `S₁` is of the form `0 ⟶ S₁.X₂ ⟶ 0`) and `S₂.f = 
0`
(e.g when `S₂` is of the form `0 ⟶ S₂.X₂ ⟶ S₂.X₃`), then `φ` is a quasi-isomorph
ism iff
the obvious short complex `S₁.X₂ ⟶ S₂.X₂ ⟶ S₂.X₃` is exact and `φ.τ₂` is a mono.
-/
lemma quasiIso_iff_of_zeros {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) :
    QuasiIso φ ↔
      (ShortComplex.mk φ.τ₂ S₂.g (by rw [φ.comm₂₃, hg₁, zero_comp])).Exact ∧ Mono φ.τ₂ := by
  have w : φ.τ₂ ≫ S₂.g = 0 := by rw [φ.comm₂₃, hg₁, zero_comp]
  rw [quasiIso_iff_isIso_liftCycles φ hf₁ hg₁ hf₂]
  constructor
  · intro h
    have : Mono φ.τ₂ := by
      rw [← S₂.liftCycles_i φ.τ₂ w]
      apply mono_comp
    refine ⟨?_, this⟩
    apply exact_of_f_is_kernel
    exact IsLimit.ofIsoLimit S₂.cyclesIsKernel
      (Fork.ext (asIso (S₂.liftCycles φ.τ₂ w)).symm (by simp))
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁.lift S₂.iCycles (by simp), ?_, ?_⟩⟩
    · rw [← cancel_mono φ.τ₂, assoc, h₁.lift_f, liftCycles_i, id_comp]
    · rw [← cancel_mono S₂.iCycles, assoc, liftCycles_i, h₁.lift_f, id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism of short complexes `φ : S₁ ⟶ S₂` in an abelian category, if `S₁.g = 0`
(e.g when `S₁` is of the form `S₁.X₁ ⟶ S₁.X₂ ⟶ 0`) and both `S₂.f` and `S₂.g` are zero
(e.g when `S₂` is of the form `0 ⟶ S₂.X₂ ⟶ 0`), then `φ` is a quasi-isomorphism iff
the obvious short complex `S₁.X₁ ⟶ S₁.X₂ ⟶ S₂.X₂` is exact and `φ.τ₂` is an epi. -/
/-
**CategoryTheory.ShortComplex.quasiIso_iff_of_zeros'** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_of_zeros' {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hg₁ : S₁.g 
= 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) : QuasiIso φ ↔ (ShortComplex.mk S₁.f φ.τ₂
 (by rw [← φ.comm₁₂, hf₂, comp_zero])).Exact ∧ Epi φ.τ₂
参数：φ : S₁ ⟶ S₂；hg₁ : S₁.g = 0；hf₂ : S₂.f = 0；hg₂ : S₂.g = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_opMap_iff`：quasiIso_opMap_iff (φ : 
S₁ ⟶ S₂) : QuasiIso (opMap φ) ↔ QuasiIso φ
· 使用定理 `CategoryTheory.Limits.op_zero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (X Y : C),  
 Quiver.Hom.op 0 = …
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_of_zeros`：quasiIso_iff_of_zeros
 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ :
 S₂.f = 0) : QuasiIso φ ↔ (ShortComplex…
· 使用引理 `CategoryTheory.ShortComplex.exact_unop_iff`：exact_unop_iff (S : ShortCom
plex Cᵒᵖ) : S.unop.Exact ↔ S.Exact
· 使用定理 `CategoryTheory.op_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {A B : C} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryTheor
y.Mono f.op
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b

--- 原说明 ---
Given a morphism of short complexes `φ : S₁ ⟶ S₂` in an abelian category, if `S₁
.g = 0`
(e.g when `S₁` is of the form `S₁.X₁ ⟶ S₁.X₂ ⟶ 0`) and both `S₂.f` and `S₂.g` ar
e zero
(e.g when `S₂` is of the form `0 ⟶ S₂.X₂ ⟶ 0`), then `φ` is a quasi-isomorphism 
iff
the obvious short complex `S₁.X₁ ⟶ S₁.X₂ ⟶ S₂.X₂` is exact and `φ.τ₂` is an epi.
-/
lemma quasiIso_iff_of_zeros' {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    QuasiIso φ ↔
      (ShortComplex.mk S₁.f φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])).Exact ∧ Epi φ.τ₂ := by
  rw [← quasiIso_opMap_iff, quasiIso_iff_of_zeros]
  rotate_left
  · dsimp
    rw [hg₂, op_zero]
  · dsimp
    rw [hf₂, op_zero]
  · dsimp
    rw [hg₁, op_zero]
  rw [← exact_unop_iff]
  have : Mono φ.τ₂.op ↔ Epi φ.τ₂ :=
    ⟨fun _ => unop_epi_of_mono φ.τ₂.op, fun _ => op_mono_of_epi _⟩
  tauto

variable {S : ShortComplex C}

/-- If `S` is an exact short complex and `f : S.X₂ ⟶ J` is a morphism to an injective object `J`
such that `S.f ≫ f = 0`, this is a morphism `φ : S.X₃ ⟶ J` such that `S.g ≫ φ = f`. -/
/-
**CategoryTheory.ShortComplex.Exact.descToInjective** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Abelian C] →       {S : CategoryTheory.ShortComplex C} →  
       S.Exact →           {J : C} →             (f : S.X₂ ⟶ J) → [CategoryTheor
y.Injective J] → CategoryTheory.CategoryStruct.comp S.f f = 0 → (S.X₃ ⟶ J)
参数：f : S.X₂ ⟶ J；S.X₃ ⟶ J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an exact short complex and `f : S.X₂ ⟶ J` is a morphism to an injectiv
e object `J`
such that `S.f ≫ f = 0`, this is a morphism `φ : S.X₃ ⟶ J` such that `S.g ≫ φ = 
f`.
-/
noncomputable def Exact.descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.X₃ ⟶ J := by
  have := hS.mono_fromOpcycles
  exact Injective.factorThru (S.descOpcycles f hf) S.fromOpcycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
/-
**CategoryTheory.ShortComplex.Exact.comp_descToInjective** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   {S : CategoryTheory.ShortComplex C} (hS : S.Exact) {J
 : C} (f : S.X₂ ⟶ J) [inst_2 : CategoryTheory.Injective J]   (hf : CategoryTheor
y.CategoryStruct.comp S.f f = 0),   CategoryTheory.CategoryStruct.comp S.g (hS.d
escToInjective f hf) = f
参数：hS : S.Exact；f : S.X₂ ⟶ J；hf : CategoryTheory.CategoryStruct.comp S.f f = 0；h
S.descToInjective f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Injective.comp_factorThru`：comp_factorThru {J X Y : C} [I
njective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g
· 使用引理 `CategoryTheory.ShortComplex.p_descOpcycles`：p_descOpcycles : S.pOpcycles
 ≫ S.descOpcycles k hk = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Exact.comp_descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.g ≫ hS.descToInjective f hf = f := by
  dsimp [descToInjective]
  simp only [← p_fromOpcycles, assoc, Injective.comp_factorThru, p_descOpcycles]

/-- If `S` is an exact short complex and `f : P ⟶ S.X₂` is a morphism from a projective object `P`
such that `f ≫ S.g = 0`, this is a morphism `φ : P ⟶ S.X₁` such that `φ ≫ S.f = f`. -/
/-
**CategoryTheory.ShortComplex.Exact.liftFromProjective** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Abelian C] →       {S : CategoryTheory.ShortComplex C} →  
       S.Exact →           {P : C} →             (f : P ⟶ S.X₂) → [CategoryTheor
y.Projective P] → CategoryTheory.CategoryStruct.comp f S.g = 0 → (P ⟶ S.X₁)
参数：f : P ⟶ S.X₂；P ⟶ S.X₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an exact short complex and `f : P ⟶ S.X₂` is a morphism from a project
ive object `P`
such that `f ≫ S.g = 0`, this is a morphism `φ : P ⟶ S.X₁` such that `φ ≫ S.f = 
f`.
-/
noncomputable def Exact.liftFromProjective
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    P ⟶ S.X₁ := by
  have := hS.epi_toCycles
  exact Projective.factorThru (S.liftCycles f hf) S.toCycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
/-
**CategoryTheory.ShortComplex.Exact.liftFromProjective_comp** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   {S : CategoryTheory.ShortComplex C} (hS : S.Exact) {P
 : C} (f : P ⟶ S.X₂) [inst_2 : CategoryTheory.Projective P]   (hf : CategoryTheo
ry.CategoryStruct.comp f S.g = 0),   CategoryTheory.CategoryStruct.comp (hS.lift
FromProjective f hf) S.f = f
参数：hS : S.Exact；f : P ⟶ S.X₂；hf : CategoryTheory.CategoryStruct.comp f S.g = 0；h
S.liftFromProjective f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `CategoryTheory.Projective.factorThru_comp_assoc`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {P X E : C} [inst_1 : CategoryTheory.Projectiv
e P] (f : P ⟶ X)   (e : E ⟶ X) [inst_…
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
-/
lemma Exact.liftFromProjective_comp
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    hS.liftFromProjective f hf ≫ S.f = f := by
  dsimp [liftFromProjective]
  rw [← toCycles_i, Projective.factorThru_comp_assoc, liftCycles_i]


end Abelian

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [Preadditive C] [Preadditive D] [HasZeroObject C]
  [HasZeroObject D] [F.PreservesZeroMorphisms] [F.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk (0 : X ⟶ X) f zero_comp
    exact ((S.map F).exact_iff_mono (by simp [S])).1
      (((S.exact_iff_mono rfl).2 hf).map F)


set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.PreservesEpimorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk f (0 : Y ⟶ Y) comp_zero
    exact ((S.map F).exact_iff_epi (by simp [S])).1
      (((S.exact_iff_epi rfl).2 hf).map F)


end Functor

namespace ShortComplex

namespace Splitting

variable [Preadditive C] [Balanced C]

/-- This is the splitting of a short complex `S` in a balanced category induced by
a section of the morphism `S.g : S.X₂ ⟶ S.X₃` -/
/-
**CategoryTheory.ShortComplex.Splitting.ofExactOfSection** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：ofExactOfSection (S : ShortComplex C) (hS : S.Exact) (s : S.X₃ ⟶ S.X₂) (s_
g : s ≫ S.g = 𝟙 S.X₃) (hf : Mono S.f) : S.Splitting where r
参数：S : ShortComplex C；hS : S.Exact；s : S.X₃ ⟶ S.X₂；s_g : s ≫ S.g = 𝟙 S.X₃；hf : M
ono S.f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the splitting of a short complex `S` in a balanced category induced by
a section of the morphism `S.g : S.X₂ ⟶ S.X₃`
-/
noncomputable def ofExactOfSection (S : ShortComplex C) (hS : S.Exact) (s : S.X₃ ⟶ S.X₂)
    (s_g : s ≫ S.g = 𝟙 S.X₃) (hf : Mono S.f) :
    S.Splitting where
  r := hS.lift (𝟙 S.X₂ - S.g ≫ s) (by simp [s_g])
  s := s
  f_r := by rw [← cancel_mono S.f, assoc, Exact.lift_f, comp_sub, comp_id,
    zero_assoc, zero_comp, sub_zero, id_comp]
  s_g := s_g

/-- This is the splitting of a short complex `S` in a balanced category induced by
a retraction of the morphism `S.f : S.X₁ ⟶ S.X₂` -/
/-
**CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.ShortComplex.Splitting`。
形式化陈述：ofExactOfRetraction (S : ShortComplex C) (hS : S.Exact) (r : S.X₂ ⟶ S.X₁) 
(f_r : S.f ≫ r = 𝟙 S.X₁) (hg : Epi S.g) : S.Splitting where r
参数：S : ShortComplex C；hS : S.Exact；r : S.X₂ ⟶ S.X₁；f_r : S.f ≫ r = 𝟙 S.X₁；hg : E
pi S.g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the splitting of a short complex `S` in a balanced category induced by
a retraction of the morphism `S.f : S.X₁ ⟶ S.X₂`
-/
noncomputable def ofExactOfRetraction (S : ShortComplex C) (hS : S.Exact) (r : S.X₂ ⟶ S.X₁)
    (f_r : S.f ≫ r = 𝟙 S.X₁) (hg : Epi S.g) :
    S.Splitting where
  r := r
  s := hS.desc (𝟙 S.X₂ - r ≫ S.f) (by simp [reassoc_of% f_r])
  f_r := f_r
  s_g := by
    rw [← cancel_epi S.g, Exact.g_desc_assoc, sub_comp, id_comp, assoc, zero,
      comp_zero, sub_zero, comp_id]

end Splitting

end ShortComplex

end CategoryTheory

