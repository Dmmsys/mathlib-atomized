/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Short exact short complexes

A short complex `S : ShortComplex C` is short exact (`S.ShortExact`) when it is exact,
`S.f` is a mono and `S.g` is an epi.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D]

namespace ShortComplex

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/-- A short complex `S` is short exact if it is exact, `S.f` is a mono and `S.g` is an epi. -/
/-
**CategoryTheory.ShortComplex.ShortExact** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ShortComplex C
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A short complex `S` is short exact if it is exact, `S.f` is a mono and `S.g` is 
an epi.
-/
structure ShortExact : Prop where
  exact : S.Exact
  [mono_f : Mono S.f]
  [epi_g : Epi S.g]

variable {S}
/-
**CategoryTheory.ShortComplex.ShortExact.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
S.Exact → CategoryTheory.Mono S.f → CategoryTheory.Epi S.g → S.ShortExact
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ShortExact.mk' (h : S.Exact) (_ : Mono S.f) (_ : Epi S.g) : S.ShortExact where
  exact := h
/-
**CategoryTheory.ShortComplex.shortExact_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：shortExact_of_iso (e : S₁ ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where 
exact
参数：e : S₁ ≅ S₂；h : S₁.ShortExact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
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
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₁`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₃`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.epi_of_epi`：epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ 
g)] : Epi g
-/
lemma shortExact_of_iso (e : S₁ ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where
  exact := exact_of_iso e h.exact
  mono_f := by
    suffices Mono (S₂.f ≫ e.inv.τ₂) by
      exact mono_of_mono _ e.inv.τ₂
    have := h.mono_f
    rw [← e.inv.comm₁₂]
    apply mono_comp
  epi_g := by
    suffices Epi (e.hom.τ₂ ≫ S₂.g) by
      exact epi_of_epi e.hom.τ₂ _
    have := h.epi_g
    rw [e.hom.comm₂₃]
    apply epi_comp
/-
**CategoryTheory.ShortComplex.shortExact_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：shortExact_iff_of_iso (e : S₁ ≅ S₂) : S₁.ShortExact ↔ S₂.ShortExact
参数：e : S₁ ≅ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.shortExact_of_iso`：shortExact_of_iso (e : S₁
 ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where exact
-/
lemma shortExact_iff_of_iso (e : S₁ ≅ S₂) : S₁.ShortExact ↔ S₂.ShortExact := by
  constructor
  · exact shortExact_of_iso e
  · exact shortExact_of_iso e.symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.ShortExact.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C}, 
S.ShortExact → S.op.ShortExact
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.op`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.op_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {A B : C} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryTheor
y.Mono f.op
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
-/
lemma ShortExact.op (h : S.ShortExact) : S.op.ShortExact where
  exact := h.exact.op
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.ShortExact.unop** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex Cᵒᵖ}
, S.ShortExact → S.unop.ShortExact
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.unop`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.unop_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {A B : Cᵒᵖ} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryT
heory.Mono f.unop
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
-/
lemma ShortExact.unop {S : ShortComplex Cᵒᵖ} (h : S.ShortExact) : S.unop.ShortExact where
  exact := h.exact.unop
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

variable (S)
/-
**CategoryTheory.ShortComplex.shortExact_iff_op** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：shortExact_iff_op : S.ShortExact ↔ S.op.ShortExact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.op`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.unop`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {S : CategoryTheory.Sho…
-/
lemma shortExact_iff_op : S.ShortExact ↔ S.op.ShortExact :=
  ⟨ShortExact.op, ShortExact.unop⟩
/-
**CategoryTheory.ShortComplex.shortExact_iff_unop** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：shortExact_iff_unop (S : ShortComplex Cᵒᵖ) : S.ShortExact ↔ S.unop.ShortEx
act
参数：S : ShortComplex Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.ShortComplex.shortExact_iff_op`：shortExact_iff_op : S.Sho
rtExact ↔ S.op.ShortExact
-/
lemma shortExact_iff_unop (S : ShortComplex Cᵒᵖ) : S.ShortExact ↔ S.unop.ShortExact :=
  S.unop.shortExact_iff_op.symm

variable {S}
/-
**CategoryTheory.ShortComplex.ShortExact.map** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C},   S.ShortExact →     ∀ (F : CategoryTheory.
Functor C D) [inst_4 : F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]  
     [F.PreservesRightHomologyOf S] [CategoryTheory.Mono (F.map S.f)] [CategoryT
heory.Epi (F.map S.g)],       (S.map F).ShortExact
参数：F : CategoryTheory.Functor C D；F.map S.f；F.map S.g；S.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma ShortExact.map (h : S.ShortExact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [Mono (F.map S.f)] [Epi (F.map S.g)] :
    (S.map F).ShortExact where
  exact := h.exact.map F
  mono_f := (inferInstance : Mono (F.map S.f))
  epi_g := (inferInstance : Epi (F.map S.g))
/-
**CategoryTheory.ShortComplex.ShortExact.map_of_exact** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] 
{S : CategoryTheory.ShortComplex C},   S.ShortExact →     ∀ (F : CategoryTheory.
Functor C D) [inst_4 : F.PreservesZeroMorphisms]       [CategoryTheory.Limits.Pr
eservesFiniteLimits F] [CategoryTheory.Limits.PreservesFiniteColimits F],       
(S.map F).ShortExact
参数：F : CategoryTheory.Functor C D；S.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma ShortExact.map_of_exact (hS : S.ShortExact)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (S.map F).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map F

end

section Preadditive

variable [Preadditive C]

/-
**CategoryTheory.ShortComplex.ShortExact.isIso_f_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C},   S.ShortExa
ct → ∀ [CategoryTheory.Balanced C], CategoryTheory.IsIso S.f ↔ CategoryTheory.Li
mits.IsZero S.X₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasZeroObject`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.zero_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   (self : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi`：exact_iff_epi [HasZeroObject 
C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
-/
lemma ShortExact.isIso_f_iff {S : ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.f ↔ IsZero S.X₃ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_epi S.g, ← cancel_epi S.f,
      S.zero_assoc, zero_comp]
  · intro hX₃
    have : Epi S.f := (S.exact_iff_epi (hX₃.eq_of_tgt _ _)).1 hS.exact
    apply isIso_of_mono_of_epi
/-
**CategoryTheory.ShortComplex.ShortExact.isIso_g_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C},   S.ShortExa
ct → ∀ [CategoryTheory.Balanced C], CategoryTheory.IsIso S.g ↔ CategoryTheory.Li
mits.IsZero S.X₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasZeroObject`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono`：exact_iff_mono [HasZeroObjec
t C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
-/
lemma ShortExact.isIso_g_iff {S : ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.g ↔ IsZero S.X₁ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono S.f, ← cancel_mono S.g,
      S.zero, zero_comp, assoc, comp_zero]
  · intro hX₁
    have : Mono S.g := (S.exact_iff_mono (hX₁.eq_of_src _ _)).1 hS.exact
    apply isIso_of_mono_of_epi
/-
**CategoryTheory.ShortComplex.isIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso₂_of_shortExact_of_isIso₁₃ [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [IsIso φ.τ₁] [IsIso φ.τ₃] : IsIso φ.τ₂ := by
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  have := mono_τ₂_of_exact_of_mono φ h₁.exact
  have := epi_τ₂_of_exact_of_epi φ h₂.exact
  apply isIso_of_mono_of_epi
/-
**CategoryTheory.ShortComplex.isIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso₂_of_shortExact_of_isIso₁₃' [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (_ : IsIso φ.τ₁) (_ : IsIso φ.τ₃) : IsIso φ.τ₂ :=
  isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂

/-- If `S` is a short exact short complex in a balanced category,
then `S.X₁` is the kernel of `S.g`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.fIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.ShortExact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [CategoryTheory.Balanced C] →      
   {S : CategoryTheory.ShortComplex C} →           S.ShortExact → CategoryTheory
.Limits.IsLimit (CategoryTheory.Limits.KernelFork.ofι S.f ⋯)
参数：CategoryTheory.Limits.KernelFork.ofι S.f ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a short exact short complex in a balanced category,
then `S.X₁` is the kernel of `S.g`.
-/
noncomputable def ShortExact.fIsKernel [Balanced C] {S : ShortComplex C} (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  have := hS.mono_f
  exact hS.exact.fIsKernel

/-- If `S` is a short exact short complex in a balanced category,
then `S.X₃` is the cokernel of `S.f`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.gIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [CategoryTheory.Balanced C] →      
   {S : CategoryTheory.ShortComplex C} →           S.ShortExact → CategoryTheory
.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ S.g ⋯)
参数：CategoryTheory.Limits.CokernelCofork.ofπ S.g ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a short exact short complex in a balanced category,
then `S.X₃` is the cokernel of `S.f`.
-/
noncomputable def ShortExact.gIsCokernel [Balanced C] {S : ShortComplex C} (hS : S.ShortExact) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  have := hS.epi_g
  exact hS.exact.gIsCokernel

/-- Is `S` is an exact short complex and `h : S.HomologyData`, there is
a short exact sequence `0 ⟶ h.left.K ⟶ S.X₂ ⟶ h.right.Q ⟶ 0`. -/
/-
**CategoryTheory.ShortComplex.Exact.shortExact** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C} (hS : S.Exact
) (h : S.HomologyData),   { X₁ := h.left.K, X₂ := S.X₂, X₃ := h.right.Q, f := h.
left.i, g := h.right.p, zero := ⋯ }.ShortExact
参数：hS : S.Exact；h : S.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.exact_iff_i_p_zero`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f'`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g'`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`：exact_iff
_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : S₁.
Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instEpiP`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
Is `S` is an exact short complex and `h : S.HomologyData`, there is
a short exact sequence `0 ⟶ h.left.K ⟶ S.X₂ ⟶ h.right.Q ⟶ 0`.
-/
lemma Exact.shortExact {S : ShortComplex C} (hS : S.Exact) (h : S.HomologyData) :
    (ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)).ShortExact where
  exact := by
    have := hS.epi_f' h.left
    have := hS.mono_g' h.right
    let S' := ShortComplex.mk h.left.i S.g (by simp)
    let S'' := ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)
    let a : S ⟶ S' :=
      { τ₁ := h.left.f'
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let b : S'' ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := h.right.g' }
    rwa [ShortComplex.exact_iff_of_epi_of_isIso_of_mono b,
      ← ShortComplex.exact_iff_of_epi_of_isIso_of_mono a]

/-- A split short complex is short exact. -/
/-
**CategoryTheory.ShortComplex.Splitting.shortExact** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ShortComplex.Splitting`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C} [CategoryTheo
ry.Limits.HasZeroObject C] (s : S.Splitting), S.ShortExact
参数：s : S.Splitting。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Splitting.exact`：exact [HasZeroObject C] (s 
: S.Splitting) : S.Exact
· 使用引理 `CategoryTheory.ShortComplex.Splitting.mono_f`：mono_f (s : S.Splitting) :
 Mono S.f
· 使用引理 `CategoryTheory.ShortComplex.Splitting.epi_g`：epi_g (s : S.Splitting) : E
pi S.g

--- 原说明 ---
A split short complex is short exact.
-/
lemma Splitting.shortExact {S : ShortComplex C} [HasZeroObject C] (s : S.Splitting) :
    S.ShortExact where
  exact := s.exact
  mono_f := s.mono_f
  epi_g := s.epi_g

namespace ShortExact

/-- A choice of splitting for a short exact short complex `S` in a balanced category
such that `S.X₁` is injective. -/
/-
**CategoryTheory.ShortComplex.ShortExact.splittingOfInjective** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：splittingOfInjective {S : ShortComplex C} (hS : S.ShortExact) [Injective S
.X₁] [Balanced C] : S.Splitting
参数：hS : S.ShortExact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of splitting for a short exact short complex `S` in a balanced category
such that `S.X₁` is injective.
-/
noncomputable def splittingOfInjective {S : ShortComplex C} (hS : S.ShortExact)
    [Injective S.X₁] [Balanced C] :
    S.Splitting :=
  have := hS.mono_f
  Splitting.ofExactOfRetraction S hS.exact (Injective.factorThru (𝟙 S.X₁) S.f) (by simp) hS.epi_g

/-- A choice of splitting for a short exact short complex `S` in a balanced category
such that `S.X₃` is projective. -/
/-
**CategoryTheory.ShortComplex.ShortExact.splittingOfProjective** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：splittingOfProjective {S : ShortComplex C} (hS : S.ShortExact) [Projective
 S.X₃] [Balanced C] : S.Splitting
参数：hS : S.ShortExact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of splitting for a short exact short complex `S` in a balanced category
such that `S.X₃` is projective.
-/
noncomputable def splittingOfProjective {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₃] [Balanced C] :
    S.Splitting :=
  have := hS.epi_g
  Splitting.ofExactOfSection S hS.exact (Projective.factorThru (𝟙 S.X₃) S.g) (by simp) hS.mono_f

end ShortExact

end Preadditive

end ShortComplex

end CategoryTheory

