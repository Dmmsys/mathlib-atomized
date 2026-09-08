/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.RightHomology

/-!
# Homology of short complexes

In this file, we shall define the homology of short complexes `S`, i.e. diagrams
`f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`. We shall say that
`[S.HasHomology]` when there exists `h : S.HomologyData`. A homology data
for `S` consists of compatible left/right homology data `left` and `right`. The
left homology data `left` involves an object `left.H` that is a cokernel of the canonical
map `S.X₁ ⟶ K` where `K` is a kernel of `g`. On the other hand, the dual notion `right.H`
is a kernel of the canonical morphism `Q ⟶ S.X₃` when `Q` is a cokernel of `f`.
The compatibility that is required involves an isomorphism `left.H ≅ right.H` which
makes a certain pentagon commute. When such a homology data exists, `S.homology`
shall be defined as `h.left.H` for a chosen `h : S.HomologyData`.

This definition requires very little assumption on the category (only the existence
of zero morphisms). We shall prove that in abelian categories, all short complexes
have homology data.

Note: This definition arose by the end of the Liquid Tensor Experiment which
contained a structure `has_homology` which is quite similar to `S.HomologyData`.
After the category `ShortComplex C` was introduced by J. Riou, A. Topaz suggested
such a structure could be used as a basis for the *definition* of homology.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

namespace ShortComplex

/-- A homology data for a short complex consists of two compatible left and
right homology data -/
/-
**CategoryTheory.ShortComplex.HomologyData** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：HomologyData where /-- a left homology data -/ left : S.LeftHomologyData /
-- a right homology data -/ right : S.RightHomologyData /-- the compatibility is
omorphism relating the two dual notions of `LeftHomologyData` and `RightHomology
Data` -/ iso : left.H ≅ right.H /-- the pentagon relation expressing the compati
bility of the left and right homology data -/ comm : left.π ≫ iso.hom ≫ right.ι 
= left.i ≫ right.p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homology data for a short complex consists of two compatible left and
right homology data
-/
structure HomologyData where
  /-- a left homology data -/
  left : S.LeftHomologyData
  /-- a right homology data -/
  right : S.RightHomologyData
  /-- the compatibility isomorphism relating the two dual notions of
  `LeftHomologyData` and `RightHomologyData` -/
  iso : left.H ≅ right.H
  /-- the pentagon relation expressing the compatibility of the left
  and right homology data -/
  comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p := by cat_disch

attribute [reassoc (attr := simp)] HomologyData.comm

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

/-- A homology map data for a morphism `φ : S₁ ⟶ S₂` where both `S₁` and `S₂` are
equipped with homology data consists of left and right homology map data. -/
/-
**CategoryTheory.ShortComplex.HomologyMapData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {S₁ S₂ : CategoryTheory.Short
Complex C} → (S₁ ⟶ S₂) → S₁.HomologyData → S₂.HomologyData → Type v
参数：S₁ ⟶ S₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homology map data for a morphism `φ : S₁ ⟶ S₂` where both `S₁` and `S₂` are
equipped with homology data consists of left and right homology map data.
-/
structure HomologyMapData where
  /-- a left homology map data -/
  left : LeftHomologyMapData φ h₁.left h₂.left
  /-- a right homology map data -/
  right : RightHomologyMapData φ h₁.right h₂.right

namespace HomologyMapData

variable {φ h₁ h₂}

@[reassoc]
/-
**CategoryTheory.ShortComplex.HomologyMapData.comm** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：comm (h : HomologyMapData φ h₁ h₂) : h.left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫
 h.right.φH
参数：h : HomologyMapData φ h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instEpiπ`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.commπ_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instMonoι`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.comm`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.commi_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.commι`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.comm_assoc`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.commp`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comm (h : HomologyMapData φ h₁ h₂) :
    h.left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫ h.right.φH := by
  simp only [← cancel_epi h₁.left.π, ← cancel_mono h₂.right.ι, assoc,
    LeftHomologyMapData.commπ_assoc, HomologyData.comm, LeftHomologyMapData.commi_assoc,
    RightHomologyMapData.commι, HomologyData.comm_assoc, RightHomologyMapData.commp]
/-
**CategoryTheory.ShortComplex.HomologyMapData.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.ShortComplex.HomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (HomologyMapData φ h₁ h₂) := ⟨by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩
  simp only [mk.injEq, eq_iff_true_of_subsingleton, and_self]⟩
/-
**CategoryTheory.ShortComplex.HomologyMapData.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.ShortComplex.HomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (HomologyMapData φ h₁ h₂) :=
  ⟨⟨default, default⟩⟩
/-
**CategoryTheory.ShortComplex.HomologyMapData.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.ShortComplex.HomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (HomologyMapData φ h₁ h₂) := Unique.mk' _

variable (φ h₁ h₂)

/-- A choice of the (unique) homology map data associated with a morphism
`φ : S₁ ⟶ S₂` where both short complexes `S₁` and `S₂` are equipped with
homology data. -/
/-
**CategoryTheory.ShortComplex.HomologyMapData.homologyMapData** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：homologyMapData : HomologyMapData φ h₁ h₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of the (unique) homology map data associated with a morphism
`φ : S₁ ⟶ S₂` where both short complexes `S₁` and `S₂` are equipped with
homology data.
-/
def homologyMapData : HomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}
/-
**CategoryTheory.ShortComplex.HomologyMapData.congr_left_** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congr_left_φH {γ₁ γ₂ : HomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) :
    γ₁.left.φH = γ₂.left.φH := by rw [eq]

end HomologyMapData

namespace HomologyData

set_option backward.defeqAttrib.useBackward true in
/-- When the first map `S.f` is zero, this is the homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofIsLimitKernelFork** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
 S.HomologyData where left
参数：hf : S.f = 0；c : KernelFork S.g；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the first map `S.f` is zero, this is the homology data on `S` given
by any limit kernel fork of `S.g`
-/
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsLimitKernelFork S hf c hc
  right := RightHomologyData.ofIsLimitKernelFork S hf c hc
  iso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- When the first map `S.f` is zero, this is the homology data on `S` given
by the chosen `kernel S.g` -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofHasKernel** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofHasKernel (hf : S.f = 0) [HasKernel S.g] : S.HomologyData where left
参数：hf : S.f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the first map `S.f` is zero, this is the homology data on `S` given
by the chosen `kernel S.g`
-/
noncomputable def ofHasKernel (hf : S.f = 0) [HasKernel S.g] :
    S.HomologyData where
  left := LeftHomologyData.ofHasKernel S hf
  right := RightHomologyData.ofHasKernel S hf
  iso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- When the second map `S.g` is zero, this is the homology data on `S` given
by any colimit cokernel cofork of `S.f` -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofIsColimitCokernelCofork** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : Is
Colimit c) : S.HomologyData where left
参数：hg : S.g = 0；c : CokernelCofork S.f；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the second map `S.g` is zero, this is the homology data on `S` given
by any colimit cokernel cofork of `S.f`
-/
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsColimitCokernelCofork S hg c hc
  right := RightHomologyData.ofIsColimitCokernelCofork S hg c hc
  iso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- When the second map `S.g` is zero, this is the homology data on `S` given by
the chosen `cokernel S.f` -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofHasCokernel** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofHasCokernel (hg : S.g = 0) [HasCokernel S.f] : S.HomologyData where left
参数：hg : S.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the second map `S.g` is zero, this is the homology data on `S` given by
the chosen `cokernel S.f`
-/
noncomputable def ofHasCokernel (hg : S.g = 0) [HasCokernel S.f] :
    S.HomologyData where
  left := LeftHomologyData.ofHasCokernel S hg
  right := RightHomologyData.ofHasCokernel S hg
  iso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a homology data on S -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofZeros** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.HomologyData where left
参数：hf : S.f = 0；hg : S.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a homology da
ta on S
-/
noncomputable def ofZeros (hf : S.f = 0) (hg : S.g = 0) :
    S.HomologyData where
  left := LeftHomologyData.ofZeros S hf hg
  right := RightHomologyData.ofZeros S hf hg
  iso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a homology data for `S₁` induces a homology data for `S₂`.
The inverse construction is `ofEpiOfIsIsoOfMono'`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiOfIsIsoOfMono** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁) [Epi φ.τ₁] [IsIso φ
.τ₂] [Mono φ.τ₃] : HomologyData S₂ where left
参数：φ : S₁ ⟶ S₂；h : HomologyData S₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂
` is an iso
and `φ.τ₃` is mono, then a homology data for `S₁` induces a homology data for `S
₂`.
The inverse construction is `ofEpiOfIsIsoOfMono'`.
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₂ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono φ h.right
  iso := h.iso

set_option backward.defeqAttrib.useBackward true in
/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a homology data for `S₂` induces a homology data for `S₁`.
The inverse construction is `ofEpiOfIsIsoOfMono`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiOfIsIsoOfMono'** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂) [Epi φ.τ₁] [IsIso 
φ.τ₂] [Mono φ.τ₃] : HomologyData S₁ where left
参数：φ : S₁ ⟶ S₂；h : HomologyData S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂
` is an iso
and `φ.τ₃` is mono, then a homology data for `S₂` induces a homology data for `S
₁`.
The inverse construction is `ofEpiOfIsIsoOfMono`.
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₁ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono' φ h.right
  iso := h.iso

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- If `e : S₁ ≅ S₂` is an isomorphism of short complexes and `h₁ : HomologyData S₁`,
this is the homology data for `S₂` deduced from the isomorphism. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.HomologyData.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.HomologyData`。
形式化陈述：ofIso (e : S₁ ≅ S₂) (h : HomologyData S₁)
参数：e : S₁ ≅ S₂；h : HomologyData S₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : S₁ ≅ S₂` is an isomorphism of short complexes and `h₁ : HomologyData S₁`
,
this is the homology data for `S₂` deduced from the isomorphism.
-/
noncomputable def ofIso (e : S₁ ≅ S₂) (h : HomologyData S₁) :=
  h.ofEpiOfIsIsoOfMono e.hom

variable {S}

set_option backward.defeqAttrib.useBackward true in
/-- A homology data for a short complex `S` induces a homology data for `S.op`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.op** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex.HomologyData`。
形式化陈述：op (h : S.HomologyData) : S.op.HomologyData where left
参数：h : S.HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homology data for a short complex `S` induces a homology data for `S.op`.
-/
def op (h : S.HomologyData) : S.op.HomologyData where
  left := h.right.op
  right := h.left.op
  iso := h.iso.op
  comm := Quiver.Hom.unop_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- A homology data for a short complex `S` in the opposite category
induces a homology data for `S.unop`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.unop** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ShortComplex.HomologyData`。
形式化陈述：unop {S : ShortComplex Cᵒᵖ} (h : S.HomologyData) : S.unop.HomologyData whe
re left
参数：h : S.HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homology data for a short complex `S` in the opposite category
induces a homology data for `S.unop`.
-/
def unop {S : ShortComplex Cᵒᵖ} (h : S.HomologyData) : S.unop.HomologyData where
  left := h.right.unop
  right := h.left.unop
  iso := h.iso.unop
  comm := Quiver.Hom.op_inj (by simp)

end HomologyData

/-- A short complex `S` has homology when there exists a `S.HomologyData` -/
/-
**CategoryTheory.ShortComplex.HasHomology** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ShortComplex C → Pro
p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A short complex `S` has homology when there exists a `S.HomologyData`
-/
class HasHomology : Prop where
  /-- the condition that there exists a homology data -/
  condition : Nonempty S.HomologyData

/-- A chosen `S.HomologyData` for a short complex `S` that has homology -/
/-
**CategoryTheory.ShortComplex.homologyData** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：homologyData [HasHomology S] : S.HomologyData
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.condition`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C}   {S : CategoryTheory.ShortComp…

--- 原说明 ---
A chosen `S.HomologyData` for a short complex `S` that has homology
-/
noncomputable def homologyData [HasHomology S] : S.HomologyData := HasHomology.condition.some

variable {S}
/-
**CategoryTheory.ShortComplex.HasHomology.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex.HasHomology`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h : S.
HomologyData), S.HasHomology
参数：h : S.HomologyData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HasHomology.mk' (h : S.HomologyData) : HasHomology S :=
  ⟨Nonempty.intro h⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasHomology S] : HasHomology S.op :=
  HasHomology.mk' S.homologyData.op
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : ShortComplex Cᵒᵖ) [HasHomology S] : HasHomology S.unop :=
  HasHomology.mk' S.homologyData.unop
/-
**CategoryTheory.ShortComplex.hasLeftHomology_of_hasHomology** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasLeftHomology_of_hasHomology [S.HasHomology] : S.HasLeftHomology
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
-/
instance hasLeftHomology_of_hasHomology [S.HasHomology] : S.HasLeftHomology :=
  HasLeftHomology.mk' S.homologyData.left
/-
**CategoryTheory.ShortComplex.hasRightHomology_of_hasHomology** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasRightHomology_of_hasHomology [S.HasHomology] : S.HasRightHomology
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasRightHomology.mk'`：mk' (h : S.RightHomolo
gyData) : HasRightHomology S
-/
instance hasRightHomology_of_hasHomology [S.HasHomology] : S.HasRightHomology :=
  HasRightHomology.mk' S.homologyData.right
/-
**CategoryTheory.ShortComplex.hasHomology_of_hasCokernel** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
 (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasHomology
参数：f : X ⟶ Y；Z : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
instance hasHomology_of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasCokernel _ rfl)
/-
**CategoryTheory.ShortComplex.hasHomology_of_hasKernel** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] : (Sh
ortComplex.mk (0 : X ⟶ Y) g zero_comp).HasHomology
参数：g : Y ⟶ Z；X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
instance hasHomology_of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasKernel _ rfl)
/-
**CategoryTheory.ShortComplex.hasHomology_of_zeros** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_zeros (X Y Z : C) : (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z
) zero_comp).HasHomology
参数：X Y Z : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
instance hasHomology_of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofZeros _ rfl rfl)
/-
**CategoryTheory.ShortComplex.hasHomology_of_epi_of_isIso_of_mono** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasHomology S₁] [Epi φ.
τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₂
参数：φ : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
-/
lemma hasHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono φ S₁.homologyData)
/-
**CategoryTheory.ShortComplex.hasHomology_of_epi_of_isIso_of_mono'** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasHomology S₂] [Epi φ
.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₁
参数：φ : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
-/
lemma hasHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₁ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono' φ S₂.homologyData)
/-
**CategoryTheory.ShortComplex.hasHomology_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：hasHomology_of_iso (e : S₁ ≅ S₂) [HasHomology S₁] : HasHomology S₂
参数：e : S₁ ≅ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
-/
lemma hasHomology_of_iso (e : S₁ ≅ S₂) [HasHomology S₁] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofIso e S₁.homologyData)

namespace HomologyMapData

/-- The homology map data associated to the identity morphism of a short complex. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.id** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.HomologyMapData`。
形式化陈述：id (h : S.HomologyData) : HomologyMapData (𝟙 S) h h where left
参数：h : S.HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology map data associated to the identity morphism of a short complex.
-/
def id (h : S.HomologyData) : HomologyMapData (𝟙 S) h h where
  left := LeftHomologyMapData.id h.left
  right := RightHomologyMapData.id h.right

/-- The homology map data associated to the zero morphism between two short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.zero** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) : HomologyMapData 0 h₁ 
h₂ where left
参数：h₁ : S₁.HomologyData；h₂ : S₂.HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology map data associated to the zero morphism between two short complexe
s.
-/
def zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    HomologyMapData 0 h₁ h₂ where
  left := LeftHomologyMapData.zero h₁.left h₂.left
  right := RightHomologyMapData.zero h₁.right h₂.right

/-- The composition of homology map data. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.comp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData} {h₂ : S₂.Homology
Data} {h₃ : S₃.HomologyData} (ψ : HomologyMapData φ h₁ h₂) (ψ' : HomologyMapData
 φ' h₂ h₃) : HomologyMapData (φ ≫ φ') h₁ h₃ where left
参数：ψ : HomologyMapData φ h₁ h₂；ψ' : HomologyMapData φ' h₂ h₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of homology map data.
-/
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData}
    {h₂ : S₂.HomologyData} {h₃ : S₃.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) (ψ' : HomologyMapData φ' h₂ h₃) :
    HomologyMapData (φ ≫ φ') h₁ h₃ where
  left := ψ.left.comp ψ'.left
  right := ψ.right.comp ψ'.right

/-- A homology map data for a morphism of short complexes induces
a homology map data in the opposite category. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.op** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.HomologyMapData`。
形式化陈述：op {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData} (ψ : Homolo
gyMapData φ h₁ h₂) : HomologyMapData (opMap φ) h₂.op h₁.op where left
参数：ψ : HomologyMapData φ h₁ h₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homology map data for a morphism of short complexes induces
a homology map data in the opposite category.
-/
def op {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (opMap φ) h₂.op h₁.op where
  left := ψ.right.op
  right := ψ.left.op

/-- A homology map data for a morphism of short complexes in the opposite category
induces a homology map data in the original category. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.unop** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ :
 S₂.HomologyData} (ψ : HomologyMapData φ h₁ h₂) : HomologyMapData (unopMap φ) h₂
.unop h₁.unop where left
参数：ψ : HomologyMapData φ h₁ h₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homology map data for a morphism of short complexes in the opposite category
induces a homology map data in the original category.
-/
def unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (unopMap φ) h₂.unop h₁.unop where
  left := ψ.right.unop
  right := ψ.left.unop

/-- When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on homology of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.ofZeros** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (
hg₂ : S₂.g = 0) : HomologyMapData φ (HomologyData.ofZeros S₁ hf₁ hg₁) (HomologyD
ata.ofZeros S₂ hf₂ hg₂) where left
参数：φ : S₁ ⟶ S₂；hf₁ : S₁.f = 0；hg₁ : S₁.g = 0；hf₂ : S₂.f = 0；hg₂ : S₂.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on homology of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects.
-/
noncomputable def ofZeros (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    HomologyMapData φ (HomologyData.ofZeros S₁ hf₁ hg₁) (HomologyData.ofZeros S₂ hf₂ hg₂) where
  left := LeftHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂
  right := RightHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂

/-- When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁` and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.ofIsColimitCokernelCofork** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂) (hg₁ : S₁.g = 0) (c₁ : CokernelCof
ork S₁.f) (hc₁ : IsColimit c₁) (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ 
: IsColimit c₂) (f : c₁.pt ⟶ c₂.pt) (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) : HomologyMa
pData φ (HomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁) (HomologyData.ofI
sColimitCokernelCofork S₂ hg₂ c₂ hc₂) where left
参数：φ : S₁ ⟶ S₂；hg₁ : S₁.g = 0；c₁ : CokernelCofork S₁.f；hc₁ : IsColimit c₁；hg₂ : 
S₂.g = 0；c₂ : CokernelCofork S₂.f；hc₂ : IsColimit c₂；f : c₁.pt ⟶ c₂.pt；comm : φ.
τ₂ ≫ c₂.π = c₁.π ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁`
 and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on homology of a morphism `φ : S₁
 ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`.
-/
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
    (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
    HomologyMapData φ (HomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
      (HomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm

/-- When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `c₂`
for `S₁.g` and `S₂.g` respectively, the action on homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.ofIsLimitKernelFork** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：ofIsLimitKernelFork (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) 
(hc₁ : IsLimit c₁) (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f
 : c₁.pt ⟶ c₂.pt) (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) : HomologyMapData φ (HomologyD
ata.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁) (HomologyData.ofIsLimitKernelFork S₂ hf₂ 
c₂ hc₂) where left
参数：φ : S₁ ⟶ S₂；hf₁ : S₁.f = 0；c₁ : KernelFork S₁.g；hc₁ : IsLimit c₁；hf₂ : S₂.f =
 0；c₂ : KernelFork S₂.g；hc₂ : IsLimit c₂；f : c₁.pt ⟶ c₂.pt；comm : c₁.ι ≫ φ.τ₂ = 
f ≫ c₂.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `
c₂`
for `S₁.g` and `S₂.g` respectively, the action on homology of a morphism `φ : S₁
 ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`.
-/
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    HomologyMapData φ (HomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (HomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
/-
**CategoryTheory.ShortComplex.HomologyMapData.compatibilityOfZerosOfIsColimitCok
ernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapDa
ta`。
形式化陈述：compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0
) (c : CokernelCofork S.f) (hc : IsColimit c) : HomologyMapData (𝟙 S) (HomologyD
ata.ofZeros S hf hg) (HomologyData.ofIsColimitCokernelCofork S hg c hc) where le
ft
参数：hf : S.f = 0；hg : S.g = 0；c : CokernelCofork S.f；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homo
logy map
data (for the identity of `S`) which relates the homology data `ofZeros` and
`ofIsColimitCokernelCofork`.
-/
noncomputable def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    HomologyMapData (𝟙 S) (HomologyData.ofZeros S hf hg)
      (HomologyData.ofIsColimitCokernelCofork S hg c hc) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the homology data
`HomologyData.ofIsLimitKernelFork` and `ofZeros` . -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.compatibilityOfZerosOfIsLimitKerne
lFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0) (c :
 KernelFork S.g) (hc : IsLimit c) : HomologyMapData (𝟙 S) (HomologyData.ofIsLimi
tKernelFork S hf c hc) (HomologyData.ofZeros S hf hg) where left
参数：hf : S.f = 0；hg : S.g = 0；c : KernelFork S.g；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homo
logy map
data (for the identity of `S`) which relates the homology data
`HomologyData.ofIsLimitKernelFork` and `ofZeros` .
-/
noncomputable def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    HomologyMapData (𝟙 S)
      (HomologyData.ofIsLimitKernelFork S hf c hc)
      (HomologyData.ofZeros S hf hg) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc

/-- This homology map data expresses compatibilities of the homology data
constructed by `HomologyData.ofEpiOfIsIsoOfMono` -/
/-
**CategoryTheory.ShortComplex.HomologyMapData.ofEpiOfIsIsoOfMono** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁) [Epi φ.τ₁] [IsIso φ
.τ₂] [Mono φ.τ₃] : HomologyMapData φ h (HomologyData.ofEpiOfIsIsoOfMono φ h) whe
re left
参数：φ : S₁ ⟶ S₂；h : HomologyData S₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This homology map data expresses compatibilities of the homology data
constructed by `HomologyData.ofEpiOfIsIsoOfMono`
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ h (HomologyData.ofEpiOfIsIsoOfMono φ h) where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono φ h.right

/-- This homology map data expresses compatibilities of the homology data
constructed by `HomologyData.ofEpiOfIsIsoOfMono'` -/
/-
**CategoryTheory.ShortComplex.HomologyMapData.ofEpiOfIsIsoOfMono'** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂) [Epi φ.τ₁] [IsIso 
φ.τ₂] [Mono φ.τ₃] : HomologyMapData φ (HomologyData.ofEpiOfIsIsoOfMono' φ h) h w
here left
参数：φ : S₁ ⟶ S₂；h : HomologyData S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This homology map data expresses compatibilities of the homology data
constructed by `HomologyData.ofEpiOfIsIsoOfMono'`
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ (HomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono' φ h.right

end HomologyMapData

variable (S)

/-- The homology of a short complex is the `left.H` field of a chosen homology data. -/
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology of a short complex is the `left.H` field of a chosen homology data.
-/
noncomputable def homology [HasHomology S] : C := S.homologyData.left.H

/-- When a short complex has homology, this is the canonical isomorphism
`S.leftHomology ≅ S.homology`. -/
/-
**CategoryTheory.ShortComplex.leftHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：leftHomologyIso [S.HasHomology] : S.leftHomology ≅ S.homology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a short complex has homology, this is the canonical isomorphism
`S.leftHomology ≅ S.homology`.
-/
noncomputable def leftHomologyIso [S.HasHomology] : S.leftHomology ≅ S.homology :=
  leftHomologyMapIso' (Iso.refl _) _ _

/-- When a short complex has homology, this is the canonical isomorphism
`S.rightHomology ≅ S.homology`. -/
/-
**CategoryTheory.ShortComplex.rightHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：rightHomologyIso [S.HasHomology] : S.rightHomology ≅ S.homology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a short complex has homology, this is the canonical isomorphism
`S.rightHomology ≅ S.homology`.
-/
noncomputable def rightHomologyIso [S.HasHomology] : S.rightHomology ≅ S.homology :=
  rightHomologyMapIso' (Iso.refl _) _ _ ≪≫ S.homologyData.iso.symm

variable {S}

/-- When a short complex has homology, its homology can be computed using
any left homology data. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.homologyIso** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {S : CategoryTheory.ShortComp
lex C} → (h : S.LeftHomologyData) → [inst_2 : S.HasHomology] → S.homology ≅ h.H
参数：h : S.LeftHomologyData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a short complex has homology, its homology can be computed using
any left homology data.
-/
noncomputable def LeftHomologyData.homologyIso (h : S.LeftHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

/-- When a short complex has homology, its homology can be computed using
any right homology data. -/
/-
**CategoryTheory.ShortComplex.RightHomologyData.homologyIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {S : CategoryTheory.ShortComp
lex C} → (h : S.RightHomologyData) → [inst_2 : S.HasHomology] → S.homology ≅ h.H
参数：h : S.RightHomologyData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a short complex has homology, its homology can be computed using
any right homology data.
-/
noncomputable def RightHomologyData.homologyIso (h : S.RightHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

variable (S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyData** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology], S.leftHomologyData.homologyIso = S.leftHomologyIso.symm
参数：S : CategoryTheory.ShortComplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_comp`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S₁ S₂ S₃ : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma LeftHomologyData.homologyIso_leftHomologyData [S.HasHomology] :
    S.leftHomologyData.homologyIso = S.leftHomologyIso.symm := by
  ext
  dsimp [homologyIso, leftHomologyIso, ShortComplex.leftHomologyIso]
  rw [← leftHomologyMap'_comp, comp_id]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.ShortComplex.RightHomologyData.homologyIso_rightHomologyData** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology],   S.rightHomologyData.homologyIso = S.rightHomologyIso.symm
参数：S : CategoryTheory.ShortComplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMapIso'_hom`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_id`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.homologyIso_rightHomologyData [S.HasHomology] :
    S.rightHomologyData.homologyIso = S.rightHomologyIso.symm := by
  ext
  simp [homologyIso, rightHomologyIso]

variable {S}

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced homology map `h₁.left.H ⟶ h₁.left.H`. -/
/-
**CategoryTheory.ShortComplex.homologyMap'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：homologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
 h₁.left.H ⟶ h₂.left.H
参数：φ : S₁ ⟶ S₂；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `φ : S₁ ⟶ S₂` of short complexes and homology data `h₁` and `h₂
`
for `S₁` and `S₂` respectively, this is the induced homology map `h₁.left.H ⟶ h₁
.left.H`.
-/
def homologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    h₁.left.H ⟶ h₂.left.H := leftHomologyMap' φ _ _

/-- The homology map `S₁.homology ⟶ S₂.homology` induced by a morphism
`S₁ ⟶ S₂` of short complexes. -/
/-
**CategoryTheory.ShortComplex.homologyMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex`。
形式化陈述：homologyMap (φ : S₁ ⟶ S₂) [HasHomology S₁] [HasHomology S₂] : S₁.homology 
⟶ S₂.homology
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology map `S₁.homology ⟶ S₂.homology` induced by a morphism
`S₁ ⟶ S₂` of short complexes.
-/
noncomputable def homologyMap (φ : S₁ ⟶ S₂) [HasHomology S₁] [HasHomology S₂] :
    S₁.homology ⟶ S₂.homology :=
  homologyMap' φ _ _

namespace HomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
  (γ : HomologyMapData φ h₁ h₂)

/-
**CategoryTheory.ShortComplex.HomologyMapData.homologyMap'_eq** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ 
: S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}   (γ : CategoryTheory.S
hortComplex.HomologyMapData φ h₁ h₂),   CategoryTheory.ShortComplex.homologyMap'
 φ h₁ h₂ = γ.left.φH
参数：γ : CategoryTheory.ShortComplex.HomologyMapData φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.congr_φH`：congr_φH {γ₁ γ
₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.instSubsingleton`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma homologyMap'_eq : homologyMap' φ h₁ h₂ = γ.left.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)
/-
**CategoryTheory.ShortComplex.HomologyMapData.cyclesMap'_eq** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ 
: S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}   (γ : CategoryTheory.S
hortComplex.HomologyMapData φ h₁ h₂),   CategoryTheory.ShortComplex.cyclesMap' φ
 h₁.left h₂.left = γ.left.φK
参数：γ : CategoryTheory.ShortComplex.HomologyMapData φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.congr_φK`：congr_φK {γ₁ γ
₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φK = γ₂.φK
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.instSubsingleton`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma cyclesMap'_eq : cyclesMap' φ h₁.left h₂.left = γ.left.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)
/-
**CategoryTheory.ShortComplex.HomologyMapData.opcyclesMap'_eq** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ 
: S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}   (γ : CategoryTheory.S
hortComplex.HomologyMapData φ h₁ h₂),   CategoryTheory.ShortComplex.opcyclesMap'
 φ h₁.right h₂.right = γ.right.φQ
参数：γ : CategoryTheory.ShortComplex.HomologyMapData φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyMapData.congr_φQ`：congr_φQ {γ₁ 
γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φQ = γ₂.φQ
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.instSubsingleton`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma opcyclesMap'_eq : opcyclesMap' φ h₁.right h₂.right = γ.right.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end HomologyMapData

namespace LeftHomologyMapData

variable {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_eq** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：homologyMap_eq : homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIs
o.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp [homologyMap, LeftHomologyData.homologyIso, leftHomologyIso,
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp, id_comp, comp_id]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_comm** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：homologyMap_comm : homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom
 ≫ γ.φH
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_eq`：homology
Map_eq : homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_comm :
    homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

namespace RightHomologyMapData

variable {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.homologyMap_eq** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：homologyMap_eq : homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIs
o.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ShortComplex.HomologyMapData.comm_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp [homologyMap, homologyMap', RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso]
  have γ' : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  simp only [← γ.rightHomologyMap'_eq, assoc, ← rightHomologyMap'_comp_assoc,
    id_comp, comp_id, γ'.left.leftHomologyMap'_eq, γ'.right.rightHomologyMap'_eq, ← γ'.comm_assoc,
    Iso.hom_inv_id]
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.homologyMap_comm** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：homologyMap_comm : homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom
 ≫ γ.φH
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyMapData.homologyMap_eq`：homolog
yMap_eq : homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_comm :
    homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap'_id** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h : S.
HomologyData),   CategoryTheory.ShortComplex.homologyMap' (CategoryTheory.Catego
ryStruct.id S) h h =     CategoryTheory.CategoryStruct.id h.left.H
参数：h : S.HomologyData；CategoryTheory.CategoryStruct.id S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HomologyMapData.homologyMap'_eq`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma homologyMap'_id (h : S.HomologyData) :
    homologyMap' (𝟙 S) h h = 𝟙 _ :=
  (HomologyMapData.id h).homologyMap'_eq

variable (S)

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：homologyMap_id [HasHomology S] : homologyMap (𝟙 S) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_id`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
-/
lemma homologyMap_id [HasHomology S] :
    homologyMap (𝟙 S) = 𝟙 _ :=
  homologyMap'_id _

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (h₁
 : S₁.HomologyData) (h₂ : S₂.HomologyData),   CategoryTheory.ShortComplex.homolo
gyMap' 0 h₁ h₂ = 0
参数：h₁ : S₁.HomologyData；h₂ : S₂.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HomologyMapData.homologyMap'_eq`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma homologyMap'_zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    homologyMap' 0 h₁ h₂ = 0 :=
  (HomologyMapData.zero h₁ h₂).homologyMap'_eq

variable (S₁ S₂)

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：homologyMap_zero [S₁.HasHomology] [S₂.HasHomology] : homologyMap (0 : S₁ ⟶
 S₂) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_zero`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma homologyMap_zero [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (0 : S₁ ⟶ S₂) = 0 :=
  homologyMap'_zero _ _

variable {S₁ S₂}
/-
**CategoryTheory.ShortComplex.homologyMap'_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ S₃ : CategoryTheory.ShortComplex C} 
(φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)   (h
₃ : S₃.HomologyData),   CategoryTheory.ShortComplex.homologyMap' (CategoryTheory
.CategoryStruct.comp φ₁ φ₂) h₁ h₃ =     CategoryTheory.CategoryStruct.comp (Cate
goryTheory.ShortComplex.homologyMap' φ₁ h₁ h₂)       (CategoryTheory.ShortComple
x.homologyMap' φ₂ h₂ h₃)
参数：φ₁ : S₁ ⟶ S₂；φ₂ : S₂ ⟶ S₃；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；h₃ : S₃.H
omologyData；CategoryTheory.CategoryStruct.comp φ₁ φ₂；CategoryTheory.ShortComplex
.homologyMap' φ₁ h₁ h₂；CategoryTheory.ShortComplex.homologyMap' φ₂ h₂ h₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_comp`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S₁ S₂ S₃ : CategoryThe…
-/
lemma homologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) (h₃ : S₃.HomologyData) :
    homologyMap' (φ₁ ≫ φ₂) h₁ h₃ = homologyMap' φ₁ h₁ h₂ ≫
      homologyMap' φ₂ h₂ h₃ :=
  leftHomologyMap'_comp _ _ _ _ _

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：homologyMap_comp [HasHomology S₁] [HasHomology S₂] [HasHomology S₃] (φ₁ : 
S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : homologyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫ homologyMap φ
₂
参数：φ₁ : S₁ ⟶ S₂；φ₂ : S₂ ⟶ S₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_comp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ S₃ : CategoryTheory.Sh…
-/
lemma homologyMap_comp [HasHomology S₁] [HasHomology S₂] [HasHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    homologyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫ homologyMap φ₂ :=
  homologyMap'_comp _ _ _ _ _

/-- Given an isomorphism `S₁ ≅ S₂` of short complexes and homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced homology isomorphism `h₁.left.H ≅ h₁.left.H`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.homologyMapIso'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：homologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData
) : h₁.left.H ≅ h₂.left.H where hom
参数：e : S₁ ≅ S₂；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an isomorphism `S₁ ≅ S₂` of short complexes and homology data `h₁` and `h₂
`
for `S₁` and `S₂` respectively, this is the induced homology isomorphism `h₁.lef
t.H ≅ h₁.left.H`.
-/
def homologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : h₁.left.H ≅ h₂.left.H where
  hom := homologyMap' e.hom h₁ h₂
  inv := homologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← homologyMap'_comp, e.hom_inv_id, homologyMap'_id]
  inv_hom_id := by rw [← homologyMap'_comp, e.inv_hom_id, homologyMap'_id]
/-
**CategoryTheory.ShortComplex.isIso_homologyMap'_of_isIso** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (φ 
: S₁ ⟶ S₂) [CategoryTheory.IsIso φ] (h₁ : S₁.HomologyData)   (h₂ : S₂.HomologyDa
ta), CategoryTheory.IsIso (CategoryTheory.ShortComplex.homologyMap' φ h₁ h₂)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；CategoryTheory.ShortCom
plex.homologyMap' φ h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_homologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    IsIso (homologyMap' φ h₁ h₂) :=
  inferInstanceAs <| IsIso (homologyMapIso' (asIso φ) h₁ h₂).hom

/-- The homology isomorphism `S₁.homology ⟶ S₂.homology` induced by an isomorphism
`S₁ ≅ S₂` of short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.homologyMapIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：homologyMapIso (e : S₁ ≅ S₂) [S₁.HasHomology] [S₂.HasHomology] : S₁.homolo
gy ≅ S₂.homology where hom
参数：e : S₁ ≅ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology isomorphism `S₁.homology ⟶ S₂.homology` induced by an isomorphism
`S₁ ≅ S₂` of short complexes.
-/
noncomputable def homologyMapIso (e : S₁ ≅ S₂) [S₁.HasHomology]
    [S₂.HasHomology] : S₁.homology ≅ S₂.homology where
  hom := homologyMap e.hom
  inv := homologyMap e.inv
  hom_inv_id := by rw [← homologyMap_comp, e.hom_inv_id, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id]
/-
**CategoryTheory.ShortComplex.isIso_homologyMap_of_iso** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_homologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasHomology] [S₂.HasH
omology] : IsIso (homologyMap φ)
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_homologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasHomology]
    [S₂.HasHomology] :
    IsIso (homologyMap φ) :=
  inferInstanceAs <| IsIso (homologyMapIso (asIso φ)).hom

variable {S}

section

variable (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)

/-- If a short complex `S` has both a left homology data `h₁` and a right homology data `h₂`,
this is the canonical morphism `h₁.H ⟶ h₂.H`. -/
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison'** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftRightHomologyComparison' : h₁.H ⟶ h₂.H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a short complex `S` has both a left homology data `h₁` and a right homology d
ata `h₂`,
this is the canonical morphism `h₁.H ⟶ h₂.H`.
-/
def leftRightHomologyComparison' : h₁.H ⟶ h₂.H :=
  h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero])
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison'_eq_liftH** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h₁ : S
.LeftHomologyData) (h₂ : S.RightHomologyData),   CategoryTheory.ShortComplex.lef
tRightHomologyComparison' h₁ h₂ =     h₂.liftH (h₁.descH (CategoryTheory.Categor
yStruct.comp h₁.i h₂.p) ⋯) ⋯
参数：h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData；h₁.descH (CategoryTheory.Cat
egoryStruct.comp h₁.i h₂.p) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftRightHomologyComparison'_eq_liftH :
    leftRightHomologyComparison' h₁ h₂ =
      h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
        (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
          RightHomologyData.p_g', LeftHomologyData.wi, comp_zero]) := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_leftRightHomologyComparison'_ι :
    h₁.π ≫ leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι = h₁.i ≫ h₂.p := by
  simp only [leftRightHomologyComparison'_eq_liftH,
    RightHomologyData.liftH_ι, LeftHomologyData.π_descH]
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison'_eq_descH** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h₁ : S
.LeftHomologyData) (h₂ : S.RightHomologyData),   CategoryTheory.ShortComplex.lef
tRightHomologyComparison' h₁ h₂ =     h₁.descH (h₂.liftH (CategoryTheory.Categor
yStruct.comp h₁.i h₂.p) ⋯) ⋯
参数：h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData；h₂.liftH (CategoryTheory.Cat
egoryStruct.comp h₁.i h₂.p) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instMonoι`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instEpiπ`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.π_descH_assoc`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.liftH_ι`：liftH_ι (k : A ⟶ 
h.Q) (hk : k ≫ h.g' = 0) : h.liftH k hk ≫ h.ι = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftRightHomologyComparison'_eq_descH :
    leftRightHomologyComparison' h₁ h₂ =
      h₁.descH (h₂.liftH (h₁.i ≫ h₂.p) (by simp))
        (by rw [← cancel_mono h₂.ι, assoc, RightHomologyData.liftH_ι,
          LeftHomologyData.f'_i_assoc, RightHomologyData.wp, zero_comp]) := by
  simp only [← cancel_mono h₂.ι, ← cancel_epi h₁.π, π_leftRightHomologyComparison'_ι,
    LeftHomologyData.π_descH_assoc, RightHomologyData.liftH_ι]

end

variable (S)

/-- If a short complex `S` has both a left and right homology,
this is the canonical morphism `S.leftHomology ⟶ S.rightHomology`. -/
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftRightHomologyComparison [S.HasLeftHomology] [S.HasRightHomology] : S.l
eftHomology ⟶ S.rightHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a short complex `S` has both a left and right homology,
this is the canonical morphism `S.leftHomology ⟶ S.rightHomology`.
-/
noncomputable def leftRightHomologyComparison [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomology ⟶ S.rightHomology :=
  leftRightHomologyComparison' _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_leftRightHomologyComparison_ι [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomologyπ ≫ S.leftRightHomologyComparison ≫ S.rightHomologyι =
      S.iCycles ≫ S.pOpcycles :=
  π_leftRightHomologyComparison'_ι _ _

@[reassoc]
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison'_naturality** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (φ 
: S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₁.RightHomologyData)   (h₁' : S₂.Le
ftHomologyData) (h₂' : S₂.RightHomologyData),   CategoryTheory.CategoryStruct.co
mp (CategoryTheory.ShortComplex.leftHomologyMap' φ h₁ h₁')       (CategoryTheory
.ShortComplex.leftRightHomologyComparison' h₁' h₂') =     CategoryTheory.Categor
yStruct.comp (CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂)   
    (CategoryTheory.ShortComplex.rightHomologyMap' φ h₂ h₂')
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₁.RightHomologyData；h₁' : S₂.LeftH
omologyData；h₂' : S₂.RightHomologyData；CategoryTheory.ShortComplex.leftHomologyM
ap' φ h₁ h₁'；CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁' h₂'；Ca
tegoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂；CategoryTheory.Shor
tComplex.rightHomologyMap' φ h₂ h₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instEpiπ`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyπ_naturality'_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instMonoι`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_i_assoc`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {S₁ S₂ : CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyι_naturality'`：rightHomologyι_n
aturality' : rightHomologyMap' φ h₁ h₂ ≫ h₂.ι = h₁.ι ≫ opcyclesMap' φ h₁ h₂
· 使用定理 `CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用引理 `CategoryTheory.ShortComplex.p_opcyclesMap'`：p_opcyclesMap' : h₁.p ≫ opcy
clesMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftRightHomologyComparison'_naturality (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₁.RightHomologyData) (h₁' : S₂.LeftHomologyData) (h₂' : S₂.RightHomologyData) :
    leftHomologyMap' φ h₁ h₁' ≫ leftRightHomologyComparison' h₁' h₂' =
      leftRightHomologyComparison' h₁ h₂ ≫ rightHomologyMap' φ h₂ h₂' := by
  simp only [← cancel_epi h₁.π, ← cancel_mono h₂'.ι, assoc,
    leftHomologyπ_naturality'_assoc, rightHomologyι_naturality',
    π_leftRightHomologyComparison'_ι, π_leftRightHomologyComparison'_ι_assoc,
    cyclesMap'_i_assoc, p_opcyclesMap']

variable {S}
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison'_compatibility** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h₁ h₁'
 : S.LeftHomologyData) (h₂ h₂' : S.RightHomologyData),   CategoryTheory.ShortCom
plex.leftRightHomologyComparison' h₁ h₂ =     CategoryTheory.CategoryStruct.comp
       (CategoryTheory.ShortComplex.leftHomologyMap' (CategoryTheory.CategoryStr
uct.id S) h₁ h₁')       (CategoryTheory.CategoryStruct.comp (CategoryTheory.Shor
tComplex.leftRightHomologyComparison' h₁' h₂')         (CategoryTheory.ShortComp
lex.rightHomologyMap' (CategoryTheory.CategoryStruct.id S) h₂' h₂))
参数：h₁ h₁' : S.LeftHomologyData；h₂ h₂' : S.RightHomologyData；CategoryTheory.Short
Complex.leftHomologyMap' (CategoryTheory.CategoryStruct.id S) h₁ h₁'；CategoryThe
ory.CategoryStruct.comp (CategoryTheory.ShortComplex.leftRightHomologyComparison
' h₁' h₂')         (CategoryTheory.ShortComplex.rightHomologyMap' (CategoryTheor
y.CategoryStruct.id S) h₂' h₂)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_naturality_asso
c`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_comp`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S₁ S₂ S₃ : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_id`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S : CategoryTheory.Sho…
-/
lemma leftRightHomologyComparison'_compatibility (h₁ h₁' : S.LeftHomologyData)
    (h₂ h₂' : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ = leftHomologyMap' (𝟙 S) h₁ h₁' ≫
      leftRightHomologyComparison' h₁' h₂' ≫ rightHomologyMap' (𝟙 S) _ _ := by
  rw [leftRightHomologyComparison'_naturality_assoc (𝟙 S) h₁ h₂ h₁' h₂',
    ← rightHomologyMap'_comp, comp_id, rightHomologyMap'_id, comp_id]
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison_eq** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftRightHomologyComparison_eq [S.HasLeftHomology] [S.HasRightHomology] (h
₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) : S.leftRightHomologyComparis
on = h₁.leftHomologyIso.hom ≫ leftRightHomologyComparison' h₁ h₂ ≫ h₂.rightHomol
ogyIso.inv
参数：h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_compatibility`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
-/
lemma leftRightHomologyComparison_eq [S.HasLeftHomology] [S.HasRightHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    S.leftRightHomologyComparison = h₁.leftHomologyIso.hom ≫
      leftRightHomologyComparison' h₁ h₂ ≫ h₂.rightHomologyIso.inv :=
  leftRightHomologyComparison'_compatibility _ _ _ _

@[simp]
/-
**CategoryTheory.ShortComplex.HomologyData.leftRightHomologyComparison'_eq** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h : S.
HomologyData),   CategoryTheory.ShortComplex.leftRightHomologyComparison' h.left
 h.right = h.iso.hom
参数：h : S.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instEpiπ`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S : CategoryTheory.Sho…
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.comm`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S : CategoryTheory.ShortComp…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HomologyData.leftRightHomologyComparison'_eq (h : S.HomologyData) :
    leftRightHomologyComparison' h.left h.right = h.iso.hom := by
  simp only [← cancel_epi h.left.π, ← cancel_mono h.right.ι, assoc,
    π_leftRightHomologyComparison'_ι, comm]
/-
**CategoryTheory.ShortComplex.isIso_leftRightHomologyComparison'_of_homologyData
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h : S.
HomologyData),   CategoryTheory.IsIso (CategoryTheory.ShortComplex.leftRightHomo
logyComparison' h.left h.right)
参数：h : S.HomologyData；CategoryTheory.ShortComplex.leftRightHomologyComparison' h
.left h.right。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.leftRightHomologyComparison'_eq
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_leftRightHomologyComparison'_of_homologyData (h : S.HomologyData) :
    IsIso (leftRightHomologyComparison' h.left h.right) := by
    rw [h.leftRightHomologyComparison'_eq]
    infer_instance
/-
**CategoryTheory.ShortComplex.isIso_leftRightHomologyComparison'** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_leftRightHomologyComparison'_of_homologyData (h : S.HomologyData) : 
IsIso (leftRightHomologyComparison' h.left h.right)
参数：h : S.HomologyData。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_compatibility`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoLeftHomologyMap'OfEpiτ₁Ofτ₂OfMonoτ₃
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Categ
oryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₁`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₂`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₃`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.isIso_leftRightHomologyComparison'_of_homolo
gyData`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categ
oryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoRightHomologyMap'OfEpiτ₁Ofτ₂OfMonoτ
₃`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
instance isIso_leftRightHomologyComparison' [S.HasHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    IsIso (leftRightHomologyComparison' h₁ h₂) := by
  rw [leftRightHomologyComparison'_compatibility h₁ S.homologyData.left h₂
    S.homologyData.right]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.isIso_leftRightHomologyComparison** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_leftRightHomologyComparison [S.HasHomology] : IsIso S.leftRightHomol
ogyComparison
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_leftRightHomologyComparison [S.HasHomology] :
    IsIso S.leftRightHomologyComparison := by
  dsimp only [leftRightHomologyComparison]
  infer_instance

namespace HomologyData

/-- This is the homology data for a short complex `S` that is obtained
from a left homology data `h₁` and a right homology data `h₂` when the comparison
morphism `leftRightHomologyComparison' h₁ h₂ : h₁.H ⟶ h₂.H` is an isomorphism. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofIsIsoLeftRightHomologyComparison'**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofIsIsoLeftRightHomologyComparison' (h₁ : S.LeftHomologyData) (h₂ : S.Righ
tHomologyData) [IsIso (leftRightHomologyComparison' h₁ h₂)] : S.HomologyData whe
re left
参数：h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData；leftRightHomologyComparison'
 h₁ h₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the homology data for a short complex `S` that is obtained
from a left homology data `h₁` and a right homology data `h₂` when the compariso
n
morphism `leftRightHomologyComparison' h₁ h₂ : h₁.H ⟶ h₂.H` is an isomorphism.
-/
noncomputable def ofIsIsoLeftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HomologyData where
  left := h₁
  right := h₂
  iso := asIso (leftRightHomologyComparison' h₁ h₂)

end HomologyData

/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison'_eq_leftHomologpMap'_c
omp_iso_hom_comp_rightHomologyMap'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h : S.
HomologyData) (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData),   CategoryTh
eory.ShortComplex.leftRightHomologyComparison' h₁ h₂ =     CategoryTheory.Catego
ryStruct.comp       (CategoryTheory.ShortComplex.leftHomologyMap' (CategoryTheor
y.CategoryStruct.id S) h₁ h.left)       (CategoryTheory.CategoryStruct.comp h.is
o.hom         (CategoryTheory.ShortComplex.rightHomologyMap' (CategoryTheory.Cat
egoryStruct.id S) h.right h₂))
参数：h : S.HomologyData；h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData；CategoryT
heory.ShortComplex.leftHomologyMap' (CategoryTheory.CategoryStruct.id S) h₁ h.le
ft；CategoryTheory.CategoryStruct.comp h.iso.hom         (CategoryTheory.ShortCom
plex.rightHomologyMap' (CategoryTheory.CategoryStruct.id S) h.right h₂)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.leftRightHomologyComparison'_eq
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_compatibility`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
-/
lemma leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
    (h : S.HomologyData) (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
      leftHomologyMap' (𝟙 S) h₁ h.left ≫ h.iso.hom ≫ rightHomologyMap' (𝟙 S) h.right h₂ := by
  simpa only [h.leftRightHomologyComparison'_eq] using
    leftRightHomologyComparison'_compatibility h₁ h.left h₂ h.right

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison'_fac** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h₁ : S
.LeftHomologyData) (h₂ : S.RightHomologyData) [inst_2 : S.HasHomology],   Catego
ryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂ =     CategoryTheory.Ca
tegoryStruct.comp h₁.homologyIso.inv h₂.homologyIso.hom
参数：h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_eq_leftHomologp
Map'_comp_iso_hom_comp_rightHomologyMap'`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {S : Ca
tegoryTheory.ShortComp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftRightHomologyComparison'_fac (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [S.HasHomology] :
    leftRightHomologyComparison' h₁ h₂ = h₁.homologyIso.inv ≫ h₂.homologyIso.hom := by
  rw [leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
    S.homologyData h₁ h₂]
  dsimp only [LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyMapIso', leftHomologyIso,
    RightHomologyData.homologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', rightHomologyIso]
  simp only [assoc, ← leftHomologyMap'_comp_assoc, id_comp, ← rightHomologyMap'_comp]

variable (S)

@[reassoc]
/-
**CategoryTheory.ShortComplex.leftRightHomologyComparison_fac** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftRightHomologyComparison_fac [S.HasHomology] : S.leftRightHomologyCompa
rison = S.leftHomologyIso.hom ≫ S.rightHomologyIso.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyDat
a`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.homologyIso_rightHomologyD
ata`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_fac`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.ShortComp…
-/
lemma leftRightHomologyComparison_fac [S.HasHomology] :
    S.leftRightHomologyComparison = S.leftHomologyIso.hom ≫ S.rightHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv,
    RightHomologyData.homologyIso_rightHomologyData, Iso.symm_hom] using!
      leftRightHomologyComparison'_fac S.leftHomologyData S.rightHomologyData

variable {S}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.HomologyData.right_homologyIso_eq_left_homologyIso
_trans_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h : S.
HomologyData) [inst_2 : S.HasHomology],   h.right.homologyIso = h.left.homologyI
so ≪≫ h.iso
参数：h : S.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_fac`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.leftRightHomologyComparison'_eq
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Iso.self_symm_id_assoc`：self_symm_id_assoc (α : X ≅ Y) (β
 : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β
-/
lemma HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso
    (h : S.HomologyData) [S.HasHomology] :
    h.right.homologyIso = h.left.homologyIso ≪≫ h.iso := by
  suffices h.iso = h.left.homologyIso.symm ≪≫ h.right.homologyIso by
    rw [this, Iso.self_symm_id_assoc]
  ext
  dsimp
  rw [← leftRightHomologyComparison'_fac, leftRightHomologyComparison'_eq]
/-
**CategoryTheory.ShortComplex.HomologyData.left_homologyIso_eq_right_homologyIso
_trans_iso_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.HomologyD
ata`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (h : S.
HomologyData) [inst_2 : S.HasHomology],   h.left.homologyIso = h.right.homologyI
so ≪≫ h.iso.symm
参数：h : S.HomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.right_homologyIso_eq_left_homol
ogyIso_trans_iso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Iso.self_symm_id`：self_symm_id (α : X ≅ Y) : α ≪≫ α.symm 
= Iso.refl X
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HomologyData.left_homologyIso_eq_right_homologyIso_trans_iso_symm
    (h : S.HomologyData) [S.HasHomology] :
    h.left.homologyIso = h.right.homologyIso ≪≫ h.iso.symm := by
  rw [right_homologyIso_eq_left_homologyIso_trans_iso]
  cat_disch
/-
**CategoryTheory.ShortComplex.hasHomology_of_isIso_leftRightHomologyComparison'*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_isIso_leftRightHomologyComparison' (h₁ : S.LeftHomologyData
) (h₂ : S.RightHomologyData) [IsIso (leftRightHomologyComparison' h₁ h₂)] : S.Ha
sHomology
参数：h₁ : S.LeftHomologyData；h₂ : S.RightHomologyData；leftRightHomologyComparison'
 h₁ h₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasHomology.mk'`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S : CategoryTheory.ShortComp…
-/
lemma hasHomology_of_isIso_leftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HasHomology :=
  HasHomology.mk' (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂)
/-
**CategoryTheory.ShortComplex.hasHomology_of_isIsoLeftRightHomologyComparison** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasHomology_of_isIsoLeftRightHomologyComparison [S.HasLeftHomology] [S.Has
RightHomology] [h : IsIso S.leftRightHomologyComparison] : S.HasHomology
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hasHomology_of_isIso_leftRightHomologyCompar
ison'`：hasHomology_of_isIso_leftRightHomologyComparison' (h₁ : S.LeftHomologyDat
a) (h₂ : S.RightHomologyData) [IsIso (leftRightHomologyComparison' …
-/
lemma hasHomology_of_isIsoLeftRightHomologyComparison [S.HasLeftHomology]
    [S.HasRightHomology] [h : IsIso S.leftRightHomologyComparison] :
    S.HasHomology := by
  have : IsIso (leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData) := h
  exact hasHomology_of_isIso_leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData

section

variable [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} [in
st_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology] (φ : S₁ ⟶ S₂)   (h₁ : S₁.LeftHo
mologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.CategoryStruct.comp h₁.
homologyIso.hom (CategoryTheory.ShortComplex.leftHomologyMap' φ h₁ h₂) =     Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.ShortComplex.homologyMap φ) h₂.h
omologyIso.hom
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；CategoryTheory.
ShortComplex.leftHomologyMap' φ h₁ h₂；CategoryTheory.ShortComplex.homologyMap φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.leftHomologyIso_hom_naturality
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.homologyIso.hom ≫ leftHomologyMap' φ h₁ h₂ =
      homologyMap φ ≫ h₂.homologyIso.hom := by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_inv_naturality** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} [in
st_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology] (φ : S₁ ⟶ S₂)   (h₁ : S₁.LeftHo
mologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.CategoryStruct.comp h₁.
homologyIso.inv (CategoryTheory.ShortComplex.homologyMap φ) =     CategoryTheory
.CategoryStruct.comp (CategoryTheory.ShortComplex.leftHomologyMap' φ h₁ h₂) h₂.h
omologyIso.inv
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；CategoryTheory.
ShortComplex.homologyMap φ；CategoryTheory.ShortComplex.leftHomologyMap' φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.leftHomologyIso_inv_naturality
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.homologyIso.inv ≫ homologyMap φ =
      leftHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]
/-
**CategoryTheory.ShortComplex.leftHomologyIso_hom_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftHomologyIso_hom_naturality : S₁.leftHomologyIso.hom ≫ homologyMap φ = 
leftHomologyMap φ ≫ S₂.leftHomologyIso.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyDat
a`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_inv_natural
ity`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma leftHomologyIso_hom_naturality :
    S₁.leftHomologyIso.hom ≫ homologyMap φ =
      leftHomologyMap φ ≫ S₂.leftHomologyIso.hom := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_inv_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
/-
**CategoryTheory.ShortComplex.leftHomologyIso_inv_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftHomologyIso_inv_naturality : S₁.leftHomologyIso.inv ≫ leftHomologyMap 
φ = homologyMap φ ≫ S₂.leftHomologyIso.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyDat
a`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_hom_natural
ity`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma leftHomologyIso_inv_naturality :
    S₁.leftHomologyIso.inv ≫ leftHomologyMap φ =
      homologyMap φ ≫ S₂.leftHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_hom_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
/-
**CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_hom_naturality*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} [in
st_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology] (φ : S₁ ⟶ S₂)   (h₁ : S₁.RightH
omologyData) (h₂ : S₂.RightHomologyData),   CategoryTheory.CategoryStruct.comp h
₁.homologyIso.hom (CategoryTheory.ShortComplex.rightHomologyMap' φ h₁ h₂) =     
CategoryTheory.CategoryStruct.comp (CategoryTheory.ShortComplex.homologyMap φ) h
₂.homologyIso.hom
参数：φ : S₁ ⟶ S₂；h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；CategoryTheor
y.ShortComplex.rightHomologyMap' φ h₁ h₂；CategoryTheory.ShortComplex.homologyMap
 φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_naturality`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_hom_natural
ity_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Ca
tegoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `CategoryTheory.ShortComplex.leftRightHomologyComparison'_fac`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma RightHomologyData.rightHomologyIso_hom_naturality
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.homologyIso.hom ≫ rightHomologyMap' φ h₁ h₂ =
      homologyMap φ ≫ h₂.homologyIso.hom := by
  rw [← cancel_epi h₁.homologyIso.inv, Iso.inv_hom_id_assoc,
    ← cancel_epi (leftRightHomologyComparison' S₁.leftHomologyData h₁),
    ← leftRightHomologyComparison'_naturality φ S₁.leftHomologyData h₁ S₂.leftHomologyData h₂,
    ← cancel_epi (S₁.leftHomologyData.homologyIso.hom),
    LeftHomologyData.leftHomologyIso_hom_naturality_assoc,
    leftRightHomologyComparison'_fac, leftRightHomologyComparison'_fac, assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

@[reassoc]
/-
**CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_inv_naturality*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} [in
st_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology] (φ : S₁ ⟶ S₂)   (h₁ : S₁.RightH
omologyData) (h₂ : S₂.RightHomologyData),   CategoryTheory.CategoryStruct.comp h
₁.homologyIso.inv (CategoryTheory.ShortComplex.homologyMap φ) =     CategoryTheo
ry.CategoryStruct.comp (CategoryTheory.ShortComplex.rightHomologyMap' φ h₁ h₂) h
₂.homologyIso.inv
参数：φ : S₁ ⟶ S₂；h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；CategoryTheor
y.ShortComplex.homologyMap φ；CategoryTheory.ShortComplex.rightHomologyMap' φ h₁ 
h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_hom_natur
ality`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Catego
ryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.rightHomologyIso_inv_naturality
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
      h₁.homologyIso.inv ≫ homologyMap φ =
        rightHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  simp only [← cancel_mono h₂.homologyIso.hom, assoc, Iso.inv_hom_id_assoc, comp_id,
    ← RightHomologyData.rightHomologyIso_hom_naturality φ h₁ h₂, Iso.inv_hom_id]

@[reassoc]
/-
**CategoryTheory.ShortComplex.rightHomologyIso_hom_naturality** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：rightHomologyIso_hom_naturality : S₁.rightHomologyIso.hom ≫ homologyMap φ 
= rightHomologyMap φ ≫ S₂.rightHomologyIso.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.homologyIso_rightHomologyD
ata`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_inv_natur
ality`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Catego
ryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma rightHomologyIso_hom_naturality :
    S₁.rightHomologyIso.hom ≫ homologyMap φ =
      rightHomologyMap φ ≫ S₂.rightHomologyIso.hom := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_inv_naturality φ S₁.rightHomologyData S₂.rightHomologyData

@[reassoc]
/-
**CategoryTheory.ShortComplex.rightHomologyIso_inv_naturality** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：rightHomologyIso_inv_naturality : S₁.rightHomologyIso.inv ≫ rightHomologyM
ap φ = homologyMap φ ≫ S₂.rightHomologyIso.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.homologyIso_rightHomologyD
ata`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_hom_natur
ality`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Catego
ryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma rightHomologyIso_inv_naturality :
    S₁.rightHomologyIso.inv ≫ rightHomologyMap φ =
      homologyMap φ ≫ S₂.rightHomologyIso.inv := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_hom_naturality φ S₁.rightHomologyData S₂.rightHomologyData

end

variable (C)

/-- We shall say that a category `C` is a category with homology when all short complexes
have homology. -/
/-
**CategoryTheory.ShortComplex._root_.CategoryTheory.CategoryWithHomology** 是 Mat
hlib 中的一个类，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We shall say that a category `C` is a category with homology when all short comp
lexes
have homology.
-/
class _root_.CategoryTheory.CategoryWithHomology : Prop where
  hasHomology : ∀ (S : ShortComplex C), S.HasHomology

attribute [instance] CategoryWithHomology.hasHomology
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithHomology C] : CategoryWithHomology Cᵒᵖ :=
  ⟨fun S => HasHomology.mk' S.unop.homologyData.op⟩

/-- The homology functor `ShortComplex C ⥤ C` for a category `C` with homology. -/
@[simps]
/-
**CategoryTheory.ShortComplex.homologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：homologyFunctor [CategoryWithHomology C] : ShortComplex C ⥤ C where obj S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…

--- 原说明 ---
The homology functor `ShortComplex C ⥤ C` for a category `C` with homology.
-/
noncomputable def homologyFunctor [CategoryWithHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.homology
  map f := homologyMap f

variable {C}
/-
**CategoryTheory.ShortComplex.isIso_homologyMap'_of_epi_of_isIso_of_mono** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (φ 
: S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)   [CategoryTheory.Epi φ
.τ₁] [CategoryTheory.IsIso φ.τ₂] [CategoryTheory.Mono φ.τ₃],   CategoryTheory.Is
Iso (CategoryTheory.ShortComplex.homologyMap' φ h₁ h₂)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；CategoryTheory.ShortCom
plex.homologyMap' φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoLeftHomologyMap'OfEpiτ₁Ofτ₂OfMonoτ₃
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Categ
oryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
instance isIso_homologyMap'_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap' φ h₁ h₂) := by
  dsimp only [homologyMap']
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_homologyMap_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [S₁.HasHomology] 
[S₂.HasHomology] (h₁ : Epi φ.τ₁) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃) : IsIso (hom
ologyMap φ)
参数：φ : S₁ ⟶ S₂；h₁ : Epi φ.τ₁；h₂ : IsIso φ.τ₂；h₃ : Mono φ.τ₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.isIso_homologyMap'_of_epi_of_isIso_of_mono`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
-/
lemma isIso_homologyMap_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
    (h₁ : Epi φ.τ₁) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃) :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap]
  infer_instance
/-
**CategoryTheory.ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_homologyMap_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [S₁.HasHomology] [
S₂.HasHomology] [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : IsIso (homologyMap φ)
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'`：
isIso_homologyMap_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.Ha
sHomology] (h₁ : Epi φ.τ₁) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃…
-/
instance isIso_homologyMap_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap φ) :=
  isIso_homologyMap_of_epi_of_isIso_of_mono' φ inferInstance inferInstance inferInstance
/-
**CategoryTheory.ShortComplex.isIso_homologyFunctor_map_of_epi_of_isIso_of_mono*
* 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_homologyFunctor_map_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [CategoryW
ithHomology C] [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : IsIso ((homologyFunctor C).
map φ)
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_homologyFunctor_map_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [CategoryWithHomology C]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso ((homologyFunctor C).map φ) :=
  inferInstanceAs <| IsIso (homologyMap φ)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.isIso_homologyMap_of_isIso** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_homologyMap_of_isIso (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
 [IsIso φ] : IsIso (homologyMap φ)
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoLeftHomologyMap'OfEpiτ₁Ofτ₂OfMonoτ₃
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Categ
oryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₁`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₂`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₃`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
-/
instance isIso_homologyMap_of_isIso (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] [IsIso φ] :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap, homologyMap']
  infer_instance

section

variable (S) {A : C}
variable [HasHomology S]

/-- The canonical morphism `S.cycles ⟶ S.homology` for a short complex `S` that has homology. -/
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `S.cycles ⟶ S.homology` for a short complex `S` that has 
homology.
-/
noncomputable def homologyπ : S.cycles ⟶ S.homology :=
  S.leftHomologyπ ≫ S.leftHomologyIso.hom

/-- The canonical morphism `S.homology ⟶ S.opcycles` for a short complex `S` that has homology. -/
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `S.homology ⟶ S.opcycles` for a short complex `S` that ha
s homology.
-/
noncomputable def homologyι : S.homology ⟶ S.opcycles :=
  S.rightHomologyIso.inv ≫ S.rightHomologyι

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_comp_leftHomologyIso_inv :
    S.homologyπ ≫ S.leftHomologyIso.inv = S.leftHomologyπ := by
  dsimp only [homologyπ]
  simp only [assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.rightHomologyIso_hom_comp_homology** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightHomologyIso_hom_comp_homologyι :
    S.rightHomologyIso.hom ≫ S.homologyι = S.rightHomologyι := by
  dsimp only [homologyι]
  simp only [Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.toCycles_comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCycles_comp_homologyπ :
    S.toCycles ≫ S.homologyπ = 0 := by
  dsimp only [homologyπ]
  simp only [toCycles_comp_leftHomologyπ_assoc, zero_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_comp_fromOpcycles :
    S.homologyι ≫ S.fromOpcycles = 0 := by
  dsimp only [homologyι]
  simp only [assoc, rightHomologyι_comp_fromOpcycles, comp_zero]

/-- The homology `S.homology` of a short complex is
the cokernel of the morphism `S.toCycles : S.X₁ ⟶ S.cycles`. -/
/-
**CategoryTheory.ShortComplex.homologyIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：homologyIsCokernel : IsColimit (CokernelCofork.ofπ S.homologyπ S.toCycles_
comp_homologyπ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.toCycles_comp_homologyπ`：toCycles_comp_homol
ogyπ : S.toCycles ≫ S.homologyπ = 0

--- 原说明 ---
The homology `S.homology` of a short complex is
the cokernel of the morphism `S.toCycles : S.X₁ ⟶ S.cycles`.
-/
noncomputable def homologyIsCokernel :
    IsColimit (CokernelCofork.ofπ S.homologyπ S.toCycles_comp_homologyπ) :=
  IsColimit.ofIsoColimit S.leftHomologyIsCokernel
    (Cofork.ext S.leftHomologyIso rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The homology `S.homology` of a short complex is
the kernel of the morphism `S.fromOpcycles : S.opcycles ⟶ S.X₃`. -/
/-
**CategoryTheory.ShortComplex.homologyIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：homologyIsKernel : IsLimit (KernelFork.ofι S.homologyι S.homologyι_comp_fr
omOpcycles)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.homologyι_comp_fromOpcycles`：homologyι_comp_
fromOpcycles : S.homologyι ≫ S.fromOpcycles = 0

--- 原说明 ---
The homology `S.homology` of a short complex is
the kernel of the morphism `S.fromOpcycles : S.opcycles ⟶ S.X₃`.
-/
noncomputable def homologyIsKernel :
    IsLimit (KernelFork.ofι S.homologyι S.homologyι_comp_fromOpcycles) :=
  IsLimit.ofIsoLimit S.rightHomologyIsKernel
    (Fork.ext S.rightHomologyIso (by simp))
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi S.homologyπ :=
  Limits.epi_of_isColimit_cofork (S.homologyIsCokernel)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono S.homologyι :=
  Limits.mono_of_isLimit_fork (S.homologyIsKernel)

/-- Given a morphism `k : S.cycles ⟶ A` such that `S.toCycles ≫ k = 0`, this is the
induced morphism `S.homology ⟶ A`. -/
/-
**CategoryTheory.ShortComplex.descHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) : S.homology ⟶ A
参数：k : S.cycles ⟶ A；hk : S.toCycles ≫ k = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.toCycles_comp_homologyπ`：toCycles_comp_homol
ogyπ : S.toCycles ≫ S.homologyπ = 0

--- 原说明 ---
Given a morphism `k : S.cycles ⟶ A` such that `S.toCycles ≫ k = 0`, this is the
induced morphism `S.homology ⟶ A`.
-/
noncomputable def descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.homology ⟶ A :=
  S.homologyIsCokernel.desc (CokernelCofork.ofπ k hk)

/-- Given a morphism `k : A ⟶ S.opcycles` such that `k ≫ S.fromOpcycles = 0`, this is the
induced morphism `A ⟶ S.homology`. -/
/-
**CategoryTheory.ShortComplex.liftHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：liftHomology (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) : A ⟶ S.ho
mology
参数：k : A ⟶ S.opcycles；hk : k ≫ S.fromOpcycles = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.homologyι_comp_fromOpcycles`：homologyι_comp_
fromOpcycles : S.homologyι ≫ S.fromOpcycles = 0

--- 原说明 ---
Given a morphism `k : A ⟶ S.opcycles` such that `k ≫ S.fromOpcycles = 0`, this i
s the
induced morphism `A ⟶ S.homology`.
-/
noncomputable def liftHomology (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) :
    A ⟶ S.homology :=
  S.homologyIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.homologyπ ≫ S.descHomology k hk = k :=
  Cofork.IsColimit.π_desc S.homologyIsCokernel

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.liftHomology_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftHomology_ι (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) :
    S.liftHomology k hk ≫ S.homologyι = k :=
  Fork.IsLimit.lift_ι S.homologyIsKernel

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    S₁.homologyπ ≫ homologyMap φ = cyclesMap φ ≫ S₂.homologyπ := by
  simp only [← cancel_mono S₂.leftHomologyIso.inv, assoc, ← leftHomologyIso_inv_naturality φ,
    homologyπ_comp_leftHomologyIso_inv]
  simp only [homologyπ, assoc, Iso.hom_inv_id_assoc, leftHomologyπ_naturality]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap φ ≫ S₂.homologyι = S₁.homologyι ≫ S₁.opcyclesMap φ := by
  simp only [← cancel_epi S₁.rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc φ,
    rightHomologyIso_hom_comp_homologyι, rightHomologyι_naturality]
  simp only [homologyι, assoc, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homology_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homology_π_ι :
    S.homologyπ ≫ S.homologyι = S.iCycles ≫ S.pOpcycles := by
  dsimp only [homologyπ, homologyι]
  simpa only [assoc, S.leftRightHomologyComparison_fac] using S.π_leftRightHomologyComparison_ι

/-- The homology of a short complex `S` identifies to the kernel of the induced morphism
`cokernel S.f ⟶ S.X₃`. -/
/-
**CategoryTheory.ShortComplex.homologyIsoKernelDesc** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：homologyIsoKernelDesc [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g 
S.zero)] : S.homology ≅ kernel (cokernel.desc S.f S.g S.zero)
参数：cokernel.desc S.f S.g S.zero。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
The homology of a short complex `S` identifies to the kernel of the induced morp
hism
`cokernel S.f ⟶ S.X₃`.
-/
noncomputable def homologyIsoKernelDesc [HasCokernel S.f]
    [HasKernel (cokernel.desc S.f S.g S.zero)] :
    S.homology ≅ kernel (cokernel.desc S.f S.g S.zero) :=
  S.rightHomologyIso.symm ≪≫ S.rightHomologyIsoKernelDesc

/-- The homology of a short complex `S` identifies to the cokernel of the induced morphism
`S.X₁ ⟶ kernel S.g`. -/
/-
**CategoryTheory.ShortComplex.homologyIsoCokernelLift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex`。
形式化陈述：homologyIsoCokernelLift [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f 
S.zero)] : S.homology ≅ cokernel (kernel.lift S.g S.f S.zero)
参数：kernel.lift S.g S.f S.zero。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
The homology of a short complex `S` identifies to the cokernel of the induced mo
rphism
`S.X₁ ⟶ kernel S.g`.
-/
noncomputable def homologyIsoCokernelLift [HasKernel S.g]
    [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.homology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  S.leftHomologyIso.symm ≪≫ S.leftHomologyIsoCokernelLift

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.homology** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LeftHomologyData.homologyπ_comp_homologyIso_hom (h : S.LeftHomologyData) :
    S.homologyπ ≫ h.homologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc,
    leftHomologyπ_comp_leftHomologyIso_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LeftHomologyData.π_comp_homologyIso_inv (h : S.LeftHomologyData) :
    h.π ≫ h.homologyIso.inv = h.cyclesIso.inv ≫ S.homologyπ := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, π_comp_leftHomologyIso_inv_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.RightHomologyData.homologyIso_inv_comp_homology** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RightHomologyData.homologyIso_inv_comp_homologyι (h : S.RightHomologyData) :
    h.homologyIso.inv ≫ S.homologyι = h.ι ≫ h.opcyclesIso.inv := by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, assoc, Iso.hom_inv_id_assoc,
    rightHomologyIso_inv_comp_rightHomologyι]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.RightHomologyData.homologyIso_hom_comp_** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RightHomologyData.homologyIso_hom_comp_ι (h : S.RightHomologyData) :
    h.homologyIso.hom ≫ h.ι = S.homologyι ≫ h.opcyclesIso.hom := by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, rightHomologyIso_hom_comp_ι]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_hom_comp_leftHomology
Iso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`
。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology] (h : S.LeftHomologyData),   CategoryTheory.CategoryStruct.comp
 h.homologyIso.hom h.leftHomologyIso.inv = S.leftHomologyIso.inv
参数：S : CategoryTheory.ShortComplex C；h : S.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.homologyIso_hom_comp_leftHomologyIso_inv (h : S.LeftHomologyData) :
    h.homologyIso.hom ≫ h.leftHomologyIso.inv = S.leftHomologyIso.inv := by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_hom_comp_homology
Iso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`
。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology] (h : S.LeftHomologyData),   CategoryTheory.CategoryStruct.comp
 h.leftHomologyIso.hom h.homologyIso.inv = S.leftHomologyIso.hom
参数：S : CategoryTheory.ShortComplex C；h : S.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv (h : S.LeftHomologyData) :
    h.leftHomologyIso.hom ≫ h.homologyIso.inv = S.leftHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.RightHomologyData.homologyIso_hom_comp_rightHomolo
gyIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyDa
ta`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology] (h : S.RightHomologyData),   CategoryTheory.CategoryStruct.com
p h.homologyIso.hom h.rightHomologyIso.inv = S.rightHomologyIso.inv
参数：S : CategoryTheory.ShortComplex C；h : S.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv (h : S.RightHomologyData) :
    h.homologyIso.hom ≫ h.rightHomologyIso.inv = S.rightHomologyIso.inv := by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_hom_comp_homolo
gyIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyDa
ta`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology] (h : S.RightHomologyData),   CategoryTheory.CategoryStruct.com
p h.rightHomologyIso.hom h.homologyIso.inv = S.rightHomologyIso.hom
参数：S : CategoryTheory.ShortComplex C；h : S.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv (h : S.RightHomologyData) :
    h.rightHomologyIso.hom ≫ h.homologyIso.inv = S.rightHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ShortComplex.comp_homologyMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：comp_homologyMap_comp [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) (h₁ 
: S₁.LeftHomologyData) (h₂ : S₂.RightHomologyData) : h₁.π ≫ h₁.homologyIso.inv ≫
 homologyMap φ ≫ h₂.homologyIso.hom ≫ h₂.ι = h₁.i ≫ φ.τ₂ ≫ h₂.p
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.RightHomologyData。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyι_naturality'`：rightHomologyι_n
aturality' : rightHomologyMap' φ h₁ h₂ ≫ h₂.ι = h₁.ι ≫ opcyclesMap' φ h₁ h₂
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyι_naturality'_assoc`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyπ_naturality'_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.comm_assoc`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.p_opcyclesMap'_assoc`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S₁ S₂ : CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.p_opcyclesMap'`：p_opcyclesMap' : h₁.p ≫ opcy
clesMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_i_assoc`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_homologyMap_comp [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.π ≫ h₁.homologyIso.inv ≫ homologyMap φ ≫ h₂.homologyIso.hom ≫ h₂.ι =
      h₁.i ≫ φ.τ₂ ≫ h₂.p := by
  dsimp only [LeftHomologyData.homologyIso, RightHomologyData.homologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyIso, rightHomologyIso,
    leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.cyclesIso, RightHomologyData.opcyclesIso,
    LeftHomologyData.leftHomologyIso, RightHomologyData.rightHomologyIso,
    homologyMap, homologyMap']
  simp only [assoc, rightHomologyι_naturality', rightHomologyι_naturality'_assoc,
    leftHomologyπ_naturality'_assoc, HomologyData.comm_assoc, p_opcyclesMap'_assoc,
    id_τ₂, p_opcyclesMap', id_comp, cyclesMap'_i_assoc]

@[reassoc]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_homologyMap_ι [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.homologyπ ≫ homologyMap φ ≫ S₂.homologyι = S₁.iCycles ≫ φ.τ₂ ≫ S₂.pOpcycles := by
  simp only [homologyι_naturality, homology_π_ι_assoc, p_opcyclesMap]

end

variable (S)

/-- The canonical isomorphism `S.op.homology ≅ Opposite.op S.homology` when a short
complex `S` has homology. -/
/-
**CategoryTheory.ShortComplex.homologyOpIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：homologyOpIso [S.HasHomology] : S.op.homology ≅ Opposite.op S.homology
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…

--- 原说明 ---
The canonical isomorphism `S.op.homology ≅ Opposite.op S.homology` when a short
complex `S` has homology.
-/
noncomputable def homologyOpIso [S.HasHomology] :
    S.op.homology ≅ Opposite.op S.homology :=
  S.op.leftHomologyIso.symm ≪≫ S.leftHomologyOpIso ≪≫ S.rightHomologyIso.symm.op

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.homologyMap'_op** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (φ 
: S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData),   (CategoryTheory.Shor
tComplex.homologyMap' φ h₁ h₂).op =     CategoryTheory.CategoryStruct.comp h₂.is
o.inv.op       (CategoryTheory.CategoryStruct.comp         (CategoryTheory.Short
Complex.homologyMap' (CategoryTheory.ShortComplex.opMap φ) h₂.op h₁.op) h₁.iso.h
om.op)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；CategoryTheory.ShortCom
plex.homologyMap' φ h₁ h₂；CategoryTheory.CategoryStruct.comp         (CategoryTh
eory.ShortComplex.homologyMap' (CategoryTheory.ShortComplex.opMap φ) h₂.op h₁.op
) h₁.iso.hom.op。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.HomologyMapData.homologyMap'_eq`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.HomologyMapData.comm_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap'_op : (homologyMap' φ h₁ h₂).op =
    h₂.iso.inv.op ≫ homologyMap' (opMap φ) h₂.op h₁.op ≫ h₁.iso.hom.op :=
  Quiver.Hom.unop_inj (by
    dsimp
    have γ : HomologyMapData φ h₁ h₂ := default
    simp only [γ.homologyMap'_eq, γ.op.homologyMap'_eq, HomologyData.op_left,
      HomologyMapData.op_left, RightHomologyMapData.op_φH, Quiver.Hom.unop_op, assoc,
      ← γ.comm_assoc, Iso.hom_inv_id, comp_id])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.homologyMap_op** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：homologyMap_op [HasHomology S₁] [HasHomology S₂] : (homologyMap φ).op = (S
₂.homologyOpIso).inv ≫ homologyMap (opMap φ) ≫ (S₁.homologyOpIso).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_op`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `CategoryTheory.ShortComplex.instHasLeftHomologyOppositeOpOfHasRightHomol
ogy`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_op`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_op [HasHomology S₁] [HasHomology S₂] :
    (homologyMap φ).op =
      (S₂.homologyOpIso).inv ≫ homologyMap (opMap φ) ≫ (S₁.homologyOpIso).hom := by
  dsimp only [homologyMap, homologyOpIso]
  rw [homologyMap'_op]
  dsimp only [Iso.symm, Iso.trans, Iso.op, Iso.refl, rightHomologyIso, leftHomologyIso,
    leftHomologyOpIso, leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [assoc, rightHomologyMap'_op, op_comp, ← leftHomologyMap'_comp_assoc, id_comp,
    opMap_id, comp_id, HomologyData.op_left]

@[reassoc]
/-
**CategoryTheory.ShortComplex.homologyOpIso_hom_naturality** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：homologyOpIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] : homologyM
ap (opMap φ) ≫ (S₁.homologyOpIso).hom = S₂.homologyOpIso.hom ≫ (homologyMap φ).o
p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_op`：homologyMap_op [HasHomology 
S₁] [HasHomology S₂] : (homologyMap φ).op = (S₂.homologyOpIso).inv ≫ homologyMap
 (opMap φ) ≫ (S₁.homologyOpIso).…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyOpIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (opMap φ) ≫ (S₁.homologyOpIso).hom =
      S₂.homologyOpIso.hom ≫ (homologyMap φ).op := by
  simp [homologyMap_op]

@[reassoc]
/-
**CategoryTheory.ShortComplex.homologyOpIso_inv_naturality** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：homologyOpIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] : (homology
Map φ).op ≫ (S₁.homologyOpIso).inv = S₂.homologyOpIso.inv ≫ homologyMap (opMap φ
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_op`：homologyMap_op [HasHomology 
S₁] [HasHomology S₂] : (homologyMap φ).op = (S₂.homologyOpIso).inv ≫ homologyMap
 (opMap φ) ≫ (S₁.homologyOpIso).…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyOpIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] :
    (homologyMap φ).op ≫ (S₁.homologyOpIso).inv =
      S₂.homologyOpIso.inv ≫ homologyMap (opMap φ) := by
  simp [homologyMap_op]

variable (C)

/-- The natural isomorphism `(homologyFunctor C).op ≅ opFunctor C ⋙ homologyFunctor Cᵒᵖ`
which relates the homology in `C` and in `Cᵒᵖ`. -/
/-
**CategoryTheory.ShortComplex.homologyFunctorOpNatIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex`。
形式化陈述：homologyFunctorOpNatIso [CategoryWithHomology C] : (homologyFunctor C).op 
≅ opFunctor C ⋙ homologyFunctor Cᵒᵖ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instCategoryWithHomologyOpposite`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   [CategoryTheory.CategoryWithH…

--- 原说明 ---
The natural isomorphism `(homologyFunctor C).op ≅ opFunctor C ⋙ homologyFunctor 
Cᵒᵖ`
which relates the homology in `C` and in `Cᵒᵖ`.
-/
noncomputable def homologyFunctorOpNatIso [CategoryWithHomology C] :
    (homologyFunctor C).op ≅ opFunctor C ⋙ homologyFunctor Cᵒᵖ :=
  NatIso.ofComponents (fun S => S.unop.homologyOpIso.symm)
    (fun _ ↦ homologyOpIso_inv_naturality _)

variable {C} {A : C}
/-
**CategoryTheory.ShortComplex.liftCycles_homology** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftCycles_homologyπ_eq_zero_of_boundary [S.HasHomology]
    (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.homologyπ = 0 := by
  dsimp only [homologyπ]
  rw [S.liftCycles_leftHomologyπ_eq_zero_of_boundary_assoc k x hx, zero_comp]

@[reassoc]
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_descOpcycles_eq_zero_of_boundary [S.HasHomology]
    (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    S.homologyι ≫ S.descOpcycles k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  dsimp only [homologyι]
  rw [assoc, S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary k x hx, comp_zero]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_homologyMap_of_isIso_cyclesMap_of_epi {φ : S₁ ⟶ S₂} [S₁.HasHomology]
 [S₂.HasHomology] (h₁ : IsIso (cyclesMap φ)) (h₂ : Epi φ.τ₁) : IsIso (homologyMa
p φ)
参数：h₁ : IsIso (cyclesMap φ)；h₂ : Epi φ.τ₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用引理 `CategoryTheory.ShortComplex.toCycles_comp_homologyπ`：toCycles_comp_homol
ogyπ : S.toCycles ≫ S.homologyπ = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.instEpiHomologyπ`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.ShortComplex.homologyπ_naturality_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.ShortComplex.homologyπ_naturality`：homologyπ_naturality (
φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] : S₁.homologyπ ≫ homologyMap φ = 
cyclesMap φ ≫ S₂.homologyπ
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
-/
lemma isIso_homologyMap_of_isIso_cyclesMap_of_epi {φ : S₁ ⟶ S₂}
    [S₁.HasHomology] [S₂.HasHomology] (h₁ : IsIso (cyclesMap φ)) (h₂ : Epi φ.τ₁) :
    IsIso (homologyMap φ) := by
  have h : S₂.toCycles ≫ inv (cyclesMap φ) ≫ S₁.homologyπ = 0 := by
    simp only [← cancel_epi φ.τ₁, ← toCycles_naturality_assoc,
      IsIso.hom_inv_id_assoc, toCycles_comp_homologyπ, comp_zero]
  have ⟨z, hz⟩ := CokernelCofork.IsColimit.desc' S₂.homologyIsCokernel _ h
  dsimp at hz
  refine ⟨⟨z, ?_, ?_⟩⟩
  · rw [← cancel_epi S₁.homologyπ, homologyπ_naturality_assoc, hz,
      IsIso.hom_inv_id_assoc, comp_id]
  · rw [← cancel_epi S₂.homologyπ, reassoc_of% hz, homologyπ_naturality,
      IsIso.inv_hom_id_assoc, comp_id]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_homologyMap_of_isIso_opcyclesMap_of_mono {φ : S₁ ⟶ S₂} [S₁.HasHomolo
gy] [S₂.HasHomology] (h₁ : IsIso (opcyclesMap φ)) (h₂ : Mono φ.τ₃) : IsIso (homo
logyMap φ)
参数：h₁ : IsIso (opcyclesMap φ)；h₂ : Mono φ.τ₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用引理 `CategoryTheory.ShortComplex.homologyι_comp_fromOpcycles`：homologyι_comp_
fromOpcycles : S.homologyι ≫ S.fromOpcycles = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.instMonoHomologyι`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ShortComplex.homologyι_naturality_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {S₁ S₂ : CategoryTheory.Short…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.homologyι_naturality`：homologyι_naturality (
φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] : homologyMap φ ≫ S₂.homologyι = 
S₁.homologyι ≫ S₁.opcyclesMap φ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
lemma isIso_homologyMap_of_isIso_opcyclesMap_of_mono {φ : S₁ ⟶ S₂}
    [S₁.HasHomology] [S₂.HasHomology] (h₁ : IsIso (opcyclesMap φ)) (h₂ : Mono φ.τ₃) :
    IsIso (homologyMap φ) := by
  have h : (S₂.homologyι ≫ inv (opcyclesMap φ)) ≫ S₁.fromOpcycles = 0 := by
    simp only [← cancel_mono φ.τ₃, zero_comp, assoc, ← fromOpcycles_naturality,
      IsIso.inv_hom_id_assoc, homologyι_comp_fromOpcycles]
  have ⟨z, hz⟩ := KernelFork.IsLimit.lift' S₁.homologyIsKernel _ h
  dsimp at hz
  refine ⟨⟨z, ?_, ?_⟩⟩
  · rw [← cancel_mono S₁.homologyι, id_comp, assoc, hz, homologyι_naturality_assoc,
      IsIso.hom_inv_id, comp_id]
  · rw [← cancel_mono S₂.homologyι, assoc, homologyι_naturality, reassoc_of% hz,
      IsIso.inv_hom_id, comp_id, id_comp]
/-
**CategoryTheory.ShortComplex.isZero_homology_of_isZero_X** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isZero_homology_of_isZero_X₂ (hS : IsZero S.X₂) [S.HasHomology] :
    IsZero S.homology :=
  IsZero.of_iso hS (HomologyData.ofZeros S (hS.eq_of_tgt _ _)
    (hS.eq_of_src _ _)).left.homologyIso
/-
**CategoryTheory.ShortComplex.isIso_homology** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_homologyπ (hf : S.f = 0) [S.HasHomology] :
    IsIso S.homologyπ := by
  have := S.isIso_leftHomologyπ hf
  dsimp only [homologyπ]
  infer_instance
/-
**CategoryTheory.ShortComplex.isIso_homology** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_homologyι (hg : S.g = 0) [S.HasHomology] :
    IsIso S.homologyι := by
  have := S.isIso_rightHomologyι hg
  dsimp only [homologyι]
  infer_instance

/-- The canonical isomorphism `S.cycles ≅ S.homology` when `S.f = 0`. -/
@[simps! hom]
/-
**CategoryTheory.ShortComplex.asIsoHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `S.cycles ≅ S.homology` when `S.f = 0`.
-/
noncomputable def asIsoHomologyπ (hf : S.f = 0) [S.HasHomology] :
    S.cycles ≅ S.homology := by
  have := S.isIso_homologyπ hf
  exact asIso S.homologyπ

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.asIsoHomology** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma asIsoHomologyπ_inv_comp_homologyπ (hf : S.f = 0) [S.HasHomology] :
    (S.asIsoHomologyπ hf).inv ≫ S.homologyπ = 𝟙 _ := Iso.inv_hom_id _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_comp_asIsoHomologyπ_inv (hf : S.f = 0) [S.HasHomology] :
    S.homologyπ ≫ (S.asIsoHomologyπ hf).inv = 𝟙 _ := (S.asIsoHomologyπ hf).hom_inv_id

/-- The canonical isomorphism `S.homology ≅ S.opcycles` when `S.g = 0`. -/
@[simps! hom]
/-
**CategoryTheory.ShortComplex.asIsoHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `S.homology ≅ S.opcycles` when `S.g = 0`.
-/
noncomputable def asIsoHomologyι (hg : S.g = 0) [S.HasHomology] :
    S.homology ≅ S.opcycles := by
  have := S.isIso_homologyι hg
  exact asIso S.homologyι

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.asIsoHomology** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma asIsoHomologyι_inv_comp_homologyι (hg : S.g = 0) [S.HasHomology] :
    (S.asIsoHomologyι hg).inv ≫ S.homologyι = 𝟙 _ := Iso.inv_hom_id _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：homology [HasHomology S] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_comp_asIsoHomologyι_inv (hg : S.g = 0) [S.HasHomology] :
    S.homologyι ≫ (S.asIsoHomologyι hg).inv = 𝟙 _ := (S.asIsoHomologyι hg).hom_inv_id
/-
**CategoryTheory.ShortComplex.mono_homologyMap_of_mono_opcyclesMap'** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mono_homologyMap_of_mono_opcyclesMap' [S₁.HasHomology] [S₂.HasHomology] (h
 : Mono (opcyclesMap φ)) : Mono (homologyMap φ)
参数：h : Mono (opcyclesMap φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.homologyι_naturality`：homologyι_naturality (
φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] : homologyMap φ ≫ S₂.homologyι = 
S₁.homologyι ≫ S₁.opcyclesMap φ
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.ShortComplex.instMonoHomologyι`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
-/
lemma mono_homologyMap_of_mono_opcyclesMap'
    [S₁.HasHomology] [S₂.HasHomology] (h : Mono (opcyclesMap φ)) :
    Mono (homologyMap φ) := by
  have : Mono (homologyMap φ ≫ S₂.homologyι) := by
    rw [homologyι_naturality φ]
    apply mono_comp
  exact mono_of_mono (homologyMap φ) S₂.homologyι
/-
**CategoryTheory.ShortComplex.mono_homologyMap_of_mono_opcyclesMap** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mono_homologyMap_of_mono_opcyclesMap [S₁.HasHomology] [S₂.HasHomology] [Mo
no (opcyclesMap φ)] : Mono (homologyMap φ)
参数：opcyclesMap φ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.mono_homologyMap_of_mono_opcyclesMap'`：mono_
homologyMap_of_mono_opcyclesMap' [S₁.HasHomology] [S₂.HasHomology] (h : Mono (op
cyclesMap φ)) : Mono (homologyMap φ)
-/
instance mono_homologyMap_of_mono_opcyclesMap
    [S₁.HasHomology] [S₂.HasHomology] [Mono (opcyclesMap φ)] :
    Mono (homologyMap φ) :=
  mono_homologyMap_of_mono_opcyclesMap' φ inferInstance
/-
**CategoryTheory.ShortComplex.epi_homologyMap_of_epi_cyclesMap'** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：epi_homologyMap_of_epi_cyclesMap' [S₁.HasHomology] [S₂.HasHomology] (h : E
pi (cyclesMap φ)) : Epi (homologyMap φ)
参数：h : Epi (cyclesMap φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.homologyπ_naturality`：homologyπ_naturality (
φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] : S₁.homologyπ ≫ homologyMap φ = 
cyclesMap φ ≫ S₂.homologyπ
· 使用定理 `CategoryTheory.ShortComplex.instEpiHomologyπ`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   (S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.epi_of_epi`：epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ 
g)] : Epi g
-/
lemma epi_homologyMap_of_epi_cyclesMap'
    [S₁.HasHomology] [S₂.HasHomology] (h : Epi (cyclesMap φ)) :
    Epi (homologyMap φ) := by
  have : Epi (S₁.homologyπ ≫ homologyMap φ) := by
    rw [homologyπ_naturality φ]
    apply epi_comp
  exact epi_of_epi S₁.homologyπ (homologyMap φ)
/-
**CategoryTheory.ShortComplex.epi_homologyMap_of_epi_cyclesMap** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：epi_homologyMap_of_epi_cyclesMap [S₁.HasHomology] [S₂.HasHomology] [Epi (c
yclesMap φ)] : Epi (homologyMap φ)
参数：cyclesMap φ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.epi_homologyMap_of_epi_cyclesMap'`：epi_homol
ogyMap_of_epi_cyclesMap' [S₁.HasHomology] [S₂.HasHomology] (h : Epi (cyclesMap φ
)) : Epi (homologyMap φ)
-/
instance epi_homologyMap_of_epi_cyclesMap
    [S₁.HasHomology] [S₂.HasHomology] [Epi (cyclesMap φ)] :
    Epi (homologyMap φ) :=
  epi_homologyMap_of_epi_cyclesMap' φ inferInstance

/-- Given a short complex `S` such that `S.HasHomology`, this is the canonical
left homology data for `S` whose `K` and `H` fields are
respectively `S.cycles` and `S.homology`. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.canonical** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       (S : CategoryTheory.ShortComp
lex C) → [S.HasHomology] → S.LeftHomologyData
参数：S : CategoryTheory.ShortComplex C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.toCycles_comp_homologyπ`：toCycles_comp_homol
ogyπ : S.toCycles ≫ S.homologyπ = 0

--- 原说明 ---
Given a short complex `S` such that `S.HasHomology`, this is the canonical
left homology data for `S` whose `K` and `H` fields are
respectively `S.cycles` and `S.homology`.
-/
noncomputable def LeftHomologyData.canonical [S.HasHomology] : S.LeftHomologyData where
  K := S.cycles
  H := S.homology
  i := S.iCycles
  π := S.homologyπ
  wi := by simp
  hi := S.cyclesIsKernel
  wπ := S.toCycles_comp_homologyπ
  hπ := S.homologyIsCokernel

/-- Computation of the `f'` field of `LeftHomologyData.canonical`. -/
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.canonical_f'** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology],   (CategoryTheory.ShortComplex.LeftHomologyData.canonical S).
f' = S.toCycles
参数：S : CategoryTheory.ShortComplex C；CategoryTheory.ShortComplex.LeftHomologyDat
a.canonical S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computation of the `f'` field of `LeftHomologyData.canonical`.
-/
lemma LeftHomologyData.canonical_f' [S.HasHomology] :
    (LeftHomologyData.canonical S).f' = S.toCycles := rfl

/-- Given a short complex `S` such that `S.HasHomology`, this is the canonical
right homology data for `S` whose `Q` and `H` fields are
respectively `S.opcycles` and `S.homology`. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.RightHomologyData.canonical** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       (S : CategoryTheory.ShortComp
lex C) → [S.HasHomology] → S.RightHomologyData
参数：S : CategoryTheory.ShortComplex C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.homologyι_comp_fromOpcycles`：homologyι_comp_
fromOpcycles : S.homologyι ≫ S.fromOpcycles = 0

--- 原说明 ---
Given a short complex `S` such that `S.HasHomology`, this is the canonical
right homology data for `S` whose `Q` and `H` fields are
respectively `S.opcycles` and `S.homology`.
-/
noncomputable def RightHomologyData.canonical [S.HasHomology] : S.RightHomologyData where
  Q := S.opcycles
  H := S.homology
  p := S.pOpcycles
  ι := S.homologyι
  wp := by simp
  hp := S.opcyclesIsCokernel
  wι := S.homologyι_comp_fromOpcycles
  hι := S.homologyIsKernel

/-- Computation of the `g'` field of `RightHomologyData.canonical`. -/
@[simp]
/-
**CategoryTheory.ShortComplex.RightHomologyData.canonical_g'** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [inst_2
 : S.HasHomology],   (CategoryTheory.ShortComplex.RightHomologyData.canonical S)
.g' = S.fromOpcycles
参数：S : CategoryTheory.ShortComplex C；CategoryTheory.ShortComplex.RightHomologyDa
ta.canonical S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computation of the `g'` field of `RightHomologyData.canonical`.
-/
lemma RightHomologyData.canonical_g' [S.HasHomology] :
    (RightHomologyData.canonical S).g' = S.fromOpcycles := rfl

set_option backward.defeqAttrib.useBackward true in
/-- Given a short complex `S` such that `S.HasHomology`, this is the canonical
homology data for `S` whose `left.K`, `left/right.H` and `right.Q` fields are
respectively `S.cycles`, `S.homology` and `S.opcycles`. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.HomologyData.canonical** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       (S : CategoryTheory.ShortComp
lex C) → [S.HasHomology] → S.HomologyData
参数：S : CategoryTheory.ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short complex `S` such that `S.HasHomology`, this is the canonical
homology data for `S` whose `left.K`, `left/right.H` and `right.Q` fields are
respectively `S.cycles`, `S.homology` and `S.opcycles`.
-/
noncomputable def HomologyData.canonical [S.HasHomology] : S.HomologyData where
  left := LeftHomologyData.canonical S
  right := RightHomologyData.canonical S
  iso := Iso.refl _

end ShortComplex

end CategoryTheory

