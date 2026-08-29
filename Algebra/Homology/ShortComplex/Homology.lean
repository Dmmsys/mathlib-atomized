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

/--
Definition of `HomologyData` / `HomologyData` 的定义

English:
structure HomologyData
  parameters: where
  axioms and operations (4):
    - left : S.LeftHomologyData
    - right : S.RightHomologyData
    - iso : left.H ≅ right.H
    - comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p  [default: by cat_disch]

中文:
结构 同调数据
  参数: where
  公理与运算 (4 个):
    - left : S.LeftHomologyData
    - right : S.RightHomologyData
    - iso : left.H ≅ right.H
    - comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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

/--
Definition of `HomologyMapData` / `HomologyMapData` 的定义

English:
structure HomologyMapData
  parameters: where
  axioms and operations (2):
    - left : LeftHomologyMapData φ h₁.left h₂.left
    - right : RightHomologyMapData φ h₁.right h₂.right

中文:
结构 同调映射数据
  参数: where
  公理与运算 (2 个):
    - left : LeftHomologyMapData φ h₁.left h₂.left
    - right : RightHomologyMapData φ h₁.right h₂.right

Depends on / 依赖: infer_instance
-/
structure HomologyMapData where
  /-- a left homology map data -/
  left : LeftHomologyMapData φ h₁.left h₂.left
  /-- a right homology map data -/
  right : RightHomologyMapData φ h₁.right h₂.right

namespace HomologyMapData

variable {φ h₁ h₂}

@[reassoc]
/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  given: (h : HomologyMapData φ h₁ h₂)
  proof: by
  simp only [← cancel_epi h₁.left.π, ← cancel_mono h₂.right.ι, assoc,
    LeftHomologyMapData.commπ_assoc, HomologyData.comm, LeftHomologyMapData.commi_assoc,
    RightHomologyMapData.commι, HomologyData.comm_assoc, RightHomologyMapData.commp]

中文:
引理 comm
  条件: (h : 同调映射数据 φ h₁ h₂)
  证明: by
  simp only [← cancel_epi h₁.left.π, ← cancel_mono h₂.right.ι, assoc,
    LeftHomologyMapData.commπ_assoc, HomologyData.comm, LeftHomologyMapData.commi_assoc,
    RightHomologyMapData.commι, HomologyData.comm_assoc, RightHomologyMapData.commp]

Depends on / 依赖: HomologyData, HomologyData.comm, HomologyData.comm_assoc, LeftHomologyMapData, LeftHomologyMapData.comm, LeftHomologyMapData.commi_assoc, RightHomologyMapData, RightHomologyMapData.comm, RightHomologyMapData.commp, cancel_epi, cancel_mono, comm_assoc, commi_assoc
-/
lemma comm (h : HomologyMapData φ h₁ h₂) :
    h.left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫ h.right.φH := by
  simp only [← cancel_epi h₁.left.π, ← cancel_mono h₂.right.ι, assoc,
    LeftHomologyMapData.commπ_assoc, HomologyData.comm, LeftHomologyMapData.commi_assoc,
    RightHomologyMapData.commι, HomologyData.comm_assoc, RightHomologyMapData.commp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (HomologyMapData φ h₁ h₂)
  body: ⟨by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩
  simp only [mk.injEq, eq_iff_true_of_subsingleton, and_self]⟩

中文:
实例 :
  签名: 子单例 (同调映射数据 φ h₁ h₂)
  定义体: ⟨by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩
  simp only [mk.injEq, eq_iff_true_of_subsingleton, and_self]⟩

Depends on / 依赖: and_self, eq_iff_true_of_subsingleton, mk.injEq
-/
instance : Subsingleton (HomologyMapData φ h₁ h₂) := ⟨by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩
  simp only [mk.injEq, eq_iff_true_of_subsingleton, and_self]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (HomologyMapData φ h₁ h₂)
  body: ⟨⟨default, default⟩⟩

中文:
实例 :
  签名: 可居 (同调映射数据 φ h₁ h₂)
  定义体: ⟨⟨default, default⟩⟩
-/
instance : Inhabited (HomologyMapData φ h₁ h₂) :=
  ⟨⟨default, default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (HomologyMapData φ h₁ h₂)
  body: Unique.mk' _

中文:
实例 :
  签名: 唯一 (同调映射数据 φ h₁ h₂)
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance : Unique (HomologyMapData φ h₁ h₂) := Unique.mk' _

variable (φ h₁ h₂)

/--
Definition of `homologyMapData` / `homologyMapData` 的定义

English:
definition homologyMapData
  signature: : HomologyMapData φ h₁ h₂
  body: default

中文:
定义 homologyMapData
  签名: : 同调映射数据 φ h₁ h₂
  定义体: default
-/
def homologyMapData : HomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

/--
lemma `congr_left_φH` / 引理 `congr_left_φH`

English:
lemma congr_left_φH
  given: {γ₁ γ₂ : HomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  proof: by rw [eq]

中文:
引理 congr_left_φH
  条件: {γ₁ γ₂ : 同调映射数据 φ h₁ h₂} (eq : γ₁ = γ₂)
  证明: by rw [eq]
-/
lemma congr_left_φH {γ₁ γ₂ : HomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) :
    γ₁.left.φH = γ₂.left.φH := by rw [eq]

end HomologyMapData

namespace HomologyData

set_option backward.defeqAttrib.useBackward true in
/-- When the first map `S.f` is zero, this is the homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
/--
Definition of `ofIsLimitKernelFork` / `ofIsLimitKernelFork` 的定义

English:
definition ofIsLimitKernelFork
  signature: (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
  body: LeftHomologyData.ofIsLimitKernelFork S hf c hc
  right := RightHomologyData.ofIsLimitKernelFork S hf c hc
  iso := Iso.refl _

中文:
定义 ofIsLimitKernelFork
  签名: (hf : S.f = 0) (c : 核叉 S.g) (hc : 是极限 c)
  定义体: LeftHomologyData.ofIsLimitKernelFork S hf c hc
  right := RightHomologyData.ofIsLimitKernelFork S hf c hc
  iso := Iso.refl _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofIsLimitKernelFork, infer_instance, ofIsLimitKernelFork
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
/--
Definition of `ofHasKernel` / `ofHasKernel` 的定义

English:
definition ofHasKernel
  signature: (hf : S.f = 0) [HasKernel S.g]
  body: LeftHomologyData.ofHasKernel S hf
  right := RightHomologyData.ofHasKernel S hf
  iso := Iso.refl _

中文:
定义 ofHasKernel
  签名: (hf : S.f = 0) [HasKernel S.g]
  定义体: LeftHomologyData.ofHasKernel S hf
  right := RightHomologyData.ofHasKernel S hf
  iso := Iso.refl _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofHasKernel, ofHasKernel
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
/--
Definition of `ofIsColimitCokernelCofork` / `ofIsColimitCokernelCofork` 的定义

English:
definition ofIsColimitCokernelCofork
  signature: (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c)
  body: LeftHomologyData.ofIsColimitCokernelCofork S hg c hc
  right := RightHomologyData.ofIsColimitCokernelCofork S hg c hc
  iso := Iso.refl _

中文:
定义 ofIsColimitCokernelCofork
  签名: (hg : S.g = 0) (c : 余核余叉 S.f) (hc : 是余极限 c)
  定义体: LeftHomologyData.ofIsColimitCokernelCofork S hg c hc
  right := RightHomologyData.ofIsColimitCokernelCofork S hg c hc
  iso := Iso.refl _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofIsColimitCokernelCofork, ofIsColimitCokernelCofork
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
/--
Definition of `ofHasCokernel` / `ofHasCokernel` 的定义

English:
definition ofHasCokernel
  signature: (hg : S.g = 0) [HasCokernel S.f]
  body: LeftHomologyData.ofHasCokernel S hg
  right := RightHomologyData.ofHasCokernel S hg
  iso := Iso.refl _

中文:
定义 ofHasCokernel
  签名: (hg : S.g = 0) [HasCokernel S.f]
  定义体: LeftHomologyData.ofHasCokernel S hg
  right := RightHomologyData.ofHasCokernel S hg
  iso := Iso.refl _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofHasCokernel, ofHasCokernel
-/
noncomputable def ofHasCokernel (hg : S.g = 0) [HasCokernel S.f] :
    S.HomologyData where
  left := LeftHomologyData.ofHasCokernel S hg
  right := RightHomologyData.ofHasCokernel S hg
  iso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a homology data on S -/
@[simps]
/--
Definition of `ofZeros` / `ofZeros` 的定义

English:
definition ofZeros
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: LeftHomologyData.ofZeros S hf hg
  right := RightHomologyData.ofZeros S hf hg
  iso := Iso.refl _

中文:
定义 ofZeros
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: LeftHomologyData.ofZeros S hf hg
  right := RightHomologyData.ofZeros S hf hg
  iso := Iso.refl _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofZeros, ofZeros
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
/--
Definition of `ofEpiOfIsIsoOfMono` / `ofEpiOfIsIsoOfMono` 的定义

English:
definition ofEpiOfIsIsoOfMono
  signature: (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
  body: LeftHomologyData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono φ h.right
  iso := h.iso

中文:
定义 ofEpiOfIsIsoOfMono
  签名: (φ : S₁ ⟶ S₂) (h : 同调数据 S₁)
  定义体: LeftHomologyData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono φ h.right
  iso := h.iso

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofEpiOfIsIsoOfMono, h.left, ofEpiOfIsIsoOfMono
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
/--
Definition of `ofEpiOfIsIsoOfMono'` / `ofEpiOfIsIsoOfMono'` 的定义

English:
definition ofEpiOfIsIsoOfMono'
  signature: (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
  body: LeftHomologyData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono' φ h.right
  iso := h.iso

#adaptation_note

中文:
定义 ofEpiOfIsIsoOfMono'
  签名: (φ : S₁ ⟶ S₂) (h : 同调数据 S₂)
  定义体: LeftHomologyData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono' φ h.right
  iso := h.iso

#adaptation_note

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofEpiOfIsIsoOfMono, h.left, ofEpiOfIsIsoOfMono
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
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (e : S₁ ≅ S₂) (h : HomologyData S₁)
  body: h.ofEpiOfIsIsoOfMono e.hom

中文:
定义 ofIso
  签名: (e : S₁ ≅ S₂) (h : 同调数据 S₁)
  定义体: h.ofEpiOfIsIsoOfMono e.hom

Depends on / 依赖: e.hom, h.ofEpiOfIsIsoOfMono, ofEpiOfIsIsoOfMono
-/
noncomputable def ofIso (e : S₁ ≅ S₂) (h : HomologyData S₁) :=
  h.ofEpiOfIsIsoOfMono e.hom

variable {S}

set_option backward.defeqAttrib.useBackward true in
/-- A homology data for a short complex `S` induces a homology data for `S.op`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (h : S.HomologyData)
  body: h.right.op
  right := h.left.op
  iso := h.iso.op
  comm := Quiver.Hom.unop_inj (by simp)

中文:
定义 op
  签名: (h : S.同调数据)
  定义体: h.right.op
  right := h.left.op
  iso := h.iso.op
  comm := Quiver.Hom.unop_inj (by simp)

Depends on / 依赖: h.right.op
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
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {S : ShortComplex Cᵒᵖ} (h : S.HomologyData)
  body: h.right.unop
  right := h.left.unop
  iso := h.iso.unop
  comm := Quiver.Hom.op_inj (by simp)

中文:
定义 unop
  签名: {S : 短复形 Cᵒᵖ} (h : S.同调数据)
  定义体: h.right.unop
  right := h.left.unop
  iso := h.iso.unop
  comm := Quiver.Hom.op_inj (by simp)

Depends on / 依赖: h.right.unop
-/
def unop {S : ShortComplex Cᵒᵖ} (h : S.HomologyData) : S.unop.HomologyData where
  left := h.right.unop
  right := h.left.unop
  iso := h.iso.unop
  comm := Quiver.Hom.op_inj (by simp)

end HomologyData

/--
Definition of `HasHomology` / `HasHomology` 的定义

English:
class HasHomology
  parameters: : Prop where
  axioms and operations (1):
    - condition : Nonempty S.HomologyData

中文:
类 有同调
  参数: : 命题 where
  公理与运算 (1 个):
    - condition : 非空 S.同调数据
-/
class HasHomology : Prop where
  /-- the condition that there exists a homology data -/
  condition : Nonempty S.HomologyData

/--
Definition of `homologyData` / `homologyData` 的定义

English:
definition homologyData
  signature: [HasHomology S]
  body: HasHomology.condition.some

中文:
定义 homologyData
  签名: [有同调 S]
  定义体: HasHomology.condition.some

Depends on / 依赖: HasHomology, HasHomology.condition.some, condition
-/
noncomputable def homologyData [HasHomology S] : S.HomologyData := HasHomology.condition.some

variable {S}

/--
lemma `HasHomology.mk'` / 引理 `HasHomology.mk'`

English:
lemma HasHomology.mk'
  given: (h : S.HomologyData)
  statement: HasHomology S
  proof: ⟨Nonempty.intro h⟩

中文:
引理 有同调.mk'
  条件: (h : S.同调数据)
  结论: 有同调 S
  证明: ⟨Nonempty.intro h⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
lemma HasHomology.mk' (h : S.HomologyData) : HasHomology S :=
  ⟨Nonempty.intro h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasHomology
  signature: S] : HasHomology S.op
  body: HasHomology.mk' S.homologyData.op

中文:
实例 [有同调
  签名: S] : 有同调 S.op
  定义体: HasHomology.mk' S.homologyData.op

Depends on / 依赖: HasHomology, HasHomology.mk, S.homologyData.op, homologyData
-/
instance [HasHomology S] : HasHomology S.op :=
  HasHomology.mk' S.homologyData.op

instance (S : ShortComplex Cᵒᵖ) [HasHomology S] : HasHomology S.unop :=
  HasHomology.mk' S.homologyData.unop

/--
Instance `hasLeftHomology_of_hasHomology` / 实例 `hasLeftHomology_of_hasHomology`

English:
instance hasLeftHomology_of_hasHomology
  signature: [S.HasHomology]
  body: HasLeftHomology.mk' S.homologyData.left

中文:
实例 hasLeftHomology_of_hasHomology
  签名: [S.有同调]
  定义体: HasLeftHomology.mk' S.homologyData.left

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, S.homologyData.left, homologyData
-/
instance hasLeftHomology_of_hasHomology [S.HasHomology] : S.HasLeftHomology :=
  HasLeftHomology.mk' S.homologyData.left

/--
Instance `hasRightHomology_of_hasHomology` / 实例 `hasRightHomology_of_hasHomology`

English:
instance hasRightHomology_of_hasHomology
  signature: [S.HasHomology]
  body: HasRightHomology.mk' S.homologyData.right

中文:
实例 hasRightHomology_of_hasHomology
  签名: [S.有同调]
  定义体: HasRightHomology.mk' S.homologyData.right

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, S.homologyData.right, homologyData
-/
instance hasRightHomology_of_hasHomology [S.HasHomology] : S.HasRightHomology :=
  HasRightHomology.mk' S.homologyData.right

/--
Instance `hasHomology_of_hasCokernel` / 实例 `hasHomology_of_hasCokernel`

English:
instance hasHomology_of_hasCokernel
  signature: {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f]
  body: HasHomology.mk' (HomologyData.ofHasCokernel _ rfl)

中文:
实例 hasHomology_of_hasCokernel
  签名: {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f]
  定义体: HasHomology.mk' (HomologyData.ofHasCokernel _ rfl)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofHasCokernel, ofHasCokernel
-/
instance hasHomology_of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasCokernel _ rfl)

/--
Instance `hasHomology_of_hasKernel` / 实例 `hasHomology_of_hasKernel`

English:
instance hasHomology_of_hasKernel
  signature: {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g]
  body: HasHomology.mk' (HomologyData.ofHasKernel _ rfl)

中文:
实例 hasHomology_of_hasKernel
  签名: {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g]
  定义体: HasHomology.mk' (HomologyData.ofHasKernel _ rfl)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofHasKernel, ofHasKernel
-/
instance hasHomology_of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasKernel _ rfl)

/--
Instance `hasHomology_of_zeros` / 实例 `hasHomology_of_zeros`

English:
instance hasHomology_of_zeros
  signature: (X Y Z : C)
  body: HasHomology.mk' (HomologyData.ofZeros _ rfl rfl)

中文:
实例 hasHomology_of_zeros
  签名: (X Y Z : C)
  定义体: HasHomology.mk' (HomologyData.ofZeros _ rfl rfl)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofZeros, ofZeros
-/
instance hasHomology_of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofZeros _ rfl rfl)

/--
lemma `hasHomology_of_epi_of_isIso_of_mono` / 引理 `hasHomology_of_epi_of_isIso_of_mono`

English:
lemma hasHomology_of_epi_of_isIso_of_mono
  statement: (φ : S₁ ⟶ S₂) [HasHomology S₁]
  proof: HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono φ S₁.homologyData)

中文:
引理 hasHomology_of_epi_of_isIso_of_mono
  结论: (φ : S₁ ⟶ S₂) [有同调 S₁]
  证明: HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono φ S₁.homologyData)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofEpiOfIsIsoOfMono, homologyData, ofEpiOfIsIsoOfMono
-/
lemma hasHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono φ S₁.homologyData)

/--
lemma `hasHomology_of_epi_of_isIso_of_mono'` / 引理 `hasHomology_of_epi_of_isIso_of_mono'`

English:
lemma hasHomology_of_epi_of_isIso_of_mono'
  statement: (φ : S₁ ⟶ S₂) [HasHomology S₂]
  proof: HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono' φ S₂.homologyData)

中文:
引理 hasHomology_of_epi_of_isIso_of_mono'
  结论: (φ : S₁ ⟶ S₂) [有同调 S₂]
  证明: HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono' φ S₂.homologyData)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofEpiOfIsIsoOfMono, homologyData, ofEpiOfIsIsoOfMono
-/
lemma hasHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₁ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono' φ S₂.homologyData)

/--
lemma `hasHomology_of_iso` / 引理 `hasHomology_of_iso`

English:
lemma hasHomology_of_iso
  given: (e : S₁ ≅ S₂) [HasHomology S₁]
  statement: HasHomology S₂
  proof: HasHomology.mk' (HomologyData.ofIso e S₁.homologyData)

中文:
引理 hasHomology_of_iso
  条件: (e : S₁ ≅ S₂) [有同调 S₁]
  结论: 有同调 S₂
  证明: HasHomology.mk' (HomologyData.ofIso e S₁.homologyData)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofIso, homologyData
-/
lemma hasHomology_of_iso (e : S₁ ≅ S₂) [HasHomology S₁] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofIso e S₁.homologyData)

namespace HomologyMapData

/-- The homology map data associated to the identity morphism of a short complex. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (h : S.HomologyData)
  body: LeftHomologyMapData.id h.left
  right := RightHomologyMapData.id h.right

中文:
定义 id
  签名: (h : S.同调数据)
  定义体: LeftHomologyMapData.id h.left
  right := RightHomologyMapData.id h.right

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.id, h.left
-/
def id (h : S.HomologyData) : HomologyMapData (𝟙 S) h h where
  left := LeftHomologyMapData.id h.left
  right := RightHomologyMapData.id h.right

/-- The homology map data associated to the zero morphism between two short complexes. -/
@[simps]
/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)
  body: LeftHomologyMapData.zero h₁.left h₂.left
  right := RightHomologyMapData.zero h₁.right h₂.right

中文:
定义 zero
  签名: (h₁ : S₁.同调数据) (h₂ : S₂.同调数据)
  定义体: LeftHomologyMapData.zero h₁.left h₂.left
  right := RightHomologyMapData.zero h₁.right h₂.right

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.zero
-/
def zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    HomologyMapData 0 h₁ h₂ where
  left := LeftHomologyMapData.zero h₁.left h₂.left
  right := RightHomologyMapData.zero h₁.right h₂.right

/-- The composition of homology map data. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData}
  body: ψ.left.comp ψ'.left
  right := ψ.right.comp ψ'.right

中文:
定义 comp
  签名: {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.同调数据}
  定义体: ψ.left.comp ψ'.left
  right := ψ.right.comp ψ'.right

Depends on / 依赖: left.comp
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
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
  body: ψ.right.op
  right := ψ.left.op

中文:
定义 op
  签名: {φ : S₁ ⟶ S₂} {h₁ : S₁.同调数据} {h₂ : S₂.同调数据}
  定义体: ψ.right.op
  right := ψ.left.op

Depends on / 依赖: right.op
-/
def op {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (opMap φ) h₂.op h₁.op where
  left := ψ.right.op
  right := ψ.left.op

/-- A homology map data for a morphism of short complexes in the opposite category
induces a homology map data in the original category. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
  body: ψ.right.unop
  right := ψ.left.unop

中文:
定义 unop
  签名: {S₁ S₂ : 短复形 Cᵒᵖ} {φ : S₁ ⟶ S₂}
  定义体: ψ.right.unop
  right := ψ.left.unop

Depends on / 依赖: right.unop
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
/--
Definition of `ofZeros` / `ofZeros` 的定义

English:
definition ofZeros
  signature: (φ : S₁ ⟶ S₂)
  body: LeftHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂
  right := RightHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂

中文:
定义 ofZeros
  签名: (φ : S₁ ⟶ S₂)
  定义体: LeftHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂
  right := RightHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.ofZeros, ofZeros
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
/--
Definition of `ofIsColimitCokernelCofork` / `ofIsColimitCokernelCofork` 的定义

English:
definition ofIsColimitCokernelCofork
  signature: (φ : S₁ ⟶ S₂)
  body: LeftHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm

中文:
定义 ofIsColimitCokernelCofork
  签名: (φ : S₁ ⟶ S₂)
  定义体: LeftHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.ofIsColimitCokernelCofork, ofIsColimitCokernelCofork
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
/--
Definition of `ofIsLimitKernelFork` / `ofIsLimitKernelFork` 的定义

English:
definition ofIsLimitKernelFork
  signature: (φ : S₁ ⟶ S₂)
  body: LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm

中文:
定义 ofIsLimitKernelFork
  签名: (φ : S₁ ⟶ S₂)
  定义体: LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.ofIsLimitKernelFork, ofIsLimitKernelFork
-/
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    HomologyMapData φ (HomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (HomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm

/--
Definition of `compatibilityOfZerosOfIsColimitCokernelCofork` / `compatibilityOfZerosOfIsColimitCokernelCofork` 的定义

English:
definition compatibilityOfZerosOfIsColimitCokernelCofork
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: LeftHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc

中文:
定义 compatibilityOfZerosOfIsColimitCokernelCofork
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: LeftHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork, compatibilityOfZerosOfIsColimitCokernelCofork
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
/--
Definition of `compatibilityOfZerosOfIsLimitKernelFork` / `compatibilityOfZerosOfIsLimitKernelFork` 的定义

English:
definition compatibilityOfZerosOfIsLimitKernelFork
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc

中文:
定义 compatibilityOfZerosOfIsLimitKernelFork
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork, compatibilityOfZerosOfIsLimitKernelFork
-/
noncomputable def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    HomologyMapData (𝟙 S)
      (HomologyData.ofIsLimitKernelFork S hf c hc)
      (HomologyData.ofZeros S hf hg) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc

/--
Definition of `ofEpiOfIsIsoOfMono` / `ofEpiOfIsIsoOfMono` 的定义

English:
definition ofEpiOfIsIsoOfMono
  signature: (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
  body: LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono φ h.right

中文:
定义 ofEpiOfIsIsoOfMono
  签名: (φ : S₁ ⟶ S₂) (h : 同调数据 S₁)
  定义体: LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono φ h.right

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.ofEpiOfIsIsoOfMono, h.left, ofEpiOfIsIsoOfMono
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ h (HomologyData.ofEpiOfIsIsoOfMono φ h) where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono φ h.right

/--
Definition of `ofEpiOfIsIsoOfMono'` / `ofEpiOfIsIsoOfMono'` 的定义

English:
definition ofEpiOfIsIsoOfMono'
  signature: (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
  body: LeftHomologyMapData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono' φ h.right

中文:
定义 ofEpiOfIsIsoOfMono'
  签名: (φ : S₁ ⟶ S₂) (h : 同调数据 S₂)
  定义体: LeftHomologyMapData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono' φ h.right

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.ofEpiOfIsIsoOfMono, h.left, ofEpiOfIsIsoOfMono
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ (HomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono' φ h.right

end HomologyMapData

variable (S)

/--
Definition of `homology` / `homology` 的定义

English:
definition homology
  signature: [HasHomology S]
  body: S.homologyData.left.H

中文:
定义 homology
  签名: [有同调 S]
  定义体: S.homologyData.left.H

Depends on / 依赖: S.homologyData.left.H, homologyData
-/
noncomputable def homology [HasHomology S] : C := S.homologyData.left.H

/--
Definition of `leftHomologyIso` / `leftHomologyIso` 的定义

English:
definition leftHomologyIso
  signature: [S.HasHomology]
  body: leftHomologyMapIso' (Iso.refl _) _ _

中文:
定义 leftHomologyIso
  签名: [S.有同调]
  定义体: leftHomologyMapIso' (Iso.refl _) _ _

Depends on / 依赖: Iso.refl, leftHomologyMapIso
-/
noncomputable def leftHomologyIso [S.HasHomology] : S.leftHomology ≅ S.homology :=
  leftHomologyMapIso' (Iso.refl _) _ _

/--
Definition of `rightHomologyIso` / `rightHomologyIso` 的定义

English:
definition rightHomologyIso
  signature: [S.HasHomology]
  body: rightHomologyMapIso' (Iso.refl _) _ _ ≪≫ S.homologyData.iso.symm

中文:
定义 rightHomologyIso
  签名: [S.有同调]
  定义体: rightHomologyMapIso' (Iso.refl _) _ _ ≪≫ S.homologyData.iso.symm

Depends on / 依赖: Iso.refl, S.homologyData.iso.symm, homologyData, rightHomologyMapIso
-/
noncomputable def rightHomologyIso [S.HasHomology] : S.rightHomology ≅ S.homology :=
  rightHomologyMapIso' (Iso.refl _) _ _ ≪≫ S.homologyData.iso.symm

variable {S}

/--
Definition of `LeftHomologyData.homologyIso` / `LeftHomologyData.homologyIso` 的定义

English:
definition LeftHomologyData.homologyIso
  signature: (h : S.LeftHomologyData) [S.HasHomology]
  body: S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

中文:
定义 LeftHomologyData.homologyIso
  签名: (h : S.LeftHomologyData) [S.有同调]
  定义体: S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

Depends on / 依赖: S.leftHomologyIso.symm, h.leftHomologyIso, leftHomologyIso
-/
noncomputable def LeftHomologyData.homologyIso (h : S.LeftHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

/--
Definition of `RightHomologyData.homologyIso` / `RightHomologyData.homologyIso` 的定义

English:
definition RightHomologyData.homologyIso
  signature: (h : S.RightHomologyData) [S.HasHomology]
  body: S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

中文:
定义 RightHomologyData.homologyIso
  签名: (h : S.RightHomologyData) [S.有同调]
  定义体: S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

Depends on / 依赖: S.rightHomologyIso.symm, h.rightHomologyIso, rightHomologyIso
-/
noncomputable def RightHomologyData.homologyIso (h : S.RightHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

variable (S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `LeftHomologyData.homologyIso_leftHomologyData` / 引理 `LeftHomologyData.homologyIso_leftHomologyData`

English:
lemma LeftHomologyData.homologyIso_leftHomologyData
  given: [S.HasHomology]
  proof: by
  ext
  dsimp [homologyIso, leftHomologyIso, ShortComplex.leftHomologyIso]
  rw [← leftHomologyMap'_comp]; rw [comp_id]

中文:
引理 LeftHomologyData.homologyIso_leftHomologyData
  条件: [S.有同调]
  证明: by
  ext
  dsimp [homologyIso, leftHomologyIso, ShortComplex.leftHomologyIso]
  rw [← leftHomologyMap'_comp]; rw [comp_id]

Depends on / 依赖: ShortComplex, ShortComplex.leftHomologyIso, _comp, comp_id, homologyIso, leftHomologyIso, leftHomologyMap
-/
lemma LeftHomologyData.homologyIso_leftHomologyData [S.HasHomology] :
    S.leftHomologyData.homologyIso = S.leftHomologyIso.symm := by
  ext
  dsimp [homologyIso, leftHomologyIso, ShortComplex.leftHomologyIso]
  rw [← leftHomologyMap'_comp]; rw [comp_id]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `RightHomologyData.homologyIso_rightHomologyData` / 引理 `RightHomologyData.homologyIso_rightHomologyData`

English:
lemma RightHomologyData.homologyIso_rightHomologyData
  given: [S.HasHomology]
  proof: by
  ext
  simp [homologyIso, rightHomologyIso]

中文:
引理 RightHomologyData.homologyIso_rightHomologyData
  条件: [S.有同调]
  证明: by
  ext
  simp [homologyIso, rightHomologyIso]

Depends on / 依赖: CommMagma, IsCommJordan, IsCommJordan.toIsJordan, IsJordan, homologyIso, rightHomologyIso, toIsJordan
-/
lemma RightHomologyData.homologyIso_rightHomologyData [S.HasHomology] :
    S.rightHomologyData.homologyIso = S.rightHomologyIso.symm := by
  ext
  simp [homologyIso, rightHomologyIso]

variable {S}

/--
Definition of `homologyMap'` / `homologyMap'` 的定义

English:
definition homologyMap'
  signature: (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)
  body: leftHomologyMap' φ _ _

中文:
定义 homologyMap'
  签名: (φ : S₁ ⟶ S₂) (h₁ : S₁.同调数据) (h₂ : S₂.同调数据)
  定义体: leftHomologyMap' φ _ _

Depends on / 依赖: IsJordan, Semigroup, Semigroup.isJordan, isJordan, leftHomologyMap
-/
def homologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    h₁.left.H ⟶ h₂.left.H := leftHomologyMap' φ _ _

/--
Definition of `homologyMap` / `homologyMap` 的定义

English:
definition homologyMap
  signature: (φ : S₁ ⟶ S₂) [HasHomology S₁] [HasHomology S₂]
  body: homologyMap' φ _ _

中文:
定义 homologyMap
  签名: (φ : S₁ ⟶ S₂) [有同调 S₁] [有同调 S₂]
  定义体: homologyMap' φ _ _

Depends on / 依赖: CommSemigroup, CommSemigroup.isCommJordan, IsCommJordan, homologyMap, isCommJordan
-/
noncomputable def homologyMap (φ : S₁ ⟶ S₂) [HasHomology S₁] [HasHomology S₂] :
    S₁.homology ⟶ S₂.homology :=
  homologyMap' φ _ _

namespace HomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
  (γ : HomologyMapData φ h₁ h₂)

/--
lemma `homologyMap'_eq` / 引理 `homologyMap'_eq`

English:
lemma homologyMap'_eq
  statement: homologyMap' φ h₁ h₂ = γ.left.φH
  proof: LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

中文:
引理 homologyMap'_eq
  结论: homologyMap' φ h₁ h₂ = γ.left.φH
  证明: LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.congr_, Subsingleton, Subsingleton.elim
-/
lemma homologyMap'_eq : homologyMap' φ h₁ h₂ = γ.left.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

/--
lemma `cyclesMap'_eq` / 引理 `cyclesMap'_eq`

English:
lemma cyclesMap'_eq
  statement: cyclesMap' φ h₁.left h₂.left = γ.left.φK
  proof: LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

中文:
引理 cyclesMap'_eq
  结论: cyclesMap' φ h₁.left h₂.left = γ.left.φK
  证明: LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.congr_, Subsingleton, Subsingleton.elim
-/
lemma cyclesMap'_eq : cyclesMap' φ h₁.left h₂.left = γ.left.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

/--
lemma `opcyclesMap'_eq` / 引理 `opcyclesMap'_eq`

English:
lemma opcyclesMap'_eq
  statement: opcyclesMap' φ h₁.right h₂.right = γ.right.φQ
  proof: RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

中文:
引理 opcyclesMap'_eq
  结论: opcyclesMap' φ h₁.right h₂.right = γ.right.φQ
  证明: RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.congr_, Subsingleton, Subsingleton.elim
-/
lemma opcyclesMap'_eq : opcyclesMap' φ h₁.right h₂.right = γ.right.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end HomologyMapData

namespace LeftHomologyMapData

variable {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologyMap_eq` / 引理 `homologyMap_eq`

English:
lemma homologyMap_eq
  proof: by
  dsimp [homologyMap, LeftHomologyData.homologyIso, leftHomologyIso,
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp, id_comp, comp_id]

中文:
引理 homologyMap_eq
  证明: by
  dsimp [homologyMap, LeftHomologyData.homologyIso, leftHomologyIso,
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp, id_comp, comp_id]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso, _comp, comp_id, homologyIso, homologyMap, id_comp, leftHomologyIso, leftHomologyMap
-/
lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp [homologyMap, LeftHomologyData.homologyIso, leftHomologyIso,
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp, id_comp, comp_id]

/--
lemma `homologyMap_comm` / 引理 `homologyMap_comm`

English:
lemma homologyMap_comm
  proof: by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 homologyMap_comm
  证明: by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, homologyMap_eq, inv_hom_id
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
/--
lemma `homologyMap_eq` / 引理 `homologyMap_eq`

English:
lemma homologyMap_eq
  proof: by
  dsimp [homologyMap, homologyMap', RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso]
  have γ' : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  simp only [← γ.rightHomologyMap'_eq, assoc, ← rightHomologyMap'_comp_assoc,
    id_comp, comp_id,

中文:
引理 homologyMap_eq
  证明: by
  dsimp [homologyMap, homologyMap', RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso]
  have γ' : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  simp only [← γ.rightHomologyMap'_eq, assoc, ← rightHomologyMap'_comp_assoc,
    id_comp, comp_id,

Depends on / 依赖: HomologyMapData, Iso.hom_inv_id, RightHomologyData, RightHomologyData.homologyIso, RightHomologyData.rightHomologyIso, _comp_assoc, comm_assoc, comp_id, hom_inv_id, homologyData, homologyIso, homologyMap, id_comp, left.leftHomologyMap, leftHomologyMap, right.rightHomologyMap, rightHomologyIso, rightHomologyMap
-/
lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp [homologyMap, homologyMap', RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso]
  have γ' : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  simp only [← γ.rightHomologyMap'_eq, assoc, ← rightHomologyMap'_comp_assoc,
    id_comp, comp_id, γ'.left.leftHomologyMap'_eq, γ'.right.rightHomologyMap'_eq, ← γ'.comm_assoc,
    Iso.hom_inv_id]

/--
lemma `homologyMap_comm` / 引理 `homologyMap_comm`

English:
lemma homologyMap_comm
  proof: by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 homologyMap_comm
  证明: by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, homologyMap_eq, inv_hom_id
-/
lemma homologyMap_comm :
    homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

@[simp]
/--
lemma `homologyMap'_id` / 引理 `homologyMap'_id`

English:
lemma homologyMap'_id
  given: (h : S.HomologyData)
  proof: (HomologyMapData.id h).homologyMap'_eq

中文:
引理 homologyMap'_id
  条件: (h : S.同调数据)
  证明: (HomologyMapData.id h).homologyMap'_eq
-/
lemma homologyMap'_id (h : S.HomologyData) :
    homologyMap' (𝟙 S) h h = 𝟙 _ :=
  (HomologyMapData.id h).homologyMap'_eq

variable (S)

@[simp]
/--
lemma `homologyMap_id` / 引理 `homologyMap_id`

English:
lemma homologyMap_id
  given: [HasHomology S]
  proof: homologyMap'_id _

@[simp]

中文:
引理 homologyMap_id
  条件: [有同调 S]
  证明: homologyMap'_id _

@[simp]

Depends on / 依赖: homologyMap
-/
lemma homologyMap_id [HasHomology S] :
    homologyMap (𝟙 S) = 𝟙 _ :=
  homologyMap'_id _

@[simp]
/--
lemma `homologyMap'_zero` / 引理 `homologyMap'_zero`

English:
lemma homologyMap'_zero
  given: (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)
  proof: (HomologyMapData.zero h₁ h₂).homologyMap'_eq

中文:
引理 homologyMap'_zero
  条件: (h₁ : S₁.同调数据) (h₂ : S₂.同调数据)
  证明: (HomologyMapData.zero h₁ h₂).homologyMap'_eq
-/
lemma homologyMap'_zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    homologyMap' 0 h₁ h₂ = 0 :=
  (HomologyMapData.zero h₁ h₂).homologyMap'_eq

variable (S₁ S₂)

@[simp]
/--
lemma `homologyMap_zero` / 引理 `homologyMap_zero`

English:
lemma homologyMap_zero
  given: [S₁.HasHomology] [S₂.HasHomology]
  proof: homologyMap'_zero _ _

中文:
引理 homologyMap_zero
  条件: [S₁.有同调] [S₂.有同调]
  证明: homologyMap'_zero _ _

Depends on / 依赖: _zero, homologyMap
-/
lemma homologyMap_zero [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (0 : S₁ ⟶ S₂) = 0 :=
  homologyMap'_zero _ _

variable {S₁ S₂}

/--
lemma `homologyMap'_comp` / 引理 `homologyMap'_comp`

English:
lemma homologyMap'_comp
  statement: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  proof: leftHomologyMap'_comp _ _ _ _ _

@[simp]

中文:
引理 homologyMap'_comp
  结论: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  证明: leftHomologyMap'_comp _ _ _ _ _

@[simp]
-/
lemma homologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) (h₃ : S₃.HomologyData) :
    homologyMap' (φ₁ ≫ φ₂) h₁ h₃ = homologyMap' φ₁ h₁ h₂ ≫
      homologyMap' φ₂ h₂ h₃ :=
  leftHomologyMap'_comp _ _ _ _ _

@[simp]
/--
lemma `homologyMap_comp` / 引理 `homologyMap_comp`

English:
lemma homologyMap_comp
  statement: [HasHomology S₁] [HasHomology S₂] [HasHomology S₃]
  proof: homologyMap'_comp _ _ _ _ _

中文:
引理 homologyMap_comp
  结论: [有同调 S₁] [有同调 S₂] [有同调 S₃]
  证明: homologyMap'_comp _ _ _ _ _

Depends on / 依赖: _comp, homologyMap
-/
lemma homologyMap_comp [HasHomology S₁] [HasHomology S₂] [HasHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    homologyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫ homologyMap φ₂ :=
  homologyMap'_comp _ _ _ _ _

/-- Given an isomorphism `S₁ ≅ S₂` of short complexes and homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced homology isomorphism `h₁.left.H ≅ h₁.left.H`. -/
@[simps]
/--
Definition of `homologyMapIso'` / `homologyMapIso'` 的定义

English:
definition homologyMapIso'
  signature: (e : S₁ ≅ S₂) (h₁ : S₁.HomologyData)
  body: homologyMap' e.hom h₁ h₂
  inv := homologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← homologyMap'_comp, e.hom_inv_id, homologyMap'_id]
  inv_hom_id := by rw [← homologyMap'_comp, e.inv_hom_id, homologyMap'_id]

中文:
定义 homologyMapIso'
  签名: (e : S₁ ≅ S₂) (h₁ : S₁.同调数据)
  定义体: homologyMap' e.hom h₁ h₂
  inv := homologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← homologyMap'_comp, e.hom_inv_id, homologyMap'_id]
  inv_hom_id := by rw [← homologyMap'_comp, e.inv_hom_id, homologyMap'_id]

Depends on / 依赖: e.hom, homologyMap
-/
def homologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : h₁.left.H ≅ h₂.left.H where
  hom := homologyMap' e.hom h₁ h₂
  inv := homologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← homologyMap'_comp, e.hom_inv_id, homologyMap'_id]
  inv_hom_id := by rw [← homologyMap'_comp, e.inv_hom_id, homologyMap'_id]

/--
Instance `isIso_homologyMap'_of_isIso` / 实例 `isIso_homologyMap'_of_isIso`

English:
instance isIso_homologyMap'_of_isIso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ]
  body: inferInstanceAs IsIso (homologyMapIso' (asIso φ) h₁ h₂).hom

中文:
实例 isIso_homologyMap'_of_isIso
  签名: (φ : S₁ ⟶ S₂) [是同构 φ]
  定义体: inferInstanceAs IsIso (homologyMapIso' (asIso φ) h₁ h₂).hom

Depends on / 依赖: homologyMapIso
-/
instance isIso_homologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    IsIso (homologyMap' φ h₁ h₂) :=
inferInstanceAs IsIso (homologyMapIso' (asIso φ) h₁ h₂).hom

/-- The homology isomorphism `S₁.homology ⟶ S₂.homology` induced by an isomorphism
`S₁ ≅ S₂` of short complexes. -/
@[simps]
/--
Definition of `homologyMapIso` / `homologyMapIso` 的定义

English:
definition homologyMapIso
  signature: (e : S₁ ≅ S₂) [S₁.HasHomology]
  body: homologyMap e.hom
  inv := homologyMap e.inv
  hom_inv_id := by rw [← homologyMap_comp, e.hom_inv_id, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id]

中文:
定义 homologyMapIso
  签名: (e : S₁ ≅ S₂) [S₁.有同调]
  定义体: homologyMap e.hom
  inv := homologyMap e.inv
  hom_inv_id := by rw [← homologyMap_comp, e.hom_inv_id, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id]

Depends on / 依赖: e.hom, homologyMap
-/
noncomputable def homologyMapIso (e : S₁ ≅ S₂) [S₁.HasHomology]
    [S₂.HasHomology] : S₁.homology ≅ S₂.homology where
  hom := homologyMap e.hom
  inv := homologyMap e.inv
  hom_inv_id := by rw [← homologyMap_comp, e.hom_inv_id, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id]

/--
Instance `isIso_homologyMap_of_iso` / 实例 `isIso_homologyMap_of_iso`

English:
instance isIso_homologyMap_of_iso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasHomology]
  body: inferInstanceAs IsIso (homologyMapIso (asIso φ)).hom

中文:
实例 isIso_homologyMap_of_iso
  签名: (φ : S₁ ⟶ S₂) [是同构 φ] [S₁.有同调]
  定义体: inferInstanceAs IsIso (homologyMapIso (asIso φ)).hom

Depends on / 依赖: homologyMapIso
-/
instance isIso_homologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasHomology]
    [S₂.HasHomology] :
    IsIso (homologyMap φ) :=
inferInstanceAs IsIso (homologyMapIso (asIso φ)).hom

variable {S}

section

variable (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)

/--
Definition of `leftRightHomologyComparison'` / `leftRightHomologyComparison'` 的定义

English:
definition leftRightHomologyComparison'
  signature: : h₁.H ⟶ h₂.H
  body: h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero])

中文:
定义 leftRightHomologyComparison'
  签名: : h₁.H ⟶ h₂.H
  定义体: h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero])

Depends on / 依赖: LeftHomologyData, LeftHomologyData.wi, RightHomologyData, RightHomologyData.p_g, cancel_epi, comp_zero
-/
def leftRightHomologyComparison' : h₁.H ⟶ h₂.H :=
  h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero])

/--
lemma `leftRightHomologyComparison'_eq_liftH` / 引理 `leftRightHomologyComparison'_eq_liftH`

English:
lemma leftRightHomologyComparison'_eq_liftH
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 leftRightHomologyComparison'_eq_liftH
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma leftRightHomologyComparison'_eq_liftH :
    leftRightHomologyComparison' h₁ h₂ =
      h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
        (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
          RightHomologyData.p_g', LeftHomologyData.wi, comp_zero]) := rfl

@[reassoc (attr := simp)]
/--
lemma `π_leftRightHomologyComparison'_ι` / 引理 `π_leftRightHomologyComparison'_ι`

English:
lemma π_leftRightHomologyComparison'_ι
  proof: by
  simp only [leftRightHomologyComparison'_eq_liftH,
    RightHomologyData.liftH_ι, LeftHomologyData.π_descH]

中文:
引理 π_leftRightHomologyComparison'_ι
  证明: by
  simp only [leftRightHomologyComparison'_eq_liftH,
    RightHomologyData.liftH_ι, LeftHomologyData.π_descH]

Depends on / 依赖: LeftHomologyData, RightHomologyData, RightHomologyData.liftH_, _eq_liftH, leftRightHomologyComparison
-/
lemma π_leftRightHomologyComparison'_ι :
    h₁.π ≫ leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι = h₁.i ≫ h₂.p := by
  simp only [leftRightHomologyComparison'_eq_liftH,
    RightHomologyData.liftH_ι, LeftHomologyData.π_descH]

/--
lemma `leftRightHomologyComparison'_eq_descH` / 引理 `leftRightHomologyComparison'_eq_descH`

English:
lemma leftRightHomologyComparison'_eq_descH
  proof: by
  simp only [← cancel_mono h₂.ι, ← cancel_epi h₁.π, π_leftRightHomologyComparison'_ι,
    LeftHomologyData.π_descH_assoc, RightHomologyData.liftH_ι]

中文:
引理 leftRightHomologyComparison'_eq_descH
  证明: by
  simp only [← cancel_mono h₂.ι, ← cancel_epi h₁.π, π_leftRightHomologyComparison'_ι,
    LeftHomologyData.π_descH_assoc, RightHomologyData.liftH_ι]
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

/--
Definition of `leftRightHomologyComparison` / `leftRightHomologyComparison` 的定义

English:
definition leftRightHomologyComparison
  signature: [S.HasLeftHomology] [S.HasRightHomology]
  body: leftRightHomologyComparison' _ _

@[reassoc (attr := simp)]

中文:
定义 leftRightHomologyComparison
  签名: [S.有LeftHomology] [S.有RightHomology]
  定义体: leftRightHomologyComparison' _ _

@[reassoc (attr := simp)]

Depends on / 依赖: leftRightHomologyComparison
-/
noncomputable def leftRightHomologyComparison [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomology ⟶ S.rightHomology :=
  leftRightHomologyComparison' _ _

@[reassoc (attr := simp)]
/--
lemma `π_leftRightHomologyComparison_ι` / 引理 `π_leftRightHomologyComparison_ι`

English:
lemma π_leftRightHomologyComparison_ι
  given: [S.HasLeftHomology] [S.HasRightHomology]
  proof: π_leftRightHomologyComparison'_ι _ _

@[reassoc]

中文:
引理 π_leftRightHomologyComparison_ι
  条件: [S.有LeftHomology] [S.有RightHomology]
  证明: π_leftRightHomologyComparison'_ι _ _

@[reassoc]
-/
lemma π_leftRightHomologyComparison_ι [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomologyπ ≫ S.leftRightHomologyComparison ≫ S.rightHomologyι =
      S.iCycles ≫ S.pOpcycles :=
  π_leftRightHomologyComparison'_ι _ _

@[reassoc]
/--
lemma `leftRightHomologyComparison'_naturality` / 引理 `leftRightHomologyComparison'_naturality`

English:
lemma leftRightHomologyComparison'_naturality
  statement: (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData)
  proof: by
  simp only [← cancel_epi h₁.π, ← cancel_mono h₂'.ι, assoc,
    leftHomologyπ_naturality'_assoc, rightHomologyι_naturality',
    π_leftRightHomologyComparison'_ι, π_leftRightHomologyComparison'_ι_assoc,
    cyclesMap'_i_assoc, p_opcyclesMap']

中文:
引理 leftRightHomologyComparison'_naturality
  结论: (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData)
  证明: by
  simp only [← cancel_epi h₁.π, ← cancel_mono h₂'.ι, assoc,
    leftHomologyπ_naturality'_assoc, rightHomologyι_naturality',
    π_leftRightHomologyComparison'_ι, π_leftRightHomologyComparison'_ι_assoc,
    cyclesMap'_i_assoc, p_opcyclesMap']
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

/--
lemma `leftRightHomologyComparison'_compatibility` / 引理 `leftRightHomologyComparison'_compatibility`

English:
lemma leftRightHomologyComparison'_compatibility
  statement: (h₁ h₁' : S.LeftHomologyData)
  proof: by
  rw [leftRightHomologyComparison'_naturality_assoc (𝟙 S) h₁ h₂ h₁' h₂']; rw [← rightHomologyMap'_comp]; rw [comp_id]; rw [rightHomologyMap'_id]; rw [comp_id]

中文:
引理 leftRightHomologyComparison'_compatibility
  结论: (h₁ h₁' : S.LeftHomologyData)
  证明: by
  rw [leftRightHomologyComparison'_naturality_assoc (𝟙 S) h₁ h₂ h₁' h₂']; rw [← rightHomologyMap'_comp]; rw [comp_id]; rw [rightHomologyMap'_id]; rw [comp_id]
-/
lemma leftRightHomologyComparison'_compatibility (h₁ h₁' : S.LeftHomologyData)
    (h₂ h₂' : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ = leftHomologyMap' (𝟙 S) h₁ h₁' ≫
      leftRightHomologyComparison' h₁' h₂' ≫ rightHomologyMap' (𝟙 S) _ _ := by
  rw [leftRightHomologyComparison'_naturality_assoc (𝟙 S) h₁ h₂ h₁' h₂']; rw [← rightHomologyMap'_comp]; rw [comp_id]; rw [rightHomologyMap'_id]; rw [comp_id]

/--
lemma `leftRightHomologyComparison_eq` / 引理 `leftRightHomologyComparison_eq`

English:
lemma leftRightHomologyComparison_eq
  statement: [S.HasLeftHomology] [S.HasRightHomology]
  proof: leftRightHomologyComparison'_compatibility _ _ _ _

@[simp]

中文:
引理 leftRightHomologyComparison_eq
  结论: [S.有LeftHomology] [S.有RightHomology]
  证明: leftRightHomologyComparison'_compatibility _ _ _ _

@[simp]

Depends on / 依赖: _compatibility, leftRightHomologyComparison
-/
lemma leftRightHomologyComparison_eq [S.HasLeftHomology] [S.HasRightHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    S.leftRightHomologyComparison = h₁.leftHomologyIso.hom ≫
      leftRightHomologyComparison' h₁ h₂ ≫ h₂.rightHomologyIso.inv :=
  leftRightHomologyComparison'_compatibility _ _ _ _

@[simp]
/--
lemma `HomologyData.leftRightHomologyComparison'_eq` / 引理 `HomologyData.leftRightHomologyComparison'_eq`

English:
lemma HomologyData.leftRightHomologyComparison'_eq
  given: (h : S.HomologyData)
  proof: by
  simp only [← cancel_epi h.left.π, ← cancel_mono h.right.ι, assoc,
    π_leftRightHomologyComparison'_ι, comm]

中文:
引理 同调数据.leftRightHomologyComparison'_eq
  条件: (h : S.同调数据)
  证明: by
  simp only [← cancel_epi h.left.π, ← cancel_mono h.right.ι, assoc,
    π_leftRightHomologyComparison'_ι, comm]

Depends on / 依赖: cancel_epi, cancel_mono, h.left, h.right
-/
lemma HomologyData.leftRightHomologyComparison'_eq (h : S.HomologyData) :
    leftRightHomologyComparison' h.left h.right = h.iso.hom := by
  simp only [← cancel_epi h.left.π, ← cancel_mono h.right.ι, assoc,
    π_leftRightHomologyComparison'_ι, comm]

/--
Instance `isIso_leftRightHomologyComparison'_of_homologyData` / 实例 `isIso_leftRightHomologyComparison'_of_homologyData`

English:
instance isIso_leftRightHomologyComparison'_of_homologyData
  signature: (h : S.HomologyData)
  body: by
    rw [h.leftRightHomologyComparison'_eq]
    infer_instance

中文:
实例 isIso_leftRightHomologyComparison'_of_homologyData
  签名: (h : S.同调数据)
  定义体: by
    rw [h.leftRightHomologyComparison'_eq]
    infer_instance

Depends on / 依赖: h.leftRightHomologyComparison, infer_instance, leftRightHomologyComparison
-/
instance isIso_leftRightHomologyComparison'_of_homologyData (h : S.HomologyData) :
    IsIso (leftRightHomologyComparison' h.left h.right) := by
    rw [h.leftRightHomologyComparison'_eq]
    infer_instance

/--
Instance `isIso_leftRightHomologyComparison'` / 实例 `isIso_leftRightHomologyComparison'`

English:
instance isIso_leftRightHomologyComparison'
  signature: [S.HasHomology]
  body: by
  rw [leftRightHomologyComparison'_compatibility h₁ S.homologyData.left h₂
    S.homologyData.right]
  infer_instance

中文:
实例 isIso_leftRightHomologyComparison'
  签名: [S.有同调]
  定义体: by
  rw [leftRightHomologyComparison'_compatibility h₁ S.homologyData.left h₂
    S.homologyData.right]
  infer_instance
-/
instance isIso_leftRightHomologyComparison' [S.HasHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    IsIso (leftRightHomologyComparison' h₁ h₂) := by
  rw [leftRightHomologyComparison'_compatibility h₁ S.homologyData.left h₂
    S.homologyData.right]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isIso_leftRightHomologyComparison` / 实例 `isIso_leftRightHomologyComparison`

English:
instance isIso_leftRightHomologyComparison
  signature: [S.HasHomology]
  body: by
  dsimp only [leftRightHomologyComparison]
  infer_instance

中文:
实例 isIso_leftRightHomologyComparison
  签名: [S.有同调]
  定义体: by
  dsimp only [leftRightHomologyComparison]
  infer_instance

Depends on / 依赖: infer_instance, leftRightHomologyComparison
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
/--
Definition of `ofIsIsoLeftRightHomologyComparison'` / `ofIsIsoLeftRightHomologyComparison'` 的定义

English:
definition ofIsIsoLeftRightHomologyComparison'
  body: h₁
  right := h₂
  iso := asIso (leftRightHomologyComparison' h₁ h₂)

中文:
定义 ofIsIsoLeftRightHomologyComparison'
  定义体: h₁
  right := h₂
  iso := asIso (leftRightHomologyComparison' h₁ h₂)
-/
noncomputable def ofIsIsoLeftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HomologyData where
  left := h₁
  right := h₂
  iso := asIso (leftRightHomologyComparison' h₁ h₂)

end HomologyData

/--
lemma `leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'` / 引理 `leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'`

English:
lemma leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
  proof: by
  simpa only [h.leftRightHomologyComparison'_eq] using
    leftRightHomologyComparison'_compatibility h₁ h.left h₂ h.right

中文:
引理 leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
  证明: by
  simpa only [h.leftRightHomologyComparison'_eq] using
    leftRightHomologyComparison'_compatibility h₁ h.left h₂ h.right
-/
lemma leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
    (h : S.HomologyData) (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
      leftHomologyMap' (𝟙 S) h₁ h.left ≫ h.iso.hom ≫ rightHomologyMap' (𝟙 S) h.right h₂ := by
  simpa only [h.leftRightHomologyComparison'_eq] using
    leftRightHomologyComparison'_compatibility h₁ h.left h₂ h.right

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `leftRightHomologyComparison'_fac` / 引理 `leftRightHomologyComparison'_fac`

English:
lemma leftRightHomologyComparison'_fac
  statement: (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  proof: by
  rw [leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
    S.homologyData h₁ h₂]
  dsimp only [LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyMapIso', leftHomologyIso,
    RightHomologyData.homolog

中文:
引理 leftRightHomologyComparison'_fac
  结论: (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  证明: by
  rw [leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
    S.homologyData h₁ h₂]
  dsimp only [LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyMapIso', leftHomologyIso,
    RightHomologyData.homolog
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
/--
lemma `leftRightHomologyComparison_fac` / 引理 `leftRightHomologyComparison_fac`

English:
lemma leftRightHomologyComparison_fac
  given: [S.HasHomology]
  proof: by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv,
    RightHomologyData.homologyIso_rightHomologyData, Iso.symm_hom] using!
      leftRightHomologyComparison'_fac S.leftHomologyData S.rightHomologyData

中文:
引理 leftRightHomologyComparison_fac
  条件: [S.有同调]
  证明: by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv,
    RightHomologyData.homologyIso_rightHomologyData, Iso.symm_hom] using!
      leftRightHomologyComparison'_fac S.leftHomologyData S.rightHomologyData

Depends on / 依赖: Iso.symm_hom, Iso.symm_inv, LeftHomologyData, LeftHomologyData.homologyIso_leftHomologyData, RightHomologyData, RightHomologyData.homologyIso_rightHomologyData, S.leftHomologyData, S.rightHomologyData, _fac, homologyIso_leftHomologyData, homologyIso_rightHomologyData, leftHomologyData, leftRightHomologyComparison, rightHomologyData, symm_hom, symm_inv
-/
lemma leftRightHomologyComparison_fac [S.HasHomology] :
    S.leftRightHomologyComparison = S.leftHomologyIso.hom ≫ S.rightHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv,
    RightHomologyData.homologyIso_rightHomologyData, Iso.symm_hom] using!
      leftRightHomologyComparison'_fac S.leftHomologyData S.rightHomologyData

variable {S}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso` / 引理 `HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso`

English:
lemma HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso
  proof: by
  suffices h.iso = h.left.homologyIso.symm ≪≫ h.right.homologyIso by
    rw [this]; rw [Iso.self_symm_id_assoc]
  ext
  dsimp
  rw [← leftRightHomologyComparison'_fac]; rw [leftRightHomologyComparison'_eq]

中文:
引理 同调数据.right_homologyIso_eq_left_homologyIso_trans_iso
  证明: by
  suffices h.iso = h.left.homologyIso.symm ≪≫ h.right.homologyIso by
    rw [this]; rw [Iso.self_symm_id_assoc]
  ext
  dsimp
  rw [← leftRightHomologyComparison'_fac]; rw [leftRightHomologyComparison'_eq]

Depends on / 依赖: Iso.self_symm_id_assoc, _fac, h.iso, h.left.homologyIso.symm, h.right.homologyIso, homologyIso, leftRightHomologyComparison, self_symm_id_assoc
-/
lemma HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso
    (h : S.HomologyData) [S.HasHomology] :
    h.right.homologyIso = h.left.homologyIso ≪≫ h.iso := by
  suffices h.iso = h.left.homologyIso.symm ≪≫ h.right.homologyIso by
    rw [this]; rw [Iso.self_symm_id_assoc]
  ext
  dsimp
  rw [← leftRightHomologyComparison'_fac]; rw [leftRightHomologyComparison'_eq]

/--
lemma `HomologyData.left_homologyIso_eq_right_homologyIso_trans_iso_symm` / 引理 `HomologyData.left_homologyIso_eq_right_homologyIso_trans_iso_symm`

English:
lemma HomologyData.left_homologyIso_eq_right_homologyIso_trans_iso_symm
  proof: by
  rw [right_homologyIso_eq_left_homologyIso_trans_iso]
  cat_disch

中文:
引理 同调数据.left_homologyIso_eq_right_homologyIso_trans_iso_symm
  证明: by
  rw [right_homologyIso_eq_left_homologyIso_trans_iso]
  cat_disch

Depends on / 依赖: cat_disch, right_homologyIso_eq_left_homologyIso_trans_iso
-/
lemma HomologyData.left_homologyIso_eq_right_homologyIso_trans_iso_symm
    (h : S.HomologyData) [S.HasHomology] :
    h.left.homologyIso = h.right.homologyIso ≪≫ h.iso.symm := by
  rw [right_homologyIso_eq_left_homologyIso_trans_iso]
  cat_disch

/--
lemma `hasHomology_of_isIso_leftRightHomologyComparison'` / 引理 `hasHomology_of_isIso_leftRightHomologyComparison'`

English:
lemma hasHomology_of_isIso_leftRightHomologyComparison'
  proof: HasHomology.mk' (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

中文:
引理 hasHomology_of_isIso_leftRightHomologyComparison'
  证明: HasHomology.mk' (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofIsIsoLeftRightHomologyComparison, ofIsIsoLeftRightHomologyComparison
-/
lemma hasHomology_of_isIso_leftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HasHomology :=
  HasHomology.mk' (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

/--
lemma `hasHomology_of_isIsoLeftRightHomologyComparison` / 引理 `hasHomology_of_isIsoLeftRightHomologyComparison`

English:
lemma hasHomology_of_isIsoLeftRightHomologyComparison
  statement: [S.HasLeftHomology]
  proof: by
  have : IsIso (leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData) := h
  exact hasHomology_of_isIso_leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData

中文:
引理 hasHomology_of_isIsoLeftRightHomologyComparison
  结论: [S.有LeftHomology]
  证明: by
  have : IsIso (leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData) := h
  exact hasHomology_of_isIso_leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData

Depends on / 依赖: S.leftHomologyData, S.rightHomologyData, hasHomology_of_isIso_leftRightHomologyComparison, leftHomologyData, leftRightHomologyComparison, rightHomologyData
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
/--
lemma `LeftHomologyData.leftHomologyIso_hom_naturality` / 引理 `LeftHomologyData.leftHomologyIso_hom_naturality`

English:
lemma LeftHomologyData.leftHomologyIso_hom_naturality
  proof: by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

中文:
引理 LeftHomologyData.leftHomologyIso_hom_naturality
  证明: by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

Depends on / 依赖: ShortComplex, ShortComplex.leftHomologyIso, _comp, comp_id, homologyIso, homologyMap, id_comp, leftHomologyIso, leftHomologyMap
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
/--
lemma `LeftHomologyData.leftHomologyIso_inv_naturality` / 引理 `LeftHomologyData.leftHomologyIso_inv_naturality`

English:
lemma LeftHomologyData.leftHomologyIso_inv_naturality
  proof: by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]

中文:
引理 LeftHomologyData.leftHomologyIso_inv_naturality
  证明: by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]

Depends on / 依赖: ShortComplex, ShortComplex.leftHomologyIso, _comp, comp_id, homologyIso, homologyMap, id_comp, leftHomologyIso, leftHomologyMap
-/
lemma LeftHomologyData.leftHomologyIso_inv_naturality
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.homologyIso.inv ≫ homologyMap φ =
      leftHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]
/--
lemma `leftHomologyIso_hom_naturality` / 引理 `leftHomologyIso_hom_naturality`

English:
lemma leftHomologyIso_hom_naturality
  proof: by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_inv_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]

中文:
引理 leftHomologyIso_hom_naturality
  证明: by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_inv_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]

Depends on / 依赖: Iso.symm_inv, LeftHomologyData, LeftHomologyData.homologyIso_leftHomologyData, LeftHomologyData.leftHomologyIso_inv_naturality, homologyIso_leftHomologyData, leftHomologyData, leftHomologyIso_inv_naturality, symm_inv
-/
lemma leftHomologyIso_hom_naturality :
    S₁.leftHomologyIso.hom ≫ homologyMap φ =
      leftHomologyMap φ ≫ S₂.leftHomologyIso.hom := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_inv_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
/--
lemma `leftHomologyIso_inv_naturality` / 引理 `leftHomologyIso_inv_naturality`

English:
lemma leftHomologyIso_inv_naturality
  proof: by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_hom_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]

中文:
引理 leftHomologyIso_inv_naturality
  证明: by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_hom_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]

Depends on / 依赖: Iso.symm_inv, LeftHomologyData, LeftHomologyData.homologyIso_leftHomologyData, LeftHomologyData.leftHomologyIso_hom_naturality, homologyIso_leftHomologyData, leftHomologyData, leftHomologyIso_hom_naturality, symm_inv
-/
lemma leftHomologyIso_inv_naturality :
    S₁.leftHomologyIso.inv ≫ leftHomologyMap φ =
      homologyMap φ ≫ S₂.leftHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using!
    LeftHomologyData.leftHomologyIso_hom_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
/--
lemma `RightHomologyData.rightHomologyIso_hom_naturality` / 引理 `RightHomologyData.rightHomologyIso_hom_naturality`

English:
lemma RightHomologyData.rightHomologyIso_hom_naturality
  proof: by
  rw [← cancel_epi h₁.homologyIso.inv]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (leftRightHomologyComparison' S₁.leftHomologyData h₁)]; rw [← leftRightHomologyComparison'_naturality φ S₁.leftHomologyData h₁ S₂.leftHomologyData h₂]; rw [← cancel_epi (S₁.leftHomologyData.homologyIso.hom)]; rw [

中文:
引理 RightHomologyData.rightHomologyIso_hom_naturality
  证明: by
  rw [← cancel_epi h₁.homologyIso.inv]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (leftRightHomologyComparison' S₁.leftHomologyData h₁)]; rw [← leftRightHomologyComparison'_naturality φ S₁.leftHomologyData h₁ S₂.leftHomologyData h₂]; rw [← cancel_epi (S₁.leftHomologyData.homologyIso.hom)]; rw [

Depends on / 依赖: Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, LeftHomologyData, LeftHomologyData.leftHomologyIso_hom_naturality_assoc, _fac, _naturality, cancel_epi, hom_inv_id_assoc, homologyIso, homologyIso.inv, inv_hom_id_assoc, leftHomologyData, leftHomologyData.homologyIso.hom, leftHomologyIso_hom_naturality_assoc, leftRightHomologyComparison
-/
lemma RightHomologyData.rightHomologyIso_hom_naturality
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.homologyIso.hom ≫ rightHomologyMap' φ h₁ h₂ =
      homologyMap φ ≫ h₂.homologyIso.hom := by
  rw [← cancel_epi h₁.homologyIso.inv]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (leftRightHomologyComparison' S₁.leftHomologyData h₁)]; rw [← leftRightHomologyComparison'_naturality φ S₁.leftHomologyData h₁ S₂.leftHomologyData h₂]; rw [← cancel_epi (S₁.leftHomologyData.homologyIso.hom)]; rw [LeftHomologyData.leftHomologyIso_hom_naturality_assoc]; rw [leftRightHomologyComparison'_fac]; rw [leftRightHomologyComparison'_fac]; rw [assoc]; rw [Iso.hom_inv_id_assoc]; rw [Iso.hom_inv_id_assoc]; rw [Iso.hom_inv_id_assoc]

@[reassoc]
/--
lemma `RightHomologyData.rightHomologyIso_inv_naturality` / 引理 `RightHomologyData.rightHomologyIso_inv_naturality`

English:
lemma RightHomologyData.rightHomologyIso_inv_naturality
  proof: by
  simp only [← cancel_mono h₂.homologyIso.hom, assoc, Iso.inv_hom_id_assoc, comp_id,
    ← RightHomologyData.rightHomologyIso_hom_naturality φ h₁ h₂, Iso.inv_hom_id]

@[reassoc]

中文:
引理 RightHomologyData.rightHomologyIso_inv_naturality
  证明: by
  simp only [← cancel_mono h₂.homologyIso.hom, assoc, Iso.inv_hom_id_assoc, comp_id,
    ← RightHomologyData.rightHomologyIso_hom_naturality φ h₁ h₂, Iso.inv_hom_id]

@[reassoc]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, RightHomologyData, RightHomologyData.rightHomologyIso_hom_naturality, cancel_mono, comp_id, homologyIso, homologyIso.hom, inv_hom_id, inv_hom_id_assoc, rightHomologyIso_hom_naturality
-/
lemma RightHomologyData.rightHomologyIso_inv_naturality
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
      h₁.homologyIso.inv ≫ homologyMap φ =
        rightHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  simp only [← cancel_mono h₂.homologyIso.hom, assoc, Iso.inv_hom_id_assoc, comp_id,
    ← RightHomologyData.rightHomologyIso_hom_naturality φ h₁ h₂, Iso.inv_hom_id]

@[reassoc]
/--
lemma `rightHomologyIso_hom_naturality` / 引理 `rightHomologyIso_hom_naturality`

English:
lemma rightHomologyIso_hom_naturality
  proof: by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_inv_naturality φ S₁.rightHomologyData S₂.rightHomologyData

@[reassoc]

中文:
引理 rightHomologyIso_hom_naturality
  证明: by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_inv_naturality φ S₁.rightHomologyData S₂.rightHomologyData

@[reassoc]

Depends on / 依赖: Iso.symm_inv, RightHomologyData, RightHomologyData.homologyIso_rightHomologyData, RightHomologyData.rightHomologyIso_inv_naturality, homologyIso_rightHomologyData, rightHomologyData, rightHomologyIso_inv_naturality, symm_inv
-/
lemma rightHomologyIso_hom_naturality :
    S₁.rightHomologyIso.hom ≫ homologyMap φ =
      rightHomologyMap φ ≫ S₂.rightHomologyIso.hom := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_inv_naturality φ S₁.rightHomologyData S₂.rightHomologyData

@[reassoc]
/--
lemma `rightHomologyIso_inv_naturality` / 引理 `rightHomologyIso_inv_naturality`

English:
lemma rightHomologyIso_inv_naturality
  proof: by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_hom_naturality φ S₁.rightHomologyData S₂.rightHomologyData

中文:
引理 rightHomologyIso_inv_naturality
  证明: by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_hom_naturality φ S₁.rightHomologyData S₂.rightHomologyData

Depends on / 依赖: Iso.symm_inv, RightHomologyData, RightHomologyData.homologyIso_rightHomologyData, RightHomologyData.rightHomologyIso_hom_naturality, homologyIso_rightHomologyData, rightHomologyData, rightHomologyIso_hom_naturality, symm_inv
-/
lemma rightHomologyIso_inv_naturality :
    S₁.rightHomologyIso.inv ≫ rightHomologyMap φ =
      homologyMap φ ≫ S₂.rightHomologyIso.inv := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using!
    RightHomologyData.rightHomologyIso_hom_naturality φ S₁.rightHomologyData S₂.rightHomologyData

end

variable (C)

/--
Definition of `_root_.CategoryTheory.CategoryWithHomology` / `_root_.CategoryTheory.CategoryWithHomology` 的定义

English:
class _root_.CategoryTheory.CategoryWithHomology
  parameters: : Prop where
  axioms and operations (1):
    - hasHomology : forall (S : ShortComplex C), S.HasHomology

中文:
类 _root_.范畴论.带同调范畴
  参数: : 命题 where
  公理与运算 (1 个):
    - hasHomology : 对任意 (S : 短复形 C), S.有同调
-/
class _root_.CategoryTheory.CategoryWithHomology : Prop where
  hasHomology : forall (S : ShortComplex C), S.HasHomology

attribute [instance] CategoryWithHomology.hasHomology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithHomology
  signature: C] : CategoryWithHomology Cᵒᵖ
  body: ⟨fun S => HasHomology.mk' S.unop.homologyData.op⟩

中文:
实例 [带同调范畴
  签名: C] : 带同调范畴 Cᵒᵖ
  定义体: ⟨fun S => HasHomology.mk' S.unop.homologyData.op⟩

Depends on / 依赖: HasHomology, HasHomology.mk, S.unop.homologyData.op, homologyData
-/
instance [CategoryWithHomology C] : CategoryWithHomology Cᵒᵖ :=
  ⟨fun S => HasHomology.mk' S.unop.homologyData.op⟩

/-- The homology functor `ShortComplex C ⥤ C` for a category `C` with homology. -/
@[simps]
/--
Definition of `homologyFunctor` / `homologyFunctor` 的定义

English:
definition homologyFunctor
  signature: [CategoryWithHomology C]
  body: S.homology
  map f := homologyMap f

中文:
定义 homologyFunctor
  签名: [带同调范畴 C]
  定义体: S.homology
  map f := homologyMap f

Depends on / 依赖: S.homology, homology
-/
noncomputable def homologyFunctor [CategoryWithHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.homology
  map f := homologyMap f

variable {C}

/--
Instance `isIso_homologyMap'_of_epi_of_isIso_of_mono` / 实例 `isIso_homologyMap'_of_epi_of_isIso_of_mono`

English:
instance isIso_homologyMap'_of_epi_of_isIso_of_mono
  signature: (φ : S₁ ⟶ S₂)
  body: by
  dsimp only [homologyMap']
  infer_instance

中文:
实例 isIso_homologyMap'_of_epi_of_isIso_of_mono
  签名: (φ : S₁ ⟶ S₂)
  定义体: by
  dsimp only [homologyMap']
  infer_instance
-/
instance isIso_homologyMap'_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap' φ h₁ h₂) := by
  dsimp only [homologyMap']
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_homologyMap_of_epi_of_isIso_of_mono'` / 引理 `isIso_homologyMap_of_epi_of_isIso_of_mono'`

English:
lemma isIso_homologyMap_of_epi_of_isIso_of_mono'
  statement: (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  dsimp only [homologyMap]
  infer_instance

中文:
引理 isIso_homologyMap_of_epi_of_isIso_of_mono'
  结论: (φ : S₁ ⟶ S₂) [S₁.有同调] [S₂.有同调]
  证明: by
  dsimp only [homologyMap]
  infer_instance

Depends on / 依赖: homologyMap, infer_instance
-/
lemma isIso_homologyMap_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
    (h₁ : Epi φ.τ₁) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃) :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap]
  infer_instance

/--
Instance `isIso_homologyMap_of_epi_of_isIso_of_mono` / 实例 `isIso_homologyMap_of_epi_of_isIso_of_mono`

English:
instance isIso_homologyMap_of_epi_of_isIso_of_mono
  signature: (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
  body: isIso_homologyMap_of_epi_of_isIso_of_mono' φ inferInstance inferInstance inferInstance

中文:
实例 isIso_homologyMap_of_epi_of_isIso_of_mono
  签名: (φ : S₁ ⟶ S₂) [S₁.有同调] [S₂.有同调]
  定义体: isIso_homologyMap_of_epi_of_isIso_of_mono' φ inferInstance inferInstance inferInstance

Depends on / 依赖: isIso_homologyMap_of_epi_of_isIso_of_mono
-/
instance isIso_homologyMap_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap φ) :=
  isIso_homologyMap_of_epi_of_isIso_of_mono' φ inferInstance inferInstance inferInstance

/--
Instance `isIso_homologyFunctor_map_of_epi_of_isIso_of_mono` / 实例 `isIso_homologyFunctor_map_of_epi_of_isIso_of_mono`

English:
instance isIso_homologyFunctor_map_of_epi_of_isIso_of_mono
  signature: (φ : S₁ ⟶ S₂) [CategoryWithHomology C]
  body: inferInstanceAs IsIso (homologyMap φ)

中文:
实例 isIso_homologyFunctor_map_of_epi_of_isIso_of_mono
  签名: (φ : S₁ ⟶ S₂) [带同调范畴 C]
  定义体: inferInstanceAs IsIso (homologyMap φ)

Depends on / 依赖: homologyMap
-/
instance isIso_homologyFunctor_map_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [CategoryWithHomology C]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso ((homologyFunctor C).map φ) :=
inferInstanceAs IsIso (homologyMap φ)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isIso_homologyMap_of_isIso` / 实例 `isIso_homologyMap_of_isIso`

English:
instance isIso_homologyMap_of_isIso
  signature: (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] [IsIso φ]
  body: by
  dsimp only [homologyMap, homologyMap']
  infer_instance

中文:
实例 isIso_homologyMap_of_isIso
  签名: (φ : S₁ ⟶ S₂) [S₁.有同调] [S₂.有同调] [是同构 φ]
  定义体: by
  dsimp only [homologyMap, homologyMap']
  infer_instance

Depends on / 依赖: homologyMap, infer_instance
-/
instance isIso_homologyMap_of_isIso (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] [IsIso φ] :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap, homologyMap']
  infer_instance

section

variable (S) {A : C}
variable [HasHomology S]

/--
Definition of `homologyπ` / `homologyπ` 的定义

English:
definition homologyπ
  signature: : S.cycles ⟶ S.homology
  body: S.leftHomologyπ ≫ S.leftHomologyIso.hom

中文:
定义 homologyπ
  签名: : S.cycles ⟶ S.homology
  定义体: S.leftHomologyπ ≫ S.leftHomologyIso.hom

Depends on / 依赖: S.leftHomology, S.leftHomologyIso.hom, leftHomologyIso
-/
noncomputable def homologyπ : S.cycles ⟶ S.homology :=
  S.leftHomologyπ ≫ S.leftHomologyIso.hom

/--
Definition of `homologyι` / `homologyι` 的定义

English:
definition homologyι
  signature: : S.homology ⟶ S.opcycles
  body: S.rightHomologyIso.inv ≫ S.rightHomologyι

@[reassoc (attr := simp)]

中文:
定义 homologyι
  签名: : S.homology ⟶ S.opcycles
  定义体: S.rightHomologyIso.inv ≫ S.rightHomologyι

@[reassoc (attr := simp)]

Depends on / 依赖: S.rightHomology, S.rightHomologyIso.inv, rightHomologyIso
-/
noncomputable def homologyι : S.homology ⟶ S.opcycles :=
  S.rightHomologyIso.inv ≫ S.rightHomologyι

@[reassoc (attr := simp)]
/--
lemma `homologyπ_comp_leftHomologyIso_inv` / 引理 `homologyπ_comp_leftHomologyIso_inv`

English:
lemma homologyπ_comp_leftHomologyIso_inv
  proof: by
  dsimp only [homologyπ]
  simp only [assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]

中文:
引理 homologyπ_comp_leftHomologyIso_inv
  证明: by
  dsimp only [homologyπ]
  simp only [assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, comp_id, hom_inv_id
-/
lemma homologyπ_comp_leftHomologyIso_inv :
    S.homologyπ ≫ S.leftHomologyIso.inv = S.leftHomologyπ := by
  dsimp only [homologyπ]
  simp only [assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
/--
lemma `rightHomologyIso_hom_comp_homologyι` / 引理 `rightHomologyIso_hom_comp_homologyι`

English:
lemma rightHomologyIso_hom_comp_homologyι
  proof: by
  dsimp only [homologyι]
  simp only [Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

中文:
引理 rightHomologyIso_hom_comp_homologyι
  证明: by
  dsimp only [homologyι]
  simp only [Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id_assoc, hom_inv_id_assoc
-/
lemma rightHomologyIso_hom_comp_homologyι :
    S.rightHomologyIso.hom ≫ S.homologyι = S.rightHomologyι := by
  dsimp only [homologyι]
  simp only [Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/--
lemma `toCycles_comp_homologyπ` / 引理 `toCycles_comp_homologyπ`

English:
lemma toCycles_comp_homologyπ
  proof: by
  dsimp only [homologyπ]
  simp only [toCycles_comp_leftHomologyπ_assoc, zero_comp]

@[reassoc (attr := simp)]

中文:
引理 toCycles_comp_homologyπ
  证明: by
  dsimp only [homologyπ]
  simp only [toCycles_comp_leftHomologyπ_assoc, zero_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: zero_comp
-/
lemma toCycles_comp_homologyπ :
    S.toCycles ≫ S.homologyπ = 0 := by
  dsimp only [homologyπ]
  simp only [toCycles_comp_leftHomologyπ_assoc, zero_comp]

@[reassoc (attr := simp)]
/--
lemma `homologyι_comp_fromOpcycles` / 引理 `homologyι_comp_fromOpcycles`

English:
lemma homologyι_comp_fromOpcycles
  proof: by
  dsimp only [homologyι]
  simp only [assoc, rightHomologyι_comp_fromOpcycles, comp_zero]

中文:
引理 homologyι_comp_fromOpcycles
  证明: by
  dsimp only [homologyι]
  simp only [assoc, rightHomologyι_comp_fromOpcycles, comp_zero]

Depends on / 依赖: comp_zero
-/
lemma homologyι_comp_fromOpcycles :
    S.homologyι ≫ S.fromOpcycles = 0 := by
  dsimp only [homologyι]
  simp only [assoc, rightHomologyι_comp_fromOpcycles, comp_zero]

/--
Definition of `homologyIsCokernel` / `homologyIsCokernel` 的定义

English:
definition homologyIsCokernel
  signature: :
  body: IsColimit.ofIsoColimit S.leftHomologyIsCokernel
    (Cofork.ext S.leftHomologyIso rfl)

中文:
定义 homologyIsCokernel
  签名: :
  定义体: IsColimit.ofIsoColimit S.leftHomologyIsCokernel
    (Cofork.ext S.leftHomologyIso rfl)

Depends on / 依赖: Cofork, Cofork.ext, IsColimit, IsColimit.ofIsoColimit, S.leftHomologyIsCokernel, S.leftHomologyIso, leftHomologyIsCokernel, leftHomologyIso, ofIsoColimit
-/
noncomputable def homologyIsCokernel :
    IsColimit (CokernelCofork.ofπ S.homologyπ S.toCycles_comp_homologyπ) :=
  IsColimit.ofIsoColimit S.leftHomologyIsCokernel
    (Cofork.ext S.leftHomologyIso rfl)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `homologyIsKernel` / `homologyIsKernel` 的定义

English:
definition homologyIsKernel
  signature: :
  body: IsLimit.ofIsoLimit S.rightHomologyIsKernel
    (Fork.ext S.rightHomologyIso (by simp))

中文:
定义 homologyIsKernel
  签名: :
  定义体: IsLimit.ofIsoLimit S.rightHomologyIsKernel
    (Fork.ext S.rightHomologyIso (by simp))

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.ofIsoLimit, S.rightHomologyIsKernel, S.rightHomologyIso, ofIsoLimit, rightHomologyIsKernel, rightHomologyIso
-/
noncomputable def homologyIsKernel :
    IsLimit (KernelFork.ofι S.homologyι S.homologyι_comp_fromOpcycles) :=
  IsLimit.ofIsoLimit S.rightHomologyIsKernel
    (Fork.ext S.rightHomologyIso (by simp))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi S.homologyπ
  body: Limits.epi_of_isColimit_cofork (S.homologyIsCokernel)

中文:
实例 :
  签名: 满态射 S.homologyπ
  定义体: Limits.epi_of_isColimit_cofork (S.homologyIsCokernel)

Depends on / 依赖: Limits, Limits.epi_of_isColimit_cofork, S.homologyIsCokernel, epi_of_isColimit_cofork, homologyIsCokernel
-/
instance : Epi S.homologyπ :=
  Limits.epi_of_isColimit_cofork (S.homologyIsCokernel)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono S.homologyι
  body: Limits.mono_of_isLimit_fork (S.homologyIsKernel)

中文:
实例 :
  签名: 单态射 S.homologyι
  定义体: Limits.mono_of_isLimit_fork (S.homologyIsKernel)

Depends on / 依赖: Limits, Limits.mono_of_isLimit_fork, S.homologyIsKernel, homologyIsKernel, mono_of_isLimit_fork
-/
instance : Mono S.homologyι :=
  Limits.mono_of_isLimit_fork (S.homologyIsKernel)

/--
Definition of `descHomology` / `descHomology` 的定义

English:
definition descHomology
  signature: (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0)
  body: S.homologyIsCokernel.desc (CokernelCofork.ofπ k hk)

中文:
定义 descHomology
  签名: (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0)
  定义体: S.homologyIsCokernel.desc (CokernelCofork.ofπ k hk)

Depends on / 依赖: CokernelCofork, CokernelCofork.of, S.homologyIsCokernel.desc, homologyIsCokernel
-/
noncomputable def descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.homology ⟶ A :=
  S.homologyIsCokernel.desc (CokernelCofork.ofπ k hk)

/--
Definition of `liftHomology` / `liftHomology` 的定义

English:
definition liftHomology
  signature: (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0)
  body: S.homologyIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

中文:
定义 liftHomology
  签名: (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0)
  定义体: S.homologyIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: KernelFork, KernelFork.of, S.homologyIsKernel.lift, homologyIsKernel
-/
noncomputable def liftHomology (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) :
    A ⟶ S.homology :=
  S.homologyIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
/--
lemma `π_descHomology` / 引理 `π_descHomology`

English:
lemma π_descHomology
  given: (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0)
  proof: Cofork.IsColimit.π_desc S.homologyIsCokernel

@[reassoc (attr := simp)]

中文:
引理 π_descHomology
  条件: (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0)
  证明: Cofork.IsColimit.π_desc S.homologyIsCokernel

@[reassoc (attr := simp)]

Depends on / 依赖: Cofork, Cofork.IsColimit, IsColimit, S.homologyIsCokernel, homologyIsCokernel
-/
lemma π_descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.homologyπ ≫ S.descHomology k hk = k :=
  Cofork.IsColimit.π_desc S.homologyIsCokernel

@[reassoc (attr := simp)]
/--
lemma `liftHomology_ι` / 引理 `liftHomology_ι`

English:
lemma liftHomology_ι
  given: (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0)
  proof: Fork.IsLimit.lift_ι S.homologyIsKernel

@[reassoc (attr := simp)]

中文:
引理 liftHomology_ι
  条件: (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0)
  证明: Fork.IsLimit.lift_ι S.homologyIsKernel

@[reassoc (attr := simp)]

Depends on / 依赖: Fork.IsLimit.lift_, IsLimit, S.homologyIsKernel, homologyIsKernel
-/
lemma liftHomology_ι (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) :
    S.liftHomology k hk ≫ S.homologyι = k :=
  Fork.IsLimit.lift_ι S.homologyIsKernel

@[reassoc (attr := simp)]
/--
lemma `homologyπ_naturality` / 引理 `homologyπ_naturality`

English:
lemma homologyπ_naturality
  given: (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  simp only [← cancel_mono S₂.leftHomologyIso.inv, assoc, ← leftHomologyIso_inv_naturality φ,
    homologyπ_comp_leftHomologyIso_inv]
  simp only [homologyπ, assoc, Iso.hom_inv_id_assoc, leftHomologyπ_naturality]

@[reassoc (attr := simp)]

中文:
引理 homologyπ_naturality
  条件: (φ : S₁ ⟶ S₂) [S₁.有同调] [S₂.有同调]
  证明: by
  simp only [← cancel_mono S₂.leftHomologyIso.inv, assoc, ← leftHomologyIso_inv_naturality φ,
    homologyπ_comp_leftHomologyIso_inv]
  simp only [homologyπ, assoc, Iso.hom_inv_id_assoc, leftHomologyπ_naturality]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id_assoc, cancel_mono, hom_inv_id_assoc, leftHomologyIso, leftHomologyIso.inv, leftHomologyIso_inv_naturality
-/
lemma homologyπ_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    S₁.homologyπ ≫ homologyMap φ = cyclesMap φ ≫ S₂.homologyπ := by
  simp only [← cancel_mono S₂.leftHomologyIso.inv, assoc, ← leftHomologyIso_inv_naturality φ,
    homologyπ_comp_leftHomologyIso_inv]
  simp only [homologyπ, assoc, Iso.hom_inv_id_assoc, leftHomologyπ_naturality]

@[reassoc (attr := simp)]
/--
lemma `homologyι_naturality` / 引理 `homologyι_naturality`

English:
lemma homologyι_naturality
  given: (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  simp only [← cancel_epi S₁.rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc φ,
    rightHomologyIso_hom_comp_homologyι, rightHomologyι_naturality]
  simp only [homologyι, assoc, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

中文:
引理 homologyι_naturality
  条件: (φ : S₁ ⟶ S₂) [S₁.有同调] [S₂.有同调]
  证明: by
  simp only [← cancel_epi S₁.rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc φ,
    rightHomologyIso_hom_comp_homologyι, rightHomologyι_naturality]
  simp only [homologyι, assoc, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id_assoc, cancel_epi, hom_inv_id_assoc, rightHomologyIso, rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc
-/
lemma homologyι_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap φ ≫ S₂.homologyι = S₁.homologyι ≫ S₁.opcyclesMap φ := by
  simp only [← cancel_epi S₁.rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc φ,
    rightHomologyIso_hom_comp_homologyι, rightHomologyι_naturality]
  simp only [homologyι, assoc, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/--
lemma `homology_π_ι` / 引理 `homology_π_ι`

English:
lemma homology_π_ι
  proof: by
  dsimp only [homologyπ, homologyι]
  simpa only [assoc, S.leftRightHomologyComparison_fac] using S.π_leftRightHomologyComparison_ι

中文:
引理 homology_π_ι
  证明: by
  dsimp only [homologyπ, homologyι]
  simpa only [assoc, S.leftRightHomologyComparison_fac] using S.π_leftRightHomologyComparison_ι

Depends on / 依赖: S.leftRightHomologyComparison_fac, leftRightHomologyComparison_fac
-/
lemma homology_π_ι :
    S.homologyπ ≫ S.homologyι = S.iCycles ≫ S.pOpcycles := by
  dsimp only [homologyπ, homologyι]
  simpa only [assoc, S.leftRightHomologyComparison_fac] using S.π_leftRightHomologyComparison_ι

/--
Definition of `homologyIsoKernelDesc` / `homologyIsoKernelDesc` 的定义

English:
definition homologyIsoKernelDesc
  signature: [HasCokernel S.f]
  body: S.rightHomologyIso.symm ≪≫ S.rightHomologyIsoKernelDesc

中文:
定义 homologyIsoKernelDesc
  签名: [HasCokernel S.f]
  定义体: S.rightHomologyIso.symm ≪≫ S.rightHomologyIsoKernelDesc

Depends on / 依赖: S.rightHomologyIso.symm, S.rightHomologyIsoKernelDesc, rightHomologyIso, rightHomologyIsoKernelDesc
-/
noncomputable def homologyIsoKernelDesc [HasCokernel S.f]
    [HasKernel (cokernel.desc S.f S.g S.zero)] :
    S.homology ≅ kernel (cokernel.desc S.f S.g S.zero) :=
  S.rightHomologyIso.symm ≪≫ S.rightHomologyIsoKernelDesc

/--
Definition of `homologyIsoCokernelLift` / `homologyIsoCokernelLift` 的定义

English:
definition homologyIsoCokernelLift
  signature: [HasKernel S.g]
  body: S.leftHomologyIso.symm ≪≫ S.leftHomologyIsoCokernelLift

@[reassoc (attr := simp)]

中文:
定义 homologyIsoCokernelLift
  签名: [HasKernel S.g]
  定义体: S.leftHomologyIso.symm ≪≫ S.leftHomologyIsoCokernelLift

@[reassoc (attr := simp)]

Depends on / 依赖: S.leftHomologyIso.symm, S.leftHomologyIsoCokernelLift, leftHomologyIso, leftHomologyIsoCokernelLift
-/
noncomputable def homologyIsoCokernelLift [HasKernel S.g]
    [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.homology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  S.leftHomologyIso.symm ≪≫ S.leftHomologyIsoCokernelLift

@[reassoc (attr := simp)]
/--
lemma `LeftHomologyData.homologyπ_comp_homologyIso_hom` / 引理 `LeftHomologyData.homologyπ_comp_homologyIso_hom`

English:
lemma LeftHomologyData.homologyπ_comp_homologyIso_hom
  given: (h : S.LeftHomologyData)
  proof: by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc,
    leftHomologyπ_comp_leftHomologyIso_hom]

@[reassoc (attr := simp)]

中文:
引理 LeftHomologyData.homologyπ_comp_homologyIso_hom
  条件: (h : S.LeftHomologyData)
  证明: by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc,
    leftHomologyπ_comp_leftHomologyIso_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id_assoc, Iso.symm_hom, Iso.trans_hom, hom_inv_id_assoc, homologyIso, symm_hom, trans_hom
-/
lemma LeftHomologyData.homologyπ_comp_homologyIso_hom (h : S.LeftHomologyData) :
    S.homologyπ ≫ h.homologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc,
    leftHomologyπ_comp_leftHomologyIso_hom]

@[reassoc (attr := simp)]
/--
lemma `LeftHomologyData.π_comp_homologyIso_inv` / 引理 `LeftHomologyData.π_comp_homologyIso_inv`

English:
lemma LeftHomologyData.π_comp_homologyIso_inv
  given: (h : S.LeftHomologyData)
  proof: by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, π_comp_leftHomologyIso_inv_assoc]

@[reassoc (attr := simp)]

中文:
引理 LeftHomologyData.π_comp_homologyIso_inv
  条件: (h : S.LeftHomologyData)
  证明: by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, π_comp_leftHomologyIso_inv_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.symm_inv, Iso.trans_inv, homologyIso, symm_inv, trans_inv
-/
lemma LeftHomologyData.π_comp_homologyIso_inv (h : S.LeftHomologyData) :
    h.π ≫ h.homologyIso.inv = h.cyclesIso.inv ≫ S.homologyπ := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, π_comp_leftHomologyIso_inv_assoc]

@[reassoc (attr := simp)]
/--
lemma `RightHomologyData.homologyIso_inv_comp_homologyι` / 引理 `RightHomologyData.homologyIso_inv_comp_homologyι`

English:
lemma RightHomologyData.homologyIso_inv_comp_homologyι
  given: (h : S.RightHomologyData)
  proof: by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, assoc, Iso.hom_inv_id_assoc,
    rightHomologyIso_inv_comp_rightHomologyι]

@[reassoc (attr := simp)]

中文:
引理 RightHomologyData.homologyIso_inv_comp_homologyι
  条件: (h : S.RightHomologyData)
  证明: by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, assoc, Iso.hom_inv_id_assoc,
    rightHomologyIso_inv_comp_rightHomologyι]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id_assoc, Iso.symm_inv, Iso.trans_inv, hom_inv_id_assoc, homologyIso, symm_inv, trans_inv
-/
lemma RightHomologyData.homologyIso_inv_comp_homologyι (h : S.RightHomologyData) :
    h.homologyIso.inv ≫ S.homologyι = h.ι ≫ h.opcyclesIso.inv := by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, assoc, Iso.hom_inv_id_assoc,
    rightHomologyIso_inv_comp_rightHomologyι]

@[reassoc (attr := simp)]
/--
lemma `RightHomologyData.homologyIso_hom_comp_ι` / 引理 `RightHomologyData.homologyIso_hom_comp_ι`

English:
lemma RightHomologyData.homologyIso_hom_comp_ι
  given: (h : S.RightHomologyData)
  proof: by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, rightHomologyIso_hom_comp_ι]

@[reassoc (attr := simp)]

中文:
引理 RightHomologyData.homologyIso_hom_comp_ι
  条件: (h : S.RightHomologyData)
  证明: by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, rightHomologyIso_hom_comp_ι]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.symm_hom, Iso.trans_hom, homologyIso, symm_hom, trans_hom
-/
lemma RightHomologyData.homologyIso_hom_comp_ι (h : S.RightHomologyData) :
    h.homologyIso.hom ≫ h.ι = S.homologyι ≫ h.opcyclesIso.hom := by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, rightHomologyIso_hom_comp_ι]

@[reassoc (attr := simp)]
/--
lemma `LeftHomologyData.homologyIso_hom_comp_leftHomologyIso_inv` / 引理 `LeftHomologyData.homologyIso_hom_comp_leftHomologyIso_inv`

English:
lemma LeftHomologyData.homologyIso_hom_comp_leftHomologyIso_inv
  given: (h : S.LeftHomologyData)
  proof: by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]

中文:
引理 LeftHomologyData.homologyIso_hom_comp_leftHomologyIso_inv
  条件: (h : S.LeftHomologyData)
  证明: by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, Iso.symm_hom, Iso.trans_hom, comp_id, hom_inv_id, homologyIso, symm_hom, trans_hom
-/
lemma LeftHomologyData.homologyIso_hom_comp_leftHomologyIso_inv (h : S.LeftHomologyData) :
    h.homologyIso.hom ≫ h.leftHomologyIso.inv = S.leftHomologyIso.inv := by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
/--
lemma `LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv` / 引理 `LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv`

English:
lemma LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv
  given: (h : S.LeftHomologyData)
  proof: by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

中文:
引理 LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv
  条件: (h : S.LeftHomologyData)
  证明: by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id_assoc, Iso.symm_inv, Iso.trans_inv, hom_inv_id_assoc, homologyIso, symm_inv, trans_inv
-/
lemma LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv (h : S.LeftHomologyData) :
    h.leftHomologyIso.hom ≫ h.homologyIso.inv = S.leftHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/--
lemma `RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv` / 引理 `RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv`

English:
lemma RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv
  given: (h : S.RightHomologyData)
  proof: by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]

中文:
引理 RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv
  条件: (h : S.RightHomologyData)
  证明: by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, Iso.symm_hom, Iso.trans_hom, LieAlgebra, LieAlgebra.toModule_injective, comp_id, hom_inv_id, homologyIso, subsingleton, symm_hom, toModule_injective, trans_hom
-/
lemma RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv (h : S.RightHomologyData) :
    h.homologyIso.hom ≫ h.rightHomologyIso.inv = S.rightHomologyIso.inv := by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
/--
lemma `RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv` / 引理 `RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv`

English:
lemma RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv
  given: (h : S.RightHomologyData)
  proof: by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

中文:
引理 RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv
  条件: (h : S.RightHomologyData)
  证明: by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, Iso.symm_inv, Iso.trans_inv, hom_inv_id_assoc, homologyIso, symm_inv, trans_inv
-/
lemma RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv (h : S.RightHomologyData) :
    h.rightHomologyIso.hom ≫ h.homologyIso.inv = S.rightHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `comp_homologyMap_comp` / 引理 `comp_homologyMap_comp`

English:
lemma comp_homologyMap_comp
  statement: [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)
  proof: by
  dsimp only [LeftHomologyData.homologyIso, RightHomologyData.homologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyIso, rightHomologyIso,
    leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.cyclesIso, RightHomologyData.opcyclesIso,
    LeftHomologyData.leftHomologyIso, Righ

中文:
引理 comp_homologyMap_comp
  结论: [S₁.有同调] [S₂.有同调] (φ : S₁ ⟶ S₂)
  证明: by
  dsimp only [LeftHomologyData.homologyIso, RightHomologyData.homologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyIso, rightHomologyIso,
    leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.cyclesIso, RightHomologyData.opcyclesIso,
    LeftHomologyData.leftHomologyIso, Righ

Depends on / 依赖: HomologyData, HomologyData.comm_assoc, Iso.refl, Iso.symm, Iso.trans, LeftHomologyData, LeftHomologyData.cyclesIso, LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso, RightHomologyData, RightHomologyData.homologyIso, RightHomologyData.opcyclesIso, RightHomologyData.rightHomologyIso, _assoc, comm_assoc, cyclesIso, homologyIso, homologyMap, leftHomologyIso, leftHomologyMapIso
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
/--
lemma `π_homologyMap_ι` / 引理 `π_homologyMap_ι`

English:
lemma π_homologyMap_ι
  given: [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)
  proof: by
  simp only [homologyι_naturality, homology_π_ι_assoc, p_opcyclesMap]

中文:
引理 π_homologyMap_ι
  条件: [S₁.有同调] [S₂.有同调] (φ : S₁ ⟶ S₂)
  证明: by
  simp only [homologyι_naturality, homology_π_ι_assoc, p_opcyclesMap]

Depends on / 依赖: p_opcyclesMap
-/
lemma π_homologyMap_ι [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.homologyπ ≫ homologyMap φ ≫ S₂.homologyι = S₁.iCycles ≫ φ.τ₂ ≫ S₂.pOpcycles := by
  simp only [homologyι_naturality, homology_π_ι_assoc, p_opcyclesMap]

end

variable (S)

/--
Definition of `homologyOpIso` / `homologyOpIso` 的定义

English:
definition homologyOpIso
  signature: [S.HasHomology]
  body: S.op.leftHomologyIso.symm ≪≫ S.leftHomologyOpIso ≪≫ S.rightHomologyIso.symm.op

中文:
定义 homologyOpIso
  签名: [S.有同调]
  定义体: S.op.leftHomologyIso.symm ≪≫ S.leftHomologyOpIso ≪≫ S.rightHomologyIso.symm.op

Depends on / 依赖: S.leftHomologyOpIso, S.op.leftHomologyIso.symm, S.rightHomologyIso.symm.op, leftHomologyIso, leftHomologyOpIso, rightHomologyIso
-/
noncomputable def homologyOpIso [S.HasHomology] :
    S.op.homology ≅ Opposite.op S.homology :=
  S.op.leftHomologyIso.symm ≪≫ S.leftHomologyOpIso ≪≫ S.rightHomologyIso.symm.op

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `homologyMap'_op` / 引理 `homologyMap'_op`

English:
lemma homologyMap'_op
  statement: (homologyMap' φ h₁ h₂).op =
  proof: Quiver.Hom.unop_inj (by
    dsimp
    have γ : HomologyMapData φ h₁ h₂ := default
    simp only [γ.homologyMap'_eq, γ.op.homologyMap'_eq, HomologyData.op_left,
      HomologyMapData.op_left, RightHomologyMapData.op_φH, Quiver.Hom.unop_op, assoc,
      ← γ.comm_assoc, Iso.hom_inv_id, comp_id])

中文:
引理 homologyMap'_op
  结论: (homologyMap' φ h₁ h₂).op =
  证明: Quiver.Hom.unop_inj (by
    dsimp
    have γ : HomologyMapData φ h₁ h₂ := default
    simp only [γ.homologyMap'_eq, γ.op.homologyMap'_eq, HomologyData.op_left,
      HomologyMapData.op_left, RightHomologyMapData.op_φH, Quiver.Hom.unop_op, assoc,
      ← γ.comm_assoc, Iso.hom_inv_id, comp_id])
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
/--
lemma `homologyMap_op` / 引理 `homologyMap_op`

English:
lemma homologyMap_op
  given: [HasHomology S₁] [HasHomology S₂]
  proof: by
  dsimp only [homologyMap, homologyOpIso]
  rw [homologyMap'_op]
  dsimp only [Iso.symm, Iso.trans, Iso.op, Iso.refl, rightHomologyIso, leftHomologyIso,
    leftHomologyOpIso, leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [assoc, rightH

中文:
引理 homologyMap_op
  条件: [有同调 S₁] [有同调 S₂]
  证明: by
  dsimp only [homologyMap, homologyOpIso]
  rw [homologyMap'_op]
  dsimp only [Iso.symm, Iso.trans, Iso.op, Iso.refl, rightHomologyIso, leftHomologyIso,
    leftHomologyOpIso, leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [assoc, rightH

Depends on / 依赖: HomologyData, HomologyData.op_left, Iso.op, Iso.refl, Iso.symm, Iso.trans, LeftHomologyData, LeftHomologyData.leftHomologyIso, _comp_assoc, comp_id, homologyMap, homologyOpIso, id_comp, leftHomologyIso, leftHomologyMap, leftHomologyMapIso, leftHomologyOpIso, opMap_id, op_comp, op_left
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
/--
lemma `homologyOpIso_hom_naturality` / 引理 `homologyOpIso_hom_naturality`

English:
lemma homologyOpIso_hom_naturality
  given: [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  simp [homologyMap_op]

@[reassoc]

中文:
引理 homologyOpIso_hom_naturality
  条件: [S₁.有同调] [S₂.有同调]
  证明: by
  simp [homologyMap_op]

@[reassoc]

Depends on / 依赖: homologyMap_op
-/
lemma homologyOpIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (opMap φ) ≫ (S₁.homologyOpIso).hom =
      S₂.homologyOpIso.hom ≫ (homologyMap φ).op := by
  simp [homologyMap_op]

@[reassoc]
/--
lemma `homologyOpIso_inv_naturality` / 引理 `homologyOpIso_inv_naturality`

English:
lemma homologyOpIso_inv_naturality
  given: [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  simp [homologyMap_op]

中文:
引理 homologyOpIso_inv_naturality
  条件: [S₁.有同调] [S₂.有同调]
  证明: by
  simp [homologyMap_op]

Depends on / 依赖: homologyMap_op
-/
lemma homologyOpIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] :
    (homologyMap φ).op ≫ (S₁.homologyOpIso).inv =
      S₂.homologyOpIso.inv ≫ homologyMap (opMap φ) := by
  simp [homologyMap_op]

variable (C)

/--
Definition of `homologyFunctorOpNatIso` / `homologyFunctorOpNatIso` 的定义

English:
definition homologyFunctorOpNatIso
  signature: [CategoryWithHomology C]
  body: NatIso.ofComponents (fun S => S.unop.homologyOpIso.symm)
    (fun _ => homologyOpIso_inv_naturality _)

中文:
定义 homologyFunctorOp自然数Iso
  签名: [带同调范畴 C]
  定义体: NatIso.ofComponents (fun S => S.unop.homologyOpIso.symm)
    (fun _ => homologyOpIso_inv_naturality _)

Depends on / 依赖: NatIso, NatIso.ofComponents, S.unop.homologyOpIso.symm, homologyOpIso, homologyOpIso_inv_naturality, ofComponents
-/
noncomputable def homologyFunctorOpNatIso [CategoryWithHomology C] :
    (homologyFunctor C).op ≅ opFunctor C ⋙ homologyFunctor Cᵒᵖ :=
  NatIso.ofComponents (fun S => S.unop.homologyOpIso.symm)
    (fun _ => homologyOpIso_inv_naturality _)

variable {C} {A : C}

/--
lemma `liftCycles_homologyπ_eq_zero_of_boundary` / 引理 `liftCycles_homologyπ_eq_zero_of_boundary`

English:
lemma liftCycles_homologyπ_eq_zero_of_boundary
  statement: [S.HasHomology]
  proof: by
  dsimp only [homologyπ]
  rw [S.liftCycles_leftHomologyπ_eq_zero_of_boundary_assoc k x hx]; rw [zero_comp]

@[reassoc]

中文:
引理 liftCycles_homologyπ_eq_zero_of_boundary
  结论: [S.有同调]
  证明: by
  dsimp only [homologyπ]
  rw [S.liftCycles_leftHomologyπ_eq_zero_of_boundary_assoc k x hx]; rw [zero_comp]

@[reassoc]

Depends on / 依赖: S.liftCycles_leftHomology, zero_comp
-/
lemma liftCycles_homologyπ_eq_zero_of_boundary [S.HasHomology]
    (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.homologyπ = 0 := by
  dsimp only [homologyπ]
  rw [S.liftCycles_leftHomologyπ_eq_zero_of_boundary_assoc k x hx]; rw [zero_comp]

@[reassoc]
/--
lemma `homologyι_descOpcycles_eq_zero_of_boundary` / 引理 `homologyι_descOpcycles_eq_zero_of_boundary`

English:
lemma homologyι_descOpcycles_eq_zero_of_boundary
  statement: [S.HasHomology]
  proof: by
  dsimp only [homologyι]
  rw [assoc]; rw [S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary k x hx]; rw [comp_zero]

中文:
引理 homologyι_descOpcycles_eq_zero_of_boundary
  结论: [S.有同调]
  证明: by
  dsimp only [homologyι]
  rw [assoc]; rw [S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary k x hx]; rw [comp_zero]

Depends on / 依赖: S.rightHomology, comp_zero
-/
lemma homologyι_descOpcycles_eq_zero_of_boundary [S.HasHomology]
    (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    S.homologyι ≫ S.descOpcycles k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  dsimp only [homologyι]
  rw [assoc]; rw [S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary k x hx]; rw [comp_zero]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_homologyMap_of_isIso_cyclesMap_of_epi` / 引理 `isIso_homologyMap_of_isIso_cyclesMap_of_epi`

English:
lemma isIso_homologyMap_of_isIso_cyclesMap_of_epi
  statement: {φ : S₁ ⟶ S₂}
  proof: by
  have h : S₂.toCycles ≫ inv (cyclesMap φ) ≫ S₁.homologyπ = 0 := by
    simp only [← cancel_epi φ.τ₁, ← toCycles_naturality_assoc,
      IsIso.hom_inv_id_assoc, toCycles_comp_homologyπ, comp_zero]
  have ⟨z, hz⟩ := CokernelCofork.IsColimit.desc' S₂.homologyIsCokernel _ h
  dsimp at hz
  refine ⟨⟨

中文:
引理 isIso_homologyMap_of_isIso_cyclesMap_of_epi
  结论: {φ : S₁ ⟶ S₂}
  证明: by
  have h : S₂.toCycles ≫ inv (cyclesMap φ) ≫ S₁.homologyπ = 0 := by
    simp only [← cancel_epi φ.τ₁, ← toCycles_naturality_assoc,
      IsIso.hom_inv_id_assoc, toCycles_comp_homologyπ, comp_zero]
  have ⟨z, hz⟩ := CokernelCofork.IsColimit.desc' S₂.homologyIsCokernel _ h
  dsimp at hz
  refine ⟨⟨

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, cancel_epi, comp_id, comp_zero, cyclesMap, hom_inv_id_assoc, homologyIsCokernel, inv_hom_id_assoc, reassoc_of, toCycles, toCycles_naturality_assoc
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
/--
lemma `isIso_homologyMap_of_isIso_opcyclesMap_of_mono` / 引理 `isIso_homologyMap_of_isIso_opcyclesMap_of_mono`

English:
lemma isIso_homologyMap_of_isIso_opcyclesMap_of_mono
  statement: {φ : S₁ ⟶ S₂}
  proof: by
  have h : (S₂.homologyι ≫ inv (opcyclesMap φ)) ≫ S₁.fromOpcycles = 0 := by
    simp only [← cancel_mono φ.τ₃, zero_comp, assoc, ← fromOpcycles_naturality,
      IsIso.inv_hom_id_assoc, homologyι_comp_fromOpcycles]
  have ⟨z, hz⟩ := KernelFork.IsLimit.lift' S₁.homologyIsKernel _ h
  dsimp at hz
 

中文:
引理 isIso_homologyMap_of_isIso_opcyclesMap_of_mono
  结论: {φ : S₁ ⟶ S₂}
  证明: by
  have h : (S₂.homologyι ≫ inv (opcyclesMap φ)) ≫ S₁.fromOpcycles = 0 := by
    simp only [← cancel_mono φ.τ₃, zero_comp, assoc, ← fromOpcycles_naturality,
      IsIso.inv_hom_id_assoc, homologyι_comp_fromOpcycles]
  have ⟨z, hz⟩ := KernelFork.IsLimit.lift' S₁.homologyIsKernel _ h
  dsimp at hz
 

Depends on / 依赖: IsIso.hom_inv_id, IsIso.in, IsIso.inv_hom_id_assoc, IsLimit, KernelFork, KernelFork.IsLimit.lift, cancel_mono, comp_id, fromOpcycles, fromOpcycles_naturality, hom_inv_id, homologyIsKernel, id_comp, inv_hom_id_assoc, opcyclesMap, reassoc_of, zero_comp
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

/--
lemma `isZero_homology_of_isZero_X₂` / 引理 `isZero_homology_of_isZero_X₂`

English:
lemma isZero_homology_of_isZero_X₂
  given: (hS : IsZero S.X₂) [S.HasHomology]
  proof: IsZero.of_iso hS (HomologyData.ofZeros S (hS.eq_of_tgt _ _)
    (hS.eq_of_src _ _)).left.homologyIso

中文:
引理 isZero_homology_of_isZero_X₂
  条件: (hS : 是零 S.X₂) [S.有同调]
  证明: IsZero.of_iso hS (HomologyData.ofZeros S (hS.eq_of_tgt _ _)
    (hS.eq_of_src _ _)).left.homologyIso

Depends on / 依赖: HomologyData, HomologyData.ofZeros, IsZero, IsZero.of_iso, eq_of_src, eq_of_tgt, hS.eq_of_src, hS.eq_of_tgt, homologyIso, left.homologyIso, ofZeros, of_iso
-/
lemma isZero_homology_of_isZero_X₂ (hS : IsZero S.X₂) [S.HasHomology] :
    IsZero S.homology :=
  IsZero.of_iso hS (HomologyData.ofZeros S (hS.eq_of_tgt _ _)
    (hS.eq_of_src _ _)).left.homologyIso

/--
lemma `isIso_homologyπ` / 引理 `isIso_homologyπ`

English:
lemma isIso_homologyπ
  given: (hf : S.f = 0) [S.HasHomology]
  proof: by
  have := S.isIso_leftHomologyπ hf
  dsimp only [homologyπ]
  infer_instance

中文:
引理 isIso_homologyπ
  条件: (hf : S.f = 0) [S.有同调]
  证明: by
  have := S.isIso_leftHomologyπ hf
  dsimp only [homologyπ]
  infer_instance

Depends on / 依赖: S.isIso_leftHomology, infer_instance
-/
lemma isIso_homologyπ (hf : S.f = 0) [S.HasHomology] :
    IsIso S.homologyπ := by
  have := S.isIso_leftHomologyπ hf
  dsimp only [homologyπ]
  infer_instance

/--
lemma `isIso_homologyι` / 引理 `isIso_homologyι`

English:
lemma isIso_homologyι
  given: (hg : S.g = 0) [S.HasHomology]
  proof: by
  have := S.isIso_rightHomologyι hg
  dsimp only [homologyι]
  infer_instance

中文:
引理 isIso_homologyι
  条件: (hg : S.g = 0) [S.有同调]
  证明: by
  have := S.isIso_rightHomologyι hg
  dsimp only [homologyι]
  infer_instance

Depends on / 依赖: S.isIso_rightHomology, infer_instance
-/
lemma isIso_homologyι (hg : S.g = 0) [S.HasHomology] :
    IsIso S.homologyι := by
  have := S.isIso_rightHomologyι hg
  dsimp only [homologyι]
  infer_instance

/-- The canonical isomorphism `S.cycles ≅ S.homology` when `S.f = 0`. -/
@[simps! hom]
/--
Definition of `asIsoHomologyπ` / `asIsoHomologyπ` 的定义

English:
definition asIsoHomologyπ
  signature: (hf : S.f = 0) [S.HasHomology]
  body: by
  have := S.isIso_homologyπ hf
  exact asIso S.homologyπ

@[reassoc (attr := simp)]

中文:
定义 asIsoHomologyπ
  签名: (hf : S.f = 0) [S.有同调]
  定义体: by
  have := S.isIso_homologyπ hf
  exact asIso S.homologyπ

@[reassoc (attr := simp)]

Depends on / 依赖: S.homology, S.isIso_homology
-/
noncomputable def asIsoHomologyπ (hf : S.f = 0) [S.HasHomology] :
    S.cycles ≅ S.homology := by
  have := S.isIso_homologyπ hf
  exact asIso S.homologyπ

@[reassoc (attr := simp)]
/--
lemma `asIsoHomologyπ_inv_comp_homologyπ` / 引理 `asIsoHomologyπ_inv_comp_homologyπ`

English:
lemma asIsoHomologyπ_inv_comp_homologyπ
  given: (hf : S.f = 0) [S.HasHomology]
  proof: Iso.inv_hom_id _

@[reassoc (attr := simp)]

中文:
引理 asIsoHomologyπ_inv_comp_homologyπ
  条件: (hf : S.f = 0) [S.有同调]
  证明: Iso.inv_hom_id _

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, inv_hom_id
-/
lemma asIsoHomologyπ_inv_comp_homologyπ (hf : S.f = 0) [S.HasHomology] :
    (S.asIsoHomologyπ hf).inv ≫ S.homologyπ = 𝟙 _ := Iso.inv_hom_id _

@[reassoc (attr := simp)]
/--
lemma `homologyπ_comp_asIsoHomologyπ_inv` / 引理 `homologyπ_comp_asIsoHomologyπ_inv`

English:
lemma homologyπ_comp_asIsoHomologyπ_inv
  given: (hf : S.f = 0) [S.HasHomology]
  proof: (S.asIsoHomologyπ hf).hom_inv_id

中文:
引理 homologyπ_comp_asIsoHomologyπ_inv
  条件: (hf : S.f = 0) [S.有同调]
  证明: (S.asIsoHomologyπ hf).hom_inv_id

Depends on / 依赖: S.asIsoHomology, hom_inv_id
-/
lemma homologyπ_comp_asIsoHomologyπ_inv (hf : S.f = 0) [S.HasHomology] :
    S.homologyπ ≫ (S.asIsoHomologyπ hf).inv = 𝟙 _ := (S.asIsoHomologyπ hf).hom_inv_id

/-- The canonical isomorphism `S.homology ≅ S.opcycles` when `S.g = 0`. -/
@[simps! hom]
/--
Definition of `asIsoHomologyι` / `asIsoHomologyι` 的定义

English:
definition asIsoHomologyι
  signature: (hg : S.g = 0) [S.HasHomology]
  body: by
  have := S.isIso_homologyι hg
  exact asIso S.homologyι

@[reassoc (attr := simp)]

中文:
定义 asIsoHomologyι
  签名: (hg : S.g = 0) [S.有同调]
  定义体: by
  have := S.isIso_homologyι hg
  exact asIso S.homologyι

@[reassoc (attr := simp)]

Depends on / 依赖: S.homology, S.isIso_homology
-/
noncomputable def asIsoHomologyι (hg : S.g = 0) [S.HasHomology] :
    S.homology ≅ S.opcycles := by
  have := S.isIso_homologyι hg
  exact asIso S.homologyι

@[reassoc (attr := simp)]
/--
lemma `asIsoHomologyι_inv_comp_homologyι` / 引理 `asIsoHomologyι_inv_comp_homologyι`

English:
lemma asIsoHomologyι_inv_comp_homologyι
  given: (hg : S.g = 0) [S.HasHomology]
  proof: Iso.inv_hom_id _

@[reassoc (attr := simp)]

中文:
引理 asIsoHomologyι_inv_comp_homologyι
  条件: (hg : S.g = 0) [S.有同调]
  证明: Iso.inv_hom_id _

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, inv_hom_id
-/
lemma asIsoHomologyι_inv_comp_homologyι (hg : S.g = 0) [S.HasHomology] :
    (S.asIsoHomologyι hg).inv ≫ S.homologyι = 𝟙 _ := Iso.inv_hom_id _

@[reassoc (attr := simp)]
/--
lemma `homologyι_comp_asIsoHomologyι_inv` / 引理 `homologyι_comp_asIsoHomologyι_inv`

English:
lemma homologyι_comp_asIsoHomologyι_inv
  given: (hg : S.g = 0) [S.HasHomology]
  proof: (S.asIsoHomologyι hg).hom_inv_id

中文:
引理 homologyι_comp_asIsoHomologyι_inv
  条件: (hg : S.g = 0) [S.有同调]
  证明: (S.asIsoHomologyι hg).hom_inv_id

Depends on / 依赖: S.asIsoHomology, hom_inv_id
-/
lemma homologyι_comp_asIsoHomologyι_inv (hg : S.g = 0) [S.HasHomology] :
    S.homologyι ≫ (S.asIsoHomologyι hg).inv = 𝟙 _ := (S.asIsoHomologyι hg).hom_inv_id

/--
lemma `mono_homologyMap_of_mono_opcyclesMap'` / 引理 `mono_homologyMap_of_mono_opcyclesMap'`

English:
lemma mono_homologyMap_of_mono_opcyclesMap'
  proof: by
  have : Mono (homologyMap φ ≫ S₂.homologyι) := by
    rw [homologyι_naturality φ]
    apply mono_comp
  exact mono_of_mono (homologyMap φ) S₂.homologyι

中文:
引理 mono_homologyMap_of_mono_opcyclesMap'
  证明: by
  have : Mono (homologyMap φ ≫ S₂.homologyι) := by
    rw [homologyι_naturality φ]
    apply mono_comp
  exact mono_of_mono (homologyMap φ) S₂.homologyι

Depends on / 依赖: homologyMap, mono_comp, mono_of_mono, zsmul_lie
-/
lemma mono_homologyMap_of_mono_opcyclesMap'
    [S₁.HasHomology] [S₂.HasHomology] (h : Mono (opcyclesMap φ)) :
    Mono (homologyMap φ) := by
  have : Mono (homologyMap φ ≫ S₂.homologyι) := by
    rw [homologyι_naturality φ]
    apply mono_comp
  exact mono_of_mono (homologyMap φ) S₂.homologyι

/--
Instance `mono_homologyMap_of_mono_opcyclesMap` / 实例 `mono_homologyMap_of_mono_opcyclesMap`

English:
instance mono_homologyMap_of_mono_opcyclesMap
  body: mono_homologyMap_of_mono_opcyclesMap' φ inferInstance

中文:
实例 mono_homologyMap_of_mono_opcyclesMap
  定义体: mono_homologyMap_of_mono_opcyclesMap' φ inferInstance

Depends on / 依赖: mono_homologyMap_of_mono_opcyclesMap
-/
instance mono_homologyMap_of_mono_opcyclesMap
    [S₁.HasHomology] [S₂.HasHomology] [Mono (opcyclesMap φ)] :
    Mono (homologyMap φ) :=
  mono_homologyMap_of_mono_opcyclesMap' φ inferInstance

/--
lemma `epi_homologyMap_of_epi_cyclesMap'` / 引理 `epi_homologyMap_of_epi_cyclesMap'`

English:
lemma epi_homologyMap_of_epi_cyclesMap'
  proof: by
  have : Epi (S₁.homologyπ ≫ homologyMap φ) := by
    rw [homologyπ_naturality φ]
    apply epi_comp
  exact epi_of_epi S₁.homologyπ (homologyMap φ)

中文:
引理 epi_homologyMap_of_epi_cyclesMap'
  证明: by
  have : Epi (S₁.homologyπ ≫ homologyMap φ) := by
    rw [homologyπ_naturality φ]
    apply epi_comp
  exact epi_of_epi S₁.homologyπ (homologyMap φ)

Depends on / 依赖: epi_comp, epi_of_epi, homologyMap
-/
lemma epi_homologyMap_of_epi_cyclesMap'
    [S₁.HasHomology] [S₂.HasHomology] (h : Epi (cyclesMap φ)) :
    Epi (homologyMap φ) := by
  have : Epi (S₁.homologyπ ≫ homologyMap φ) := by
    rw [homologyπ_naturality φ]
    apply epi_comp
  exact epi_of_epi S₁.homologyπ (homologyMap φ)

/--
Instance `epi_homologyMap_of_epi_cyclesMap` / 实例 `epi_homologyMap_of_epi_cyclesMap`

English:
instance epi_homologyMap_of_epi_cyclesMap
  body: epi_homologyMap_of_epi_cyclesMap' φ inferInstance

中文:
实例 epi_homologyMap_of_epi_cyclesMap
  定义体: epi_homologyMap_of_epi_cyclesMap' φ inferInstance

Depends on / 依赖: epi_homologyMap_of_epi_cyclesMap
-/
instance epi_homologyMap_of_epi_cyclesMap
    [S₁.HasHomology] [S₂.HasHomology] [Epi (cyclesMap φ)] :
    Epi (homologyMap φ) :=
  epi_homologyMap_of_epi_cyclesMap' φ inferInstance

/-- Given a short complex `S` such that `S.HasHomology`, this is the canonical
left homology data for `S` whose `K` and `H` fields are
respectively `S.cycles` and `S.homology`. -/
@[simps!]
/--
Definition of `LeftHomologyData.canonical` / `LeftHomologyData.canonical` 的定义

English:
definition LeftHomologyData.canonical
  signature: [S.HasHomology]
  body: S.cycles
  H := S.homology
  i := S.iCycles
  π := S.homologyπ
  wi := by simp
  hi := S.cyclesIsKernel
  wπ := S.toCycles_comp_homologyπ
  hπ := S.homologyIsCokernel

中文:
定义 LeftHomologyData.canonical
  签名: [S.有同调]
  定义体: S.cycles
  H := S.homology
  i := S.iCycles
  π := S.homologyπ
  wi := by simp
  hi := S.cyclesIsKernel
  wπ := S.toCycles_comp_homologyπ
  hπ := S.homologyIsCokernel

Depends on / 依赖: S.cycles, cycles
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
/--
lemma `LeftHomologyData.canonical_f'` / 引理 `LeftHomologyData.canonical_f'`

English:
lemma LeftHomologyData.canonical_f'
  given: [S.HasHomology]
  proof: rfl

中文:
引理 LeftHomologyData.canonical_f'
  条件: [S.有同调]
  证明: rfl
-/
lemma LeftHomologyData.canonical_f' [S.HasHomology] :
    (LeftHomologyData.canonical S).f' = S.toCycles := rfl

/-- Given a short complex `S` such that `S.HasHomology`, this is the canonical
right homology data for `S` whose `Q` and `H` fields are
respectively `S.opcycles` and `S.homology`. -/
@[simps!]
/--
Definition of `RightHomologyData.canonical` / `RightHomologyData.canonical` 的定义

English:
definition RightHomologyData.canonical
  signature: [S.HasHomology]
  body: S.opcycles
  H := S.homology
  p := S.pOpcycles
  ι := S.homologyι
  wp := by simp
  hp := S.opcyclesIsCokernel
  wι := S.homologyι_comp_fromOpcycles
  hι := S.homologyIsKernel

中文:
定义 RightHomologyData.canonical
  签名: [S.有同调]
  定义体: S.opcycles
  H := S.homology
  p := S.pOpcycles
  ι := S.homologyι
  wp := by simp
  hp := S.opcyclesIsCokernel
  wι := S.homologyι_comp_fromOpcycles
  hι := S.homologyIsKernel

Depends on / 依赖: S.opcycles, opcycles
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
/--
lemma `RightHomologyData.canonical_g'` / 引理 `RightHomologyData.canonical_g'`

English:
lemma RightHomologyData.canonical_g'
  given: [S.HasHomology]
  proof: rfl

中文:
引理 RightHomologyData.canonical_g'
  条件: [S.有同调]
  证明: rfl
-/
lemma RightHomologyData.canonical_g' [S.HasHomology] :
    (RightHomologyData.canonical S).g' = S.fromOpcycles := rfl

set_option backward.defeqAttrib.useBackward true in
/-- Given a short complex `S` such that `S.HasHomology`, this is the canonical
homology data for `S` whose `left.K`, `left/right.H` and `right.Q` fields are
respectively `S.cycles`, `S.homology` and `S.opcycles`. -/
@[simps!]
/--
Definition of `HomologyData.canonical` / `HomologyData.canonical` 的定义

English:
definition HomologyData.canonical
  signature: [S.HasHomology]
  body: LeftHomologyData.canonical S
  right := RightHomologyData.canonical S
  iso := Iso.refl _

中文:
定义 同调数据.canonical
  签名: [S.有同调]
  定义体: LeftHomologyData.canonical S
  right := RightHomologyData.canonical S
  iso := Iso.refl _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.canonical, canonical
-/
noncomputable def HomologyData.canonical [S.HasHomology] : S.HomologyData where
  left := LeftHomologyData.canonical S
  right := RightHomologyData.canonical S
  iso := Iso.refl _

end ShortComplex

end CategoryTheory
