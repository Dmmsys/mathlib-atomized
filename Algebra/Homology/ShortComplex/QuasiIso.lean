/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Quasi-isomorphisms of short complexes

This file introduces the typeclass `QuasiIso φ` for a morphism `φ : S₁ ⟶ S₂`
of short complexes (which have homology): the condition is that the induced
morphism `homologyMap φ` in homology is an isomorphism.

-/

public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

/-- A morphism `φ : S₁ ⟶ S₂` of short complexes that have homology is a quasi-isomorphism if
the induced map `homologyMap φ : S₁.homology ⟶ S₂.homology` is an isomorphism. -/
/-
**CategoryTheory.ShortComplex.QuasiIso** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {S₁ S₂ : CategoryTheory
.ShortComplex C} → [S₁.HasHomology] → [S₂.HasHomology] → (S₁ ⟶ S₂) → Prop
参数：S₁ ⟶ S₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : S₁ ⟶ S₂` of short complexes that have homology is a quasi-isomor
phism if
the induced map `homologyMap φ : S₁.homology ⟶ S₂.homology` is an isomorphism.
-/
class QuasiIso (φ : S₁ ⟶ S₂) : Prop where
  /-- the homology map is an isomorphism -/
  isIso' : IsIso (homologyMap φ)
/-
**CategoryTheory.ShortComplex.QuasiIso.isIso** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ShortComplex.QuasiIso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} [inst_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology] (φ : S₁ ⟶ S₂)   [Category
Theory.ShortComplex.QuasiIso φ], CategoryTheory.IsIso (CategoryTheory.ShortCompl
ex.homologyMap φ)
参数：φ : S₁ ⟶ S₂；CategoryTheory.ShortComplex.homologyMap φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.QuasiIso.isIso'`：∀ {C : Type u_1} {inst : Ca
tegoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C}   {S₁ S₂ : CategoryTheory…
-/
instance QuasiIso.isIso (φ : S₁ ⟶ S₂) [QuasiIso φ] : IsIso (homologyMap φ) := QuasiIso.isIso'
/-
**CategoryTheory.ShortComplex.quasiIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：quasiIso_iff (φ : S₁ ⟶ S₂) : QuasiIso φ ↔ IsIso (homologyMap φ)
参数：φ : S₁ ⟶ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.QuasiIso.isIso`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {S₁ S₂ : CategoryTheory…
-/
lemma quasiIso_iff (φ : S₁ ⟶ S₂) :
    QuasiIso φ ↔ IsIso (homologyMap φ) := by
  constructor
  · intro h
    infer_instance
  · intro h
    exact ⟨h⟩
/-
**CategoryTheory.ShortComplex.quasiIso_of_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：quasiIso_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ] : QuasiIso φ
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance quasiIso_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ] : QuasiIso φ :=
  ⟨(homologyMapIso (asIso φ)).isIso_hom⟩
/-
**CategoryTheory.ShortComplex.quasiIso_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：quasiIso_comp (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] [hφ' : QuasiI
so φ'] : QuasiIso (φ ≫ φ')
参数：φ : S₁ ⟶ S₂；φ' : S₂ ⟶ S₃。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_comp`：homologyMap_comp [HasHomol
ogy S₁] [HasHomology S₂] [HasHomology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : homolo
gyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫…
-/
instance quasiIso_comp (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') := by
  rw [quasiIso_iff] at hφ hφ' ⊢
  rw [homologyMap_comp]
  infer_instance
/-
**CategoryTheory.ShortComplex.quasiIso_of_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：quasiIso_of_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] [hφφ'
 : QuasiIso (φ ≫ φ')] : QuasiIso φ'
参数：φ : S₁ ⟶ S₂；φ' : S₂ ⟶ S₃；φ ≫ φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_comp`：homologyMap_comp [HasHomol
ogy S₁] [HasHomology S₂] [HasHomology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : homolo
gyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫…
-/
lemma quasiIso_of_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ' := by
  rw [quasiIso_iff] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ) (homologyMap φ')
/-
**CategoryTheory.ShortComplex.quasiIso_iff_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] : Qu
asiIso (φ ≫ φ') ↔ QuasiIso φ'
参数：φ : S₁ ⟶ S₂；φ' : S₂ ⟶ S₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_of_comp_left`：quasiIso_of_comp_left
 (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] : Qua
siIso φ'
-/
lemma quasiIso_iff_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' := by
  constructor
  · intro
    exact quasiIso_of_comp_left φ φ'
  · intro
    exact quasiIso_comp φ φ'
/-
**CategoryTheory.ShortComplex.quasiIso_of_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_of_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ'] [h
φφ' : QuasiIso (φ ≫ φ')] : QuasiIso φ
参数：φ : S₁ ⟶ S₂；φ' : S₂ ⟶ S₃；φ ≫ φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_right`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X) [CategoryTheory.I
sIso f]   [CategoryTheory.IsIs…
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_comp`：homologyMap_comp [HasHomol
ogy S₁] [HasHomology S₂] [HasHomology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : homolo
gyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫…
-/
lemma quasiIso_of_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    [hφ' : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ := by
  rw [quasiIso_iff] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ) (homologyMap φ')
/-
**CategoryTheory.ShortComplex.quasiIso_iff_comp_right** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ'] :
 QuasiIso (φ ≫ φ') ↔ QuasiIso φ
参数：φ : S₁ ⟶ S₂；φ' : S₂ ⟶ S₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_of_comp_right`：quasiIso_of_comp_rig
ht (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
 QuasiIso φ
-/
lemma quasiIso_iff_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  constructor
  · intro
    exact quasiIso_of_comp_right φ φ'
  · intro
    exact quasiIso_comp φ φ'

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_of_arrow_mk_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Ar
row.mk φ') [hφ : QuasiIso φ] : QuasiIso φ'
参数：φ : S₁ ⟶ S₂；φ' : S₃ ⟶ S₄；e : Arrow.mk φ ≅ Arrow.mk φ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.w_mk_right_assoc`：∀ {T : Type u} [inst : CategoryTh
eory.Category.{v, u} T] {f : CategoryTheory.Arrow T} {X Y : T} {g : X ⟶ Y}   (sq
 : f ⟶ CategoryTheory.Arrow…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma quasiIso_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
    [hφ : QuasiIso φ] : QuasiIso φ' := by
  let α : S₃ ⟶ S₁ := e.inv.left
  let β : S₂ ⟶ S₄ := e.hom.right
  suffices φ' = α ≫ φ ≫ β by
    rw [this]
    infer_instance
  simp only [α, β, Arrow.w_mk_right_assoc, Arrow.mk_hom,
    ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right, comp_id]
/-
**CategoryTheory.ShortComplex.quasiIso_iff_of_arrow_mk_iso** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ 
≅ Arrow.mk φ') : QuasiIso φ ↔ QuasiIso φ'
参数：φ : S₁ ⟶ S₂；φ' : S₃ ⟶ S₄；e : Arrow.mk φ ≅ Arrow.mk φ'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_of_arrow_mk_iso`：quasiIso_of_arrow_
mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ') [hφ : QuasiIs
o φ] : QuasiIso φ'
-/
lemma quasiIso_iff_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ') :
    QuasiIso φ ↔ QuasiIso φ' :=
  ⟨fun _ => quasiIso_of_arrow_mk_iso φ φ' e, fun _ => quasiIso_of_arrow_mk_iso φ' φ e.symm⟩
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} [inst_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology] {φ : S₁ ⟶ S₂}   {h₁ : S₁.
LeftHomologyData} {h₂ : S₂.LeftHomologyData} (γ : CategoryTheory.ShortComplex.Le
ftHomologyMapData φ h₁ h₂),   CategoryTheory.ShortComplex.QuasiIso φ ↔ CategoryT
heory.IsIso γ.φH
参数：γ : CategoryTheory.ShortComplex.LeftHomologyMapData φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_eq`：homology
Map_eq : homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_right`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X) [CategoryTheory.I
sIso f]   [CategoryTheory.IsIs…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma LeftHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
    {h₂ : S₂.LeftHomologyData} (γ : LeftHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [ShortComplex.quasiIso_iff, γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (LeftHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (LeftHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (LeftHomologyData.homologyIso h₂).inv
  · intro h
    infer_instance
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_iff** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} [inst_2 : S₁.HasHomology] [inst_3 : S₂.HasHomology] {φ : S₁ ⟶ S₂}   {h₁ : S₁.
RightHomologyData} {h₂ : S₂.RightHomologyData}   (γ : CategoryTheory.ShortComple
x.RightHomologyMapData φ h₁ h₂),   CategoryTheory.ShortComplex.QuasiIso φ ↔ Cate
goryTheory.IsIso γ.φH
参数：γ : CategoryTheory.ShortComplex.RightHomologyMapData φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyMapData.homologyMap_eq`：homolog
yMap_eq : homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_right`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X) [CategoryTheory.I
sIso f]   [CategoryTheory.IsIs…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma RightHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (γ : RightHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [ShortComplex.quasiIso_iff, γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (RightHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (RightHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (RightHomologyData.homologyIso h₂).inv
  · intro h
    infer_instance
/-
**CategoryTheory.ShortComplex.quasiIso_iff_isIso_leftHomologyMap'** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_isIso_leftHomologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyDat
a) (h₂ : S₂.LeftHomologyData) : QuasiIso φ ↔ IsIso (leftHomologyMap' φ h₁ h₂)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiIso_iff_isIso_leftHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    QuasiIso φ ↔ IsIso (leftHomologyMap' φ h₁ h₂) := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff, γ.leftHomologyMap'_eq]
/-
**CategoryTheory.ShortComplex.quasiIso_iff_isIso_rightHomologyMap'** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_isIso_rightHomologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyD
ata) (h₂ : S₂.RightHomologyData) : QuasiIso φ ↔ IsIso (rightHomologyMap' φ h₁ h₂
)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_iff`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiIso_iff_isIso_rightHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    QuasiIso φ ↔ IsIso (rightHomologyMap' φ h₁ h₂) := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff, γ.rightHomologyMap'_eq]
/-
**CategoryTheory.ShortComplex.quasiIso_iff_isIso_homologyMap'** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_isIso_homologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ :
 S₂.HomologyData) : QuasiIso φ ↔ IsIso (homologyMap' φ h₁ h₂)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.HomologyData；h₂ : S₂.HomologyData。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff_isIso_leftHomologyMap'`：quasiIs
o_iff_isIso_leftHomologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.L
eftHomologyData) : QuasiIso φ ↔ IsIso (leftHomologyMa…
-/
lemma quasiIso_iff_isIso_homologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    QuasiIso φ ↔ IsIso (homologyMap' φ h₁ h₂) :=
  quasiIso_iff_isIso_leftHomologyMap' _ _ _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.quasiIso_of_epi_of_isIso_of_mono** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mo
no φ.τ₃] : QuasiIso φ
参数：φ : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma quasiIso_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    QuasiIso φ := by
  rw [((LeftHomologyMapData.ofEpiOfIsIsoOfMono φ) S₁.leftHomologyData).quasiIso_iff]
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.quasiIso_opMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：quasiIso_opMap_iff (φ : S₁ ⟶ S₂) : QuasiIso (opMap φ) ↔ QuasiIso φ
参数：φ : S₁ ⟶ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_iff`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.isIso_of_op`：isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.o
p] : IsIso f
-/
lemma quasiIso_opMap_iff (φ : S₁ ⟶ S₂) :
    QuasiIso (opMap φ) ↔ QuasiIso φ := by
  have γ : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  rw [γ.left.quasiIso_iff, γ.op.right.quasiIso_iff]
  dsimp
  constructor
  · intro h
    apply isIso_of_op
  · intro h
    infer_instance
/-
**CategoryTheory.ShortComplex.quasiIso_opMap** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：quasiIso_opMap (φ : S₁ ⟶ S₂) [QuasiIso φ] : QuasiIso (opMap φ)
参数：φ : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_opMap_iff`：quasiIso_opMap_iff (φ : 
S₁ ⟶ S₂) : QuasiIso (opMap φ) ↔ QuasiIso φ
-/
lemma quasiIso_opMap (φ : S₁ ⟶ S₂) [QuasiIso φ] :
    QuasiIso (opMap φ) := by
  rw [quasiIso_opMap_iff]
  infer_instance
/-
**CategoryTheory.ShortComplex.quasiIso_unopMap** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：quasiIso_unopMap {S₁ S₂ : ShortComplex Cᵒᵖ} [S₁.HasHomology] [S₂.HasHomolo
gy] [S₁.unop.HasHomology] [S₂.unop.HasHomology] (φ : S₁ ⟶ S₂) [QuasiIso φ] : Qua
siIso (unopMap φ)
参数：φ : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instHasHomologyOppositeOp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_opMap_iff`：quasiIso_opMap_iff (φ : 
S₁ ⟶ S₂) : QuasiIso (opMap φ) ↔ QuasiIso φ
-/
lemma quasiIso_unopMap {S₁ S₂ : ShortComplex Cᵒᵖ} [S₁.HasHomology] [S₂.HasHomology]
    [S₁.unop.HasHomology] [S₂.unop.HasHomology]
    (φ : S₁ ⟶ S₂) [QuasiIso φ] : QuasiIso (unopMap φ) := by
  rw [← quasiIso_opMap_iff]
  change QuasiIso φ
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_iff_isIso_liftCycles** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_isIso_liftCycles (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g =
 0) (hf₂ : S₂.f = 0) : QuasiIso φ ↔ IsIso (S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, 
hg₁, zero_comp]))
参数：φ : S₁ ⟶ S₂；hf₁ : S₁.f = 0；hg₁ : S₁.g = 0；hf₂ : S₂.f = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.ofZeros_f'`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.ofIsLimitKernelFork_f'`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.quasiIso_iff`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma quasiIso_iff_isIso_liftCycles (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) :
    QuasiIso φ ↔ IsIso (S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])) := by
  let H : LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ _ S₂.cyclesIsKernel) :=
    { φK := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])
      φH := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp]) }
  exact H.quasiIso_iff

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_iff_isIso_descOpcycles** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_isIso_descOpcycles (φ : S₁ ⟶ S₂) (hg₁ : S₁.g = 0) (hf₂ : S₂.f
 = 0) (hg₂ : S₂.g = 0) : QuasiIso φ ↔ IsIso (S₁.descOpcycles φ.τ₂ (by rw [← φ.co
mm₁₂, hf₂, comp_zero]))
参数：φ : S₁ ⟶ S₂；hg₁ : S₁.g = 0；hf₂ : S₂.f = 0；hg₂ : S₂.g = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.f_pOpcycles`：f_pOpcycles : S.f ≫ S.pOpcycles
 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.ShortComplex.p_descOpcycles`：p_descOpcycles : S.pOpcycles
 ≫ S.descOpcycles k hk = k
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.ofZeros_g'`：ofZeros_g' (hf
 : S.f = 0) (hg : S.g = 0) : (ofZeros S hf hg).g' = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.ofIsColimitCokernelCofork_
g'`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.quasiIso_iff`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma quasiIso_iff_isIso_descOpcycles (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    QuasiIso φ ↔ IsIso (S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])) := by
  let H : RightHomologyMapData φ
      (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ _ S₁.opcyclesIsCokernel)
        (RightHomologyData.ofZeros S₂ hf₂ hg₂) :=
    { φQ := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])
      φH := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero]) }
  exact H.quasiIso_iff

end ShortComplex

end CategoryTheory

