/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Dominant rational maps

This file defines `RationalMap.IsDominant` and establishes its connection to
`IsDominant` on the underlying partial maps.

## Main definition

- `Scheme.RationalMap.IsDominant`: a rational map is dominant if some (equivalently, any)
  representative partial map has dominant underlying morphism.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme

namespace PartialMap

set_option backward.defeqAttrib.useBackward true in
/-- Restricting a dominant partial map to a dense open yields a dominant partial map. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.isDominant_restrict_hom** 是 Mathlib 中的一个实例
，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：isDominant_restrict_hom (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Ope
ns) (hU : Dense (U : Set X)) (hU' : U <= f.domain) : IsDominant (f.restrict U hU
 hU').hom
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Opens.isDominant_homOfLE`：∀ {X : AlgebraicGeometry.Sch
eme} {U V : X.Opens},   Dense ↑U → ∀ (hU' : U ≤ V), AlgebraicGeometry.IsDominant
 (X.homOfLE hU')
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsDominant.comp_iff`：∀ {X Y Z : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsDominant f],   AlgebraicGeometr
y.IsDominant (CategoryTheor…

--- 原说明 ---
Restricting a dominant partial map to a dense open yields a dominant partial map
.
-/
instance isDominant_restrict_hom (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) : IsDominant (f.restrict U hU hU').hom := by
  dsimp only [restrict_domain, restrict_hom]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU hU'
  rwa [IsDominant.comp_iff]

/-- If a restriction of `f` is dominant, then `f` is dominant. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.isDominant_hom_of_isDominant_restrict_hom*
* 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：isDominant_hom_of_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Open
s) (hU : Dense (U : Set X)) (hU' : U <= f.domain) [H : IsDominant (f.restrict U 
hU hU').hom] : IsDominant f.hom
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain；f.r
estrict U hU hU'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsDominant.of_comp`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) (g : Y ⟶ Z)   [H : AlgebraicGeometry.IsDominant (CategoryTheory.C
ategoryStruct.comp f g)], …

--- 原说明 ---
If a restriction of `f` is dominant, then `f` is dominant.
-/
lemma isDominant_hom_of_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) [H : IsDominant (f.restrict U hU hU').hom] :
    IsDominant f.hom :=
  IsDominant.of_comp (X.homOfLE hU') f.hom (H := H)

/-- `f.hom` is dominant iff any restriction of `f` is. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.isDominant_hom_iff_isDominant_restrict_hom
** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：isDominant_hom_iff_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Ope
ns) (hU : Dense (U : Set X)) (hU' : U <= f.domain) : IsDominant f.hom ↔ IsDomina
nt (f.restrict U hU hU').hom
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.isDominant_hom_of_isDominant_restric
t_hom`：isDominant_hom_of_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Ope
ns) (hU : Dense (U : Set X)) (hU' : U <= f.domain) [H : IsDominant …

--- 原说明 ---
`f.hom` is dominant iff any restriction of `f` is.
-/
lemma isDominant_hom_iff_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    IsDominant f.hom ↔ IsDominant (f.restrict U hU hU').hom :=
  ⟨fun _ ↦ f.isDominant_restrict_hom U hU hU',
    fun _ ↦ f.isDominant_hom_of_isDominant_restrict_hom U hU hU'⟩

set_option backward.defeqAttrib.useBackward true in
/-- Dominance of the underlying morphism is invariant under equivalence of partial maps. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.isDominant_hom_iff_of_equiv** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：isDominant_hom_iff_of_equiv (f g : X.PartialMap Y) (h : f.equiv g) : IsDom
inant f.hom ↔ IsDominant g.hom
参数：f g : X.PartialMap Y；h : f.equiv g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.isDominant_hom_iff_isDominant_restri
ct_hom`：isDominant_hom_iff_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.O
pens) (hU : Dense (U : Set X)) (hU' : U <= f.domain) : IsDominant f.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Dominance of the underlying morphism is invariant under equivalence of partial m
aps.
-/
lemma isDominant_hom_iff_of_equiv (f g : X.PartialMap Y) (h : f.equiv g) :
    IsDominant f.hom ↔ IsDominant g.hom := by
  obtain ⟨W, hW, hWl, hWr, h⟩ := h
  have e₁ := isDominant_hom_iff_isDominant_restrict_hom f W hW hWl
  have e₂ := isDominant_hom_iff_isDominant_restrict_hom g W hW hWr
  dsimp only [restrict_domain, restrict_hom] at ⊢ e₁ e₂ h
  rw [e₁, h, ← e₂]

end PartialMap

/-- A rational map is dominant if some (equivalently, any) representative partial map has
dominant underlying morphism. -/
@[mk_iff, stacks 0A1Z]
/-
**AlgebraicGeometry.Scheme.RationalMap.IsDominant** 是 Mathlib 中的一个归纳类型，位于命名空间 `A
lgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.RationalMap Y → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rational map is dominant if some (equivalently, any) representative partial ma
p has
dominant underlying morphism.
-/
protected class RationalMap.IsDominant (f : X ⤏ Y) : Prop where
  out : Quotient.liftOn f (fun g ↦ IsDominant g.hom) <| fun _ _ h ↦
    propext (PartialMap.isDominant_hom_iff_of_equiv _ _ h)

@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.isDominant_toRationalMap_iff** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y), f.toRationalMap.I
sDominant ↔ AlgebraicGeometry.IsDominant f.hom
参数：f : X.PartialMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.isDominant_iff`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X.RationalMap Y),   f.IsDominant ↔ Quotient.liftOn f (fun g
 => AlgebraicGeometry.IsDominant g.hom) ⋯
-/
lemma PartialMap.isDominant_toRationalMap_iff (f : X.PartialMap Y) :
    f.toRationalMap.IsDominant ↔ IsDominant f.hom :=
  f.toRationalMap.isDominant_iff
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X.PartialMap Y) [IsDominant f.hom] :
    f.toRationalMap.IsDominant := by
  rwa [f.isDominant_toRationalMap_iff]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⤏ Y) [f.IsDominant] :
    IsDominant f.representative.hom := by
  rwa [← f.representative.isDominant_toRationalMap_iff, f.toRationalMap_representative]

end Scheme

end AlgebraicGeometry

