/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.Preradical.Colon
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Radicals

In this file we define what it means for a preradical `Φ : Preradical C` on an
abelian category `C` to be *radical*, and we define `Radical C` as the full
subcategory of `Preradical C` consisting of radicals.

Following Stenström, a preradical `Φ` is called radical if it coincides with its self colon.
We encode this as the property that the natural transformation `toColon Φ Φ : Φ ⟶ Φ.colon Φ`
is an isomorphism, and we prove a basic characterization of radicals in terms
of the vanishing of `Φ.r` on `Φ.quotient`.


## Main definitions

* `Preradical.IsRadical` :
  The property that a preradical `Φ` is radical, i.e. that `(Φ.colon Φ) ≅ Φ`.

* `Radical C` :
  The type of radicals on `C`, as a full subcategory of `Preradical C`.

## Main results

* `Preradical.isRadical_iff_isZero` :
  A preradical `Φ` is radical if and only if `Φ.quotient ⋙ Φ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

preradical, radical, torsion theory, abelian
-/

@[expose] public section

namespace CategoryTheory.Abelian
open CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace Preradical

variable (C)
/-- A preradical `Φ` is *radical* if `Φ.colon Φ ≅ Φ`. -/
/-
**CategoryTheory.Abelian.Preradical.isRadical** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Abelian.Preradical`。
形式化陈述：isRadical : ObjectProperty (Preradical C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preradical `Φ` is *radical* if `Φ.colon Φ ≅ Φ`.
-/
def isRadical : ObjectProperty (Preradical C) :=
  fun Φ ↦ IsIso (toColon Φ Φ)
/-
**CategoryTheory.Abelian.Preradical.isRadical_iff_isIso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：isRadical_iff_isIso (Φ : Preradical C) : isRadical C Φ ↔ IsIso (toColon Φ 
Φ)
参数：Φ : Preradical C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRadical_iff_isIso (Φ : Preradical C) :
    isRadical C Φ ↔ IsIso (toColon Φ Φ) :=
  Iff.rfl

/-- A preradical `Φ` is radical if and only if it `Φ` vanishes on the quotient `Φ.quotient`. -/
/-
**CategoryTheory.Abelian.Preradical.isRadical_iff_isZero** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：isRadical_iff_isZero (Φ : Preradical C) : isRadical C Φ ↔ IsZero (Φ.quotie
nt ⋙ Φ.r)
参数：Φ : Preradical C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Preradical.isRadical_iff_isIso`：isRadical_iff_isI
so (Φ : Preradical C) : isRadical C Φ ↔ IsIso (toColon Φ Φ)
· 使用定理 `CategoryTheory.Abelian.Preradical.isIso_toColon_iff`：isIso_toColon_iff {
Φ Ψ : Preradical C} : IsIso (toColon Φ Ψ) ↔ IsZero (Φ.quotient ⋙ Ψ.r)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A preradical `Φ` is radical if and only if it `Φ` vanishes on the quotient `Φ.qu
otient`.
-/
lemma isRadical_iff_isZero (Φ : Preradical C) :
    isRadical C Φ ↔ IsZero (Φ.quotient ⋙ Φ.r) := by
  rw [isRadical_iff_isIso, isIso_toColon_iff]

end Preradical

variable (C) in
/-- The category of radicals on `C`, defined as the full subcategory of
`Preradical C` consisting of preradicals `Φ` such that `toColon Φ Φ` is an isomorphism. -/
/-
**CategoryTheory.Abelian.Radical** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abe
lian`。
形式化陈述：Radical
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of radicals on `C`, defined as the full subcategory of
`Preradical C` consisting of preradicals `Φ` such that `toColon Φ Φ` is an isomo
rphism.
-/
abbrev Radical := (Preradical.isRadical C).FullSubcategory

namespace Radical

/-
**CategoryTheory.Abelian.Radical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abel
ian.Radical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Φ : Radical C) : IsIso (Preradical.toColon Φ.obj Φ.obj) := Φ.property
/-
**CategoryTheory.Abelian.Radical.isZero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Abelian.Radical`。
形式化陈述：isZero (Φ : Radical C) : IsZero (Φ.obj.quotient ⋙ Φ.obj.r)
参数：Φ : Radical C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.Preradical.isRadical_iff_isZero`：isRadical_iff_is
Zero (Φ : Preradical C) : isRadical C Φ ↔ IsZero (Φ.quotient ⋙ Φ.r)
· 使用引理 `CategoryTheory.Abelian.Preradical.isRadical_iff_isIso`：isRadical_iff_isI
so (Φ : Preradical C) : isRadical C Φ ↔ IsIso (toColon Φ Φ)
· 使用定理 `CategoryTheory.Abelian.Radical.instIsIsoPreradicalToColonObjIsRadical`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Abelian C]   (Φ : CategoryTheory.Abelian.Radical C),…
-/
lemma isZero (Φ : Radical C) : IsZero (Φ.obj.quotient ⋙ Φ.obj.r) := by
  rw [← Preradical.isRadical_iff_isZero, Preradical.isRadical_iff_isIso]
  infer_instance

end Radical

end CategoryTheory.Abelian

