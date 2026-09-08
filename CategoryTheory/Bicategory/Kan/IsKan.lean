/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Extension

/-!
# Kan extensions and Kan lifts in bicategories

The left Kan extension of a 1-morphism `g : a ⟶ c` along a 1-morphism `f : a ⟶ b` is the initial
object in the category of left extensions `LeftExtension f g`. The universal property can be
accessed by the following definition and lemmas:
* `LeftExtension.IsKan.desc`: the family of 2-morphisms out of the left Kan extension.
* `LeftExtension.IsKan.fac`: the unit of any left extension factors through the left Kan extension.
* `LeftExtension.IsKan.hom_ext`: two 2-morphisms out of the left Kan extension are equal if their
  compositions with each unit are equal.

We also define left Kan lifts, right Kan extensions, and right Kan lifts.

## Implementation Notes

We use the Is-Has design pattern, which is used for the implementation of limits and colimits in
the category theory library. This means that `IsKan t` is a structure containing the data of
2-morphisms which ensure that `t` is a Kan extension, while `HasLeftKanExtension f g`
(and similarly for lifts) defined in `CategoryTheory.Bicategory.Kan.HasKan`
is a `Prop`-valued typeclass asserting that a Kan extension of `g` along `f` exists.

We define `LeftExtension.IsKan t` for an extension `t : LeftExtension f g` (which is an
abbreviation of `t : StructuredArrow g (precomp _ f)`) to be an abbreviation for
`StructuredArrow.IsUniversal t`. This means that we can use the definitions and lemmas living
in the namespace `StructuredArrow.IsUniversal`.

## References
https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- A left Kan extension of `g` along `f` is an initial object in `LeftExtension f g`. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Bicategory.LeftExtension`。
形式化陈述：IsKan (t : LeftExtension f g)
参数：t : LeftExtension f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left Kan extension of `g` along `f` is an initial object in `LeftExtension f g
`.
-/
abbrev IsKan (t : LeftExtension f g) := t.IsUniversal

/-- An absolute left Kan extension is a Kan extension that commutes with any 1-morphism. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsAbsKan** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：IsAbsKan (t : LeftExtension f g)
参数：t : LeftExtension f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute left Kan extension is a Kan extension that commutes with any 1-morph
ism.
-/
abbrev IsAbsKan (t : LeftExtension f g) :=
  ∀ {x : B} (h : c ⟶ x), IsKan (t.whisker h)

namespace IsKan

variable {s t : LeftExtension f g}

/-- To show that a left extension `t` is a Kan extension, we need to show that for every left
extension `s` there is a unique morphism `t ⟶ s`. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：mk (desc : forall s, t ⟶ s) (w : forall s τ, τ = desc s) : IsKan t
参数：desc : forall s, t ⟶ s；w : forall s τ, τ = desc s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that a left extension `t` is a Kan extension, we need to show that for e
very left
extension `s` there is a unique morphism `t ⟶ s`.
-/
abbrev mk (desc : ∀ s, t ⟶ s) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/-- The family of 2-morphisms out of a left Kan extension. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.desc** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：desc (H : IsKan t) (s : LeftExtension f g) : t.extension ⟶ s.extension
参数：H : IsKan t；s : LeftExtension f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms out of a left Kan extension.
-/
abbrev desc (H : IsKan t) (s : LeftExtension f g) : t.extension ⟶ s.extension :=
  StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.fac** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：fac (H : IsKan t) (s : LeftExtension f g) : t.unit ≫ f ◁ H.desc s = s.unit
参数：H : IsKan t；s : LeftExtension f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.fac`：fac (h : IsUniversal f) 
(g : StructuredArrow S T) : f.hom ≫ T.map (h.desc g) = g.hom
-/
theorem fac (H : IsKan t) (s : LeftExtension f g) :
    t.unit ≫ f ◁ H.desc s = s.unit :=
  StructuredArrow.IsUniversal.fac H s

/-- Two 2-morphisms out of a left Kan extension are equal if their compositions with
each triangle 2-morphism are equal. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.hom_ext** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：hom_ext (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k} (w : t.unit ≫ f
 ◁ τ = t.unit ≫ f ◁ τ') : τ = τ'
参数：H : IsKan t；w : t.unit ≫ f ◁ τ = t.unit ≫ f ◁ τ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.hom_ext`：hom_ext (h : IsUnive
rsal f) {c : C} {η η' : f.right ⟶ c} (w : f.hom ≫ T.map η = f.hom ≫ T.map η') : 
η = η'

--- 原说明 ---
Two 2-morphisms out of a left Kan extension are equal if their compositions with
each triangle 2-morphism are equal.
-/
theorem hom_ext (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k}
    (w : t.unit ≫ f ◁ τ = t.unit ≫ f ◁ τ') : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w

/-- Kan extensions on `g` along `f` are unique up to isomorphism. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.uniqueUpToIso** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t
参数：P : IsKan s；Q : IsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kan extensions on `g` along `f` are unique up to isomorphism.
-/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q

@[simp]
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.uniqueUpToIso_hom_right** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) : (uniqueUpToIso P Q).
hom.right = P.desc t
参数：P : IsKan s；Q : IsKan t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl

@[simp]
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.uniqueUpToIso_inv_right** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) : (uniqueUpToIso P Q).
inv.right = Q.desc s
参数：P : IsKan s；Q : IsKan t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl

/-- Transport evidence that a left extension is a Kan extension across an isomorphism
of extensions. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.ofIsoKan** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t
参数：P : IsKan s；i : s ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport evidence that a left extension is a Kan extension across an isomorphis
m
of extensions.
-/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/-- If `t : LeftExtension f (g ≫ 𝟙 c)` is a Kan extension, then `t.ofCompId : LeftExtension f g`
is also a Kan extension. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.ofCompId** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) (P : IsKan t) : IsKan t.ofCompId
参数：t : LeftExtension f (g ≫ 𝟙 c)；P : IsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t : LeftExtension f (g ≫ 𝟙 c)` is a Kan extension, then `t.ofCompId : LeftEx
tension f g`
is also a Kan extension.
-/
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) (P : IsKan t) : IsKan t.ofCompId :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftExtension.w τ]

/-- If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.whiskerOfCommute** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：whiskerOfCommute (s t : LeftExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
 (P : IsKan (s.whisker h)) : IsKan (t.whisker h)
参数：s t : LeftExtension f g；i : s ≅ t；h : c ⟶ x；P : IsKan (s.whisker h)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`.
-/
def whiskerOfCommute (s t : LeftExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h

end IsKan

namespace IsAbsKan

variable {s t : LeftExtension f g}

/-- The family of 2-morphisms out of an absolute left Kan extension. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsAbsKan.desc** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.Bicategory.LeftExtension.IsAbsKan`。
形式化陈述：desc (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h)) : 
t.extension ≫ h ⟶ s.extension
参数：H : IsAbsKan t；s : LeftExtension f (g ≫ h)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms out of an absolute left Kan extension.
-/
abbrev desc (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h)) :
    t.extension ≫ h ⟶ s.extension :=
  (H h).desc s

/-- An absolute left Kan extension is a left Kan extension. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsAbsKan.isKan** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Bicategory.LeftExtension.IsAbsKan`。
形式化陈述：isKan (H : IsAbsKan t) : IsKan t
参数：H : IsAbsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute left Kan extension is a left Kan extension.
-/
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofCompId _).ofIsoKan <| whiskerOfCompIdIsoSelf t

/-- Transport evidence that a left extension is a Kan extension across an isomorphism
of extensions. -/
/-
**CategoryTheory.Bicategory.LeftExtension.IsAbsKan.ofIsoAbsKan** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Bicategory.LeftExtension.IsAbsKan`。
形式化陈述：ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t
参数：P : IsAbsKan s；i : s ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport evidence that a left extension is a Kan extension across an isomorphis
m
of extensions.
-/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)

end IsAbsKan

end LeftExtension

namespace LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- A left Kan lift of `g` along `f` is an initial object in `LeftLift f g`. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Bicategory.LeftLift`。
形式化陈述：IsKan (t : LeftLift f g)
参数：t : LeftLift f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left Kan lift of `g` along `f` is an initial object in `LeftLift f g`.
-/
abbrev IsKan (t : LeftLift f g) := t.IsUniversal

/-- An absolute left Kan lift is a Kan lift such that every 1-morphism commutes with it. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsAbsKan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Bicategory.LeftLift`。
形式化陈述：IsAbsKan (t : LeftLift f g)
参数：t : LeftLift f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute left Kan lift is a Kan lift such that every 1-morphism commutes with
 it.
-/
abbrev IsAbsKan (t : LeftLift f g) :=
  ∀ {x : B} (h : x ⟶ c), IsKan (t.whisker h)

namespace IsKan

variable {s t : LeftLift f g}

/-- To show that a left lift `t` is a Kan lift, we need to show that for every left lift `s`
there is a unique morphism `t ⟶ s`. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：mk (desc : forall s, t ⟶ s) (w : forall s τ, τ = desc s) : IsKan t
参数：desc : forall s, t ⟶ s；w : forall s τ, τ = desc s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that a left lift `t` is a Kan lift, we need to show that for every left 
lift `s`
there is a unique morphism `t ⟶ s`.
-/
abbrev mk (desc : ∀ s, t ⟶ s) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/-- The family of 2-morphisms out of a left Kan lift. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.desc** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：desc (H : IsKan t) (s : LeftLift f g) : t.lift ⟶ s.lift
参数：H : IsKan t；s : LeftLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms out of a left Kan lift.
-/
abbrev desc (H : IsKan t) (s : LeftLift f g) : t.lift ⟶ s.lift :=
  StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.fac** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：fac (H : IsKan t) (s : LeftLift f g) : t.unit ≫ H.desc s ▷ f = s.unit
参数：H : IsKan t；s : LeftLift f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.fac`：fac (h : IsUniversal f) 
(g : StructuredArrow S T) : f.hom ≫ T.map (h.desc g) = g.hom
-/
theorem fac (H : IsKan t) (s : LeftLift f g) :
    t.unit ≫ H.desc s ▷ f = s.unit :=
  StructuredArrow.IsUniversal.fac H s

/-- Two 2-morphisms out of a left Kan lift are equal if their compositions with
each triangle 2-morphism are equal. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : t.lift ⟶ k} (w : t.unit ≫ τ ▷ f 
= t.unit ≫ τ' ▷ f) : τ = τ'
参数：H : IsKan t；w : t.unit ≫ τ ▷ f = t.unit ≫ τ' ▷ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.hom_ext`：hom_ext (h : IsUnive
rsal f) {c : C} {η η' : f.right ⟶ c} (w : f.hom ≫ T.map η = f.hom ≫ T.map η') : 
η = η'

--- 原说明 ---
Two 2-morphisms out of a left Kan lift are equal if their compositions with
each triangle 2-morphism are equal.
-/
theorem hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : t.lift ⟶ k}
    (w : t.unit ≫ τ ▷ f = t.unit ≫ τ' ▷ f) : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w

/-- Kan lifts on `g` along `f` are unique up to isomorphism. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t
参数：P : IsKan s；Q : IsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kan lifts on `g` along `f` are unique up to isomorphism.
-/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q

@[simp]
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.uniqueUpToIso_hom_right** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) : (uniqueUpToIso P Q).
hom.right = P.desc t
参数：P : IsKan s；Q : IsKan t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl

@[simp]
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.uniqueUpToIso_inv_right** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) : (uniqueUpToIso P Q).
inv.right = Q.desc s
参数：P : IsKan s；Q : IsKan t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl

/-- Transport evidence that a left lift is a Kan lift across an isomorphism of lifts. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.ofIsoKan** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t
参数：P : IsKan s；i : s ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport evidence that a left lift is a Kan lift across an isomorphism of lifts
.
-/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/-- If `t : LeftLift f (𝟙 c ≫ g)` is a Kan lift, then `t.ofIdComp : LeftLift f g` is also
a Kan lift. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.ofIdComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：ofIdComp (t : LeftLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp
参数：t : LeftLift f (𝟙 c ≫ g)；P : IsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t : LeftLift f (𝟙 c ≫ g)` is a Kan lift, then `t.ofIdComp : LeftLift f g` is
 also
a Kan lift.
-/
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftLift.w τ]

/-- If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.whiskerOfCommute** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：whiskerOfCommute (s t : LeftLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c) (P :
 IsKan (s.whisker h)) : IsKan (t.whisker h)
参数：s t : LeftLift f g；i : s ≅ t；h : x ⟶ c；P : IsKan (s.whisker h)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`.
-/
def whiskerOfCommute (s t : LeftLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h

end IsKan

namespace IsAbsKan

variable {s t : LeftLift f g}

/-- The family of 2-morphisms out of an absolute left Kan lift. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsAbsKan.desc** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Bicategory.LeftLift.IsAbsKan`。
形式化陈述：desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g)) : h ≫ t
.lift ⟶ s.lift
参数：H : IsAbsKan t；s : LeftLift f (h ≫ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms out of an absolute left Kan lift.
-/
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g)) :
    h ≫ t.lift ⟶ s.lift :=
  (H h).desc s

/-- An absolute left Kan lift is a left Kan lift. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsAbsKan.isKan** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.LeftLift.IsAbsKan`。
形式化陈述：isKan (H : IsAbsKan t) : IsKan t
参数：H : IsAbsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute left Kan lift is a left Kan lift.
-/
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofIdComp _).ofIsoKan <| whiskerOfIdCompIsoSelf t

/-- Transport evidence that a left lift is a Kan lift across an isomorphism of lifts. -/
/-
**CategoryTheory.Bicategory.LeftLift.IsAbsKan.ofIsoAbsKan** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Bicategory.LeftLift.IsAbsKan`。
形式化陈述：ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t
参数：P : IsAbsKan s；i : s ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport evidence that a left lift is a Kan lift across an isomorphism of lifts
.
-/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)

end IsAbsKan

end LeftLift

namespace RightExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- A right Kan extension of `g` along `f` is a terminal object in `RightExtension f g`. -/
/-
**CategoryTheory.Bicategory.RightExtension.IsKan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Bicategory.RightExtension`。
形式化陈述：IsKan (t : RightExtension f g)
参数：t : RightExtension f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right Kan extension of `g` along `f` is a terminal object in `RightExtension f
 g`.
-/
abbrev IsKan (t : RightExtension f g) := t.IsUniversal

end RightExtension

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- A right Kan lift of `g` along `f` is a terminal object in `RightLift f g`. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Bicategory.RightLift`。
形式化陈述：IsKan (t : RightLift f g)
参数：t : RightLift f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right Kan lift of `g` along `f` is a terminal object in `RightLift f g`.
-/
abbrev IsKan (t : RightLift f g) := t.IsUniversal

/-- An absolute right Kan lift is a Kan lift such that every 1-morphism commutes with it. -/
/-
**CategoryTheory.Bicategory.RightLift.IsAbsKan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Bicategory.RightLift`。
形式化陈述：IsAbsKan (t : RightLift f g)
参数：t : RightLift f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute right Kan lift is a Kan lift such that every 1-morphism commutes wit
h it.
-/
abbrev IsAbsKan (t : RightLift f g) :=
  ∀ {x : B} (h : x ⟶ c), IsKan (t.whisker h)

namespace IsKan

variable {s t : RightLift f g}

/-- To show that a right lift `t` is a Kan lift, we need to show that for every right lift `s`
there is a unique morphism `s ⟶ t`. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：mk (desc : forall s, s ⟶ t) (w : forall s τ, τ = desc s) : IsKan t
参数：desc : forall s, s ⟶ t；w : forall s τ, τ = desc s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that a right lift `t` is a Kan lift, we need to show that for every righ
t lift `s`
there is a unique morphism `s ⟶ t`.
-/
abbrev mk (desc : ∀ s, s ⟶ t) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/-- The family of 2-morphisms into a right Kan lift. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan.desc** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：desc (H : IsKan t) (s : RightLift f g) : s.lift ⟶ t.lift
参数：H : IsKan t；s : RightLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms into a right Kan lift.
-/
abbrev desc (H : IsKan t) (s : RightLift f g) : s.lift ⟶ t.lift :=
  CostructuredArrow.IsUniversal.lift H s

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.RightLift.IsKan.fac** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：fac (H : IsKan t) (s : RightLift f g) : H.desc s ▷ f ≫ t.counit = s.counit
参数：H : IsKan t；s : RightLift f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.IsUniversal.fac`：fac (h : IsUniversal f
) (g : CostructuredArrow S T) : S.map (h.lift g) ≫ f.hom = g.hom
-/
theorem fac (H : IsKan t) (s : RightLift f g) :
    H.desc s ▷ f ≫ t.counit = s.counit :=
  CostructuredArrow.IsUniversal.fac H s

/-- Two 2-morphisms into a right Kan lift are equal if their compositions with
each triangle 2-morphism are equal. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : k ⟶ t.lift} (w : τ ▷ f ≫ t.couni
t = τ' ▷ f ≫ t.counit) : τ = τ'
参数：H : IsKan t；w : τ ▷ f ≫ t.counit = τ' ▷ f ≫ t.counit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.IsUniversal.hom_ext`：hom_ext (h : IsUni
versal f) {c : C} {η η' : c ⟶ f.left} (w : S.map η ≫ f.hom = S.map η' ≫ f.hom) :
 η = η'

--- 原说明 ---
Two 2-morphisms into a right Kan lift are equal if their compositions with
each triangle 2-morphism are equal.
-/
theorem hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : k ⟶ t.lift}
    (w : τ ▷ f ≫ t.counit = τ' ▷ f ≫ t.counit) : τ = τ' :=
  CostructuredArrow.IsUniversal.hom_ext H w

/-- Kan lifts on `g` along `f` are unique up to isomorphism. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t
参数：P : IsKan s；Q : IsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kan lifts on `g` along `f` are unique up to isomorphism.
-/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsTerminal.uniqueUpToIso P Q

@[simp]
/-
**CategoryTheory.Bicategory.RightLift.IsKan.uniqueUpToIso_hom_left** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：uniqueUpToIso_hom_left (P : IsKan s) (Q : IsKan t) : (uniqueUpToIso P Q).h
om.left = Q.desc s
参数：P : IsKan s；Q : IsKan t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueUpToIso_hom_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.left = Q.desc s := rfl

@[simp]
/-
**CategoryTheory.Bicategory.RightLift.IsKan.uniqueUpToIso_inv_left** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：uniqueUpToIso_inv_left (P : IsKan s) (Q : IsKan t) : (uniqueUpToIso P Q).i
nv.left = P.desc t
参数：P : IsKan s；Q : IsKan t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueUpToIso_inv_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.left = P.desc t := rfl

/-- Transport evidence that a right lift is a Kan lift across an isomorphism of lifts. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan.ofIsoKan** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t
参数：P : IsKan s；i : s ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport evidence that a right lift is a Kan lift across an isomorphism of lift
s.
-/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsTerminal.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/-- If `t : RightLift f (𝟙 c ≫ g)` is a Kan lift, then `t.ofIdComp : RightLift f g` is also
a Kan lift. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan.ofIdComp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：ofIdComp (t : RightLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp
参数：t : RightLift f (𝟙 c ≫ g)；P : IsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t : RightLift f (𝟙 c ≫ g)` is a Kan lift, then `t.ofIdComp : RightLift f g` 
is also
a Kan lift.
-/
def ofIdComp (t : RightLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.from (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← RightLift.w τ]

/-- If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`. -/
/-
**CategoryTheory.Bicategory.RightLift.IsKan.whiskerOfCommute** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Bicategory.RightLift.IsKan`。
形式化陈述：whiskerOfCommute (s t : RightLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c) (P 
: IsKan (s.whisker h)) : IsKan (t.whisker h)
参数：s t : RightLift f g；i : s ≅ t；h : x ⟶ c；P : IsKan (s.whisker h)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`.
-/
def whiskerOfCommute (s t : RightLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h

end IsKan

namespace IsAbsKan

variable {s t : RightLift f g}

/-- The family of 2-morphisms into an absolute right Kan lift. -/
/-
**CategoryTheory.Bicategory.RightLift.IsAbsKan.desc** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Bicategory.RightLift.IsAbsKan`。
形式化陈述：desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : RightLift f (h ≫ g)) : s.li
ft ⟶ h ≫ t.lift
参数：H : IsAbsKan t；s : RightLift f (h ≫ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms into an absolute right Kan lift.
-/
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : RightLift f (h ≫ g)) :
    s.lift ⟶ h ≫ t.lift :=
  (H h).desc s

/-- An absolute right Kan lift is a right Kan lift. -/
/-
**CategoryTheory.Bicategory.RightLift.IsAbsKan.isKan** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.RightLift.IsAbsKan`。
形式化陈述：isKan (H : IsAbsKan t) : IsKan t
参数：H : IsAbsKan t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute right Kan lift is a right Kan lift.
-/
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofIdComp _).ofIsoKan <| whiskerOfIdCompIsoSelf t

/-- Transport evidence that a right lift is a Kan lift across an isomorphism of lifts. -/
/-
**CategoryTheory.Bicategory.RightLift.IsAbsKan.ofIsoAbsKan** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Bicategory.RightLift.IsAbsKan`。
形式化陈述：ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t
参数：P : IsAbsKan s；i : s ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport evidence that a right lift is a Kan lift across an isomorphism of lift
s.
-/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)

end IsAbsKan

end RightLift

end Bicategory

end CategoryTheory

