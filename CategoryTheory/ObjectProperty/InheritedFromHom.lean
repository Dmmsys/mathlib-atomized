/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Object properties transported along morphisms

In this file we define the predicates `InheritedFromSource` and `InheritedFromTarget`
for an object property `P` along a morphism property `Q`.
`P` is inherited from the source (resp. target) along `Q` if for every morphism
`f : X ⟶ Y` with `Q f`, `P X` implies `P Y` (resp. `P Y` implies `P X`).
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace ObjectProperty

variable (P P' : ObjectProperty C) (Q Q' : MorphismProperty C)

/-- A property of objects `P` is inherited from the source of morphisms satisfying `Q` if
whenever `P` holds for `X` and `f : X ⟶ Y` is a `Q`-morphism, then `P` holds for `Y`. -/
/-
**CategoryTheory.ObjectProperty.InheritedFromSource** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects `P` is inherited from the source of morphisms satisfying `
Q` if
whenever `P` holds for `X` and `f : X ⟶ Y` is a `Q`-morphism, then `P` holds for
 `Y`.
-/
class InheritedFromSource (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_source {X Y : C} (f : X ⟶ Y) (hf : Q f) : P X → P Y

/-- A property of objects `P` is inherited from the target of morphisms satisfying `Q` if
whenever `P` holds for `Y` and `f : X ⟶ Y` is a `Q`-morphism, then `P` holds for `X`. -/
/-
**CategoryTheory.ObjectProperty.InheritedFromTarget** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects `P` is inherited from the target of morphisms satisfying `
Q` if
whenever `P` holds for `Y` and `f : X ⟶ Y` is a `Q`-morphism, then `P` holds for
 `X`.
-/
class InheritedFromTarget (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_target {X Y : C} (f : X ⟶ Y) (hf : Q f) : P Y → P X

export InheritedFromSource (of_hom_of_source)
export InheritedFromTarget (of_hom_of_target)

namespace InheritedFromSource

/-
**CategoryTheory.ObjectProperty.InheritedFromSource.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ObjectProperty.InheritedFromSource`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] :
    P.InheritedFromSource (MorphismProperty.isomorphisms C) where
  of_hom_of_source f (_ : IsIso f) h := P.prop_of_iso (asIso f) h
/-
**CategoryTheory.ObjectProperty.InheritedFromSource.op** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ObjectProperty.InheritedFromSource`。
形式化陈述：op [P.InheritedFromSource Q] : P.op.InheritedFromTarget Q.op where of_hom_
of_target f hf h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.InheritedFromSource.of_hom_of_source`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheory.O
bjectProperty C}   {Q : CategoryTheory.MorphismProperty …
-/
instance op [P.InheritedFromSource Q] : P.op.InheritedFromTarget Q.op where
  of_hom_of_target f hf h := P.of_hom_of_source f.unop hf h
/-
**CategoryTheory.ObjectProperty.InheritedFromSource.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ObjectProperty.InheritedFromSource`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.InheritedFromSource Q] [P'.InheritedFromSource Q] :
    (P ⊓ P').InheritedFromSource Q where
  of_hom_of_source f hf h := ⟨P.of_hom_of_source f hf h.1, P'.of_hom_of_source f hf h.2⟩
/-
**CategoryTheory.ObjectProperty.InheritedFromSource.of_le** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty.InheritedFromSource`。
形式化陈述：of_le (hQ : Q <= Q') [P.InheritedFromSource Q'] : P.InheritedFromSource Q 
where of_hom_of_source f hf h
参数：hQ : Q <= Q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.InheritedFromSource.of_hom_of_source`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheory.O
bjectProperty C}   {Q : CategoryTheory.MorphismProperty …
-/
lemma of_le (hQ : Q ≤ Q') [P.InheritedFromSource Q'] : P.InheritedFromSource Q where
  of_hom_of_source f hf h := P.of_hom_of_source f (hQ _ hf) h

end InheritedFromSource

namespace InheritedFromTarget

/-
**CategoryTheory.ObjectProperty.InheritedFromTarget.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ObjectProperty.InheritedFromTarget`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] :
    P.InheritedFromTarget (MorphismProperty.isomorphisms C) where
  of_hom_of_target f (_ : IsIso f) h := P.prop_of_iso (asIso f).symm h
/-
**CategoryTheory.ObjectProperty.InheritedFromTarget.op** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ObjectProperty.InheritedFromTarget`。
形式化陈述：op [P.InheritedFromTarget Q] : P.op.InheritedFromSource Q.op where of_hom_
of_source f hf h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.InheritedFromTarget.of_hom_of_target`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheory.O
bjectProperty C}   {Q : CategoryTheory.MorphismProperty …
-/
instance op [P.InheritedFromTarget Q] : P.op.InheritedFromSource Q.op where
  of_hom_of_source f hf h := P.of_hom_of_target f.unop hf h
/-
**CategoryTheory.ObjectProperty.InheritedFromTarget.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ObjectProperty.InheritedFromTarget`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.InheritedFromTarget Q] [P'.InheritedFromTarget Q] :
    (P ⊓ P').InheritedFromTarget Q where
  of_hom_of_target f hf h := ⟨P.of_hom_of_target f hf h.1, P'.of_hom_of_target f hf h.2⟩
/-
**CategoryTheory.ObjectProperty.InheritedFromTarget.of_le** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty.InheritedFromTarget`。
形式化陈述：of_le (hQ : Q <= Q') [P.InheritedFromTarget Q'] : P.InheritedFromTarget Q 
where of_hom_of_target f hf h
参数：hQ : Q <= Q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.InheritedFromTarget.of_hom_of_target`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheory.O
bjectProperty C}   {Q : CategoryTheory.MorphismProperty …
-/
lemma of_le (hQ : Q ≤ Q') [P.InheritedFromTarget Q'] : P.InheritedFromTarget Q where
  of_hom_of_target f hf h := P.of_hom_of_target f (hQ _ hf) h

end InheritedFromTarget

/-
**CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms.of_inheritedFromSource
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphi
sms`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.ObjectProperty C)   (Q : CategoryTheory.MorphismProperty C) [P.Inherite
dFromSource Q] [Q.RespectsIso] [Q.ContainsIdentities],   P.IsClosedUnderIsomorph
isms
参数：P : CategoryTheory.ObjectProperty C；Q : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.InheritedFromSource.of_hom_of_source`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheory.O
bjectProperty C}   {Q : CategoryTheory.MorphismProperty …
· 使用引理 `CategoryTheory.MorphismProperty.of_isIso`：of_isIso (P : MorphismProperty
 C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y) [IsIso f] : P f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma IsClosedUnderIsomorphisms.of_inheritedFromSource [P.InheritedFromSource Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_source e.hom (Q.of_isIso e.hom) h
/-
**CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms.of_inheritedFromTarget
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphi
sms`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.ObjectProperty C)   (Q : CategoryTheory.MorphismProperty C) [P.Inherite
dFromTarget Q] [Q.RespectsIso] [Q.ContainsIdentities],   P.IsClosedUnderIsomorph
isms
参数：P : CategoryTheory.ObjectProperty C；Q : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.InheritedFromTarget.of_hom_of_target`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheory.O
bjectProperty C}   {Q : CategoryTheory.MorphismProperty …
· 使用引理 `CategoryTheory.MorphismProperty.of_isIso`：of_isIso (P : MorphismProperty
 C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y) [IsIso f] : P f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma IsClosedUnderIsomorphisms.of_inheritedFromTarget [P.InheritedFromTarget Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_target e.inv (Q.of_isIso e.inv) h

end ObjectProperty

end CategoryTheory

