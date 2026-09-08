/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Factoring through subobjects

The predicate `h : P.Factors f`, for `P : Subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factorThru f : X ⟶ (P : C)` making the obvious diagram commute.

-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

/-- When `f : X ⟶ Y` and `P : MonoOver Y`,
`P.Factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.Factors f`, you can recover the morphism as `P.factorThru f h`.
-/
/-
**CategoryTheory.MonoOver.Factors** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mono
Over`。
形式化陈述：Factors {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) : Prop
参数：P : MonoOver Y；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f : X ⟶ Y` and `P : MonoOver Y`,
`P.Factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.Factors f`, you can recover the morphism as `P.factorThru f h`.
-/
def Factors {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) : Prop :=
  ∃ g : X ⟶ (P : C), g ≫ P.arrow = f
/-
**CategoryTheory.MonoOver.factors_congr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.MonoOver`。
形式化陈述：factors_congr {X : C} {f g : MonoOver X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) :
 f.Factors h ↔ g.Factors h
参数：h : Y ⟶ X；e : f ≅ g。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_congr {X : C} {f g : MonoOver X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) :
    f.Factors h ↔ g.Factors h :=
  ⟨fun ⟨u, hu⟩ => ⟨u ≫ ((MonoOver.forget _).map e.hom).left, by simp [hu]⟩, fun ⟨u, hu⟩ =>
    ⟨u ≫ ((MonoOver.forget _).map e.inv).left, by simp [hu]⟩⟩

/-- `P.factorThru f h` provides a factorisation of `f : X ⟶ Y` through some `P : MonoOver Y`,
given the evidence `h : P.Factors f` that such a factorisation exists. -/
/-
**CategoryTheory.MonoOver.factorThru** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onoOver`。
形式化陈述：factorThru {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ 
(P : C)
参数：P : MonoOver Y；f : X ⟶ Y；h : Factors P f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.factorThru f h` provides a factorisation of `f : X ⟶ Y` through some `P : Mon
oOver Y`,
given the evidence `h : P.Factors f` that such a factorisation exists.
-/
def factorThru {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ (P : C) :=
  Classical.choose h

end MonoOver

namespace Subobject

/-- When `f : X ⟶ Y` and `P : Subobject Y`,
`P.Factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.Factors f`, you can recover the morphism as `P.factorThru f h`.
-/
/-
**CategoryTheory.Subobject.Factors** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：Factors {X Y : C} (P : Subobject Y) (f : X ⟶ Y) : Prop
参数：P : Subobject Y；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f : X ⟶ Y` and `P : Subobject Y`,
`P.Factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.Factors f`, you can recover the morphism as `P.factorThru f h`.
-/
def Factors {X Y : C} (P : Subobject Y) (f : X ⟶ Y) : Prop :=
  Quotient.liftOn' P (fun P => P.Factors f)
    (by
      rintro P Q ⟨h⟩
      apply propext
      constructor
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.hom.hom.left, by rw [Category.assoc, Over.w h.hom.hom, w]⟩
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.inv.hom.left, by rw [Category.assoc, Over.w h.inv.hom, w]⟩)

@[simp]
/-
**CategoryTheory.Subobject.mk_factors_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：mk_factors_iff {X Y Z : C} (f : Y ⟶ X) [Mono f] (g : Z ⟶ X) : (Subobject.m
k f).Factors g ↔ (MonoOver.mk f).Factors g
参数：f : Y ⟶ X；g : Z ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_factors_iff {X Y Z : C} (f : Y ⟶ X) [Mono f] (g : Z ⟶ X) :
    (Subobject.mk f).Factors g ↔ (MonoOver.mk f).Factors g :=
  Iff.rfl
/-
**CategoryTheory.Subobject.mk_factors_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：mk_factors_self (f : X ⟶ Y) [Mono f] : (mk f).Factors f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_factors_self (f : X ⟶ Y) [Mono f] : (mk f).Factors f :=
  ⟨𝟙 _, by simp⟩
/-
**CategoryTheory.Subobject.factors_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：factors_iff {X Y : C} (P : Subobject Y) (f : X ⟶ Y) : P.Factors f ↔ (repre
sentative.obj P).Factors f
参数：P : Subobject Y；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `CategoryTheory.MonoOver.factors_congr`：factors_congr {X : C} {f g : Mono
Over X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) : f.Factors h ↔ g.Factors h
-/
theorem factors_iff {X Y : C} (P : Subobject Y) (f : X ⟶ Y) :
    P.Factors f ↔ (representative.obj P).Factors f :=
  Quot.inductionOn P fun _ => MonoOver.factors_congr _ (representativeIso _).symm
/-
**CategoryTheory.Subobject.factors_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：factors_self {X : C} (P : Subobject X) : P.Factors P.arrow
参数：P : Subobject X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_self {X : C} (P : Subobject X) : P.Factors P.arrow :=
  (factors_iff _ _).mpr ⟨𝟙 (P : C), by simp⟩
/-
**CategoryTheory.Subobject.factors_comp_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：factors_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) : P.Factors (f 
≫ P.arrow)
参数：f : X ⟶ P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
-/
theorem factors_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) : P.Factors (f ≫ P.arrow) :=
  (factors_iff _ _).mpr ⟨f, rfl⟩
/-
**CategoryTheory.Subobject.factors_of_factors_right** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Subobject`。
形式化陈述：factors_of_factors_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y 
⟶ Z} (h : P.Factors g) : P.Factors (f ≫ g)
参数：f : X ⟶ Y；h : P.Factors g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_of_factors_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z}
    (h : P.Factors g) : P.Factors (f ≫ g) := by
  induction P using Quotient.ind'
  obtain ⟨g, rfl⟩ := h
  exact ⟨f ≫ g, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.factors_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：factors_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} : P.Factors 
(0 : X ⟶ Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} : P.Factors (0 : X ⟶ Y) :=
  (factors_iff _ _).mpr ⟨0, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subobject.factors_of_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：factors_of_le {Y Z : C} {P Q : Subobject Y} (f : Z ⟶ Y) (h : P <= Q) : P.F
actors f -> Q.Factors f
参数：f : Z ⟶ Y；h : P <= Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_of_le {Y Z : C} {P Q : Subobject Y} (f : Z ⟶ Y) (h : P ≤ Q) :
    P.Factors f → Q.Factors f := by
  simp only [factors_iff]
  exact fun ⟨u, hu⟩ => ⟨u ≫ ofLE _ _ h, by simp [← hu]⟩

/-- `P.factorThru f h` provides a factorisation of `f : X ⟶ Y` through some `P : Subobject Y`,
given the evidence `h : P.Factors f` that such a factorisation exists. -/
/-
**CategoryTheory.Subobject.factorThru** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：factorThru {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶
 P
参数：P : Subobject Y；f : X ⟶ Y；h : Factors P f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.factorThru f h` provides a factorisation of `f : X ⟶ Y` through some `P : Sub
object Y`,
given the evidence `h : P.Factors f` that such a factorisation exists.
-/
def factorThru {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ P :=
  Classical.choose ((factors_iff _ _).mp h)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.factorThru_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：factorThru_arrow {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f)
 : P.factorThru f h ≫ P.arrow = f
参数：P : Subobject Y；f : X ⟶ Y；h : Factors P f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
-/
theorem factorThru_arrow {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f) :
    P.factorThru f h ≫ P.arrow = f :=
  Classical.choose_spec ((factors_iff _ _).mp h)

@[simp]
/-
**CategoryTheory.Subobject.factorThru_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：factorThru_self {X : C} (P : Subobject X) (h) : P.factorThru P.arrow h = 𝟙
 (P : C)
参数：P : Subobject X；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_self {X : C} (P : Subobject X) (h) : P.factorThru P.arrow h = 𝟙 (P : C) := by
  ext
  simp

@[simp]
/-
**CategoryTheory.Subobject.factorThru_mk_self** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：factorThru_mk_self (f : X ⟶ Y) [Mono f] : (mk f).factorThru f (mk_factors_
self f) = (underlyingIso f).inv
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Subobject.mk_factors_self`：mk_factors_self (f : X ⟶ Y) [M
ono f] : (mk f).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_mk_self (f : X ⟶ Y) [Mono f] :
    (mk f).factorThru f (mk_factors_self f) = (underlyingIso f).inv := by
  ext
  simp

@[simp]
/-
**CategoryTheory.Subobject.factorThru_comp_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subobject`。
形式化陈述：factorThru_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) (h) : P.fact
orThru (f ≫ P.arrow) h = f
参数：f : X ⟶ P；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) (h) :
    P.factorThru (f ≫ P.arrow) h = f := by
  ext
  simp

@[simp]
/-
**CategoryTheory.Subobject.factorThru_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：factorThru_eq_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} {f : X
 ⟶ Y} {h : Factors P f} : P.factorThru f h = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem factorThru_eq_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} {f : X ⟶ Y}
    {h : Factors P f} : P.factorThru f h = 0 ↔ f = 0 := by
  fconstructor
  · intro w
    replace w := w =≫ P.arrow
    simpa using w
  · rintro rfl
    ext
    simp
/-
**CategoryTheory.Subobject.factorThru_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：factorThru_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h 
: P.Factors g) : f ≫ P.factorThru g h = P.factorThru (f ≫ g) (factors_of_factors
_right f h)
参数：f : X ⟶ Y；g : Y ⟶ Z；h : P.Factors g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Subobject.factors_of_factors_right`：factors_of_factors_ri
ght {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z} (h : P.Factors g) : P.
Factors (f ≫ g)
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.Factors g) :
    f ≫ P.factorThru g h = P.factorThru (f ≫ g) (factors_of_factors_right f h) := by
  apply (cancel_mono P.arrow).mp
  simp

@[simp]
/-
**CategoryTheory.Subobject.factorThru_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：factorThru_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} (h : P.Fa
ctors (0 : X ⟶ Y)) : P.factorThru 0 h = 0
参数：h : P.Factors (0 : X ⟶ Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y}
    (h : P.Factors (0 : X ⟶ Y)) : P.factorThru 0 h = 0 := by simp

-- `h` is an explicit argument here so we can use
-- `rw factorThru_ofLE h`, obtaining a subgoal `P.Factors f`.
-- (While the reverse direction looks plausible as a simp lemma, it seems to be unproductive.)
/-
**CategoryTheory.Subobject.factorThru_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：factorThru_ofLE {Y Z : C} {P Q : Subobject Y} {f : Z ⟶ Y} (h : P <= Q) (w 
: P.Factors f) : Q.factorThru f (factors_of_le f h w) = P.factorThru f w ≫ ofLE 
P Q h
参数：h : P <= Q；w : P.Factors f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Subobject.factors_of_le`：factors_of_le {Y Z : C} {P Q : S
ubobject Y} (f : Z ⟶ Y) (h : P <= Q) : P.Factors f -> Q.Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_ofLE {Y Z : C} {P Q : Subobject Y} {f : Z ⟶ Y} (h : P ≤ Q) (w : P.Factors f) :
    Q.factorThru f (factors_of_le f h w) = P.factorThru f w ≫ ofLE P Q h := by
  ext
  simp
/-
**CategoryTheory.Subobject.le_of_factors** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：le_of_factors {P Q : Subobject Y} (h : Q.Factors P.arrow) : P <= Q
参数：h : Q.Factors P.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
-/
theorem le_of_factors {P Q : Subobject Y} (h : Q.Factors P.arrow) : P ≤ Q :=
  le_of_comm (Q.factorThru P.arrow h) (Q.factorThru_arrow P.arrow h)

/--
Given two subobjects `P Q : Subobject Y`, if `P` factors through `Q`, then there is a morphism of
subobjects from `P` to `Q`.
-/
/-
**CategoryTheory.Subobject.homOfFactors** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：homOfFactors {P Q : Subobject Y} (h : Q.Factors P.arrow) : P ⟶ Q
参数：h : Q.Factors P.arrow。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_factors`：le_of_factors {P Q : Subobject Y
} (h : Q.Factors P.arrow) : P <= Q

--- 原说明 ---
Given two subobjects `P Q : Subobject Y`, if `P` factors through `Q`, then there
 is a morphism of
subobjects from `P` to `Q`.
-/
def homOfFactors {P Q : Subobject Y} (h : Q.Factors P.arrow) : P ⟶ Q :=
  homOfLE <| le_of_factors h

section Preadditive

variable [Preadditive C]

/-
**CategoryTheory.Subobject.factors_add** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (wf : P.Factors f) (
wg : P.Factors g) : P.Factors (f + g)
参数：f g : X ⟶ Y；wf : P.Factors f；wg : P.Factors g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (wf : P.Factors f)
    (wg : P.Factors g) : P.Factors (f + g) :=
  (factors_iff _ _).mpr ⟨P.factorThru f wf + P.factorThru g wg, by simp⟩

-- This can't be a `simp` lemma as `wf` and `wg` may not exist.
-- However you can `rw` by it to assert that `f` and `g` factor through `P` separately.
/-
**CategoryTheory.Subobject.factorThru_add** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：factorThru_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f
 + g)) (wf : P.Factors f) (wg : P.Factors g) : P.factorThru (f + g) w = P.factor
Thru f wf + P.factorThru g wg
参数：f g : X ⟶ Y；w : P.Factors (f + g)；wf : P.Factors f；wg : P.Factors g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
    (wf : P.Factors f) (wg : P.Factors g) :
    P.factorThru (f + g) w = P.factorThru f wf + P.factorThru g wg := by
  ext
  simp
/-
**CategoryTheory.Subobject.factors_left_of_factors_add** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Subobject`。
形式化陈述：factors_left_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w :
 P.Factors (f + g)) (wg : P.Factors g) : P.Factors f
参数：f g : X ⟶ Y；w : P.Factors (f + g)；wg : P.Factors g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_left_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wg : P.Factors g) : P.Factors f :=
  (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru g wg, by simp⟩

@[simp]
/-
**CategoryTheory.Subobject.factorThru_add_sub_factorThru_right** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Subobject`。
形式化陈述：factorThru_add_sub_factorThru_right {X Y : C} {P : Subobject Y} (f g : X ⟶
 Y) (w : P.Factors (f + g)) (wg : P.Factors g) : P.factorThru (f + g) w - P.fact
orThru g wg = P.factorThru f (factors_left_of_factors_add f g w wg)
参数：f g : X ⟶ Y；w : P.Factors (f + g)；wg : P.Factors g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Subobject.factors_left_of_factors_add`：factors_left_of_fa
ctors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g)) (wg 
: P.Factors g) : P.Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_add_sub_factorThru_right {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wg : P.Factors g) :
    P.factorThru (f + g) w - P.factorThru g wg =
      P.factorThru f (factors_left_of_factors_add f g w wg) := by
  ext
  simp
/-
**CategoryTheory.Subobject.factors_right_of_factors_add** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Subobject`。
形式化陈述：factors_right_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w 
: P.Factors (f + g)) (wf : P.Factors f) : P.Factors g
参数：f g : X ⟶ Y；w : P.Factors (f + g)；wf : P.Factors f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_right_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wf : P.Factors f) : P.Factors g :=
  (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru f wf, by simp⟩

@[simp]
/-
**CategoryTheory.Subobject.factorThru_add_sub_factorThru_left** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Subobject`。
形式化陈述：factorThru_add_sub_factorThru_left {X Y : C} {P : Subobject Y} (f g : X ⟶ 
Y) (w : P.Factors (f + g)) (wf : P.Factors f) : P.factorThru (f + g) w - P.facto
rThru f wf = P.factorThru g (factors_right_of_factors_add f g w wf)
参数：f g : X ⟶ Y；w : P.Factors (f + g)；wf : P.Factors f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Subobject.factors_right_of_factors_add`：factors_right_of_
factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g)) (w
f : P.Factors f) : P.Factors g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThru_add_sub_factorThru_left {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wf : P.Factors f) :
    P.factorThru (f + g) w - P.factorThru f wf =
      P.factorThru g (factors_right_of_factors_add f g w wf) := by
  ext
  simp

end Preadditive

end Subobject

end CategoryTheory

