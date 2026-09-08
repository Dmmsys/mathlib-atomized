/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Properties of objects on categories equipped with shift

Given a predicate `P : ObjectProperty C` on objects of a category equipped with a shift
by `A`, we define shifted properties of objects `P.shift a` for all `a : A`.
We also introduce a typeclass `P.IsStableUnderShift A` to say that `P X`
implies `P (X⟦a⟧)` for all `a : A`.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type*} [Category* C] (P Q : ObjectProperty C)
  {A : Type*} [AddMonoid A] [HasShift C A]
  {E : Type*} [Category* E] [HasShift E A]

namespace ObjectProperty

/-- Given a predicate `P : C → Prop` on objects of a category equipped with a shift by `A`,
this is the predicate which is satisfied by `X` if `P (X⟦a⟧)`. -/
/-
**CategoryTheory.ObjectProperty.shift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ObjectProperty`。
形式化陈述：shift (a : A) : ObjectProperty C
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `P : C → Prop` on objects of a category equipped with a shift 
by `A`,
this is the predicate which is satisfied by `X` if `P (X⟦a⟧)`.
-/
def shift (a : A) : ObjectProperty C := fun X => P (X⟦a⟧)
/-
**CategoryTheory.ObjectProperty.prop_shift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：prop_shift_iff (a : A) (X : C) : P.shift a X ↔ P (X⟦a⟧)
参数：a : A；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prop_shift_iff (a : A) (X : C) : P.shift a X ↔ P (X⟦a⟧) := Iff.rfl
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : A) [P.IsClosedUnderIsomorphisms] :
    (P.shift a).IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso ((shiftFunctor C a).mapIso e) hX

variable (A)

@[simp]
/-
**CategoryTheory.ObjectProperty.shift_zero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：shift_zero [P.IsClosedUnderIsomorphisms] : P.shift (0 : A) = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
-/
lemma shift_zero [P.IsClosedUnderIsomorphisms] : P.shift (0 : A) = P := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorZero C A).app X)

variable {A}
/-
**CategoryTheory.ObjectProperty.shift_shift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：shift_shift (a b c : A) (h : a + b = c) [P.IsClosedUnderIsomorphisms] : (P
.shift b).shift a = P.shift c
参数：a b c : A；h : a + b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
-/
lemma shift_shift (a b c : A) (h : a + b = c) [P.IsClosedUnderIsomorphisms] :
    (P.shift b).shift a = P.shift c := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorAdd' C a b c h).symm.app X)
/-
**CategoryTheory.ObjectProperty.shift_sup** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ObjectProperty`。
形式化陈述：shift_sup (a : A) : (P ⊔ Q).shift a = P.shift a ⊔ Q.shift a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma shift_sup (a : A) : (P ⊔ Q).shift a = P.shift a ⊔ Q.shift a := by
  ext
  simp [prop_shift_iff]
/-
**CategoryTheory.ObjectProperty.shift_iSup** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：shift_iSup {ι : Sort*} (P : ι -> ObjectProperty C) (a : A) : (⨆ (i : ι), P
 i).shift a = ⨆ (i : ι), (P i).shift a
参数：P : ι -> ObjectProperty C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma shift_iSup {ι : Sort*} (P : ι → ObjectProperty C) (a : A) :
    (⨆ (i : ι), P i).shift a = ⨆ (i : ι), (P i).shift a := by
  ext
  simp [prop_shift_iff]

/-- `P : ObjectProperty C` is stable under the shift by `a : A` if
`P X` implies `P X⟦a⟧`. -/
/-
**CategoryTheory.ObjectProperty.IsStableUnderShiftBy** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C → {A : Type u_2} → [inst_1 : AddMonoid A] → [Catego
ryTheory.HasShift C A] → A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P : ObjectProperty C` is stable under the shift by `a : A` if
`P X` implies `P X⟦a⟧`.
-/
class IsStableUnderShiftBy (a : A) : Prop where
  le_shift : P ≤ P.shift a
/-
**CategoryTheory.ObjectProperty.le_shift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：le_shift (a : A) [P.IsStableUnderShiftBy a] : P <= P.shift a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderShiftBy.le_shift`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheory.ObjectPr
operty C} {A : Type u_2}   {inst_1 : AddMonoid A}…
-/
lemma le_shift (a : A) [P.IsStableUnderShiftBy a] :
    P ≤ P.shift a := IsStableUnderShiftBy.le_shift
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : A) [P.IsStableUnderShiftBy a] [P.Nonempty] : (P.shift a).Nonempty :=
  .mono (P.le_shift a)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : A) : IsStableUnderShiftBy (⊥ : ObjectProperty C) a where
  le_shift _ h := False.elim h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : A) : IsStableUnderShiftBy (⊤ : ObjectProperty C) a where
  le_shift _ _ := by trivial
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : A) [P.IsStableUnderShiftBy a] :
    P.isoClosure.IsStableUnderShiftBy a where
  le_shift := by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦a⟧, P.le_shift a _ hY, ⟨(shiftFunctor C a).mapIso e⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : A) [P.IsStableUnderShiftBy a]
    [Q.IsStableUnderShiftBy a] : (P ⊓ Q).IsStableUnderShiftBy a where
  le_shift _ hX :=
    ⟨P.le_shift a _ hX.1, Q.le_shift a _ hX.2⟩

variable (A) in
/-- `P : ObjectProperty C` is stable under the shift by `A` if
`P X` implies `P X⟦a⟧` for any `a : A`. -/
/-
**CategoryTheory.ObjectProperty.IsStableUnderShift** 是 Mathlib 中的一个类，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：IsStableUnderShift where isStableUnderShiftBy (a : A) : P.IsStableUnderShi
ftBy a
参数：a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P : ObjectProperty C` is stable under the shift by `A` if
`P X` implies `P X⟦a⟧` for any `a : A`.
-/
class IsStableUnderShift where
  isStableUnderShiftBy (a : A) : P.IsStableUnderShiftBy a := by infer_instance

attribute [instance] IsStableUnderShift.isStableUnderShiftBy
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderShift A] :
    P.isoClosure.IsStableUnderShift A where
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderShift A]
    [Q.IsStableUnderShift A] : (P ⊓ Q).IsStableUnderShift A where
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderShift (⊥ : ObjectProperty C) A where
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderShift (⊤ : ObjectProperty C) A where
/-
**CategoryTheory.ObjectProperty.prop_shift_iff_of_isStableUnderShift** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_shift_iff_of_isStableUnderShift {G : Type*} [AddGroup G] [HasShift C 
G] [P.IsStableUnderShift G] [P.IsClosedUnderIsomorphisms] (X : C) (g : G) : P (X
⟦g⟧) ↔ P X
参数：X : C；g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.shift_zero`：shift_zero [P.IsClosedUnderIso
morphisms] : P.shift (0 : A) = P
· 使用引理 `CategoryTheory.ObjectProperty.shift_shift`：shift_shift (a b c : A) (h : 
a + b = c) [P.IsClosedUnderIsomorphisms] : (P.shift b).shift a = P.shift c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ObjectProperty.le_shift`：le_shift (a : A) [P.IsStableUnde
rShiftBy a] : P <= P.shift a
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderShift.isStableUnderShiftBy`：∀
 {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheor
y.ObjectProperty C} {A : Type u_2}   {inst_1 : AddMonoid A}…
-/
lemma prop_shift_iff_of_isStableUnderShift {G : Type*} [AddGroup G] [HasShift C G]
    [P.IsStableUnderShift G] [P.IsClosedUnderIsomorphisms] (X : C) (g : G) :
    P (X⟦g⟧) ↔ P X := by
  refine ⟨fun hX ↦ ?_, P.le_shift g _⟩
  rw [← P.shift_zero G, ← P.shift_shift g (-g) 0 (by simp)]
  exact P.le_shift (-g) _ hX

variable (A) in
/-- The closure by shifts and isomorphism of a predicate on objects in a category. -/
/-
**CategoryTheory.ObjectProperty.shiftClosure** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：shiftClosure : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure by shifts and isomorphism of a predicate on objects in a category.
-/
def shiftClosure : ObjectProperty C := fun X => ∃ (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y
/-
**CategoryTheory.ObjectProperty.prop_shiftClosure_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：prop_shiftClosure_iff (X : C) : shiftClosure P A X ↔ exists (Y : C) (a : A
) (_ : X ≅ Y⟦a⟧), P Y
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prop_shiftClosure_iff (X : C) :
    shiftClosure P A X ↔ ∃ (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y := Iff.rfl
/-
**CategoryTheory.ObjectProperty.le_shiftClosure** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：le_shiftClosure : P <= P.shiftClosure A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_shiftClosure : P ≤ P.shiftClosure A := by
  intro X hX
  exact ⟨X, 0, (shiftFunctorZero C A).symm.app X, hX⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : (P.shiftClosure A).Nonempty :=
  .mono P.le_shiftClosure

variable {P Q} in
/-
**CategoryTheory.ObjectProperty.monotone_shiftClosure** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：monotone_shiftClosure (h : P <= Q) : P.shiftClosure A <= Q.shiftClosure A
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_shiftClosure (h : P ≤ Q) : P.shiftClosure A ≤ Q.shiftClosure A := by
  rintro X ⟨Y, a, i, hY⟩
  refine ⟨Y, a, i, h Y hY⟩
/-
**CategoryTheory.ObjectProperty.shiftClosure_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A
] : P.shiftClosure A = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用引理 `CategoryTheory.ObjectProperty.le_shift`：le_shift (a : A) [P.IsStableUnde
rShiftBy a] : P <= P.shift a
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderShift.isStableUnderShiftBy`：∀
 {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheor
y.ObjectProperty C} {A : Type u_2}   {inst_1 : AddMonoid A}…
· 使用引理 `CategoryTheory.ObjectProperty.le_shiftClosure`：le_shiftClosure : P <= P.
shiftClosure A
-/
lemma shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A] :
    P.shiftClosure A = P := by
  refine le_antisymm ?_ P.le_shiftClosure
  rintro X ⟨Y, a, i, hY⟩
  exact P.prop_of_iso i.symm (P.le_shift a Y hY)

@[simp]
/-
**CategoryTheory.ObjectProperty.shiftClosure_bot** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：shiftClosure_bot : shiftClosure (⊥ : ObjectProperty C) A = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.shiftClosure_eq_self`：shiftClosure_eq_self
 [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A] : P.shiftClosure A = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsBot`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊥.IsClosedUnderIsomorphisms
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderShiftBot`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} [inst_1 : AddMono
id A]   [inst_2 : CategoryTheory.HasShift C A…
-/
lemma shiftClosure_bot : shiftClosure (⊥ : ObjectProperty C) A = ⊥ := shiftClosure_eq_self _

@[simp]
/-
**CategoryTheory.ObjectProperty.shiftClosure_top** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：shiftClosure_top : shiftClosure (⊤ : ObjectProperty C) A = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.shiftClosure_eq_self`：shiftClosure_eq_self
 [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A] : P.shiftClosure A = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsClosedUnderIsomorphisms
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderShiftTop`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u_2} [inst_1 : AddMono
id A]   [inst_2 : CategoryTheory.HasShift C A…
-/
lemma shiftClosure_top : shiftClosure (⊤ : ObjectProperty C) A = ⊤ := shiftClosure_eq_self _
/-
**CategoryTheory.ObjectProperty.shiftClosure_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：shiftClosure_le_iff [IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A]
 : shiftClosure P A <= Q ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_shiftClosure`：le_shiftClosure : P <= P.
shiftClosure A
· 使用引理 `CategoryTheory.ObjectProperty.monotone_shiftClosure`：monotone_shiftClosu
re (h : P <= Q) : P.shiftClosure A <= Q.shiftClosure A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.shiftClosure_eq_self`：shiftClosure_eq_self
 [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A] : P.shiftClosure A = P
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma shiftClosure_le_iff [IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A] :
    shiftClosure P A ≤ Q ↔ P ≤ Q :=
  ⟨(le_shiftClosure P).trans,
    fun h => (monotone_shiftClosure h).trans (by rw [shiftClosure_eq_self])⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.shiftClosure A).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro X Y i ⟨Z, a, i', hZ⟩
    exact ⟨Z, a, i.symm.trans i', hZ⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : A) : (P.shiftClosure A).IsStableUnderShiftBy a where
  le_shift := by
    rintro X ⟨Y, b, i, hY⟩
    exact ⟨Y, b + a, ((shiftFunctor C a).mapIso i).trans <|
      (shiftFunctorAdd C b a).symm.app Y, hY⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.shiftClosure A).IsStableUnderShift A where
/-
**CategoryTheory.ObjectProperty.isStableUnderShift_iff_shiftClosure_eq_self** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isStableUnderShift_iff_shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] 
: IsStableUnderShift P A ↔ shiftClosure P A = P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.shiftClosure_eq_self`：shiftClosure_eq_self
 [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A] : P.shiftClosure A = P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderShiftShiftClosure`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Obj
ectProperty C) {A : Type u_2}   [inst_1 : AddMonoid A]…
-/
lemma isStableUnderShift_iff_shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] :
    IsStableUnderShift P A ↔ shiftClosure P A = P :=
  ⟨fun _ ↦ shiftClosure_eq_self _, fun h ↦ by rw [← h]; infer_instance⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] (G : Type*) [AddGroup G]
    [HasShift C G] : (⨆ (a : G), P.shift a).IsStableUnderShift G where
  isStableUnderShiftBy a := IsStableUnderShiftBy.mk <| by
    rw [shift_iSup]
    intro X hX
    rw [prop_iSup_iff] at hX ⊢
    obtain ⟨b, hb⟩ := hX
    exact ⟨-a + b, by rwa [P.shift_shift _ _ _ (add_neg_cancel_left a b)]⟩
/-
**CategoryTheory.ObjectProperty.shiftClosure_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：shiftClosure_eq_iSup [P.IsClosedUnderIsomorphisms] (G : Type*) [AddGroup G
] [HasShift C G] : P.shiftClosure G = ⨆ (x : G), P.shift x
参数：G : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.shiftClosure_le_iff`：shiftClosure_le_iff [
IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A] : shiftClosure P A <= Q ↔ 
P <= Q
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsISup`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {α : Sort u_1} (P : α → Catego
ryTheory.ObjectProperty C)   [∀ (a : α), (P a).IsClos…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsShift`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Obj
ectProperty C) {A : Type u_2}   [inst_1 : AddMonoid A]…
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderShiftISupShiftOfIsClosedU
nderIsomorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C]
 (P : CategoryTheory.ObjectProperty C)   [P.IsClosedUnderIsomorphisms] (G : Ty…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.shift_zero`：shift_zero [P.IsClosedUnderIso
morphisms] : P.shift (0 : A) = P
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ObjectProperty.prop_iSup_iff`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {α : Sort u_1} (P : α → CategoryTheory.ObjectPrope
rty C)   (X : C), (⨆ a, P a) X ↔ …
-/
lemma shiftClosure_eq_iSup [P.IsClosedUnderIsomorphisms] (G : Type*) [AddGroup G] [HasShift C G] :
    P.shiftClosure G = ⨆ (x : G), P.shift x := by
  apply le_antisymm
  · rw [shiftClosure_le_iff]
    conv_lhs => rw [← P.shift_zero G]
    exact le_iSup P.shift (0 : G)
  · intro X hX
    obtain ⟨a, ha⟩ := (prop_iSup_iff _ _).mp hX
    exact ⟨X⟦a⟧, -a, (shiftShiftNeg X a).symm, ha⟩

variable [P.IsStableUnderShift A]
/-
**CategoryTheory.ObjectProperty.hasShift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：hasShift : HasShift P.FullSubcategory A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance hasShift :
    HasShift P.FullSubcategory A :=
  P.fullyFaithfulι.hasShift (fun n ↦ ObjectProperty.lift _ (P.ι ⋙ shiftFunctor C n)
    (fun X ↦ P.le_shift n _ X.2)) (fun _ => P.liftCompιIso _ _)
/-
**CategoryTheory.ObjectProperty.commShift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commShiftι : P.ι.CommShift A :=
  Functor.CommShift.ofHasShiftOfFullyFaithful _ _ _

-- these definitions are made irreducible to prevent any abuse of defeq
attribute [irreducible] hasShift commShiftι

section

variable (F : E ⥤ C) (hF : ∀ (X : E), P (F.obj X))

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [F.CommShift A] :
    (P.lift F hF).CommShift A :=
  Functor.CommShift.ofComp (P.liftCompιIso F hF) A
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [F.CommShift A] :
    NatTrans.CommShift (P.liftCompιIso F hF).hom A :=
  Functor.CommShift.ofComp_compatibility _ _

end

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] (F : E ⥤ C) [F.CommShift A] :
    (P.inverseImage F).IsStableUnderShift A where
  isStableUnderShiftBy n :=
    { le_shift _ hY := P.prop_of_iso ((F.commShiftIso n).symm.app _) (P.le_shift n _ hY) }

end ObjectProperty

end CategoryTheory

