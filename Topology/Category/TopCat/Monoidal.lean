/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.UnitInterval
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The cartesian monoidal structure on `TopCat`

We define the cartesian monoidal category structure on `TopCat`.
We also introduce the unit interval as an object `TopCat.I` of `TopCat`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace TopCat

/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CartesianMonoidalCategory TopCat.{u} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y ↦ ⟨prodBinaryFan X Y, X.prodBinaryFanIsLimit Y⟩)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory TopCat.{u} := .ofCartesianMonoidalCategory

@[simp]
/-
**TopCat.tensor_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：tensor_apply {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : ↑(W otime
s Y)) : (f otimesₘ g).hom p = (f p.1, g p.2)
参数：f : W ⟶ X；g : Y ⟶ Z；p : ↑(W otimes Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensor_apply {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : ↑(W ⊗ Y)) :
    (f ⊗ₘ g).hom p = (f p.1, g p.2) :=
  rfl

@[simp]
/-
**TopCat.whiskerLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：whiskerLeft_apply (X : TopCat.{u}) {Y Z : TopCat.{u}} (f : Y ⟶ Z) (p : ↑(X
 otimes Y)) : (X ◁ f) p = (p.1, f p.2)
参数：X : TopCat.{u}；f : Y ⟶ Z；p : ↑(X otimes Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_apply (X : TopCat.{u}) {Y Z : TopCat.{u}} (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) :
    (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
/-
**TopCat.whiskerRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：whiskerRight_apply {Y Z : TopCat.{u}} (f : Y ⟶ Z) (X : TopCat.{u}) (p : ↑(
Y otimes X)) : (f ▷ X) p = (f p.1, p.2)
参数：f : Y ⟶ Z；X : TopCat.{u}；p : ↑(Y otimes X)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight_apply {Y Z : TopCat.{u}} (f : Y ⟶ Z) (X : TopCat.{u}) (p : ↑(Y ⊗ X)) :
    (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
/-
**TopCat.leftUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：leftUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} : (fun_ 
X).hom (p, x) = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (λ_ X).hom (p, x) = x :=
  rfl

@[simp]
/-
**TopCat.leftUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：leftUnitor_inv_apply {X : TopCat.{u}} {x : X} : (fun_ X).inv x = (PUnit.un
it, x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (λ_ X).inv x = (PUnit.unit, x) :=
  rfl

@[simp]
/-
**TopCat.rightUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：rightUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} : (ρ_ X
).hom (x, p) = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (ρ_ X).hom (x, p) = x :=
  rfl

@[simp]
/-
**TopCat.rightUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：rightUnitor_inv_apply {X : TopCat.{u}} {x : X} : (ρ_ X).inv x = (x, .unit)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (ρ_ X).inv x = (x, .unit) :=
  rfl

@[simp]
/-
**TopCat.associator_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：associator_hom_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} : (α_ X 
Y Z).hom ((x, y), z) = (x, (y, z))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) :=
  rfl

@[simp]
/-
**TopCat.associator_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：associator_inv_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} : (α_ X 
Y Z).inv (x, (y, z)) = ((x, y), z)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_inv_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) :=
  rfl
/-
**TopCat.associator_hom_apply_1** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat}   {x : ↑(CategoryTheory.MonoidalCategoryStruct.tensorOb
j (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z)},   ((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).ho
m) x).1 = x.1.1
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryTheory.MonoidalCateg
oryStruct.tensorObj X Y) Z；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.
MonoidalCategoryStruct.associator X Y Z).hom) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_hom_apply_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).1 = x.1.1 :=
  rfl
/-
**TopCat.associator_hom_apply_2_1** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat}   {x : ↑(CategoryTheory.MonoidalCategoryStruct.tensorOb
j (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z)},   ((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).ho
m) x).2.1 = x.1.2
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryTheory.MonoidalCateg
oryStruct.tensorObj X Y) Z；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.
MonoidalCategoryStruct.associator X Y Z).hom) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_hom_apply_2_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.1 = x.1.2 :=
  rfl
/-
**TopCat.associator_hom_apply_2_2** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat}   {x : ↑(CategoryTheory.MonoidalCategoryStruct.tensorOb
j (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z)},   ((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).ho
m) x).2.2 = x.2
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryTheory.MonoidalCateg
oryStruct.tensorObj X Y) Z；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.
MonoidalCategoryStruct.associator X Y Z).hom) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_hom_apply_2_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.2 = x.2 :=
  rfl
/-
**TopCat.associator_inv_apply_1_1** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat}   {x : ↑(CategoryTheory.MonoidalCategoryStruct.tensorOb
j X (CategoryTheory.MonoidalCategoryStruct.tensorObj Y Z))},   ((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).in
v) x).1.1 = x.1
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj X (CategoryTheory.MonoidalCat
egoryStruct.tensorObj Y Z)；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.
MonoidalCategoryStruct.associator X Y Z).inv) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_inv_apply_1_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.1 = x.1 :=
  rfl
/-
**TopCat.associator_inv_apply_1_2** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat}   {x : ↑(CategoryTheory.MonoidalCategoryStruct.tensorOb
j X (CategoryTheory.MonoidalCategoryStruct.tensorObj Y Z))},   ((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).in
v) x).1.2 = x.2.1
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj X (CategoryTheory.MonoidalCat
egoryStruct.tensorObj Y Z)；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.
MonoidalCategoryStruct.associator X Y Z).inv) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_inv_apply_1_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.2 = x.2.1 :=
  rfl
/-
**TopCat.associator_inv_apply_2** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat}   {x : ↑(CategoryTheory.MonoidalCategoryStruct.tensorOb
j X (CategoryTheory.MonoidalCategoryStruct.tensorObj Y Z))},   ((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).in
v) x).2 = x.2.2
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj X (CategoryTheory.MonoidalCat
egoryStruct.tensorObj Y Z)；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.
MonoidalCategoryStruct.associator X Y Z).inv) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_inv_apply_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).2 = x.2.2 :=
  rfl

@[simp]
/-
**TopCat.braiding_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：braiding_hom_apply {X Y : TopCat.{u}} {x : X} {y : Y} : (β_ X Y).hom (x, y
) = (y, x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_hom_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).hom (x, y) = (y, x) :=
  rfl

@[simp]
/-
**TopCat.braiding_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：braiding_inv_apply {X Y : TopCat.{u}} {x : X} {y : Y} : (β_ X Y).inv (y, x
) = (x, y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_inv_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).inv (y, x) = (x, y) :=
  rfl

@[simp]
/-
**TopCat.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat} {f : X ⟶ Y} {g : X ⟶ Z} {x : ↑X},   (CategoryTheory.Con
creteCategory.hom (CategoryTheory.CartesianMonoidalCategory.lift f g)) x =     (
(CategoryTheory.ConcreteCategory.hom f) x, (CategoryTheory.ConcreteCategory.hom 
g) x)
参数：CategoryTheory.ConcreteCategory.hom (CategoryTheory.CartesianMonoidalCategory
.lift f g)；(CategoryTheory.ConcreteCategory.hom f) x, (CategoryTheory.ConcreteCa
tegory.hom g) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem lift_apply {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z} {x : X} :
    CartesianMonoidalCategory.lift f g x = (f x, g x) :=
  rfl

/-- The unit interval, as an object of `TopCat`. -/
/-
**TopCat.I** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：I : TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit interval, as an object of `TopCat`.
-/
def I : TopCat.{u} := TopCat.of (ULift unitInterval)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyCompactSpace I :=
  inferInstanceAs (LocallyCompactSpace (ULift unitInterval))

namespace I

/-- The unit interval `TopCat.I` is homeomorphic to `unitInterval`. -/
/-
**TopCat.I.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.I`。
形式化陈述：homeomorph : I ≃ₜ unitInterval
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit interval `TopCat.I` is homeomorphic to `unitInterval`.
-/
def homeomorph : I ≃ₜ unitInterval := Homeomorph.ulift

@[ext]
/-
**TopCat.I.ext** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.I`。
形式化陈述：ext {x y : I.{u}} (h : homeomorph x = homeomorph y) : x = y
参数：h : homeomorph x = homeomorph y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
-/
lemma ext {x y : I.{u}} (h : homeomorph x = homeomorph y) : x = y :=
  homeomorph.injective h

/-- The symmetrization map `TopCat.I ⟶ TopCat.I`. -/
/-
**TopCat.I.symm** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.I`。
形式化陈述：symm : I.{u} ⟶ I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetrization map `TopCat.I ⟶ TopCat.I`.
-/
def symm : I.{u} ⟶ I :=
  ofHom ⟨homeomorph.symm ∘ unitInterval.symm ∘ homeomorph, by fun_prop⟩

@[simp]
/-
**TopCat.I.homeomorph_symm** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.I`。
形式化陈述：homeomorph_symm (x : I) : homeomorph (symm x) = unitInterval.symm (homeomo
rph x)
参数：x : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homeomorph_symm (x : I) :
    homeomorph (symm x) = unitInterval.symm (homeomorph x) := rfl
/-
**TopCat.I.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.I`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OfNat I.{u} 0 := ⟨homeomorph.symm 0⟩
/-
**TopCat.I.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.I`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OfNat I.{u} 1 := ⟨homeomorph.symm 1⟩
/-
**TopCat.I.homeomorph_zero** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.I`。
形式化陈述：TopCat.I.homeomorph 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma homeomorph_zero : homeomorph (0 : I.{u}) = 0 := by simp [OfNat.ofNat]
/-
**TopCat.I.homeomorph_one** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.I`。
形式化陈述：TopCat.I.homeomorph 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma homeomorph_one : homeomorph (1 : I.{u}) = 1 := by simp [OfNat.ofNat]
/-
**TopCat.I.symm_one** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.I`。
形式化陈述：(CategoryTheory.ConcreteCategory.hom TopCat.I.symm) 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.I.ext`：ext {x y : I.{u}} (h : homeomorph x = homeomorph y) : x = 
y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.I.homeomorph_one`：TopCat.I.homeomorph 1 = 1
· 使用定理 `unitInterval.symm_one`：symm_one : σ 1 = 0
· 使用定理 `TopCat.I.homeomorph_zero`：TopCat.I.homeomorph 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma symm_one : I.symm 1 = 0 := by aesop
/-
**TopCat.I.symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.I`。
形式化陈述：(CategoryTheory.ConcreteCategory.hom TopCat.I.symm) 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.I.ext`：ext {x y : I.{u}} (h : homeomorph x = homeomorph y) : x = 
y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.I.homeomorph_zero`：TopCat.I.homeomorph 0 = 0
· 使用定理 `unitInterval.symm_zero`：symm_zero : σ 0 = 1
· 使用定理 `TopCat.I.homeomorph_one`：TopCat.I.homeomorph 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma symm_zero : I.symm 0 = 1 := by aesop

end I

open CartesianMonoidalCategory

/-- The inclusion `X ⟶ X ⊗ I` given by `0 : I` for `X : TopCat`. -/
/-
**TopCat.** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `X ⟶ X ⊗ I` given by `0 : I` for `X : TopCat`.
-/
noncomputable def ι₀ {X : TopCat.{u}} : X ⟶ X ⊗ I :=
  lift (𝟙 X) (const 0)

@[reassoc (attr := simp)]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_comp {X Y : TopCat.{u}} (f : X ⟶ Y) : ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_fst (X : TopCat.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_snd (X : TopCat.{u}) : ι₀ ≫ snd X _ = TopCat.const 0 := rfl
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ι₀_apply {X : TopCat.{u}} (x : X) : ι₀ x = ⟨x, 0⟩ := rfl

/-- The inclusion `X ⟶ X ⊗ I` given by `1 : I` for `X : TopCat`. -/
/-
**TopCat.** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `X ⟶ X ⊗ I` given by `1 : I` for `X : TopCat`.
-/
noncomputable def ι₁ {X : TopCat.{u}} : X ⟶ X ⊗ I :=
  lift (𝟙 X) (const 1)

@[reassoc (attr := simp)]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_comp {X Y : TopCat.{u}} (f : X ⟶ Y) : ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[reassoc (attr := simp)]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_fst (X : TopCat.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_snd (X : TopCat.{u}) : ι₁ ≫ snd X _ = const 1 := rfl

@[simp]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_apply {X : TopCat.{u}} (x : X) : ι₁ x = ⟨x, 1⟩ := rfl

end TopCat

