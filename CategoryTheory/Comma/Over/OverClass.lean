/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Typeclasses for `S`-objects and `S`-morphisms

**Warning**: This is not usually how typeclasses should be used.
This is only a sensible approach when the morphism is considered as a structure on `X`,
typically in algebraic geometry.

This is analogous to how we view ringhoms as structures via the `Algebra` typeclass.

For other applications use unbundled arrows or `CategoryTheory.Over`.

## Main definition
- `CategoryTheory.OverClass`: `OverClass X S` equips `X` with a morphism into `S`.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `CategoryTheory.HomIsOver`:
  `HomIsOver f S` asserts that `f` commutes with the structure morphisms.

-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y Z : C} (f : X ⟶ Y) (S S' : C)

/--
`OverClass X S` is the typeclass containing the data of a structure morphism `X ↘ S : X ⟶ S`.
-/
/-
**CategoryTheory.OverClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → C → C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OverClass X S` is the typeclass containing the data of a structure morphism `X 
↘ S : X ⟶ S`.
-/
class OverClass (X S : C) : Type v where
  ofHom ::
  /-- The structure morphism. Use `X ↘ S` instead. -/
  hom : X ⟶ S

/--
The structure morphism `X ↘ S : X ⟶ S` given `OverClass X S`.
The instance argument is an `optParam` instead so that it appears in the discrimination tree.
-/
/-
**CategoryTheory.over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：over (X S : C) (_ : OverClass X S
参数：X S : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure morphism `X ↘ S : X ⟶ S` given `OverClass X S`.
The instance argument is an `optParam` instead so that it appears in the discrim
ination tree.
-/
def over (X S : C) (_ : OverClass X S := by infer_instance) : X ⟶ S := OverClass.hom

/-- The structure morphism `X ↘ S : X ⟶ S` given `OverClass X S`. -/
notation:90 X:90 " ↘ " S:90 => CategoryTheory.over X S inferInstance

/-- See Note [custom simps projection] -/
/-
**CategoryTheory.OverClass.Simps.over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
OverClass.Simps`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (X S : C) → [Ca
tegoryTheory.OverClass X S] → X ⟶ S
参数：X S : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def OverClass.Simps.over (X S : C) [OverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections OverClass (hom → over)

/--
`X.CanonicallyOverClass S` is the typeclass containing the data of a
structure morphism `X ↘ S : X ⟶ S`,
and that `S` is (uniquely) inferable from the structure of `X`.
-/
/-
**CategoryTheory.CanonicallyOverClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → C → semiOutParam C → T
ype v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X.CanonicallyOverClass S` is the typeclass containing the data of a
structure morphism `X ↘ S : X ⟶ S`,
and that `S` is (uniquely) inferable from the structure of `X`.
-/
class CanonicallyOverClass (X : C) (S : semiOutParam C) extends OverClass X S where

/-- See Note [custom simps projection] -/
/-
**CategoryTheory.CanonicallyOverClass.Simps.over** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.CanonicallyOverClass.Simps`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (X S : C) → [Ca
tegoryTheory.CanonicallyOverClass X S] → X ⟶ S
参数：X S : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def CanonicallyOverClass.Simps.over (X S : C) [CanonicallyOverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections CanonicallyOverClass (hom → over)

@[simps]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OverClass X X := ⟨𝟙 _⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (S ↘ S) := inferInstanceAs (IsIso (𝟙 S))

namespace CanonicallyOverClass
-- This cannot be a simp lemma because it loops with `comp_over`.
@[simps -isSimp]
/-
**CategoryTheory.CanonicallyOverClass.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.CanonicallyOverClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [CanonicallyOverClass X Y] [OverClass Y S] : OverClass X S :=
  ⟨X ↘ Y ≫ Y ↘ S⟩
end CanonicallyOverClass

/-- Given `OverClass X S` and `OverClass Y S` and `f : X ⟶ Y`,
`HomIsOver f S` is the typeclass asserting `f` commutes with the structure morphisms. -/
/-
**CategoryTheory.HomIsOver** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：HomIsOver (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S] : Prop where
 comp_over : f ≫ Y ↘ S = X ↘ S
参数：f : X ⟶ Y；S : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `OverClass X S` and `OverClass Y S` and `f : X ⟶ Y`,
`HomIsOver f S` is the typeclass asserting `f` commutes with the structure morph
isms.
-/
class HomIsOver (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S] : Prop where
  comp_over : f ≫ Y ↘ S = X ↘ S := by aesop

@[reassoc (attr := simp)]
/-
**CategoryTheory.comp_over** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：comp_over [OverClass X S] [OverClass Y S] [HomIsOver f S] : f ≫ Y ↘ S = X 
↘ S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HomIsOver.comp_over`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} {S : C}   {inst_1 : CategoryTheory.Ov
erClass X S} {inst_2 : C…
-/
lemma comp_over [OverClass X S] [OverClass Y S] [HomIsOver f S] :
    f ≫ Y ↘ S = X ↘ S :=
  HomIsOver.comp_over
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OverClass X S] : HomIsOver (𝟙 X) S where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OverClass X S] [OverClass Y S] [OverClass Z S]
    (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    HomIsOver (f ≫ g) S where

/-- `IsOverTower X Y S` is the typeclass asserting that the structure morphisms
`X ↘ Y`, `Y ↘ S`, and `X ↘ S` commute. -/
/-
**CategoryTheory.IsOverTower** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsOverTower (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y]
参数：X Y S : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsOverTower X Y S` is the typeclass asserting that the structure morphisms
`X ↘ Y`, `Y ↘ S`, and `X ↘ S` commute.
-/
abbrev IsOverTower (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y] :=
  HomIsOver (X ↘ Y) S
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OverClass X S] : IsOverTower X X S where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OverClass X S] : IsOverTower X S S where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CanonicallyOverClass X Y] [OverClass Y S] : IsOverTower X Y S :=
  ⟨rfl⟩
/-
**CategoryTheory.homIsOver_of_isOverTower** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：homIsOver_of_isOverTower [OverClass X S] [OverClass X S'] [OverClass Y S] 
[OverClass Y S'] [OverClass S S'] [IsOverTower X S S'] [IsOverTower Y S S'] [Hom
IsOver f S] : HomIsOver f S'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `CategoryTheory.comp_over_assoc`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X Y : C} (f : X ⟶ Y) (S : C)   [inst_1 : CategoryTheory.OverCl
ass X S] [inst_2 : C…
-/
lemma homIsOver_of_isOverTower [OverClass X S] [OverClass X S'] [OverClass Y S]
    [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' := by
  constructor
  rw [← comp_over (Y ↘ S), comp_over_assoc f, comp_over]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CanonicallyOverClass X S]
    [OverClass X S'] [OverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OverClass X S]
    [OverClass X S'] [CanonicallyOverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

variable (X) in
/-- Bundle `X` with an `OverClass X S` instance into `Over S`. -/
@[simps! hom left]
/-
**CategoryTheory.OverClass.asOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over
Class`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → (X S : C) → [
CategoryTheory.OverClass X S] → CategoryTheory.Over S
参数：X S : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `X` with an `OverClass X S` instance into `Over S`.
-/
def OverClass.asOver [OverClass X S] : Over S := Over.mk (X ↘ S)

/-- Bundle a morphism `f : X ⟶ Y` with `HomIsOver f S` into a morphism in `Over S`. -/
@[simps! left]
/-
**CategoryTheory.OverClass.asOverHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
verClass`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (S : C) →         [inst_1 : CategoryTheory.OverClass X S] →           [
inst_2 : CategoryTheory.OverClass Y S] →             (f : X ⟶ Y) →              
 [CategoryTheory.HomIsOver f S] → CategoryTheory.OverClass.asOver X S ⟶ Category
Theory.OverClass.asOver Y S
参数：S : C；f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S

--- 原说明 ---
Bundle a morphism `f : X ⟶ Y` with `HomIsOver f S` into a morphism in `Over S`.
-/
def OverClass.asOverHom [OverClass X S] [OverClass Y S] (f : X ⟶ Y) [HomIsOver f S] :
    OverClass.asOver X S ⟶ OverClass.asOver Y S :=
  Over.homMk f (comp_over f S)

@[simps]
/-
**CategoryTheory.OverClass.fromOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ov
erClass`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {S : C} → (X 
: CategoryTheory.Over S) → CategoryTheory.OverClass X.left S
参数：X : CategoryTheory.Over S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OverClass.fromOver {S : C} (X : Over S) : OverClass X.left S where
  hom := X.hom
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : C} {X Y : Over S} (f : X ⟶ Y) : HomIsOver f.left S where
  comp_over := Over.w f

variable [OverClass X S] [OverClass Y S] [OverClass Z S]

namespace OverClass

/-
**CategoryTheory.OverClass.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.OverClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [IsIso f] [HomIsOver f S] : IsIso (asOverHom S f) :=
  have : IsIso ((Over.forget S).map (asOverHom S f)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

attribute [local simp] Iso.inv_comp_eq in
/-
**CategoryTheory.OverClass.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.OverClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {e : X ≅ Y} [HomIsOver e.hom S] : HomIsOver e.inv S where

set_option linter.style.whitespace false in -- linter false positive
attribute [local simp ←] Iso.eq_inv_comp in
/-
**CategoryTheory.OverClass.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.OverClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {e : X ≅ Y} [HomIsOver e.inv S] : HomIsOver e.hom S where
/-
**CategoryTheory.OverClass.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.OverClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).hom S where
/-
**CategoryTheory.OverClass.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.OverClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).inv S where
/-
**CategoryTheory.OverClass.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.OverClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (inv f) S where
/-
**CategoryTheory.OverClass.asOverHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.OverClass`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (S : C) [
inst_1 : CategoryTheory.OverClass X S],   CategoryTheory.OverClass.asOverHom S (
CategoryTheory.CategoryStruct.id X) =     CategoryTheory.CategoryStruct.id (Cate
goryTheory.OverClass.asOver X S)
参数：S : C；CategoryTheory.CategoryStruct.id X；CategoryTheory.OverClass.asOver X S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHomIsOverId`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.HomIsOver…
-/
@[simp] lemma asOverHom_id : asOverHom S (𝟙 X) = 𝟙 (asOver X S) := rfl
/-
**CategoryTheory.OverClass.asOverHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.OverClass`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (S : 
C) [inst_1 : CategoryTheory.OverClass X S]   [inst_2 : CategoryTheory.OverClass 
Y S] [inst_3 : CategoryTheory.OverClass Z S] (f : X ⟶ Y) (g : Y ⟶ Z)   [inst_4 :
 CategoryTheory.HomIsOver f S] [inst_5 : CategoryTheory.HomIsOver g S],   Catego
ryTheory.OverClass.asOverHom S (CategoryTheory.CategoryStruct.comp f g) =     Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.OverClass.asOverHom S f) (Categ
oryTheory.OverClass.asOverHom S g)
参数：S : C；f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheo
ry.OverClass.asOverHom S f；CategoryTheory.OverClass.asOverHom S g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHomIsOverComp`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (S : C) [inst_1 : CategoryTheory.OverClass X S]  
 [inst_2 : CategoryThe…
-/
@[simp, reassoc] lemma asOverHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    asOverHom S (f ≫ g) = asOverHom S f ≫ asOverHom S g := rfl
/-
**CategoryTheory.OverClass.asOverHom_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.OverClass`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (S : C)
 [inst_1 : CategoryTheory.OverClass X S]   [inst_2 : CategoryTheory.OverClass Y 
S] (f : X ⟶ Y) [inst_3 : CategoryTheory.IsIso f]   [inst_4 : CategoryTheory.HomI
sOver f S],   CategoryTheory.OverClass.asOverHom S (CategoryTheory.inv f) =     
CategoryTheory.inv (CategoryTheory.OverClass.asOverHom S f)
参数：S : C；f : X ⟶ Y；CategoryTheory.inv f；CategoryTheory.OverClass.asOverHom S f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.OverClass.instHomIsOverInv`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (S : C) [inst_1 : CategoryTheory.OverClass
 X S]   [inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.OverClass.instIsIsoOverAsOverHom`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {X Y : C} (S : C) [inst_1 : CategoryTheory.Ove
rClass X S]   [inst_2 : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.OverClass.asOverHom.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y : C} (S : C) [inst_1 : CategoryTheory.OverC
lass X S]   [inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.instHomIsOverComp`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (S : C) [inst_1 : CategoryTheory.OverClass X S]  
 [inst_2 : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma asOverHom_inv (f : X ⟶ Y) [IsIso f] [HomIsOver f S] :
    asOverHom S (inv f) = inv (asOverHom S f) := by simp [← hom_comp_eq_id, ← asOverHom_comp]

end OverClass

set_option backward.isDefEq.respectTransparency.types false in
/-- Reinterpret an isomorphism over an object `S` into an isomorphism in the category over `S`. -/
@[simps]
/-
**CategoryTheory.Iso.asOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (S : C) →         [inst_1 : CategoryTheory.OverClass X S] →           [
inst_2 : CategoryTheory.OverClass Y S] →             (e : X ≅ Y) →              
 [CategoryTheory.HomIsOver e.hom S] →                 CategoryTheory.OverClass.a
sOver X S ≅ CategoryTheory.OverClass.asOver Y S
参数：S : C；e : X ≅ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.OverClass.instHomIsOverInvOfHom`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y : C} (S : C) [inst_1 : CategoryTheory.Over
Class X S]   [inst_2 : CategoryTheor…

--- 原说明 ---
Reinterpret an isomorphism over an object `S` into an isomorphism in the categor
y over `S`.
-/
def Iso.asOver (e : X ≅ Y) [HomIsOver e.hom S] : OverClass.asOver X S ≅ OverClass.asOver Y S where
  hom := OverClass.asOverHom S e.hom
  inv := OverClass.asOverHom S e.inv

end CategoryTheory

