/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax
public import Mathlib.CategoryTheory.Bicategory.End
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonads in a bicategory

We define comonads in a bicategory `B` as comonoid objects in an endomorphism monoidal category.
We show that this is equivalent to oplax functors from the trivial bicategory to `B`. From this,
we show that comonads in `B` form a bicategory.

## TODO

We can also define monads in a bicategory. This is not yet done as we don't have the bicategory
structure on the set of lax functors at this point, which is needed to show that monads form a
bicategory.
-/

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- A comonad in a bicategory `B` is a 1-morphism `t : a ⟶ a` together with 2-morphisms
`Δ : t ⟶ t ≫ t` and `ε : t ⟶ 𝟙 a` satisfying the comonad laws. -/
/-
**CategoryTheory.Bicategory.Comonad** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Bicategory`。
形式化陈述：Comonad {a : B} (t : a ⟶ a)
参数：t : a ⟶ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A comonad in a bicategory `B` is a 1-morphism `t : a ⟶ a` together with 2-morphi
sms
`Δ : t ⟶ t ≫ t` and `ε : t ⟶ 𝟙 a` satisfying the comonad laws.
-/
abbrev Comonad {a : B} (t : a ⟶ a) := ComonObj t

/-- The counit 2-morphism of the comonad. -/
/-
**CategoryTheory.Bicategory.Comonad.counit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Bicategory.Comonad`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a : B} → {t :
 a ⟶ a} → [CategoryTheory.Bicategory.Comonad t] → t ⟶ CategoryTheory.CategoryStr
uct.id a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit 2-morphism of the comonad.
-/
abbrev Comonad.counit {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ 𝟙 a := ComonObj.counit

/-- The comultiplication 2-morphism of the comonad. -/
/-
**CategoryTheory.Bicategory.Comonad.comul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Bicategory.Comonad`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a : B} → {t :
 a ⟶ a} → [CategoryTheory.Bicategory.Comonad t] → t ⟶ CategoryTheory.CategoryStr
uct.comp t t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comultiplication 2-morphism of the comonad.
-/
abbrev Comonad.comul {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ t ≫ t := ComonObj.comul

@[inherit_doc] scoped notation "ε" => Comonad.counit
@[inherit_doc] scoped notation "ε[" x "]" => Comonad.counit (t := x)
@[inherit_doc] scoped notation "Δ" => Comonad.comul
@[inherit_doc] scoped notation "Δ[" x "]" => Comonad.comul (t := x)

namespace Comonad

variable {a : B}

/- Comonad laws -/
section

variable (t : a ⟶ a) [Comonad t]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.Comonad.counit_comul** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory.Comonad`。
形式化陈述：counit_comul : Δ ≫ ε ▷ t = (fun_ t).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComonObj.counit_comul`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)  
 [self : CategoryTheory.Co…
-/
theorem counit_comul : Δ ≫ ε ▷ t = (λ_ t).inv := ComonObj.counit_comul t

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.Comonad.comul_counit** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory.Comonad`。
形式化陈述：comul_counit : Δ ≫ t ◁ ε = (ρ_ t).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComonObj.comul_counit`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)  
 [self : CategoryTheory.Co…
-/
theorem comul_counit : Δ ≫ t ◁ ε = (ρ_ t).inv := ComonObj.comul_counit t

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.Comonad.comul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory.Comonad`。
形式化陈述：comul_assoc : Δ ≫ t ◁ Δ = Δ ≫ Δ ▷ t ≫ (α_ t t t).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComonObj.comul_assoc`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   
[self : CategoryTheory.Co…
-/
theorem comul_assoc : Δ ≫ t ◁ Δ = Δ ≫ Δ ▷ t ≫ (α_ t t t).hom := ComonObj.comul_assoc t

@[reassoc]
/-
**CategoryTheory.Bicategory.Comonad.comul_assoc_flip** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Bicategory.Comonad`。
形式化陈述：comul_assoc_flip : Δ ≫ Δ ▷ t = Δ ≫ t ◁ Δ ≫ (α_ t t t).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComonObj.comul_assoc_flip`：comul_assoc_flip (X : C) [Como
nObj X] : Δ ≫ Δ ▷ X = Δ ≫ X ◁ Δ ≫ (α_ X X X).inv
-/
theorem comul_assoc_flip : Δ ≫ Δ ▷ t = Δ ≫ t ◁ Δ ≫ (α_ t t t).inv := ComonObj.comul_assoc_flip t

end

@[simps! counit]
/-
**CategoryTheory.Bicategory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.B
icategory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : B} : Comonad (𝟙 a) :=
  ComonObj.instTensorUnit (a ⟶ a)

/-- An oplax functor from the trivial bicategory to `B` defines a comonad in `B`. -/
@[instance_reducible]
/-
**CategoryTheory.Bicategory.Comonad.ofOplaxFromUnit** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.Comonad`。
形式化陈述：ofOplaxFromUnit (F : LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B) : Comonad (F.
map (𝟙 ⟨⟨Unit.unit⟩⟩)) where comul
参数：F : LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oplax functor from the trivial bicategory to `B` defines a comonad in `B`.
-/
def ofOplaxFromUnit (F : LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B) :
    Comonad (F.map (𝟙 ⟨⟨Unit.unit⟩⟩)) where
  comul := F.map₂ (ρ_ _).inv ≫ F.mapComp _ _
  counit := F.mapId _
  comul_assoc := by
    simp only [tensorObj_def, MonoidalCategory.whiskerLeft_comp, whiskerLeft_def, Category.assoc,
      MonoidalCategory.comp_whiskerRight, whiskerRight_def, associator_def]
    rw [← F.mapComp_naturality_left_assoc, ← F.mapComp_naturality_right_assoc]
    simp only [whiskerLeft_rightUnitor_inv, PrelaxFunctor.map₂_comp, Category.assoc,
      OplaxFunctor.map₂_associator, whiskerRight_id, Iso.hom_inv_id_assoc]
  counit_comul := by
    simp only [tensorUnit_def, tensorObj_def, whiskerRight_def, Category.assoc, leftUnitor_def]
    rw [F.mapComp_id_left, unitors_equal, F.map₂_inv_hom_assoc]
  comul_counit := by
    simp only [tensorUnit_def, tensorObj_def, whiskerLeft_def, rightUnitor_def]
    rw [Category.assoc, F.mapComp_id_right, F.map₂_inv_hom_assoc]

/-- A comonad in `B` defines an oplax functor from the trivial bicategory to `B`. -/
/-
**CategoryTheory.Bicategory.Comonad.toOplax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Bicategory.Comonad`。
形式化陈述：toOplax {a : B} (t : a ⟶ a) [Comonad t] : LocallyDiscrete (Discrete Unit) 
⥤ᵒᵖᴸ B where obj _
参数：t : a ⟶ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A comonad in `B` defines an oplax functor from the trivial bicategory to `B`.
-/
def toOplax {a : B} (t : a ⟶ a) [Comonad t] : LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B where
  obj _ := a
  map _ := t
  map₂ _ := 𝟙 _
  mapId _ := ε
  mapComp _ _ := Δ
  map₂_associator _ _ _ := by
    rw [Category.id_comp]
    apply Comonad.comul_assoc

end Comonad

/- In this section, we define bicategory structure on comonads by using the bicategory structure on
oplax functors. We may use oplax, lax, or pseudonatural transformations to provide the bicategory
structure, and the namespace below indicates that we use oplax transformations here. The
constructions for the other two cases would be given in the corresponding namespaces. -/
namespace OplaxTrans

/-- The bicategory of comonads in `B`. -/
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.OplaxTrans`。
形式化陈述：ComonadBicat (B : Type u) [Bicategory.{w, v} B]
参数：B : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicategory of comonads in `B`.
-/
def ComonadBicat (B : Type u) [Bicategory.{w, v} B] :=
  LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B

namespace ComonadBicat

open scoped Oplax.OplaxTrans.OplaxFunctor in
/-- The bicategory of comonads in `B`. -/
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicategory of comonads in `B`.
-/
scoped instance : Bicategory (ComonadBicat B) :=
  inferInstanceAs <| Bicategory (LocallyDiscrete (Discrete PUnit) ⥤ᵒᵖᴸ B)

/-- The oplax functor from the trivial bicategory to `B` associated with the comonad. -/
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.toOplax** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
形式化陈述：toOplax (m : ComonadBicat B) : LocallyDiscrete (Discrete PUnit) ⥤ᵒᵖᴸ B
参数：m : ComonadBicat B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The oplax functor from the trivial bicategory to `B` associated with the comonad
.
-/
def toOplax (m : ComonadBicat B) : LocallyDiscrete (Discrete PUnit) ⥤ᵒᵖᴸ B :=
  m

/-- The object in `B` associated with the comonad. -/
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.obj** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
形式化陈述：obj (m : ComonadBicat B)
参数：m : ComonadBicat B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in `B` associated with the comonad.
-/
def obj (m : ComonadBicat B) :=
  m.toOplax.obj ⟨⟨PUnit.unit⟩⟩

/-- The morphism in `B` associated with the comonad. -/
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.hom** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
形式化陈述：hom (m : ComonadBicat B) : m.obj ⟶ m.obj
参数：m : ComonadBicat B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in `B` associated with the comonad.
-/
def hom (m : ComonadBicat B) : m.obj ⟶ m.obj :=
  m.toOplax.map (𝟙 (⟨⟨PUnit.unit⟩⟩ : LocallyDiscrete (Discrete PUnit)))
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (m : ComonadBicat B) : Comonad m.hom :=
  Comonad.ofOplaxFromUnit <| m.toOplax

/-- Construct a comonad as an object in `ComonadBicat B`. -/
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.mkOfComonad** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
形式化陈述：mkOfComonad {a : B} (t : a ⟶ a) [Comonad t] : ComonadBicat B
参数：t : a ⟶ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a comonad as an object in `ComonadBicat B`.
-/
def mkOfComonad {a : B} (t : a ⟶ a) [Comonad t] : ComonadBicat B :=
  Comonad.toOplax t

open Comonad

section

variable {a : B} (t : a ⟶ a) [Comonad t]

/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.mkOfComonad_hom** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
形式化陈述：mkOfComonad_hom : (mkOfComonad t).hom = t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkOfComonad_hom : (mkOfComonad t).hom = t := rfl
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.mkOfComonad_counit** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
形式化陈述：mkOfComonad_counit : ε[(mkOfComonad t).hom] = ε[t]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkOfComonad_counit : ε[(mkOfComonad t).hom] = ε[t] := rfl
/-
**CategoryTheory.Bicategory.OplaxTrans.ComonadBicat.mkOfComonad_comul** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.OplaxTrans.ComonadBicat`。
形式化陈述：mkOfComonad_comul : Δ[(mkOfComonad t).hom] = Δ[t]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem mkOfComonad_comul : Δ[(mkOfComonad t).hom] = Δ[t] := by
  change 𝟙 t ≫ Δ = Δ
  apply Category.id_comp

end

end ComonadBicat

end OplaxTrans

end Bicategory

end CategoryTheory

