/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.NCompGamma

/-! # The Dold-Kan equivalence for additive categories.

This file defines `Preadditive.DoldKan.equivalence` which is the equivalence
of categories `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Idempotents AlgebraicTopology.DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

namespace CategoryTheory

namespace Preadditive

namespace DoldKan

/-- The functor `Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
/-
**CategoryTheory.Preadditive.DoldKan.N** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Preadditive.DoldKan`。
形式化陈述：N : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C Nat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)` of
the Dold-Kan equivalence for additive categories.
-/
def N : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  N₂

variable [HasFiniteCoproducts C]

/-- The inverse functor `Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
/-
**CategoryTheory.Preadditive.DoldKan.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Preadditive.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor `Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)` 
of
the Dold-Kan equivalence for additive categories.
-/
def Γ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  Γ₂

set_option backward.isDefEq.respectTransparency false in
/-- The Dold-Kan equivalence `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`
for additive categories. -/
@[simps]
/-
**CategoryTheory.Preadditive.DoldKan.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Preadditive.DoldKan`。
形式化陈述：equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C Nat) 
where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dold-Kan equivalence `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C
 ℕ)`
for additive categories.
-/
def equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ) where
  functor := N
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := N₂Γ₂
  functor_unitIso_comp P := by
    let α := N.mapIso (Γ₂N₂.app P)
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← Iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← Iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P

end DoldKan

end Preadditive

end CategoryTheory

