/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Homology of preadditive categories

In this file, it is shown that if `C` is a preadditive category, then
`ShortComplex C` is a preadditive category.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

namespace ShortComplex

variable {S₁ S₂ S₃ : ShortComplex C}

attribute [local simp] Hom.comm₁₂ Hom.comm₂₃

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (S₁ ⟶ S₂)
  body: { τ₁ := φ.τ₁ + φ'.τ₁
      τ₂ := φ.τ₂ + φ'.τ₂
      τ₃ := φ.τ₃ + φ'.τ₃ }

中文:
实例 :
  签名: Add (S₁ ⟶ S₂)
  定义体: { τ₁ := φ.τ₁ + φ'.τ₁
      τ₂ := φ.τ₂ + φ'.τ₂
      τ₃ := φ.τ₃ + φ'.τ₃ }
-/
instance : Add (S₁ ⟶ S₂) where
  add φ φ' :=
    { τ₁ := φ.τ₁ + φ'.τ₁
      τ₂ := φ.τ₂ + φ'.τ₂
      τ₃ := φ.τ₃ + φ'.τ₃ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (S₁ ⟶ S₂)
  body: { τ₁ := φ.τ₁ - φ'.τ₁
      τ₂ := φ.τ₂ - φ'.τ₂
      τ₃ := φ.τ₃ - φ'.τ₃ }

中文:
实例 :
  签名: Sub (S₁ ⟶ S₂)
  定义体: { τ₁ := φ.τ₁ - φ'.τ₁
      τ₂ := φ.τ₂ - φ'.τ₂
      τ₃ := φ.τ₃ - φ'.τ₃ }
-/
instance : Sub (S₁ ⟶ S₂) where
  sub φ φ' :=
    { τ₁ := φ.τ₁ - φ'.τ₁
      τ₂ := φ.τ₂ - φ'.τ₂
      τ₃ := φ.τ₃ - φ'.τ₃ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (S₁ ⟶ S₂)
  body: { τ₁ := -φ.τ₁
      τ₂ := -φ.τ₂
      τ₃ := -φ.τ₃ }

中文:
实例 :
  签名: Neg (S₁ ⟶ S₂)
  定义体: { τ₁ := -φ.τ₁
      τ₂ := -φ.τ₂
      τ₃ := -φ.τ₃ }
-/
instance : Neg (S₁ ⟶ S₂) where
  neg φ :=
    { τ₁ := -φ.τ₁
      τ₂ := -φ.τ₂
      τ₃ := -φ.τ₃ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (S₁ ⟶ S₂)
  body: fun a b c => by ext <;> apply add_assoc
  add_zero := fun a => by ext <;> apply add_zero
  zero_add := fun a => by ext <;> apply zero_add
  neg_add_cancel := fun a => by ext <;> apply neg_add_cancel
  add_comm := fun a b => by ext <;> apply add_comm
  sub_eq_add_neg := fun a b => by ext <;> apply su

中文:
实例 :
  签名: AddCommGroup (S₁ ⟶ S₂)
  定义体: fun a b c => by ext <;> apply add_assoc
  add_zero := fun a => by ext <;> apply add_zero
  zero_add := fun a => by ext <;> apply zero_add
  neg_add_cancel := fun a => by ext <;> apply neg_add_cancel
  add_comm := fun a b => by ext <;> apply add_comm
  sub_eq_add_neg := fun a b => by ext <;> apply su

Depends on / 依赖: add_assoc
-/
instance : AddCommGroup (S₁ ⟶ S₂) where
  add_assoc := fun a b c => by ext <;> apply add_assoc
  add_zero := fun a => by ext <;> apply add_zero
  zero_add := fun a => by ext <;> apply zero_add
  neg_add_cancel := fun a => by ext <;> apply neg_add_cancel
  add_comm := fun a b => by ext <;> apply add_comm
  sub_eq_add_neg := fun a b => by ext <;> apply sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

/--
lemma `add_τ₁` / 引理 `add_τ₁`

English:
lemma add_τ₁
  given: (φ φ' : S₁ ⟶ S₂)
  statement: (φ + φ').τ₁ = φ.τ₁ + φ'.τ₁
  proof: rfl

中文:
引理 add_τ₁
  条件: (φ φ' : S₁ ⟶ S₂)
  结论: (φ + φ').τ₁ = φ.τ₁ + φ'.τ₁
  证明: rfl
-/
@[simp] lemma add_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₁ = φ.τ₁ + φ'.τ₁ := rfl
/--
lemma `add_τ₂` / 引理 `add_τ₂`

English:
lemma add_τ₂
  given: (φ φ' : S₁ ⟶ S₂)
  statement: (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂
  proof: rfl

中文:
引理 add_τ₂
  条件: (φ φ' : S₁ ⟶ S₂)
  结论: (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂
  证明: rfl
-/
@[simp] lemma add_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂ := rfl
/--
lemma `add_τ₃` / 引理 `add_τ₃`

English:
lemma add_τ₃
  given: (φ φ' : S₁ ⟶ S₂)
  statement: (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃
  proof: rfl

中文:
引理 add_τ₃
  条件: (φ φ' : S₁ ⟶ S₂)
  结论: (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃
  证明: rfl
-/
@[simp] lemma add_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃ := rfl
/--
lemma `sub_τ₁` / 引理 `sub_τ₁`

English:
lemma sub_τ₁
  given: (φ φ' : S₁ ⟶ S₂)
  statement: (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁
  proof: rfl

中文:
引理 sub_τ₁
  条件: (φ φ' : S₁ ⟶ S₂)
  结论: (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁
  证明: rfl
-/
@[simp] lemma sub_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁ := rfl
/--
lemma `sub_τ₂` / 引理 `sub_τ₂`

English:
lemma sub_τ₂
  given: (φ φ' : S₁ ⟶ S₂)
  statement: (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂
  proof: rfl

中文:
引理 sub_τ₂
  条件: (φ φ' : S₁ ⟶ S₂)
  结论: (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂
  证明: rfl
-/
@[simp] lemma sub_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂ := rfl
/--
lemma `sub_τ₃` / 引理 `sub_τ₃`

English:
lemma sub_τ₃
  given: (φ φ' : S₁ ⟶ S₂)
  statement: (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃
  proof: rfl

中文:
引理 sub_τ₃
  条件: (φ φ' : S₁ ⟶ S₂)
  结论: (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃
  证明: rfl
-/
@[simp] lemma sub_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃ := rfl
/--
lemma `neg_τ₁` / 引理 `neg_τ₁`

English:
lemma neg_τ₁
  given: (φ : S₁ ⟶ S₂)
  statement: (-φ).τ₁ = -φ.τ₁
  proof: rfl

中文:
引理 neg_τ₁
  条件: (φ : S₁ ⟶ S₂)
  结论: (-φ).τ₁ = -φ.τ₁
  证明: rfl

Depends on / 依赖: E.instLieRing, instLieRing
-/
@[simp] lemma neg_τ₁ (φ : S₁ ⟶ S₂) : (-φ).τ₁ = -φ.τ₁ := rfl
/--
lemma `neg_τ₂` / 引理 `neg_τ₂`

English:
lemma neg_τ₂
  given: (φ : S₁ ⟶ S₂)
  statement: (-φ).τ₂ = -φ.τ₂
  proof: rfl

中文:
引理 neg_τ₂
  条件: (φ : S₁ ⟶ S₂)
  结论: (-φ).τ₂ = -φ.τ₂
  证明: rfl

Depends on / 依赖: E.instLieAlgebra, instLieAlgebra
-/
@[simp] lemma neg_τ₂ (φ : S₁ ⟶ S₂) : (-φ).τ₂ = -φ.τ₂ := rfl
/--
lemma `neg_τ₃` / 引理 `neg_τ₃`

English:
lemma neg_τ₃
  given: (φ : S₁ ⟶ S₂)
  statement: (-φ).τ₃ = -φ.τ₃
  proof: rfl

中文:
引理 neg_τ₃
  条件: (φ : S₁ ⟶ S₂)
  结论: (-φ).τ₃ = -φ.τ₃
  证明: rfl
-/
@[simp] lemma neg_τ₃ (φ : S₁ ⟶ S₂) : (-φ).τ₃ = -φ.τ₃ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (ShortComplex C)

中文:
实例 :
  签名: Preadditive (ShortComplex C)
-/
instance : Preadditive (ShortComplex C) where

section LeftHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

namespace LeftHomologyMapData

variable (γ : LeftHomologyMapData φ h₁ h₂) (γ' : LeftHomologyMapData φ' h₁ h₂)

/-- Given a left homology map data for morphism `φ`, this is the induced left homology
map data for `-φ`. -/
@[simps]
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : LeftHomologyMapData (-φ) h₁ h₂ where
  body: -γ.φK
  φH := -γ.φH

中文:
定义 neg
  签名: : LeftHomologyMapData (-φ) h₁ h₂ where
  定义体: -γ.φK
  φH := -γ.φH
-/
def neg : LeftHomologyMapData (-φ) h₁ h₂ where
  φK := -γ.φK
  φH := -γ.φH

/-- Given left homology map data for morphisms `φ` and `φ'`, this is
the induced left homology map data for `φ + φ'`. -/
@[simps]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : LeftHomologyMapData (φ + φ') h₁ h₂ where
  body: γ.φK + γ'.φK
  φH := γ.φH + γ'.φH

中文:
定义 add
  签名: : LeftHomologyMapData (φ + φ') h₁ h₂ where
  定义体: γ.φK + γ'.φK
  φH := γ.φH + γ'.φH
-/
def add : LeftHomologyMapData (φ + φ') h₁ h₂ where
  φK := γ.φK + γ'.φK
  φH := γ.φH + γ'.φH

end LeftHomologyMapData

variable (h₁ h₂)

@[simp]
/--
lemma `leftHomologyMap'_neg` / 引理 `leftHomologyMap'_neg`

English:
lemma leftHomologyMap'_neg
  proof: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ.neg.leftHomologyMap'_eq, LeftHomologyMapData.neg_φH]

@[simp]

中文:
引理 leftHomologyMap'_neg
  证明: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ.neg.leftHomologyMap'_eq, LeftHomologyMapData.neg_φH]

@[simp]
-/
lemma leftHomologyMap'_neg :
    leftHomologyMap' (-φ) h₁ h₂ = -leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ.neg.leftHomologyMap'_eq, LeftHomologyMapData.neg_φH]

@[simp]
/--
lemma `cyclesMap'_neg` / 引理 `cyclesMap'_neg`

English:
lemma cyclesMap'_neg
  proof: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ.neg.cyclesMap'_eq, LeftHomologyMapData.neg_φK]

@[simp]

中文:
引理 cyclesMap'_neg
  证明: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ.neg.cyclesMap'_eq, LeftHomologyMapData.neg_φK]

@[simp]
-/
lemma cyclesMap'_neg :
    cyclesMap' (-φ) h₁ h₂ = -cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ.neg.cyclesMap'_eq, LeftHomologyMapData.neg_φK]

@[simp]
/--
lemma `leftHomologyMap'_add` / 引理 `leftHomologyMap'_add`

English:
lemma leftHomologyMap'_add
  proof: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ'.leftHomologyMap'_eq,
    (γ.add γ').leftHomologyMap'_eq, LeftHomologyMapData.add_φH]

@[simp]

中文:
引理 leftHomologyMap'_add
  证明: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ'.leftHomologyMap'_eq,
    (γ.add γ').leftHomologyMap'_eq, LeftHomologyMapData.add_φH]

@[simp]
-/
lemma leftHomologyMap'_add :
    leftHomologyMap' (φ + φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ +
      leftHomologyMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ'.leftHomologyMap'_eq,
    (γ.add γ').leftHomologyMap'_eq, LeftHomologyMapData.add_φH]

@[simp]
/--
lemma `cyclesMap'_add` / 引理 `cyclesMap'_add`

English:
lemma cyclesMap'_add
  proof: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ'.cyclesMap'_eq,
    (γ.add γ').cyclesMap'_eq, LeftHomologyMapData.add_φK]

@[simp]

中文:
引理 cyclesMap'_add
  证明: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ'.cyclesMap'_eq,
    (γ.add γ').cyclesMap'_eq, LeftHomologyMapData.add_φK]

@[simp]
-/
lemma cyclesMap'_add :
    cyclesMap' (φ + φ') h₁ h₂ = cyclesMap' φ h₁ h₂ +
      cyclesMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ'.cyclesMap'_eq,
    (γ.add γ').cyclesMap'_eq, LeftHomologyMapData.add_φK]

@[simp]
/--
lemma `leftHomologyMap'_sub` / 引理 `leftHomologyMap'_sub`

English:
lemma leftHomologyMap'_sub
  proof: by
  simp only [sub_eq_add_neg, leftHomologyMap'_add, leftHomologyMap'_neg]

@[simp]

中文:
引理 leftHomologyMap'_sub
  证明: by
  simp only [sub_eq_add_neg, leftHomologyMap'_add, leftHomologyMap'_neg]

@[simp]
-/
lemma leftHomologyMap'_sub :
    leftHomologyMap' (φ - φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ -
      leftHomologyMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, leftHomologyMap'_add, leftHomologyMap'_neg]

@[simp]
/--
lemma `cyclesMap'_sub` / 引理 `cyclesMap'_sub`

English:
lemma cyclesMap'_sub
  proof: by
  simp only [sub_eq_add_neg, cyclesMap'_add, cyclesMap'_neg]

中文:
引理 cyclesMap'_sub
  证明: by
  simp only [sub_eq_add_neg, cyclesMap'_add, cyclesMap'_neg]
-/
lemma cyclesMap'_sub :
    cyclesMap' (φ - φ') h₁ h₂ = cyclesMap' φ h₁ h₂ -
      cyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, cyclesMap'_add, cyclesMap'_neg]

variable (φ φ')

section

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

@[simp]
/--
lemma `leftHomologyMap_neg` / 引理 `leftHomologyMap_neg`

English:
lemma leftHomologyMap_neg
  statement: leftHomologyMap (-φ) = -leftHomologyMap φ
  proof: leftHomologyMap'_neg _ _

@[simp]

中文:
引理 leftHomologyMap_neg
  结论: leftHomologyMap (-φ) = -leftHomologyMap φ
  证明: leftHomologyMap'_neg _ _

@[simp]

Depends on / 依赖: _neg, leftHomologyMap
-/
lemma leftHomologyMap_neg : leftHomologyMap (-φ) = -leftHomologyMap φ :=
  leftHomologyMap'_neg _ _

@[simp]
/--
lemma `cyclesMap_neg` / 引理 `cyclesMap_neg`

English:
lemma cyclesMap_neg
  statement: cyclesMap (-φ) = -cyclesMap φ
  proof: cyclesMap'_neg _ _

@[simp]

中文:
引理 cyclesMap_neg
  结论: cyclesMap (-φ) = -cyclesMap φ
  证明: cyclesMap'_neg _ _

@[simp]

Depends on / 依赖: _neg, cyclesMap
-/
lemma cyclesMap_neg : cyclesMap (-φ) = -cyclesMap φ :=
  cyclesMap'_neg _ _

@[simp]
/--
lemma `leftHomologyMap_add` / 引理 `leftHomologyMap_add`

English:
lemma leftHomologyMap_add
  statement: leftHomologyMap (φ + φ') = leftHomologyMap φ + leftHomologyMap φ'
  proof: leftHomologyMap'_add _ _

@[simp]

中文:
引理 leftHomologyMap_add
  结论: leftHomologyMap (φ + φ') = leftHomologyMap φ + leftHomologyMap φ'
  证明: leftHomologyMap'_add _ _

@[simp]

Depends on / 依赖: _add, leftHomologyMap
-/
lemma leftHomologyMap_add : leftHomologyMap (φ + φ') = leftHomologyMap φ + leftHomologyMap φ' :=
  leftHomologyMap'_add _ _

@[simp]
/--
lemma `cyclesMap_add` / 引理 `cyclesMap_add`

English:
lemma cyclesMap_add
  statement: cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ'
  proof: cyclesMap'_add _ _

@[simp]

中文:
引理 cyclesMap_add
  结论: cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ'
  证明: cyclesMap'_add _ _

@[simp]

Depends on / 依赖: _add, cyclesMap
-/
lemma cyclesMap_add : cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ' :=
  cyclesMap'_add _ _

@[simp]
/--
lemma `leftHomologyMap_sub` / 引理 `leftHomologyMap_sub`

English:
lemma leftHomologyMap_sub
  statement: leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ'
  proof: leftHomologyMap'_sub _ _

@[simp]

中文:
引理 leftHomologyMap_sub
  结论: leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ'
  证明: leftHomologyMap'_sub _ _

@[simp]

Depends on / 依赖: _sub, leftHomologyMap
-/
lemma leftHomologyMap_sub : leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ' :=
  leftHomologyMap'_sub _ _

@[simp]
/--
lemma `cyclesMap_sub` / 引理 `cyclesMap_sub`

English:
lemma cyclesMap_sub
  statement: cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ'
  proof: cyclesMap'_sub _ _

中文:
引理 cyclesMap_sub
  结论: cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ'
  证明: cyclesMap'_sub _ _

Depends on / 依赖: _sub, cyclesMap
-/
lemma cyclesMap_sub : cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ' :=
  cyclesMap'_sub _ _

end

/--
Instance `leftHomologyFunctor_additive` / 实例 `leftHomologyFunctor_additive`

English:
instance leftHomologyFunctor_additive
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 leftHomologyFunctor_additive
  签名: [HasKernels C] [HasCokernels C]
-/
instance leftHomologyFunctor_additive [HasKernels C] [HasCokernels C] :
    (leftHomologyFunctor C).Additive where

/--
Instance `cyclesFunctor_additive` / 实例 `cyclesFunctor_additive`

English:
instance cyclesFunctor_additive
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 cyclesFunctor_additive
  签名: [HasKernels C] [HasCokernels C]
-/
instance cyclesFunctor_additive [HasKernels C] [HasCokernels C] : (cyclesFunctor C).Additive where

end LeftHomology


section RightHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

namespace RightHomologyMapData

variable (γ : RightHomologyMapData φ h₁ h₂) (γ' : RightHomologyMapData φ' h₁ h₂)

/-- Given a right homology map data for morphism `φ`, this is the induced right homology
map data for `-φ`. -/
@[simps]
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : RightHomologyMapData (-φ) h₁ h₂ where
  body: -γ.φQ
  φH := -γ.φH

中文:
定义 neg
  签名: : RightHomologyMapData (-φ) h₁ h₂ where
  定义体: -γ.φQ
  φH := -γ.φH
-/
def neg : RightHomologyMapData (-φ) h₁ h₂ where
  φQ := -γ.φQ
  φH := -γ.φH

/-- Given right homology map data for morphisms `φ` and `φ'`, this is the induced
right homology map data for `φ + φ'`. -/
@[simps]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : RightHomologyMapData (φ + φ') h₁ h₂ where
  body: γ.φQ + γ'.φQ
  φH := γ.φH + γ'.φH

中文:
定义 add
  签名: : RightHomologyMapData (φ + φ') h₁ h₂ where
  定义体: γ.φQ + γ'.φQ
  φH := γ.φH + γ'.φH
-/
def add : RightHomologyMapData (φ + φ') h₁ h₂ where
  φQ := γ.φQ + γ'.φQ
  φH := γ.φH + γ'.φH

end RightHomologyMapData

variable (h₁ h₂)

@[simp]
/--
lemma `rightHomologyMap'_neg` / 引理 `rightHomologyMap'_neg`

English:
lemma rightHomologyMap'_neg
  proof: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ.neg.rightHomologyMap'_eq, RightHomologyMapData.neg_φH]

@[simp]

中文:
引理 rightHomologyMap'_neg
  证明: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ.neg.rightHomologyMap'_eq, RightHomologyMapData.neg_φH]

@[simp]
-/
lemma rightHomologyMap'_neg :
    rightHomologyMap' (-φ) h₁ h₂ = -rightHomologyMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ.neg.rightHomologyMap'_eq, RightHomologyMapData.neg_φH]

@[simp]
/--
lemma `opcyclesMap'_neg` / 引理 `opcyclesMap'_neg`

English:
lemma opcyclesMap'_neg
  proof: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ.neg.opcyclesMap'_eq, RightHomologyMapData.neg_φQ]

@[simp]

中文:
引理 opcyclesMap'_neg
  证明: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ.neg.opcyclesMap'_eq, RightHomologyMapData.neg_φQ]

@[simp]
-/
lemma opcyclesMap'_neg :
    opcyclesMap' (-φ) h₁ h₂ = -opcyclesMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ.neg.opcyclesMap'_eq, RightHomologyMapData.neg_φQ]

@[simp]
/--
lemma `rightHomologyMap'_add` / 引理 `rightHomologyMap'_add`

English:
lemma rightHomologyMap'_add
  proof: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ'.rightHomologyMap'_eq,
    (γ.add γ').rightHomologyMap'_eq, RightHomologyMapData.add_φH]

@[simp]

中文:
引理 rightHomologyMap'_add
  证明: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ'.rightHomologyMap'_eq,
    (γ.add γ').rightHomologyMap'_eq, RightHomologyMapData.add_φH]

@[simp]
-/
lemma rightHomologyMap'_add :
    rightHomologyMap' (φ + φ') h₁ h₂ = rightHomologyMap' φ h₁ h₂ +
      rightHomologyMap' φ' h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ'.rightHomologyMap'_eq,
    (γ.add γ').rightHomologyMap'_eq, RightHomologyMapData.add_φH]

@[simp]
/--
lemma `opcyclesMap'_add` / 引理 `opcyclesMap'_add`

English:
lemma opcyclesMap'_add
  proof: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ'.opcyclesMap'_eq,
    (γ.add γ').opcyclesMap'_eq, RightHomologyMapData.add_φQ]

@[simp]

中文:
引理 opcyclesMap'_add
  证明: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ'.opcyclesMap'_eq,
    (γ.add γ').opcyclesMap'_eq, RightHomologyMapData.add_φQ]

@[simp]
-/
lemma opcyclesMap'_add :
    opcyclesMap' (φ + φ') h₁ h₂ = opcyclesMap' φ h₁ h₂ +
      opcyclesMap' φ' h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ'.opcyclesMap'_eq,
    (γ.add γ').opcyclesMap'_eq, RightHomologyMapData.add_φQ]

@[simp]
/--
lemma `rightHomologyMap'_sub` / 引理 `rightHomologyMap'_sub`

English:
lemma rightHomologyMap'_sub
  proof: by
  simp only [sub_eq_add_neg, rightHomologyMap'_add, rightHomologyMap'_neg]

@[simp]

中文:
引理 rightHomologyMap'_sub
  证明: by
  simp only [sub_eq_add_neg, rightHomologyMap'_add, rightHomologyMap'_neg]

@[simp]
-/
lemma rightHomologyMap'_sub :
    rightHomologyMap' (φ - φ') h₁ h₂ = rightHomologyMap' φ h₁ h₂ -
      rightHomologyMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, rightHomologyMap'_add, rightHomologyMap'_neg]

@[simp]
/--
lemma `opcyclesMap'_sub` / 引理 `opcyclesMap'_sub`

English:
lemma opcyclesMap'_sub
  proof: by
  simp only [sub_eq_add_neg, opcyclesMap'_add, opcyclesMap'_neg]

中文:
引理 opcyclesMap'_sub
  证明: by
  simp only [sub_eq_add_neg, opcyclesMap'_add, opcyclesMap'_neg]
-/
lemma opcyclesMap'_sub :
    opcyclesMap' (φ - φ') h₁ h₂ = opcyclesMap' φ h₁ h₂ -
      opcyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, opcyclesMap'_add, opcyclesMap'_neg]

variable (φ φ')

section

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

@[simp]
/--
lemma `rightHomologyMap_neg` / 引理 `rightHomologyMap_neg`

English:
lemma rightHomologyMap_neg
  statement: rightHomologyMap (-φ) = -rightHomologyMap φ
  proof: rightHomologyMap'_neg _ _

@[simp]

中文:
引理 rightHomologyMap_neg
  结论: rightHomologyMap (-φ) = -rightHomologyMap φ
  证明: rightHomologyMap'_neg _ _

@[simp]

Depends on / 依赖: _neg, rightHomologyMap
-/
lemma rightHomologyMap_neg : rightHomologyMap (-φ) = -rightHomologyMap φ :=
  rightHomologyMap'_neg _ _

@[simp]
/--
lemma `opcyclesMap_neg` / 引理 `opcyclesMap_neg`

English:
lemma opcyclesMap_neg
  statement: opcyclesMap (-φ) = -opcyclesMap φ
  proof: opcyclesMap'_neg _ _

@[simp]

中文:
引理 opcyclesMap_neg
  结论: opcyclesMap (-φ) = -opcyclesMap φ
  证明: opcyclesMap'_neg _ _

@[simp]

Depends on / 依赖: _neg, opcyclesMap
-/
lemma opcyclesMap_neg : opcyclesMap (-φ) = -opcyclesMap φ :=
  opcyclesMap'_neg _ _

@[simp]
/--
lemma `rightHomologyMap_add` / 引理 `rightHomologyMap_add`

English:
lemma rightHomologyMap_add
  proof: rightHomologyMap'_add _ _

@[simp]

中文:
引理 rightHomologyMap_add
  证明: rightHomologyMap'_add _ _

@[simp]

Depends on / 依赖: _add, h.smul, neg_one_smul, rightHomologyMap
-/
lemma rightHomologyMap_add :
    rightHomologyMap (φ + φ') = rightHomologyMap φ + rightHomologyMap φ' :=
  rightHomologyMap'_add _ _

@[simp]
/--
lemma `opcyclesMap_add` / 引理 `opcyclesMap_add`

English:
lemma opcyclesMap_add
  statement: opcyclesMap (φ + φ') = opcyclesMap φ + opcyclesMap φ'
  proof: opcyclesMap'_add _ _

@[simp]

中文:
引理 opcyclesMap_add
  结论: opcyclesMap (φ + φ') = opcyclesMap φ + opcyclesMap φ'
  证明: opcyclesMap'_add _ _

@[simp]

Depends on / 依赖: _add, opcyclesMap
-/
lemma opcyclesMap_add : opcyclesMap (φ + φ') = opcyclesMap φ + opcyclesMap φ' :=
  opcyclesMap'_add _ _

@[simp]
/--
lemma `rightHomologyMap_sub` / 引理 `rightHomologyMap_sub`

English:
lemma rightHomologyMap_sub
  proof: rightHomologyMap'_sub _ _

@[simp]

中文:
引理 rightHomologyMap_sub
  证明: rightHomologyMap'_sub _ _

@[simp]

Depends on / 依赖: _sub, rightHomologyMap
-/
lemma rightHomologyMap_sub :
    rightHomologyMap (φ - φ') = rightHomologyMap φ - rightHomologyMap φ' :=
  rightHomologyMap'_sub _ _

@[simp]
/--
lemma `opcyclesMap_sub` / 引理 `opcyclesMap_sub`

English:
lemma opcyclesMap_sub
  statement: opcyclesMap (φ - φ') = opcyclesMap φ - opcyclesMap φ'
  proof: opcyclesMap'_sub _ _

中文:
引理 opcyclesMap_sub
  结论: opcyclesMap (φ - φ') = opcyclesMap φ - opcyclesMap φ'
  证明: opcyclesMap'_sub _ _

Depends on / 依赖: _sub, opcyclesMap
-/
lemma opcyclesMap_sub : opcyclesMap (φ - φ') = opcyclesMap φ - opcyclesMap φ' :=
  opcyclesMap'_sub _ _

end

/--
Instance `rightHomologyFunctor_additive` / 实例 `rightHomologyFunctor_additive`

English:
instance rightHomologyFunctor_additive
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 rightHomologyFunctor_additive
  签名: [HasKernels C] [HasCokernels C]
-/
instance rightHomologyFunctor_additive [HasKernels C] [HasCokernels C] :
    (rightHomologyFunctor C).Additive where

/--
Instance `opcyclesFunctor_additive` / 实例 `opcyclesFunctor_additive`

English:
instance opcyclesFunctor_additive
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 opcyclesFunctor_additive
  签名: [HasKernels C] [HasCokernels C]
-/
instance opcyclesFunctor_additive [HasKernels C] [HasCokernels C] :
    (opcyclesFunctor C).Additive where

end RightHomology

section Homology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

namespace HomologyMapData

variable (γ : HomologyMapData φ h₁ h₂) (γ' : HomologyMapData φ' h₁ h₂)

/-- Given a homology map data for a morphism `φ`, this is the induced homology
map data for `-φ`. -/
@[simps]
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : HomologyMapData (-φ) h₁ h₂ where
  body: γ.left.neg
  right := γ.right.neg

中文:
定义 neg
  签名: : HomologyMapData (-φ) h₁ h₂ where
  定义体: γ.left.neg
  right := γ.right.neg

Depends on / 依赖: Quot.map, Rel.smulOfTower, left.neg, smulOfTower
-/
def neg : HomologyMapData (-φ) h₁ h₂ where
  left := γ.left.neg
  right := γ.right.neg

/-- Given homology map data for morphisms `φ` and `φ'`, this is the induced homology
map data for `φ + φ'`. -/
@[simps]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : HomologyMapData (φ + φ') h₁ h₂ where
  body: γ.left.add γ'.left
  right := γ.right.add γ'.right

中文:
定义 add
  签名: : HomologyMapData (φ + φ') h₁ h₂ where
  定义体: γ.left.add γ'.left
  right := γ.right.add γ'.right

Depends on / 依赖: Quot.ind, Quot.mk, congr_arg, left.add, op_smul_eq_smul
-/
def add : HomologyMapData (φ + φ') h₁ h₂ where
  left := γ.left.add γ'.left
  right := γ.right.add γ'.right

end HomologyMapData

variable (h₁ h₂)

@[simp]
/--
lemma `homologyMap'_neg` / 引理 `homologyMap'_neg`

English:
lemma homologyMap'_neg
  proof: leftHomologyMap'_neg _ _

@[simp]

中文:
引理 homologyMap'_neg
  证明: leftHomologyMap'_neg _ _

@[simp]
-/
lemma homologyMap'_neg :
    homologyMap' (-φ) h₁ h₂ = -homologyMap' φ h₁ h₂ :=
  leftHomologyMap'_neg _ _

@[simp]
/--
lemma `homologyMap'_add` / 引理 `homologyMap'_add`

English:
lemma homologyMap'_add
  proof: leftHomologyMap'_add _ _

@[simp]

中文:
引理 homologyMap'_add
  证明: leftHomologyMap'_add _ _

@[simp]
-/
lemma homologyMap'_add :
    homologyMap' (φ + φ') h₁ h₂ = homologyMap' φ h₁ h₂ + homologyMap' φ' h₁ h₂ :=
  leftHomologyMap'_add _ _

@[simp]
/--
lemma `homologyMap'_sub` / 引理 `homologyMap'_sub`

English:
lemma homologyMap'_sub
  proof: leftHomologyMap'_sub _ _

中文:
引理 homologyMap'_sub
  证明: leftHomologyMap'_sub _ _
-/
lemma homologyMap'_sub :
    homologyMap' (φ - φ') h₁ h₂ = homologyMap' φ h₁ h₂ - homologyMap' φ' h₁ h₂ :=
  leftHomologyMap'_sub _ _

variable (φ φ')

section

variable [S₁.HasHomology] [S₂.HasHomology]

@[simp]
/--
lemma `homologyMap_neg` / 引理 `homologyMap_neg`

English:
lemma homologyMap_neg
  statement: homologyMap (-φ) = -homologyMap φ
  proof: homologyMap'_neg _ _

@[simp]

中文:
引理 homologyMap_neg
  结论: homologyMap (-φ) = -homologyMap φ
  证明: homologyMap'_neg _ _

@[simp]

Depends on / 依赖: _neg, homologyMap
-/
lemma homologyMap_neg : homologyMap (-φ) = -homologyMap φ :=
  homologyMap'_neg _ _

@[simp]
/--
lemma `homologyMap_add` / 引理 `homologyMap_add`

English:
lemma homologyMap_add
  statement: homologyMap (φ + φ') = homologyMap φ + homologyMap φ'
  proof: homologyMap'_add _ _

@[simp]

中文:
引理 homologyMap_add
  结论: homologyMap (φ + φ') = homologyMap φ + homologyMap φ'
  证明: homologyMap'_add _ _

@[simp]

Depends on / 依赖: _add, homologyMap
-/
lemma homologyMap_add : homologyMap (φ + φ') = homologyMap φ + homologyMap φ' :=
  homologyMap'_add _ _

@[simp]
/--
lemma `homologyMap_sub` / 引理 `homologyMap_sub`

English:
lemma homologyMap_sub
  statement: homologyMap (φ - φ') = homologyMap φ - homologyMap φ'
  proof: homologyMap'_sub _ _

中文:
引理 homologyMap_sub
  结论: homologyMap (φ - φ') = homologyMap φ - homologyMap φ'
  证明: homologyMap'_sub _ _

Depends on / 依赖: _sub, homologyMap
-/
lemma homologyMap_sub : homologyMap (φ - φ') = homologyMap φ - homologyMap φ' :=
  homologyMap'_sub _ _

end

/--
Instance `homologyFunctor_additive` / 实例 `homologyFunctor_additive`

English:
instance homologyFunctor_additive
  signature: [CategoryWithHomology C]

中文:
实例 homologyFunctor_additive
  签名: [CategoryWithHomology C]
-/
instance homologyFunctor_additive [CategoryWithHomology C] : (homologyFunctor C).Additive where

end Homology

section Homotopy

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

/-- A homotopy between two morphisms of short complexes `S₁ ⟶ S₂` consists of various
maps and conditions which will be sufficient to show that they induce the same morphism
in homology. -/
@[ext]
/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
structure Homotopy
  parameters: where
  axioms and operations (9):
    - h₀ : S₁.X₁ ⟶ S₂.X₁
    - h₀_f : h₀ ≫ S₂.f = 0  [default: by cat_disch]
    - h₁ : S₁.X₂ ⟶ S₂.X₁
    - h₂ : S₁.X₃ ⟶ S₂.X₂
    - h₃ : S₁.X₃ ⟶ S₂.X₃
    - g_h₃ : S₁.g ≫ h₃ = 0  [default: by cat_disch]
    - comm₁ : φ₁.τ₁ = S₁.f ≫ h₁ + h₀ + φ₂.τ₁  [default: by cat_disch]
    - comm₂ : φ₁.τ₂ = S₁.g ≫ h₂ + h₁ ≫ S₂.f + φ₂.τ₂  [default: by cat_disch]
    - comm₃ : φ₁.τ₃ = h₃ + h₂ ≫ S₂.g + φ₂.τ₃  [default: by cat_disch]

中文:
结构 Homotopy
  参数: where
  公理与运算 (9 个):
    - h₀ : S₁.X₁ ⟶ S₂.X₁
    - h₀_f : h₀ ≫ S₂.f = 0  [默认: by cat_disch]
    - h₁ : S₁.X₂ ⟶ S₂.X₁
    - h₂ : S₁.X₃ ⟶ S₂.X₂
    - h₃ : S₁.X₃ ⟶ S₂.X₃
    - g_h₃ : S₁.g ≫ h₃ = 0  [默认: by cat_disch]
    - comm₁ : φ₁.τ₁ = S₁.f ≫ h₁ + h₀ + φ₂.τ₁  [默认: by cat_disch]
    - comm₂ : φ₁.τ₂ = S₁.g ≫ h₂ + h₁ ≫ S₂.f + φ₂.τ₂  [默认: by cat_disch]
    - comm₃ : φ₁.τ₃ = h₃ + h₂ ≫ S₂.g + φ₂.τ₃  [默认: by cat_disch]

Depends on / 依赖: Function, Function.Surjective.module, Quot.mk, Quot.mk_surjective, Surjective, cat_disch, mk_surjective, module
-/
structure Homotopy where
  /-- a morphism `S₁.X₁ ⟶ S₂.X₁` -/
  h₀ : S₁.X₁ ⟶ S₂.X₁
  h₀_f : h₀ ≫ S₂.f = 0 := by cat_disch
  /-- a morphism `S₁.X₂ ⟶ S₂.X₁` -/
  h₁ : S₁.X₂ ⟶ S₂.X₁
  /-- a morphism `S₁.X₃ ⟶ S₂.X₂` -/
  h₂ : S₁.X₃ ⟶ S₂.X₂
  /-- a morphism `S₁.X₃ ⟶ S₂.X₃` -/
  h₃ : S₁.X₃ ⟶ S₂.X₃
  g_h₃ : S₁.g ≫ h₃ = 0 := by cat_disch
  comm₁ : φ₁.τ₁ = S₁.f ≫ h₁ + h₀ + φ₂.τ₁ := by cat_disch
  comm₂ : φ₁.τ₂ = S₁.g ≫ h₂ + h₁ ≫ S₂.f + φ₂.τ₂ := by cat_disch
  comm₃ : φ₁.τ₃ = h₃ + h₂ ≫ S₂.g + φ₂.τ₃ := by cat_disch

attribute [reassoc (attr := simp)] Homotopy.h₀_f Homotopy.g_h₃

variable (S₁ S₂)

/-- Constructor for null homotopic morphisms, see also `Homotopy.ofNullHomotopic`
and `Homotopy.eq_add_nullHomotopic`. -/
@[simps]
/--
Definition of `nullHomotopic` / `nullHomotopic` 的定义

English:
definition nullHomotopic
  signature: (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  body: h₀ + S₁.f ≫ h₁
  τ₂ := h₁ ≫ S₂.f + S₁.g ≫ h₂
  τ₃ := h₂ ≫ S₂.g + h₃

中文:
定义 nullHomotopic
  签名: (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  定义体: h₀ + S₁.f ≫ h₁
  τ₂ := h₁ ≫ S₂.f + S₁.g ≫ h₂
  τ₃ := h₂ ≫ S₂.g + h₃
-/
def nullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    S₁ ⟶ S₂ where
  τ₁ := h₀ + S₁.f ≫ h₁
  τ₂ := h₁ ≫ S₂.f + S₁.g ≫ h₂
  τ₃ := h₂ ≫ S₂.g + h₃

namespace Homotopy

attribute [local simp] neg_comp

variable {S₁ S₂ φ₁ φ₂ φ₃ φ₄}

/-- The obvious homotopy between two equal morphisms of short complexes. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : φ₁ = φ₂)
  body: 0
  h₁ := 0
  h₂ := 0
  h₃ := 0

中文:
定义 ofEq
  签名: (h : φ₁ = φ₂)
  定义体: 0
  h₁ := 0
  h₂ := 0
  h₃ := 0
-/
def ofEq (h : φ₁ = φ₂) : Homotopy φ₁ φ₂ where
  h₀ := 0
  h₁ := 0
  h₂ := 0
  h₃ := 0

/-- The obvious homotopy between a morphism of short complexes and itself. -/
@[simps!]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (φ : S₁ ⟶ S₂)
  body: ofEq rfl

中文:
定义 refl
  签名: (φ : S₁ ⟶ S₂)
  定义体: ofEq rfl
-/
def refl (φ : S₁ ⟶ S₂) : Homotopy φ φ := ofEq rfl

/-- The symmetry of homotopy between morphisms of short complexes. -/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (h : Homotopy φ₁ φ₂)
  body: -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [h.comm₁, comp_neg]; abel
  comm₂ := by rw [h.comm₂, comp_neg, neg_comp]; abel
  comm₃ := by rw [h.comm₃, neg_comp]; abel

中文:
定义 symm
  签名: (h : Homotopy φ₁ φ₂)
  定义体: -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [h.comm₁, comp_neg]; abel
  comm₂ := by rw [h.comm₂, comp_neg, neg_comp]; abel
  comm₃ := by rw [h.comm₃, neg_comp]; abel
-/
def symm (h : Homotopy φ₁ φ₂) : Homotopy φ₂ φ₁ where
  h₀ := -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [h.comm₁, comp_neg]; abel
  comm₂ := by rw [h.comm₂, comp_neg, neg_comp]; abel
  comm₃ := by rw [h.comm₃, neg_comp]; abel

/-- If two maps of short complexes are homotopic, their opposites also are. -/
@[simps]
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: (h : Homotopy φ₁ φ₂)
  body: -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [neg_τ₁, neg_τ₁, h.comm₁, neg_add_rev, comp_neg]; abel
  comm₂ := by rw [neg_τ₂, neg_τ₂, h.comm₂, neg_add_rev, comp_neg, neg_comp]; abel
  comm₃ := by rw [neg_τ₃, neg_τ₃, h.comm₃, neg_comp]; abel

中文:
定义 neg
  签名: (h : Homotopy φ₁ φ₂)
  定义体: -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [neg_τ₁, neg_τ₁, h.comm₁, neg_add_rev, comp_neg]; abel
  comm₂ := by rw [neg_τ₂, neg_τ₂, h.comm₂, neg_add_rev, comp_neg, neg_comp]; abel
  comm₃ := by rw [neg_τ₃, neg_τ₃, h.comm₃, neg_comp]; abel
-/
def neg (h : Homotopy φ₁ φ₂) : Homotopy (-φ₁) (-φ₂) where
  h₀ := -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [neg_τ₁, neg_τ₁, h.comm₁, neg_add_rev, comp_neg]; abel
  comm₂ := by rw [neg_τ₂, neg_τ₂, h.comm₂, neg_add_rev, comp_neg, neg_comp]; abel
  comm₃ := by rw [neg_τ₃, neg_τ₃, h.comm₃, neg_comp]; abel

/-- The transitivity of homotopy between morphisms of short complexes. -/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (h₁₂ : Homotopy φ₁ φ₂) (h₂₃ : Homotopy φ₂ φ₃)
  body: h₁₂.h₀ + h₂₃.h₀
  h₁ := h₁₂.h₁ + h₂₃.h₁
  h₂ := h₁₂.h₂ + h₂₃.h₂
  h₃ := h₁₂.h₃ + h₂₃.h₃
  comm₁ := by rw [h₁₂.comm₁, h₂₃.comm₁, comp_add]; abel
  comm₂ := by rw [h₁₂.comm₂, h₂₃.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [h₁₂.comm₃, h₂₃.comm₃, add_comp]; abel

中文:
定义 trans
  签名: (h₁₂ : Homotopy φ₁ φ₂) (h₂₃ : Homotopy φ₂ φ₃)
  定义体: h₁₂.h₀ + h₂₃.h₀
  h₁ := h₁₂.h₁ + h₂₃.h₁
  h₂ := h₁₂.h₂ + h₂₃.h₂
  h₃ := h₁₂.h₃ + h₂₃.h₃
  comm₁ := by rw [h₁₂.comm₁, h₂₃.comm₁, comp_add]; abel
  comm₂ := by rw [h₁₂.comm₂, h₂₃.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [h₁₂.comm₃, h₂₃.comm₃, add_comp]; abel
-/
def trans (h₁₂ : Homotopy φ₁ φ₂) (h₂₃ : Homotopy φ₂ φ₃) : Homotopy φ₁ φ₃ where
  h₀ := h₁₂.h₀ + h₂₃.h₀
  h₁ := h₁₂.h₁ + h₂₃.h₁
  h₂ := h₁₂.h₂ + h₂₃.h₂
  h₃ := h₁₂.h₃ + h₂₃.h₃
  comm₁ := by rw [h₁₂.comm₁, h₂₃.comm₁, comp_add]; abel
  comm₂ := by rw [h₁₂.comm₂, h₂₃.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [h₁₂.comm₃, h₂₃.comm₃, add_comp]; abel

/-- Homotopy between morphisms of short complexes is compatible with addition. -/
@[simps]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄)
  body: h.h₀ + h'.h₀
  h₁ := h.h₁ + h'.h₁
  h₂ := h.h₂ + h'.h₂
  h₃ := h.h₃ + h'.h₃
  comm₁ := by rw [add_τ₁, add_τ₁, h.comm₁, h'.comm₁, comp_add]; abel
  comm₂ := by rw [add_τ₂, add_τ₂, h.comm₂, h'.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [add_τ₃, add_τ₃, h.comm₃, h'.comm₃, add_comp]; abel

中文:
定义 add
  签名: (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄)
  定义体: h.h₀ + h'.h₀
  h₁ := h.h₁ + h'.h₁
  h₂ := h.h₂ + h'.h₂
  h₃ := h.h₃ + h'.h₃
  comm₁ := by rw [add_τ₁, add_τ₁, h.comm₁, h'.comm₁, comp_add]; abel
  comm₂ := by rw [add_τ₂, add_τ₂, h.comm₂, h'.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [add_τ₃, add_τ₃, h.comm₃, h'.comm₃, add_comp]; abel
-/
def add (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ + φ₃) (φ₂ + φ₄) where
  h₀ := h.h₀ + h'.h₀
  h₁ := h.h₁ + h'.h₁
  h₂ := h.h₂ + h'.h₂
  h₃ := h.h₃ + h'.h₃
  comm₁ := by rw [add_τ₁, add_τ₁, h.comm₁, h'.comm₁, comp_add]; abel
  comm₂ := by rw [add_τ₂, add_τ₂, h.comm₂, h'.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [add_τ₃, add_τ₃, h.comm₃, h'.comm₃, add_comp]; abel

/-- Homotopy between morphisms of short complexes is compatible with subtraction. -/
@[simps]
/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄)
  body: h.h₀ - h'.h₀
  h₁ := h.h₁ - h'.h₁
  h₂ := h.h₂ - h'.h₂
  h₃ := h.h₃ - h'.h₃
  comm₁ := by rw [sub_τ₁, sub_τ₁, h.comm₁, h'.comm₁, comp_sub]; abel
  comm₂ := by rw [sub_τ₂, sub_τ₂, h.comm₂, h'.comm₂, comp_sub, sub_comp]; abel
  comm₃ := by rw [sub_τ₃, sub_τ₃, h.comm₃, h'.comm₃, sub_comp]; abel

中文:
定义 sub
  签名: (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄)
  定义体: h.h₀ - h'.h₀
  h₁ := h.h₁ - h'.h₁
  h₂ := h.h₂ - h'.h₂
  h₃ := h.h₃ - h'.h₃
  comm₁ := by rw [sub_τ₁, sub_τ₁, h.comm₁, h'.comm₁, comp_sub]; abel
  comm₂ := by rw [sub_τ₂, sub_τ₂, h.comm₂, h'.comm₂, comp_sub, sub_comp]; abel
  comm₃ := by rw [sub_τ₃, sub_τ₃, h.comm₃, h'.comm₃, sub_comp]; abel
-/
def sub (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ - φ₃) (φ₂ - φ₄) where
  h₀ := h.h₀ - h'.h₀
  h₁ := h.h₁ - h'.h₁
  h₂ := h.h₂ - h'.h₂
  h₃ := h.h₃ - h'.h₃
  comm₁ := by rw [sub_τ₁, sub_τ₁, h.comm₁, h'.comm₁, comp_sub]; abel
  comm₂ := by rw [sub_τ₂, sub_τ₂, h.comm₂, h'.comm₂, comp_sub, sub_comp]; abel
  comm₃ := by rw [sub_τ₃, sub_τ₃, h.comm₃, h'.comm₃, sub_comp]; abel

/-- Homotopy between morphisms of short complexes is compatible with precomposition. -/
@[simps]
/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: (h : Homotopy φ₁ φ₂) (ψ : S₃ ⟶ S₁)
  body: ψ.τ₁ ≫ h.h₀
  h₁ := ψ.τ₂ ≫ h.h₁
  h₂ := ψ.τ₃ ≫ h.h₂
  h₃ := ψ.τ₃ ≫ h.h₃
  g_h₃ := by rw [← ψ.comm₂₃_assoc, h.g_h₃, comp_zero]
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, comp_add, comp_add, add_left_inj, ψ.comm₁₂_assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, comp_add, comp_add, assoc, ψ.comm₂

中文:
定义 compLeft
  签名: (h : Homotopy φ₁ φ₂) (ψ : S₃ ⟶ S₁)
  定义体: ψ.τ₁ ≫ h.h₀
  h₁ := ψ.τ₂ ≫ h.h₁
  h₂ := ψ.τ₃ ≫ h.h₂
  h₃ := ψ.τ₃ ≫ h.h₃
  g_h₃ := by rw [← ψ.comm₂₃_assoc, h.g_h₃, comp_zero]
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, comp_add, comp_add, add_left_inj, ψ.comm₁₂_assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, comp_add, comp_add, assoc, ψ.comm₂
-/
def compLeft (h : Homotopy φ₁ φ₂) (ψ : S₃ ⟶ S₁) : Homotopy (ψ ≫ φ₁) (ψ ≫ φ₂) where
  h₀ := ψ.τ₁ ≫ h.h₀
  h₁ := ψ.τ₂ ≫ h.h₁
  h₂ := ψ.τ₃ ≫ h.h₂
  h₃ := ψ.τ₃ ≫ h.h₃
  g_h₃ := by rw [← ψ.comm₂₃_assoc, h.g_h₃, comp_zero]
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, comp_add, comp_add, add_left_inj, ψ.comm₁₂_assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, comp_add, comp_add, assoc, ψ.comm₂₃_assoc]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, comp_add, comp_add, assoc]

/-- Homotopy between morphisms of short complexes is compatible with postcomposition. -/
@[simps]
/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: (h : Homotopy φ₁ φ₂) (ψ : S₂ ⟶ S₃)
  body: h.h₀ ≫ ψ.τ₁
  h₁ := h.h₁ ≫ ψ.τ₁
  h₂ := h.h₂ ≫ ψ.τ₂
  h₃ := h.h₃ ≫ ψ.τ₃
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, add_comp, add_comp, assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, add_comp, add_comp, assoc, assoc, assoc, ψ.comm₁₂]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, add_comp, add_c

中文:
定义 compRight
  签名: (h : Homotopy φ₁ φ₂) (ψ : S₂ ⟶ S₃)
  定义体: h.h₀ ≫ ψ.τ₁
  h₁ := h.h₁ ≫ ψ.τ₁
  h₂ := h.h₂ ≫ ψ.τ₂
  h₃ := h.h₃ ≫ ψ.τ₃
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, add_comp, add_comp, assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, add_comp, add_comp, assoc, assoc, assoc, ψ.comm₁₂]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, add_comp, add_c
-/
def compRight (h : Homotopy φ₁ φ₂) (ψ : S₂ ⟶ S₃) : Homotopy (φ₁ ≫ ψ) (φ₂ ≫ ψ) where
  h₀ := h.h₀ ≫ ψ.τ₁
  h₁ := h.h₁ ≫ ψ.τ₁
  h₂ := h.h₂ ≫ ψ.τ₂
  h₃ := h.h₃ ≫ ψ.τ₃
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, add_comp, add_comp, assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, add_comp, add_comp, assoc, assoc, assoc, ψ.comm₁₂]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, add_comp, add_comp, assoc, assoc, ψ.comm₂₃]

/-- Homotopy between morphisms of short complexes is compatible with composition. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (h : Homotopy φ₁ φ₂) {ψ₁ ψ₂ : S₂ ⟶ S₃} (h' : Homotopy ψ₁ ψ₂)
  body: (h.compRight ψ₁).trans (h'.compLeft φ₂)

中文:
定义 comp
  签名: (h : Homotopy φ₁ φ₂) {ψ₁ ψ₂ : S₂ ⟶ S₃} (h' : Homotopy ψ₁ ψ₂)
  定义体: (h.compRight ψ₁).trans (h'.compLeft φ₂)

Depends on / 依赖: compLeft, compRight, h.compRight
-/
def comp (h : Homotopy φ₁ φ₂) {ψ₁ ψ₂ : S₂ ⟶ S₃} (h' : Homotopy ψ₁ ψ₂) :
    Homotopy (φ₁ ≫ ψ₁) (φ₂ ≫ ψ₂) :=
  (h.compRight ψ₁).trans (h'.compLeft φ₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy between morphisms in `ShortComplex Cᵒᵖ` that is induced by a homotopy
between morphisms in `ShortComplex C`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (h : Homotopy φ₁ φ₂)
  body: h.h₃.op
  h₁ := h.h₂.op
  h₂ := h.h₁.op
  h₃ := h.h₀.op
  h₀_f := Quiver.Hom.unop_inj h.g_h₃
  g_h₃ := Quiver.Hom.unop_inj h.h₀_f
  comm₁ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.unop_inj (by dsimp; rw [

中文:
定义 op
  签名: (h : Homotopy φ₁ φ₂)
  定义体: h.h₃.op
  h₁ := h.h₂.op
  h₂ := h.h₁.op
  h₃ := h.h₀.op
  h₀_f := Quiver.Hom.unop_inj h.g_h₃
  g_h₃ := Quiver.Hom.unop_inj h.h₀_f
  comm₁ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.unop_inj (by dsimp; rw [
-/
def op (h : Homotopy φ₁ φ₂) : Homotopy (opMap φ₁) (opMap φ₂) where
  h₀ := h.h₃.op
  h₁ := h.h₂.op
  h₂ := h.h₁.op
  h₃ := h.h₀.op
  h₀_f := Quiver.Hom.unop_inj h.g_h₃
  g_h₃ := Quiver.Hom.unop_inj h.h₀_f
  comm₁ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₁]; abel)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy between morphisms in `ShortComplex C` that is induced by a homotopy
between morphisms in `ShortComplex Cᵒᵖ`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {S₁ S₂ : ShortComplex Cᵒᵖ} {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂)
  body: h.h₃.unop
  h₁ := h.h₂.unop
  h₂ := h.h₁.unop
  h₃ := h.h₀.unop
  h₀_f := Quiver.Hom.op_inj h.g_h₃
  g_h₃ := Quiver.Hom.op_inj h.h₀_f
  comm₁ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.op_inj (by dsimp; rw [h.

中文:
定义 unop
  签名: {S₁ S₂ : ShortComplex Cᵒᵖ} {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂)
  定义体: h.h₃.unop
  h₁ := h.h₂.unop
  h₂ := h.h₁.unop
  h₃ := h.h₀.unop
  h₀_f := Quiver.Hom.op_inj h.g_h₃
  g_h₃ := Quiver.Hom.op_inj h.h₀_f
  comm₁ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.op_inj (by dsimp; rw [h.
-/
def unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂) :
    Homotopy (unopMap φ₁) (unopMap φ₂) where
  h₀ := h.h₃.unop
  h₁ := h.h₂.unop
  h₂ := h.h₁.unop
  h₃ := h.h₀.unop
  h₀_f := Quiver.Hom.op_inj h.g_h₃
  g_h₃ := Quiver.Hom.op_inj h.h₀_f
  comm₁ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₁]; abel)

variable (φ₁ φ₂)

/-- Equivalence expressing that two morphisms are homotopic iff
their difference is homotopic to zero. -/
@[simps]
/--
Definition of `equivSubZero` / `equivSubZero` 的定义

English:
definition equivSubZero
  signature: : Homotopy φ₁ φ₂ ≃ Homotopy (φ₁ - φ₂) 0 where
  body: (h.sub (refl φ₂)).trans (ofEq (sub_self φ₂))
  invFun h := ((ofEq (sub_add_cancel φ₁ φ₂).symm).trans
    (h.add (refl φ₂))).trans (ofEq (zero_add φ₂))
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 equivSubZero
  签名: : Homotopy φ₁ φ₂ ≃ Homotopy (φ₁ - φ₂) 0 where
  定义体: (h.sub (refl φ₂)).trans (ofEq (sub_self φ₂))
  invFun h := ((ofEq (sub_add_cancel φ₁ φ₂).symm).trans
    (h.add (refl φ₂))).trans (ofEq (zero_add φ₂))
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: h.sub, sub_self
-/
def equivSubZero : Homotopy φ₁ φ₂ ≃ Homotopy (φ₁ - φ₂) 0 where
  toFun h := (h.sub (refl φ₂)).trans (ofEq (sub_self φ₂))
  invFun h := ((ofEq (sub_add_cancel φ₁ φ₂).symm).trans
    (h.add (refl φ₂))).trans (ofEq (zero_add φ₂))
  left_inv := by cat_disch
  right_inv := by cat_disch

variable {φ₁ φ₂}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `eq_add_nullHomotopic` / 引理 `eq_add_nullHomotopic`

English:
lemma eq_add_nullHomotopic
  given: (h : Homotopy φ₁ φ₂)
  proof: by
  ext
  · dsimp; rw [h.comm₁]; abel
  · dsimp; rw [h.comm₂]; abel
  · dsimp; rw [h.comm₃]; abel

中文:
引理 eq_add_nullHomotopic
  条件: (h : Homotopy φ₁ φ₂)
  证明: by
  ext
  · dsimp; rw [h.comm₁]; abel
  · dsimp; rw [h.comm₂]; abel
  · dsimp; rw [h.comm₃]; abel

Depends on / 依赖: h.comm
-/
lemma eq_add_nullHomotopic (h : Homotopy φ₁ φ₂) :
    φ₁ = φ₂ + nullHomotopic _ _ h.h₀ h.h₀_f h.h₁ h.h₂ h.h₃ h.g_h₃ := by
  ext
  · dsimp; rw [h.comm₁]; abel
  · dsimp; rw [h.comm₂]; abel
  · dsimp; rw [h.comm₃]; abel

variable (S₁ S₂)

/-- A morphism constructed with `nullHomotopic` is homotopic to zero. -/
@[simps]
/--
Definition of `ofNullHomotopic` / `ofNullHomotopic` 的定义

English:
definition ofNullHomotopic
  signature: (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  body: h₀
  h₁ := h₁
  h₂ := h₂
  h₃ := h₃
  h₀_f := h₀_f
  g_h₃ := g_h₃
  comm₁ := by rw [nullHomotopic_τ₁, zero_τ₁, add_zero]; abel
  comm₂ := by rw [nullHomotopic_τ₂, zero_τ₂, add_zero]; abel
  comm₃ := by rw [nullHomotopic_τ₃, zero_τ₃, add_zero]; abel

中文:
定义 ofNullHomotopic
  签名: (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  定义体: h₀
  h₁ := h₁
  h₂ := h₂
  h₃ := h₃
  h₀_f := h₀_f
  g_h₃ := g_h₃
  comm₁ := by rw [nullHomotopic_τ₁, zero_τ₁, add_zero]; abel
  comm₂ := by rw [nullHomotopic_τ₂, zero_τ₂, add_zero]; abel
  comm₃ := by rw [nullHomotopic_τ₃, zero_τ₃, add_zero]; abel
-/
def ofNullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    Homotopy (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) 0 where
  h₀ := h₀
  h₁ := h₁
  h₂ := h₂
  h₃ := h₃
  h₀_f := h₀_f
  g_h₃ := g_h₃
  comm₁ := by rw [nullHomotopic_τ₁, zero_τ₁, add_zero]; abel
  comm₂ := by rw [nullHomotopic_τ₂, zero_τ₂, add_zero]; abel
  comm₃ := by rw [nullHomotopic_τ₃, zero_τ₃, add_zero]; abel

end Homotopy

variable {S₁ S₂}

/--
Definition of `LeftHomologyMapData.ofNullHomotopic` / `LeftHomologyMapData.ofNullHomotopic` 的定义

English:
definition LeftHomologyMapData.ofNullHomotopic
  body: H₂.liftK (H₁.i ≫ h₁ ≫ S₂.f) (by simp)
  φH := 0
  commf' := by
    rw [← cancel_mono H₂.i]; rw [assoc]; rw [LeftHomologyData.liftK_i]; rw [LeftHomologyData.f'_i_assoc]; rw [nullHomotopic_τ₁]; rw [add_comp]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [LeftHomologyData.f'_i]; rw [right_eq_a

中文:
定义 LeftHomologyMapData.ofNullHomotopic
  定义体: H₂.liftK (H₁.i ≫ h₁ ≫ S₂.f) (by simp)
  φH := 0
  commf' := by
    rw [← cancel_mono H₂.i]; rw [assoc]; rw [LeftHomologyData.liftK_i]; rw [LeftHomologyData.f'_i_assoc]; rw [nullHomotopic_τ₁]; rw [add_comp]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [LeftHomologyData.f'_i]; rw [right_eq_a
-/
def LeftHomologyMapData.ofNullHomotopic
    (H₁ : S₁.LeftHomologyData) (H₂ : S₂.LeftHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    LeftHomologyMapData (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ where
  φK := H₂.liftK (H₁.i ≫ h₁ ≫ S₂.f) (by simp)
  φH := 0
  commf' := by
    rw [← cancel_mono H₂.i]; rw [assoc]; rw [LeftHomologyData.liftK_i]; rw [LeftHomologyData.f'_i_assoc]; rw [nullHomotopic_τ₁]; rw [add_comp]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [LeftHomologyData.f'_i]; rw [right_eq_add]; rw [h₀_f]
  commπ := by
    rw [H₂.liftK_π_eq_zero_of_boundary (H₁.i ≫ h₁ ≫ S₂.f) (H₁.i ≫ h₁) (by rw [assoc]), comp_zero]

/--
Definition of `RightHomologyMapData.ofNullHomotopic` / `RightHomologyMapData.ofNullHomotopic` 的定义

English:
definition RightHomologyMapData.ofNullHomotopic
  body: H₁.descQ (S₁.g ≫ h₂ ≫ H₂.p) (by simp)
  φH := 0
  commg' := by
    rw [← cancel_epi H₁.p]; rw [RightHomologyData.p_descQ_assoc]; rw [RightHomologyData.p_g'_assoc]; rw [nullHomotopic_τ₃]; rw [comp_add]; rw [assoc]; rw [assoc]; rw [RightHomologyData.p_g']; rw [g_h₃]; rw [add_zero]
  commι := by
    rw

中文:
定义 RightHomologyMapData.ofNullHomotopic
  定义体: H₁.descQ (S₁.g ≫ h₂ ≫ H₂.p) (by simp)
  φH := 0
  commg' := by
    rw [← cancel_epi H₁.p]; rw [RightHomologyData.p_descQ_assoc]; rw [RightHomologyData.p_g'_assoc]; rw [nullHomotopic_τ₃]; rw [comp_add]; rw [assoc]; rw [assoc]; rw [RightHomologyData.p_g']; rw [g_h₃]; rw [add_zero]
  commι := by
    rw
-/
def RightHomologyMapData.ofNullHomotopic
    (H₁ : S₁.RightHomologyData) (H₂ : S₂.RightHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    RightHomologyMapData (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ where
  φQ := H₁.descQ (S₁.g ≫ h₂ ≫ H₂.p) (by simp)
  φH := 0
  commg' := by
    rw [← cancel_epi H₁.p]; rw [RightHomologyData.p_descQ_assoc]; rw [RightHomologyData.p_g'_assoc]; rw [nullHomotopic_τ₃]; rw [comp_add]; rw [assoc]; rw [assoc]; rw [RightHomologyData.p_g']; rw [g_h₃]; rw [add_zero]
  commι := by
    rw [H₁.ι_descQ_eq_zero_of_boundary (S₁.g ≫ h₂ ≫ H₂.p) (h₂ ≫ H₂.p) rfl]; rw [zero_comp]

@[simp]
/--
lemma `leftHomologyMap'_nullHomotopic` / 引理 `leftHomologyMap'_nullHomotopic`

English:
lemma leftHomologyMap'_nullHomotopic
  proof: (LeftHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).leftHomologyMap'_eq

@[simp]

中文:
引理 leftHomologyMap'_nullHomotopic
  证明: (LeftHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).leftHomologyMap'_eq

@[simp]
-/
lemma leftHomologyMap'_nullHomotopic
    (H₁ : S₁.LeftHomologyData) (H₂ : S₂.LeftHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    leftHomologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
  (LeftHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).leftHomologyMap'_eq

@[simp]
/--
lemma `rightHomologyMap'_nullHomotopic` / 引理 `rightHomologyMap'_nullHomotopic`

English:
lemma rightHomologyMap'_nullHomotopic
  proof: (RightHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).rightHomologyMap'_eq

@[simp]

中文:
引理 rightHomologyMap'_nullHomotopic
  证明: (RightHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).rightHomologyMap'_eq

@[simp]
-/
lemma rightHomologyMap'_nullHomotopic
    (H₁ : S₁.RightHomologyData) (H₂ : S₂.RightHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    rightHomologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
  (RightHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).rightHomologyMap'_eq

@[simp]
/--
lemma `homologyMap'_nullHomotopic` / 引理 `homologyMap'_nullHomotopic`

English:
lemma homologyMap'_nullHomotopic
  proof: by
  apply leftHomologyMap'_nullHomotopic

中文:
引理 homologyMap'_nullHomotopic
  证明: by
  apply leftHomologyMap'_nullHomotopic
-/
lemma homologyMap'_nullHomotopic
    (H₁ : S₁.HomologyData) (H₂ : S₂.HomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    homologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 := by
  apply leftHomologyMap'_nullHomotopic

variable (S₁ S₂)

@[simp]
/--
lemma `leftHomologyMap_nullHomotopic` / 引理 `leftHomologyMap_nullHomotopic`

English:
lemma leftHomologyMap_nullHomotopic
  statement: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  apply leftHomologyMap'_nullHomotopic

@[simp]

中文:
引理 leftHomologyMap_nullHomotopic
  结论: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  证明: by
  apply leftHomologyMap'_nullHomotopic

@[simp]

Depends on / 依赖: _nullHomotopic, leftHomologyMap
-/
lemma leftHomologyMap_nullHomotopic [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    leftHomologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 := by
  apply leftHomologyMap'_nullHomotopic

@[simp]
/--
lemma `rightHomologyMap_nullHomotopic` / 引理 `rightHomologyMap_nullHomotopic`

English:
lemma rightHomologyMap_nullHomotopic
  statement: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  apply rightHomologyMap'_nullHomotopic

@[simp]

中文:
引理 rightHomologyMap_nullHomotopic
  结论: [S₁.HasRightHomology] [S₂.HasRightHomology]
  证明: by
  apply rightHomologyMap'_nullHomotopic

@[simp]

Depends on / 依赖: _nullHomotopic, rightHomologyMap
-/
lemma rightHomologyMap_nullHomotopic [S₁.HasRightHomology] [S₂.HasRightHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    rightHomologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 := by
  apply rightHomologyMap'_nullHomotopic

@[simp]
/--
lemma `homologyMap_nullHomotopic` / 引理 `homologyMap_nullHomotopic`

English:
lemma homologyMap_nullHomotopic
  statement: [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  apply homologyMap'_nullHomotopic

中文:
引理 homologyMap_nullHomotopic
  结论: [S₁.HasHomology] [S₂.HasHomology]
  证明: by
  apply homologyMap'_nullHomotopic

Depends on / 依赖: _nullHomotopic, homologyMap
-/
lemma homologyMap_nullHomotopic [S₁.HasHomology] [S₂.HasHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    homologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 := by
  apply homologyMap'_nullHomotopic

namespace Homotopy

variable {φ₁ φ₂ S₁ S₂}

/--
lemma `leftHomologyMap'_congr` / 引理 `leftHomologyMap'_congr`

English:
lemma leftHomologyMap'_congr
  statement: (h : Homotopy φ₁ φ₂) (h₁ : S₁.LeftHomologyData)
  proof: by
  rw [h.eq_add_nullHomotopic]; rw [leftHomologyMap'_add]; rw [leftHomologyMap'_nullHomotopic]; rw [add_zero]

中文:
引理 leftHomologyMap'_congr
  结论: (h : Homotopy φ₁ φ₂) (h₁ : S₁.LeftHomologyData)
  证明: by
  rw [h.eq_add_nullHomotopic]; rw [leftHomologyMap'_add]; rw [leftHomologyMap'_nullHomotopic]; rw [add_zero]

Depends on / 依赖: _add, _nullHomotopic, add_zero, eq_add_nullHomotopic, h.eq_add_nullHomotopic, leftHomologyMap
-/
lemma leftHomologyMap'_congr (h : Homotopy φ₁ φ₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : leftHomologyMap' φ₁ h₁ h₂ = leftHomologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_nullHomotopic]; rw [leftHomologyMap'_add]; rw [leftHomologyMap'_nullHomotopic]; rw [add_zero]

/--
lemma `rightHomologyMap'_congr` / 引理 `rightHomologyMap'_congr`

English:
lemma rightHomologyMap'_congr
  statement: (h : Homotopy φ₁ φ₂) (h₁ : S₁.RightHomologyData)
  proof: by
  rw [h.eq_add_nullHomotopic]; rw [rightHomologyMap'_add]; rw [rightHomologyMap'_nullHomotopic]; rw [add_zero]

中文:
引理 rightHomologyMap'_congr
  结论: (h : Homotopy φ₁ φ₂) (h₁ : S₁.RightHomologyData)
  证明: by
  rw [h.eq_add_nullHomotopic]; rw [rightHomologyMap'_add]; rw [rightHomologyMap'_nullHomotopic]; rw [add_zero]

Depends on / 依赖: _add, _nullHomotopic, add_zero, eq_add_nullHomotopic, h.eq_add_nullHomotopic, rightHomologyMap
-/
lemma rightHomologyMap'_congr (h : Homotopy φ₁ φ₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : rightHomologyMap' φ₁ h₁ h₂ = rightHomologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_nullHomotopic]; rw [rightHomologyMap'_add]; rw [rightHomologyMap'_nullHomotopic]; rw [add_zero]

/--
lemma `homologyMap'_congr` / 引理 `homologyMap'_congr`

English:
lemma homologyMap'_congr
  statement: (h : Homotopy φ₁ φ₂) (h₁ : S₁.HomologyData)
  proof: by
  rw [h.eq_add_nullHomotopic]; rw [homologyMap'_add]; rw [homologyMap'_nullHomotopic]; rw [add_zero]

中文:
引理 homologyMap'_congr
  结论: (h : Homotopy φ₁ φ₂) (h₁ : S₁.HomologyData)
  证明: by
  rw [h.eq_add_nullHomotopic]; rw [homologyMap'_add]; rw [homologyMap'_nullHomotopic]; rw [add_zero]

Depends on / 依赖: _add, _nullHomotopic, add_zero, eq_add_nullHomotopic, h.eq_add_nullHomotopic, homologyMap
-/
lemma homologyMap'_congr (h : Homotopy φ₁ φ₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : homologyMap' φ₁ h₁ h₂ = homologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_nullHomotopic]; rw [homologyMap'_add]; rw [homologyMap'_nullHomotopic]; rw [add_zero]

/--
lemma `leftHomologyMap_congr` / 引理 `leftHomologyMap_congr`

English:
lemma leftHomologyMap_congr
  given: (h : Homotopy φ₁ φ₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: h.leftHomologyMap'_congr _ _

中文:
引理 leftHomologyMap_congr
  条件: (h : Homotopy φ₁ φ₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  证明: h.leftHomologyMap'_congr _ _

Depends on / 依赖: _congr, h.leftHomologyMap, leftHomologyMap
-/
lemma leftHomologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ₁ = leftHomologyMap φ₂ :=
  h.leftHomologyMap'_congr _ _

/--
lemma `rightHomologyMap_congr` / 引理 `rightHomologyMap_congr`

English:
lemma rightHomologyMap_congr
  given: (h : Homotopy φ₁ φ₂) [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: h.rightHomologyMap'_congr _ _

中文:
引理 rightHomologyMap_congr
  条件: (h : Homotopy φ₁ φ₂) [S₁.HasRightHomology] [S₂.HasRightHomology]
  证明: h.rightHomologyMap'_congr _ _

Depends on / 依赖: _congr, h.rightHomologyMap, rightHomologyMap
-/
lemma rightHomologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ₁ = rightHomologyMap φ₂ :=
  h.rightHomologyMap'_congr _ _

/--
lemma `homologyMap_congr` / 引理 `homologyMap_congr`

English:
lemma homologyMap_congr
  given: (h : Homotopy φ₁ φ₂) [S₁.HasHomology] [S₂.HasHomology]
  proof: h.homologyMap'_congr _ _

中文:
引理 homologyMap_congr
  条件: (h : Homotopy φ₁ φ₂) [S₁.HasHomology] [S₂.HasHomology]
  证明: h.homologyMap'_congr _ _

Depends on / 依赖: _congr, h.homologyMap, homologyMap
-/
lemma homologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap φ₁ = homologyMap φ₂ :=
  h.homologyMap'_congr _ _

end Homotopy

/-- A homotopy equivalence between two short complexes `S₁` and `S₂` consists
of morphisms `hom : S₁ ⟶ S₂` and `inv : S₂ ⟶ S₁` such that both compositions
`hom ≫ inv` and `inv ≫ hom` are homotopic to the identity. -/
@[ext]
/--
Definition of `HomotopyEquiv` / `HomotopyEquiv` 的定义

English:
structure HomotopyEquiv
  parameters: where
  axioms and operations (4):
    - hom : S₁ ⟶ S₂
    - inv : S₂ ⟶ S₁
    - homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 S₁)
    - homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 S₂)

中文:
结构 HomotopyEquiv
  参数: where
  公理与运算 (4 个):
    - hom : S₁ ⟶ S₂
    - inv : S₂ ⟶ S₁
    - homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 S₁)
    - homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 S₂)
-/
structure HomotopyEquiv where
  /-- the forward direction of a homotopy equivalence. -/
  hom : S₁ ⟶ S₂
  /-- the backwards direction of a homotopy equivalence. -/
  inv : S₂ ⟶ S₁
  /-- the composition of the two directions of a homotopy equivalence is
  homotopic to the identity of the source -/
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 S₁)
  /-- the composition of the two directions of a homotopy equivalence is
  homotopic to the identity of the target -/
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 S₂)

namespace HomotopyEquiv

variable {S₁ S₂}

/-- The homotopy equivalence from a short complex to itself that is induced
by the identity. -/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (S : ShortComplex C)
  body: 𝟙 S
  inv := 𝟙 S
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)

中文:
定义 refl
  签名: (S : ShortComplex C)
  定义体: 𝟙 S
  inv := 𝟙 S
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)
-/
def refl (S : ShortComplex C) : HomotopyEquiv S S where
  hom := 𝟙 S
  inv := 𝟙 S
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- The inverse of a homotopy equivalence. -/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : HomotopyEquiv S₁ S₂)
  body: e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

中文:
定义 symm
  签名: (e : HomotopyEquiv S₁ S₂)
  定义体: e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

Depends on / 依赖: e.inv
-/
def symm (e : HomotopyEquiv S₁ S₂) : HomotopyEquiv S₂ S₁ where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

/-- The composition of homotopy equivalences. -/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e : HomotopyEquiv S₁ S₂) (e' : HomotopyEquiv S₂ S₃)
  body: e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans
    (((e'.homotopyHomInvId.compRight e.inv).compLeft e.hom).trans
      ((Homotopy.ofEq (by simp)).trans e.homotopyHomInvId))
  homotopyInvHomId := (Homotopy.ofEq (by simp)).trans
    (((e.homotopyInvHomId.c

中文:
定义 trans
  签名: (e : HomotopyEquiv S₁ S₂) (e' : HomotopyEquiv S₂ S₃)
  定义体: e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans
    (((e'.homotopyHomInvId.compRight e.inv).compLeft e.hom).trans
      ((Homotopy.ofEq (by simp)).trans e.homotopyHomInvId))
  homotopyInvHomId := (Homotopy.ofEq (by simp)).trans
    (((e.homotopyInvHomId.c

Depends on / 依赖: e.hom
-/
def trans (e : HomotopyEquiv S₁ S₂) (e' : HomotopyEquiv S₂ S₃) :
    HomotopyEquiv S₁ S₃ where
  hom := e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans
    (((e'.homotopyHomInvId.compRight e.inv).compLeft e.hom).trans
      ((Homotopy.ofEq (by simp)).trans e.homotopyHomInvId))
  homotopyInvHomId := (Homotopy.ofEq (by simp)).trans
    (((e.homotopyInvHomId.compRight e'.hom).compLeft e'.inv).trans
      ((Homotopy.ofEq (by simp)).trans e'.homotopyInvHomId))

end HomotopyEquiv

end Homotopy

section

variable (S : ShortComplex C) [S.HasLeftHomology] {A : C}
    (k k' : A ⟶ S.X₂) (hk : k ≫ S.g = 0) (hk' : k' ≫ S.g = 0)

/--
lemma `add_liftCycles` / 引理 `add_liftCycles`

English:
lemma add_liftCycles
  proof: by
  simp only [← cancel_mono S.iCycles, liftCycles_i, add_comp]

中文:
引理 add_liftCycles
  证明: by
  simp only [← cancel_mono S.iCycles, liftCycles_i, add_comp]

Depends on / 依赖: S.iCycles, add_comp, cancel_mono, iCycles, liftCycles_i
-/
lemma add_liftCycles :
    S.liftCycles k hk + S.liftCycles k' hk' =
      S.liftCycles (k + k') (by rw [add_comp, hk, hk', add_zero]) := by
  simp only [← cancel_mono S.iCycles, liftCycles_i, add_comp]

/--
lemma `sub_liftCycles` / 引理 `sub_liftCycles`

English:
lemma sub_liftCycles
  proof: by
  simp only [← cancel_mono S.iCycles, liftCycles_i, sub_comp]

中文:
引理 sub_liftCycles
  证明: by
  simp only [← cancel_mono S.iCycles, liftCycles_i, sub_comp]

Depends on / 依赖: S.iCycles, cancel_mono, iCycles, liftCycles_i, sub_comp
-/
lemma sub_liftCycles :
    S.liftCycles k hk - S.liftCycles k' hk' =
      S.liftCycles (k - k') (by rw [sub_comp, hk, hk', sub_zero]) := by
  simp only [← cancel_mono S.iCycles, liftCycles_i, sub_comp]

end

end ShortComplex

end CategoryTheory
