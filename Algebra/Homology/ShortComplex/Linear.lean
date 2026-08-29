/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Homology of linear categories

In this file, it is shown that if `C` is an `R`-linear category, then
`ShortComplex C` is an `R`-linear category. Various homological notions
are also shown to be linear.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

namespace ShortComplex

variable {S₁ S₂ : ShortComplex C}

attribute [local simp] Hom.comm₁₂ Hom.comm₂₃ mul_smul add_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (S₁ ⟶ S₂)
  body: { τ₁ := a • φ.τ₁
      τ₂ := a • φ.τ₂
      τ₃ := a • φ.τ₃ }

中文:
实例 :
  签名: 标量乘法 R (S₁ ⟶ S₂)
  定义体: { τ₁ := a • φ.τ₁
      τ₂ := a • φ.τ₂
      τ₃ := a • φ.τ₃ }
-/
instance : SMul R (S₁ ⟶ S₂) where
  smul a φ :=
    { τ₁ := a • φ.τ₁
      τ₂ := a • φ.τ₂
      τ₃ := a • φ.τ₃ }

/--
lemma `smul_τ₁` / 引理 `smul_τ₁`

English:
lemma smul_τ₁
  given: (a : R) (φ : S₁ ⟶ S₂)
  statement: (a • φ).τ₁ = a • φ.τ₁
  proof: rfl

中文:
引理 smul_τ₁
  条件: (a : R) (φ : S₁ ⟶ S₂)
  结论: (a • φ).τ₁ = a • φ.τ₁
  证明: rfl
-/
@[simp] lemma smul_τ₁ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₁ = a • φ.τ₁ := rfl
/--
lemma `smul_τ₂` / 引理 `smul_τ₂`

English:
lemma smul_τ₂
  given: (a : R) (φ : S₁ ⟶ S₂)
  statement: (a • φ).τ₂ = a • φ.τ₂
  proof: rfl

中文:
引理 smul_τ₂
  条件: (a : R) (φ : S₁ ⟶ S₂)
  结论: (a • φ).τ₂ = a • φ.τ₂
  证明: rfl
-/
@[simp] lemma smul_τ₂ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₂ = a • φ.τ₂ := rfl
/--
lemma `smul_τ₃` / 引理 `smul_τ₃`

English:
lemma smul_τ₃
  given: (a : R) (φ : S₁ ⟶ S₂)
  statement: (a • φ).τ₃ = a • φ.τ₃
  proof: rfl

中文:
引理 smul_τ₃
  条件: (a : R) (φ : S₁ ⟶ S₂)
  结论: (a • φ).τ₃ = a • φ.τ₃
  证明: rfl
-/
@[simp] lemma smul_τ₃ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₃ = a • φ.τ₃ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (S₁ ⟶ S₂)
  body: by cat_disch
  one_smul := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  add_smul := by cat_disch
  mul_smul := by cat_disch

中文:
实例 :
  签名: 模 R (S₁ ⟶ S₂)
  定义体: by cat_disch
  one_smul := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  add_smul := by cat_disch
  mul_smul := by cat_disch

Depends on / 依赖: add_smul, cat_disch, mul_smul, one_smul, smul_add, smul_zero
-/
instance : Module R (S₁ ⟶ S₂) where
  zero_smul := by cat_disch
  one_smul := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  add_smul := by cat_disch
  mul_smul := by cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R (ShortComplex C)

中文:
实例 :
  签名: 线性 R (短复形 C)
-/
instance : Linear R (ShortComplex C) where

section LeftHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

namespace LeftHomologyMapData

variable (γ : LeftHomologyMapData φ h₁ h₂)

/-- Given a left homology map data for morphism `φ`, this is the induced left homology
map data for `a • φ`. -/
@[simps]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (a : R)
  body: a • γ.φK
  φH := a • γ.φH

中文:
定义 smul
  签名: (a : R)
  定义体: a • γ.φK
  φH := a • γ.φH
-/
def smul (a : R) : LeftHomologyMapData (a • φ) h₁ h₂ where
  φK := a • γ.φK
  φH := a • γ.φH

end LeftHomologyMapData

variable (h₁ h₂ φ)
variable (a : R)

@[simp]
/--
lemma `leftHomologyMap'_smul` / 引理 `leftHomologyMap'_smul`

English:
lemma leftHomologyMap'_smul
  proof: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).leftHomologyMap'_eq, LeftHomologyMapData.smul_φH, γ.leftHomologyMap'_eq]

@[simp]

中文:
引理 leftHomologyMap'_smul
  证明: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).leftHomologyMap'_eq, LeftHomologyMapData.smul_φH, γ.leftHomologyMap'_eq]

@[simp]
-/
lemma leftHomologyMap'_smul :
    leftHomologyMap' (a • φ) h₁ h₂ = a • leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).leftHomologyMap'_eq, LeftHomologyMapData.smul_φH, γ.leftHomologyMap'_eq]

@[simp]
/--
lemma `cyclesMap'_smul` / 引理 `cyclesMap'_smul`

English:
lemma cyclesMap'_smul
  proof: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).cyclesMap'_eq, LeftHomologyMapData.smul_φK, γ.cyclesMap'_eq]

中文:
引理 cyclesMap'_smul
  证明: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).cyclesMap'_eq, LeftHomologyMapData.smul_φK, γ.cyclesMap'_eq]
-/
lemma cyclesMap'_smul :
    cyclesMap' (a • φ) h₁ h₂ = a • cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).cyclesMap'_eq, LeftHomologyMapData.smul_φK, γ.cyclesMap'_eq]

section

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

@[simp]
/--
lemma `leftHomologyMap_smul` / 引理 `leftHomologyMap_smul`

English:
lemma leftHomologyMap_smul
  statement: leftHomologyMap (a • φ) = a • leftHomologyMap φ
  proof: leftHomologyMap'_smul _ _ _ _

@[simp]

中文:
引理 leftHomologyMap_smul
  结论: leftHomologyMap (a • φ) = a • leftHomologyMap φ
  证明: leftHomologyMap'_smul _ _ _ _

@[simp]

Depends on / 依赖: _smul, leftHomologyMap
-/
lemma leftHomologyMap_smul : leftHomologyMap (a • φ) = a • leftHomologyMap φ :=
  leftHomologyMap'_smul _ _ _ _

@[simp]
/--
lemma `cyclesMap_smul` / 引理 `cyclesMap_smul`

English:
lemma cyclesMap_smul
  statement: cyclesMap (a • φ) = a • cyclesMap φ
  proof: cyclesMap'_smul _ _ _ _

中文:
引理 cyclesMap_smul
  结论: cyclesMap (a • φ) = a • cyclesMap φ
  证明: cyclesMap'_smul _ _ _ _

Depends on / 依赖: _smul, cyclesMap
-/
lemma cyclesMap_smul : cyclesMap (a • φ) = a • cyclesMap φ :=
  cyclesMap'_smul _ _ _ _

end

/--
Instance `leftHomologyFunctor_linear` / 实例 `leftHomologyFunctor_linear`

English:
instance leftHomologyFunctor_linear
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 leftHomologyFunctor_linear
  签名: [有Kernels C] [有余kernels C]
-/
instance leftHomologyFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (leftHomologyFunctor C) where

/--
Instance `cyclesFunctor_linear` / 实例 `cyclesFunctor_linear`

English:
instance cyclesFunctor_linear
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 cyclesFunctor_linear
  签名: [有Kernels C] [有余kernels C]
-/
instance cyclesFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (cyclesFunctor C) where

end LeftHomology

section RightHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

namespace RightHomologyMapData

variable (γ : RightHomologyMapData φ h₁ h₂)

/-- Given a right homology map data for morphism `φ`, this is the induced right homology
map data for `a • φ`. -/
@[simps]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (a : R)
  body: a • γ.φQ
  φH := a • γ.φH

中文:
定义 smul
  签名: (a : R)
  定义体: a • γ.φQ
  φH := a • γ.φH
-/
def smul (a : R) : RightHomologyMapData (a • φ) h₁ h₂ where
  φQ := a • γ.φQ
  φH := a • γ.φH

end RightHomologyMapData

variable (h₁ h₂ φ)
variable (a : R)

@[simp]
/--
lemma `rightHomologyMap'_smul` / 引理 `rightHomologyMap'_smul`

English:
lemma rightHomologyMap'_smul
  proof: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).rightHomologyMap'_eq, RightHomologyMapData.smul_φH, γ.rightHomologyMap'_eq]

@[simp]

中文:
引理 rightHomologyMap'_smul
  证明: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).rightHomologyMap'_eq, RightHomologyMapData.smul_φH, γ.rightHomologyMap'_eq]

@[simp]

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.smul_, rightHomologyMap
-/
lemma rightHomologyMap'_smul :
    rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).rightHomologyMap'_eq, RightHomologyMapData.smul_φH, γ.rightHomologyMap'_eq]

@[simp]
/--
lemma `opcyclesMap'_smul` / 引理 `opcyclesMap'_smul`

English:
lemma opcyclesMap'_smul
  proof: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).opcyclesMap'_eq, RightHomologyMapData.smul_φQ, γ.opcyclesMap'_eq]

中文:
引理 opcyclesMap'_smul
  证明: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).opcyclesMap'_eq, RightHomologyMapData.smul_φQ, γ.opcyclesMap'_eq]

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.smul_, opcyclesMap
-/
lemma opcyclesMap'_smul :
    opcyclesMap' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).opcyclesMap'_eq, RightHomologyMapData.smul_φQ, γ.opcyclesMap'_eq]

section

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

@[simp]
/--
lemma `rightHomologyMap_smul` / 引理 `rightHomologyMap_smul`

English:
lemma rightHomologyMap_smul
  statement: rightHomologyMap (a • φ) = a • rightHomologyMap φ
  proof: rightHomologyMap'_smul _ _ _ _

@[simp]

中文:
引理 rightHomologyMap_smul
  结论: rightHomologyMap (a • φ) = a • rightHomologyMap φ
  证明: rightHomologyMap'_smul _ _ _ _

@[simp]

Depends on / 依赖: _smul, rightHomologyMap
-/
lemma rightHomologyMap_smul : rightHomologyMap (a • φ) = a • rightHomologyMap φ :=
  rightHomologyMap'_smul _ _ _ _

@[simp]
/--
lemma `opcyclesMap_smul` / 引理 `opcyclesMap_smul`

English:
lemma opcyclesMap_smul
  statement: opcyclesMap (a • φ) = a • opcyclesMap φ
  proof: opcyclesMap'_smul _ _ _ _

中文:
引理 opcyclesMap_smul
  结论: opcyclesMap (a • φ) = a • opcyclesMap φ
  证明: opcyclesMap'_smul _ _ _ _

Depends on / 依赖: _smul, opcyclesMap
-/
lemma opcyclesMap_smul : opcyclesMap (a • φ) = a • opcyclesMap φ :=
  opcyclesMap'_smul _ _ _ _

end

/--
Instance `rightHomologyFunctor_linear` / 实例 `rightHomologyFunctor_linear`

English:
instance rightHomologyFunctor_linear
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 rightHomologyFunctor_linear
  签名: [有Kernels C] [有余kernels C]
-/
instance rightHomologyFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (rightHomologyFunctor C) where

/--
Instance `opcyclesFunctor_linear` / 实例 `opcyclesFunctor_linear`

English:
instance opcyclesFunctor_linear
  signature: [HasKernels C] [HasCokernels C]

中文:
实例 opcyclesFunctor_linear
  签名: [有Kernels C] [有余kernels C]
-/
instance opcyclesFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (opcyclesFunctor C) where

end RightHomology

section Homology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

namespace HomologyMapData

variable (γ : HomologyMapData φ h₁ h₂) (γ' : HomologyMapData φ' h₁ h₂)

/-- Given a homology map data for a morphism `φ`, this is the induced homology
map data for `a • φ`. -/
@[simps]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (a : R)
  body: γ.left.smul a
  right := γ.right.smul a

中文:
定义 smul
  签名: (a : R)
  定义体: γ.left.smul a
  right := γ.right.smul a

Depends on / 依赖: left.smul
-/
def smul (a : R) : HomologyMapData (a • φ) h₁ h₂ where
  left := γ.left.smul a
  right := γ.right.smul a

end HomologyMapData

variable (h₁ h₂)
variable (a : R)

@[simp]
/--
lemma `homologyMap'_smul` / 引理 `homologyMap'_smul`

English:
lemma homologyMap'_smul
  proof: leftHomologyMap'_smul _ _ _ _

中文:
引理 homologyMap'_smul
  证明: leftHomologyMap'_smul _ _ _ _
-/
lemma homologyMap'_smul :
    homologyMap' (a • φ) h₁ h₂ = a • homologyMap' φ h₁ h₂ :=
  leftHomologyMap'_smul _ _ _ _

variable (φ φ')

@[simp]
/--
lemma `homologyMap_smul` / 引理 `homologyMap_smul`

English:
lemma homologyMap_smul
  given: [S₁.HasHomology] [S₂.HasHomology]
  proof: homologyMap'_smul _ _ _

中文:
引理 homologyMap_smul
  条件: [S₁.有同调] [S₂.有同调]
  证明: homologyMap'_smul _ _ _

Depends on / 依赖: _smul, homologyMap
-/
lemma homologyMap_smul [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (a • φ) = a • homologyMap φ :=
  homologyMap'_smul _ _ _

/--
Instance `homologyFunctor_linear` / 实例 `homologyFunctor_linear`

English:
instance homologyFunctor_linear
  signature: [CategoryWithHomology C]

中文:
实例 homologyFunctor_linear
  签名: [带同调范畴 C]
-/
instance homologyFunctor_linear [CategoryWithHomology C] :
    Functor.Linear R (homologyFunctor C) where

end Homology

/-- Homotopy between morphisms of short complexes is compatible with the scalar multiplication. -/
@[simps]
/--
Definition of `Homotopy.smul` / `Homotopy.smul` 的定义

English:
definition Homotopy.smul
  signature: {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂) (a : R)
  body: a • h.h₀
  h₁ := a • h.h₁
  h₂ := a • h.h₂
  h₃ := a • h.h₃
  comm₁ := by
    dsimp
    rw [h.comm₁]
    simp only [smul_add, Linear.comp_smul]
  comm₂ := by
    dsimp
    rw [h.comm₂]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]
  comm₃ := by
    dsimp
    rw [h.comm₃]
    simp only [smul_add, Linear.smul_comp]

中文:
定义 同伦.smul
  签名: {φ₁ φ₂ : S₁ ⟶ S₂} (h : 同伦 φ₁ φ₂) (a : R)
  定义体: a • h.h₀
  h₁ := a • h.h₁
  h₂ := a • h.h₂
  h₃ := a • h.h₃
  comm₁ := by
    dsimp
    rw [h.comm₁]
    simp only [smul_add, Linear.comp_smul]
  comm₂ := by
    dsimp
    rw [h.comm₂]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]
  comm₃ := by
    dsimp
    rw [h.comm₃]
    simp only [smul_add, Linear.smul_comp]
-/
def Homotopy.smul {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂) (a : R) :
    Homotopy (a • φ₁) (a • φ₂) where
  h₀ := a • h.h₀
  h₁ := a • h.h₁
  h₂ := a • h.h₂
  h₃ := a • h.h₃
  comm₁ := by
    dsimp
    rw [h.comm₁]
    simp only [smul_add, Linear.comp_smul]
  comm₂ := by
    dsimp
    rw [h.comm₂]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]
  comm₃ := by
    dsimp
    rw [h.comm₃]
    simp only [smul_add, Linear.smul_comp]

end ShortComplex

end CategoryTheory
