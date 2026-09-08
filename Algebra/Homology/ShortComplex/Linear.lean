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

/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (S₁ ⟶ S₂) where
  smul a φ :=
    { τ₁ := a • φ.τ₁
      τ₂ := a • φ.τ₂
      τ₃ := a • φ.τ₃ }
/-
**CategoryTheory.ShortComplex.smul_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_τ₁ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₁ = a • φ.τ₁ := rfl
/-
**CategoryTheory.ShortComplex.smul_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_τ₂ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₂ = a • φ.τ₂ := rfl
/-
**CategoryTheory.ShortComplex.smul_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_τ₃ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₃ = a • φ.τ₃ := rfl
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (S₁ ⟶ S₂) where
  zero_smul := by cat_disch
  one_smul := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  add_smul := by cat_disch
  mul_smul := by cat_disch
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear R (ShortComplex C) where

section LeftHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

namespace LeftHomologyMapData

variable (γ : LeftHomologyMapData φ h₁ h₂)

/-- Given a left homology map data for morphism `φ`, this is the induced left homology
map data for `a • φ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.smul** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：smul (a : R) : LeftHomologyMapData (a • φ) h₁ h₂ where φK
参数：a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a left homology map data for morphism `φ`, this is the induced left homolo
gy
map data for `a • φ`.
-/
def smul (a : R) : LeftHomologyMapData (a • φ) h₁ h₂ where
  φK := a • γ.φK
  φH := a • γ.φH

end LeftHomologyMapData

variable (h₁ h₂ φ)
variable (a : R)

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_smul** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C] {S₁ S₂ : CategoryTheory.ShortComplex C}   (φ : S₁ ⟶ S₂)
 (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (a : R),   CategoryTheory
.ShortComplex.leftHomologyMap' (a • φ) h₁ h₂ = a • CategoryTheory.ShortComplex.l
eftHomologyMap' φ h₁ h₂
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；a : R；a • φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.smul_φH`：∀ {R : Type u_1
} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2
} C]   [inst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftHomologyMap'_smul :
    leftHomologyMap' (a • φ) h₁ h₂ = a • leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).leftHomologyMap'_eq, LeftHomologyMapData.smul_φH, γ.leftHomologyMap'_eq]

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap'_smul** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C] {S₁ S₂ : CategoryTheory.ShortComplex C}   (φ : S₁ ⟶ S₂)
 (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (a : R),   CategoryTheory
.ShortComplex.cyclesMap' (a • φ) h₁ h₂ = a • CategoryTheory.ShortComplex.cyclesM
ap' φ h₁ h₂
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；a : R；a • φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.smul_φK`：∀ {R : Type u_1
} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2
} C]   [inst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesMap'_smul :
    cyclesMap' (a • φ) h₁ h₂ = a • cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).cyclesMap'_eq, LeftHomologyMapData.smul_φK, γ.cyclesMap'_eq]

section

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_smul : leftHomologyMap (a • φ) = a • leftHomologyMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_smul`：∀ {R : Type u_1} {C :
 Type u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2} C]  
 [inst_2 : CategoryTheory.Preadditive C…
-/
lemma leftHomologyMap_smul : leftHomologyMap (a • φ) = a • leftHomologyMap φ :=
  leftHomologyMap'_smul _ _ _ _

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：cyclesMap_smul : cyclesMap (a • φ) = a • cyclesMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_smul`：∀ {R : Type u_1} {C : Type 
u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2} C]   [inst
_2 : CategoryTheory.Preadditive C…
-/
lemma cyclesMap_smul : cyclesMap (a • φ) = a • cyclesMap φ :=
  cyclesMap'_smul _ _ _ _

end

/-
**CategoryTheory.ShortComplex.leftHomologyFunctor_linear** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.Limits.HasKernels C] [inst_5
 : CategoryTheory.Limits.HasCokernels C],   CategoryTheory.Functor.Linear R (Cat
egoryTheory.ShortComplex.leftHomologyFunctor C)
参数：CategoryTheory.ShortComplex.leftHomologyFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyFunctor_map`：∀ (C : Type u_1) [i
nst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.leftHomologyMap_smul`：leftHomologyMap_smul :
 leftHomologyMap (a • φ) = a • leftHomologyMap φ
-/
instance leftHomologyFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (leftHomologyFunctor C) where
/-
**CategoryTheory.ShortComplex.cyclesFunctor_linear** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.Limits.HasKernels C] [inst_5
 : CategoryTheory.Limits.HasCokernels C],   CategoryTheory.Functor.Linear R (Cat
egoryTheory.ShortComplex.cyclesFunctor C)
参数：CategoryTheory.ShortComplex.cyclesFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.cyclesFunctor_map`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_smul`：cyclesMap_smul : cyclesMap (
a • φ) = a • cyclesMap φ
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
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.smul** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：smul (a : R) : RightHomologyMapData (a • φ) h₁ h₂ where φQ
参数：a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right homology map data for morphism `φ`, this is the induced right homo
logy
map data for `a • φ`.
-/
def smul (a : R) : RightHomologyMapData (a • φ) h₁ h₂ where
  φQ := a • γ.φQ
  φH := a • γ.φH

end RightHomologyMapData

variable (h₁ h₂ φ)
variable (a : R)

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap'_smul** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C] {S₁ S₂ : CategoryTheory.ShortComplex C}   (φ : S₁ ⟶ S₂)
 (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (a : R),   CategoryTheo
ry.ShortComplex.rightHomologyMap' (a • φ) h₁ h₂ =     a • CategoryTheory.ShortCo
mplex.rightHomologyMap' φ h₁ h₂
参数：φ : S₁ ⟶ S₂；h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；a : R；a • φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.smul_φH`：∀ {R : Type u_
1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_
2} C]   [inst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightHomologyMap'_smul :
    rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).rightHomologyMap'_eq, RightHomologyMapData.smul_φH, γ.rightHomologyMap'_eq]

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap'_smul** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C] {S₁ S₂ : CategoryTheory.ShortComplex C}   (φ : S₁ ⟶ S₂)
 (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (a : R),   CategoryTheo
ry.ShortComplex.opcyclesMap' (a • φ) h₁ h₂ = a • CategoryTheory.ShortComplex.opc
yclesMap' φ h₁ h₂
参数：φ : S₁ ⟶ S₂；h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；a : R；a • φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.opcyclesMap'_eq`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.smul_φQ`：∀ {R : Type u_
1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_
2} C]   [inst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesMap'_smul :
    opcyclesMap' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).opcyclesMap'_eq, RightHomologyMapData.smul_φQ, γ.opcyclesMap'_eq]

section

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：rightHomologyMap_smul : rightHomologyMap (a • φ) = a • rightHomologyMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_smul`：∀ {R : Type u_1} {C 
: Type u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2} C] 
  [inst_2 : CategoryTheory.Preadditive C…
-/
lemma rightHomologyMap_smul : rightHomologyMap (a • φ) = a • rightHomologyMap φ :=
  rightHomologyMap'_smul _ _ _ _

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：opcyclesMap_smul : opcyclesMap (a • φ) = a • opcyclesMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMap'_smul`：∀ {R : Type u_1} {C : Typ
e u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2} C]   [in
st_2 : CategoryTheory.Preadditive C…
-/
lemma opcyclesMap_smul : opcyclesMap (a • φ) = a • opcyclesMap φ :=
  opcyclesMap'_smul _ _ _ _

end

/-
**CategoryTheory.ShortComplex.rightHomologyFunctor_linear** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.Limits.HasKernels C] [inst_5
 : CategoryTheory.Limits.HasCokernels C],   CategoryTheory.Functor.Linear R (Cat
egoryTheory.ShortComplex.rightHomologyFunctor C)
参数：CategoryTheory.ShortComplex.rightHomologyFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyFunctor_map`：∀ (C : Type u_1) [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap_smul`：rightHomologyMap_smul
 : rightHomologyMap (a • φ) = a • rightHomologyMap φ
-/
instance rightHomologyFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (rightHomologyFunctor C) where
/-
**CategoryTheory.ShortComplex.opcyclesFunctor_linear** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.Limits.HasKernels C] [inst_5
 : CategoryTheory.Limits.HasCokernels C],   CategoryTheory.Functor.Linear R (Cat
egoryTheory.ShortComplex.opcyclesFunctor C)
参数：CategoryTheory.ShortComplex.opcyclesFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.opcyclesFunctor_map`：∀ (C : Type u_1) [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap_smul`：opcyclesMap_smul : opcycle
sMap (a • φ) = a • opcyclesMap φ
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
/-
**CategoryTheory.ShortComplex.HomologyMapData.smul** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：smul (a : R) : HomologyMapData (a • φ) h₁ h₂ where left
参数：a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a homology map data for a morphism `φ`, this is the induced homology
map data for `a • φ`.
-/
def smul (a : R) : HomologyMapData (a • φ) h₁ h₂ where
  left := γ.left.smul a
  right := γ.right.smul a

end HomologyMapData

variable (h₁ h₂)
variable (a : R)

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap'_smul** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C] {S₁ S₂ : CategoryTheory.ShortComplex C}   {φ : S₁ ⟶ S₂}
 (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) (a : R),   CategoryTheory.ShortCo
mplex.homologyMap' (a • φ) h₁ h₂ = a • CategoryTheory.ShortComplex.homologyMap' 
φ h₁ h₂
参数：h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；a : R；a • φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_smul`：∀ {R : Type u_1} {C :
 Type u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2} C]  
 [inst_2 : CategoryTheory.Preadditive C…
-/
lemma homologyMap'_smul :
    homologyMap' (a • φ) h₁ h₂ = a • homologyMap' φ h₁ h₂ :=
  leftHomologyMap'_smul _ _ _ _

variable (φ φ')

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：homologyMap_smul [S₁.HasHomology] [S₂.HasHomology] : homologyMap (a • φ) =
 a • homologyMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_smul`：∀ {R : Type u_1} {C : Typ
e u_2} [inst : Semiring R] [inst_1 : CategoryTheory.Category.{v_1, u_2} C]   [in
st_2 : CategoryTheory.Preadditive C…
-/
lemma homologyMap_smul [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (a • φ) = a • homologyMap φ :=
  homologyMap'_smul _ _ _
/-
**CategoryTheory.ShortComplex.homologyFunctor_linear** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : Semiring R] [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.CategoryWithHomology C],   C
ategoryTheory.Functor.Linear R (CategoryTheory.ShortComplex.homologyFunctor C)
参数：CategoryTheory.ShortComplex.homologyFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.homologyFunctor_map`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   [inst_2 : CategoryTheory.Cate…
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_smul`：homologyMap_smul [S₁.HasHo
mology] [S₂.HasHomology] : homologyMap (a • φ) = a • homologyMap φ
-/
instance homologyFunctor_linear [CategoryWithHomology C] :
    Functor.Linear R (homologyFunctor C) where

end Homology

/-- Homotopy between morphisms of short complexes is compatible with the scalar multiplication. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.smul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex.Homotopy`。
形式化陈述：{R : Type u_1} →   {C : Type u_2} →     [inst : Semiring R] →       [inst_
1 : CategoryTheory.Category.{v_1, u_2} C] →         [inst_2 : CategoryTheory.Pre
additive C] →           [inst_3 : CategoryTheory.Linear R C] →             {S₁ S
₂ : CategoryTheory.ShortComplex C} →               {φ₁ φ₂ : S₁ ⟶ S₂} →          
       CategoryTheory.ShortComplex.Homotopy φ₁ φ₂ →                   (a : R) → 
CategoryTheory.ShortComplex.Homotopy (a • φ₁) (a • φ₂)
参数：a : R；a • φ₁；a • φ₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy between morphisms of short complexes is compatible with the scalar mult
iplication.
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

