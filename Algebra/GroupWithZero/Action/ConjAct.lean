/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation action of a group with zero on itself
-/

public section

assert_not_exists Ring

variable {α G₀ : Type*}

namespace ConjAct
variable [GroupWithZero G₀]

/-
**ConjAct.** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GroupWithZero (ConjAct G₀) := inferInstanceAs <| GroupWithZero G₀
/-
**ConjAct.ofConjAct_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], ConjAct.ofConjAct 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofConjAct_zero : ofConjAct 0 = (0 : G₀) := rfl
/-
**ConjAct.toConjAct_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], ConjAct.toConjAct 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConjAct_zero : toConjAct (0 : G₀) = 0 := rfl
/-
**ConjAct.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction₀ : MulAction (ConjAct G₀) G₀ where
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]
/-
**ConjAct.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：smulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] : SMu
lCommClass α (ConjAct G) G where smul_comm a ug g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjAct.smul_def`：smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g
 * h * (ofConjAct g)⁻¹
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
instance smulCommClass₀ [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass α (ConjAct G₀) G₀ where
  smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]
/-
**ConjAct.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：smulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] : SMu
lCommClass α (ConjAct G) G where smul_comm a ug g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjAct.smul_def`：smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g
 * h * (ofConjAct g)⁻¹
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
instance smulCommClass₀' [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass (ConjAct G₀) α G₀ :=
  haveI := SMulCommClass.symm G₀ α G₀
  .symm ..

end ConjAct

