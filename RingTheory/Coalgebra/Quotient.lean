/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Coalgebra structure on the quotient by a coideal

## Main definitions

* `Submodule.IsCoideal I` : the submodule `I : Submodule R C` is a coideal.
* `Coalgebra.Quotient.mkQCoalgHom` : `Submodule.mkQ` as a coalgebra homomorphism.

## Main results

* `Coalgebra` instance on `C ⧸ I` when `[I.IsCoideal]`.
-/

public section

open Coalgebra LinearMap TensorProduct

variable {R C : Type*} [CommRing R] [AddCommGroup C] [Module R C]

section CoalgebraStruct

variable [CoalgebraStruct R C]

/-- An `R`-submodule `I` of an `R`-coalgebra `C` is a *coideal* if the counit vanishes on
`I` and the comultiplication descends through the module quotient `C ⧸ I`. -/
@[mk_iff]
/-
**Submodule.IsCoideal** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：Submodule.IsCoideal (I : Submodule R C) : Prop where counit_eq_zero : fora
ll ⦃x : C⦄, x in I -> counit (R
参数：I : Submodule R C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-submodule `I` of an `R`-coalgebra `C` is a *coideal* if the counit vanish
es on
`I` and the comultiplication descends through the module quotient `C ⧸ I`.
-/
class Submodule.IsCoideal (I : Submodule R C) : Prop where
  counit_eq_zero : ∀ ⦃x : C⦄, x ∈ I → counit (R := R) x = 0
  map_mkQ_comul_eq_zero : ∀ ⦃x : C⦄, x ∈ I → TensorProduct.map I.mkQ I.mkQ (comul x) = 0

/-- A submodule is a coideal iff the counit vanishes on it and its comultiplication image lies
in `I ⊗ C + C ⊗ I`, the textbook form of the coideal condition. -/
/-
**Submodule.isCoideal_iff_comul_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.isCoideal_iff_comul_mem (I : Submodule R C) : I.IsCoideal ↔ (for
all x in I, counit (R
参数：I : Submodule R C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.map_ker`：TensorProduct.map_ker : ker (TensorProduct.map g 
g') = range (lTensor N f') ⊔ range (rTensor N' f)
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A submodule is a coideal iff the counit vanishes on it and its comultiplication 
image lies
in `I ⊗ C + C ⊗ I`, the textbook form of the coideal condition.
-/
lemma Submodule.isCoideal_iff_comul_mem (I : Submodule R C) :
    I.IsCoideal ↔ (∀ x ∈ I, counit (R := R) x = 0) ∧
      ∀ x ∈ I, comul x ∈
        LinearMap.range (lTensor C I.subtype) ⊔ LinearMap.range (rTensor C I.subtype) := by
  simp_rw [isCoideal_iff, ← LinearMap.mem_ker,
    TensorProduct.map_ker (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective]

end CoalgebraStruct

namespace Coalgebra.Quotient

section CoalgebraStruct

variable [CoalgebraStruct R C] (I : Submodule R C) [I.IsCoideal]

/-
**Coalgebra.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Coalgebra.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoalgebraStruct R (C ⧸ I) where
  comul := I.liftQ (map I.mkQ I.mkQ ∘ₗ comul) Submodule.IsCoideal.map_mkQ_comul_eq_zero
  counit := I.liftQ counit Submodule.IsCoideal.counit_eq_zero
/-
**Coalgebra.Quotient.comul_comp_mkQ** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra.Quotien
t`。
形式化陈述：comul_comp_mkQ : comul ∘ₗ I.mkQ = map I.mkQ I.mkQ ∘ₗ (comul : C ->ₗ[R] _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comul_comp_mkQ : comul ∘ₗ I.mkQ = map I.mkQ I.mkQ ∘ₗ (comul : C →ₗ[R] _) := rfl
/-
**Coalgebra.Quotient.counit_comp_mkQ** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra.Quotie
nt`。
形式化陈述：counit_comp_mkQ : counit ∘ₗ I.mkQ = (counit : C ->ₗ[R] R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counit_comp_mkQ : counit ∘ₗ I.mkQ = (counit : C →ₗ[R] R) := rfl

@[simp]
/-
**Coalgebra.Quotient.counit_mk** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra.Quotient`。
形式化陈述：counit_mk (x : C) : counit (R
参数：x : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counit_mk (x : C) : counit (R := R) (Submodule.Quotient.mk (p := I) x) = counit x := rfl

@[simp]
/-
**Coalgebra.Quotient.comul_mk** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra.Quotient`。
形式化陈述：comul_mk (x : C) : comul (R
参数：x : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comul_mk (x : C) :
    comul (R := R) (Submodule.Quotient.mk (p := I) x) = map I.mkQ I.mkQ (comul x) := rfl

/-- `Submodule.mkQ` as a coalgebra homomorphism. -/
/-
**Coalgebra.Quotient.mkQCoalgHom** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra.Quotient`。
形式化陈述：{R : Type u_1} →   {C : Type u_2} →     [inst : CommRing R] →       [inst_
1 : AddCommGroup C] →         [inst_2 : _root_.Module R C] →           [inst_3 :
 CoalgebraStruct R C] → (I : Submodule R C) → [inst_4 : I.IsCoideal] → C →ₗc[R] 
C ⧸ I
参数：I : Submodule R C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.mkQ` as a coalgebra homomorphism.
-/
@[expose] def mkQCoalgHom : C →ₗc[R] C ⧸ I := ⟨I.mkQ, rfl, rfl⟩
/-
**Coalgebra.Quotient.mkQCoalgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.Quot
ient`。
形式化陈述：∀ {R : Type u_1} {C : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 C] [inst_2 : _root_.Module R C]   [inst_3 : CoalgebraStruct R C] (I : Submodule
 R C) [inst_4 : I.IsCoideal] (x : C),   (Coalgebra.Quotient.mkQCoalgHom I) x = S
ubmodule.Quotient.mk x
参数：I : Submodule R C；x : C；Coalgebra.Quotient.mkQCoalgHom I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.mkQ` as a coalgebra homomorphism.
-/
@[simp] lemma mkQCoalgHom_apply (x : C) :
    mkQCoalgHom (R := R) I x = Submodule.Quotient.mk x := rfl

end CoalgebraStruct

variable [Coalgebra R C] (I : Submodule R C) [I.IsCoideal]

/-
**Coalgebra.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Coalgebra.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coalgebra R (C ⧸ I) := by
  constructor <;> ext : 1 <;>
    simp only [coassoc_simps, comul_comp_mkQ, counit_comp_mkQ]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

end Coalgebra.Quotient

