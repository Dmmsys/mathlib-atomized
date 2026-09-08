/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.MetricSpace.Dilation

/-!
# Dilation equivalence

In this file we define `DilationEquiv X Y`, a type of bundled equivalences between `X` and `Y` such
that `edist (f x) (f y) = r * edist x y` for some `r : ℝ≥0`, `r ≠ 0`.

We also develop basic API about these equivalences.

## TODO

- Add missing lemmas (compare to other `*Equiv` structures).
- [after-port] Add `DilationEquivInstance` for `IsometryEquiv`.
-/

@[expose] public section

open scoped NNReal ENNReal
open Function Set Filter Bornology
open Dilation (ratio ratio_ne_zero ratio_pos edist_eq)

section Class

variable (F : Type*) (X Y : outParam Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- Typeclass saying that `F` is a type of bundled equivalences such that all `e : F` are
dilations. -/
/-
**DilationEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (X : outParam (Type u_2)) →     (Y : outParam (Type u_3
)) → [PseudoEMetricSpace X] → [PseudoEMetricSpace Y] → [EquivLike F X Y] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass saying that `F` is a type of bundled equivalences such that all `e : F
` are
dilations.
-/
class DilationEquivClass [EquivLike F X Y] : Prop where
  edist_eq' : ∀ f : F, ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : X, edist (f x) (f y) = r * edist x y
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [EquivLike F X Y] [DilationEquivClass F X Y] : DilationClass F X Y :=
  { (inferInstance : FunLike F X Y), ‹DilationEquivClass F X Y› with }

end Class

/-- Type of equivalences `X ≃ Y` such that `∀ x y, edist (f x) (f y) = r * edist x y` for some
`r : ℝ≥0`, `r ≠ 0`. -/
/-
**DilationEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → (Y : Type u_2) → [PseudoEMetricSpace X] → [PseudoEMetricS
pace Y] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type of equivalences `X ≃ Y` such that `∀ x y, edist (f x) (f y) = r * edist x y
` for some
`r : ℝ≥0`, `r ≠ 0`.
-/
structure DilationEquiv (X Y : Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    extends X ≃ Y, Dilation X Y

@[inherit_doc] infixl:25 " ≃ᵈ " => DilationEquiv

namespace DilationEquiv

section PseudoEMetricSpace

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-
**DilationEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (X ≃ᵈ Y) X Y where
  coe f := f.1
  inv f := f.1.symm
  left_inv f := f.left_inv'
  right_inv f := f.right_inv'
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h -; congr; exact DFunLike.ext' h
/-
**DilationEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DilationEquivClass (X ≃ᵈ Y) X Y where
  edist_eq' f := f.edist_eq'
/-
**DilationEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   ⇑e.toEquiv = ⇑e
参数：e : X ≃ᵈ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toEquiv (e : X ≃ᵈ Y) : ⇑e.toEquiv = e := rfl

@[ext]
/-
**DilationEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {e e' : X ≃ᵈ Y},   (∀ (x : X), e x = e' x) → e = e'
参数：∀ (x : X), e x = e' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
protected theorem ext {e e' : X ≃ᵈ Y} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/-- Inverse `DilationEquiv`. -/
/-
**DilationEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `DilationEquiv`。
形式化陈述：symm (e : X ≃ᵈ Y) : Y ≃ᵈ X where toEquiv
参数：e : X ≃ᵈ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Inverse `DilationEquiv`.
-/
def symm (e : X ≃ᵈ Y) : Y ≃ᵈ X where
  toEquiv := e.1.symm
  edist_eq' := by
    refine ⟨(ratio e)⁻¹, inv_ne_zero <| ratio_ne_zero e, e.surjective.forall₂.2 fun x y ↦ ?_⟩
    simp_rw [Equiv.toFun_as_coe, Equiv.symm_apply_apply, coe_toEquiv, edist_eq]
    rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ (ratio_ne_zero e),
      ENNReal.coe_one, one_mul]
/-
**DilationEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   e.symm.symm = e
参数：e : X ≃ᵈ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_symm (e : X ≃ᵈ Y) : e.symm.symm = e := rfl
/-
**DilationEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：symm_bijective : Function.Bijective (DilationEquiv.symm : (X ≃ᵈ Y) -> Y ≃ᵈ
 X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `DilationEquiv.symm_symm`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] (e : X ≃ᵈ Y),   e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (DilationEquiv.symm : (X ≃ᵈ Y) → Y ≃ᵈ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**DilationEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y) (x : Y),   e (e.symm x) = x
参数：e : X ≃ᵈ Y；x : Y；e.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
@[simp] theorem apply_symm_apply (e : X ≃ᵈ Y) (x : Y) : e (e.symm x) = x := e.right_inv x
/-
**DilationEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y) (x : X),   e.symm (e x) = x
参数：e : X ≃ᵈ Y；x : X；e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
@[simp] theorem symm_apply_apply (e : X ≃ᵈ Y) (x : X) : e.symm (e x) = x := e.left_inv x
/-
**DilationEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：symm_apply_eq (e : X ≃ᵈ Y) {x : X} {y : Y} : e.symm y = x ↔ y = e x
参数：e : X ≃ᵈ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : X ≃ᵈ Y) {x : X} {y : Y} : e.symm y = x ↔ y = e x :=
  Equiv.symm_apply_eq _
/-
**DilationEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：eq_symm_apply (e : X ≃ᵈ Y) {x : X} {y : Y} : x = e.symm y ↔ e x = y
参数：e : X ≃ᵈ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : X ≃ᵈ Y) {x : X} {y : Y} : x = e.symm y ↔ e x = y :=
  Equiv.eq_symm_apply _

/-- See Note [custom simps projection]. -/
/-
**DilationEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `DilationEquiv.Simps`
。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [inst : PseudoEMetricSpace X] → [inst_1 
: PseudoEMetricSpace Y] → X ≃ᵈ Y → Y → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.symm_apply (e : X ≃ᵈ Y) : Y → X := e.symm

initialize_simps_projections DilationEquiv (toFun → apply, invFun → symm_apply)
/-
**DilationEquiv.ratio_toDilation** 是 Mathlib 中的一个引理，位于命名空间 `DilationEquiv`。
形式化陈述：ratio_toDilation (e : X ≃ᵈ Y) : ratio e.toDilation = ratio e
参数：e : X ≃ᵈ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ratio_toDilation (e : X ≃ᵈ Y) : ratio e.toDilation = ratio e := rfl

/-- Identity map as a `DilationEquiv`. -/
@[simps! -fullyApplied apply]
/-
**DilationEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `DilationEquiv`。
形式化陈述：refl (X : Type*) [PseudoEMetricSpace X] : X ≃ᵈ X where toEquiv
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Identity map as a `DilationEquiv`.
-/
def refl (X : Type*) [PseudoEMetricSpace X] : X ≃ᵈ X where
  toEquiv := .refl X
  edist_eq' := ⟨1, one_ne_zero, fun _ _ ↦ by simp⟩
/-
**DilationEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X], (DilationEquiv.refl X).sym
m = DilationEquiv.refl X
参数：DilationEquiv.refl X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem refl_symm : (refl X).symm = refl X := rfl
/-
**DilationEquiv.ratio_refl** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X], Dilation.ratio (DilationEq
uiv.refl X) = 1
参数：DilationEquiv.refl X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ratio_id`：ratio_id : ratio (Dilation.id α) = 1
-/
@[simp] theorem ratio_refl : ratio (refl X) = 1 := Dilation.ratio_id

/-- Composition of `DilationEquiv`s. -/
@[simps! -fullyApplied apply]
/-
**DilationEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `DilationEquiv`。
形式化陈述：trans (e₁ : X ≃ᵈ Y) (e₂ : Y ≃ᵈ Z) : X ≃ᵈ Z where toEquiv
参数：e₁ : X ≃ᵈ Y；e₂ : Y ≃ᵈ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Dilation.edist_eq'`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (self : α →ᵈ β),   ∃ r, r ≠ 0 ∧ ∀ (x y
 : α), e…

--- 原说明 ---
Composition of `DilationEquiv`s.
-/
def trans (e₁ : X ≃ᵈ Y) (e₂ : Y ≃ᵈ Z) : X ≃ᵈ Z where
  toEquiv := e₁.1.trans e₂.1
  __ := e₂.toDilation.comp e₁.toDilation
/-
**DilationEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   (DilationEquiv.refl X).trans e = e
参数：e : X ≃ᵈ Y；DilationEquiv.refl X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem refl_trans (e : X ≃ᵈ Y) : (refl X).trans e = e := rfl
/-
**DilationEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   e.trans (DilationEquiv.refl Y) = e
参数：e : X ≃ᵈ Y；DilationEquiv.refl Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem trans_refl (e : X ≃ᵈ Y) : e.trans (refl Y) = e := rfl
/-
**DilationEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   e.symm.trans e = DilationEquiv.refl Y
参数：e : X ≃ᵈ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DilationEquiv.ext`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetric
Space X] [inst_1 : PseudoEMetricSpace Y] {e e' : X ≃ᵈ Y},   (∀ (x : X), e x = e'
 x) → e…
· 使用定理 `DilationEquiv.apply_symm_apply`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] (e : X ≃ᵈ Y) (x : Y),   e 
(e.symm x) = x
-/
@[simp] theorem symm_trans_self (e : X ≃ᵈ Y) : e.symm.trans e = refl Y :=
  DilationEquiv.ext e.apply_symm_apply
/-
**DilationEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   e.trans e.symm = DilationEquiv.refl X
参数：e : X ≃ᵈ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DilationEquiv.ext`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetric
Space X] [inst_1 : PseudoEMetricSpace Y] {e e' : X ≃ᵈ Y},   (∀ (x : X), e x = e'
 x) → e…
· 使用定理 `DilationEquiv.symm_apply_apply`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] (e : X ≃ᵈ Y) (x : X),   e.
symm (e x) = x
-/
@[simp] theorem self_trans_symm (e : X ≃ᵈ Y) : e.trans e.symm = refl X :=
  DilationEquiv.ext e.symm_apply_apply
/-
**DilationEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   Function.Surjective ⇑e
参数：e : X ≃ᵈ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (e : X ≃ᵈ Y) : Surjective e := e.1.surjective
/-
**DilationEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   Function.Bijective ⇑e
参数：e : X ≃ᵈ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (e : X ≃ᵈ Y) : Bijective e := e.1.bijective
/-
**DilationEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] (e : X ≃ᵈ Y),   Function.Injective ⇑e
参数：e : X ≃ᵈ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (e : X ≃ᵈ Y) : Injective e := e.1.injective

@[simp]
/-
**DilationEquiv.ratio_trans** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：ratio_trans (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z) : ratio (e.trans e') = ratio e * ra
tio e'
参数：e : X ≃ᵈ Y；e' : Y ≃ᵈ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instDilationClassOfDilationEquivClass`：∀ (F : Type u_1) (X : outParam (T
ype u_2)) (Y : outParam (Type u_3)) [inst : PseudoEMetricSpace X]   [inst_1 : Ps
eudoEMetricSpace Y] [inst_2…
· 使用定理 `DilationEquiv.instDilationEquivClass`：∀ {X : Type u_1} {Y : Type u_2} [i
nst : PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y],   DilationEquivClas
s (X ≃ᵈ Y) X Y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `DilationEquiv.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Pseudo
EMetricSpace X] [inst_1 : PseudoEMetricSpace Y] (e : X ≃ᵈ Y),   Function.Surject
ive ⇑e
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Dilation.ratio_of_trivial`：ratio_of_trivial [DilationClass F α β] (f : F
) (h : forall x y : α, edist x y = 0 ∨ edist x y = ∞) : ratio f = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Dilation.ratio_comp'`：ratio_comp' {g : β ->ᵈ γ} {f : α ->ᵈ β} (hne : exi
sts x y : α, edist x y != 0 ∧ edist x y != ⊤) : ratio (g.comp f) = ratio g * rat
io f
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem ratio_trans (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z) : ratio (e.trans e') = ratio e * ratio e' := by
  -- If `X` is trivial, then so is `Y`, otherwise we apply `Dilation.ratio_comp'`
  by_cases! hX : ∀ x y : X, edist x y = 0 ∨ edist x y = ∞
  · have hY : ∀ x y : Y, edist x y = 0 ∨ edist x y = ∞ := e.surjective.forall₂.2 fun x y ↦ by
      refine (hX x y).imp (fun h ↦ ?_) fun h ↦ ?_ <;> simp [*, Dilation.ratio_ne_zero]
    simp [Dilation.ratio_of_trivial, *]
  exact (Dilation.ratio_comp' (g := e'.toDilation) (f := e.toDilation) hX).trans (mul_comm _ _)

@[simp]
/-
**DilationEquiv.ratio_symm** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：ratio_symm (e : X ≃ᵈ Y) : ratio e.symm = (ratio e)⁻¹
参数：e : X ≃ᵈ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `instDilationClassOfDilationEquivClass`：∀ (F : Type u_1) (X : outParam (T
ype u_2)) (Y : outParam (Type u_3)) [inst : PseudoEMetricSpace X]   [inst_1 : Ps
eudoEMetricSpace Y] [inst_2…
· 使用定理 `DilationEquiv.instDilationEquivClass`：∀ {X : Type u_1} {Y : Type u_2} [i
nst : PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y],   DilationEquivClas
s (X ≃ᵈ Y) X Y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DilationEquiv.ratio_trans`：ratio_trans (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z) : rati
o (e.trans e') = ratio e * ratio e'
· 使用定理 `DilationEquiv.symm_trans_self`：∀ {X : Type u_1} {Y : Type u_2} [inst : P
seudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] (e : X ≃ᵈ Y),   e.symm.tran
s e = DilationEquiv…
· 使用定理 `DilationEquiv.ratio_refl`：∀ {X : Type u_1} [inst : PseudoEMetricSpace X]
, Dilation.ratio (DilationEquiv.refl X) = 1
-/
theorem ratio_symm (e : X ≃ᵈ Y) : ratio e.symm = (ratio e)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by rw [← ratio_trans, symm_trans_self, ratio_refl]
/-
**DilationEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (X ≃ᵈ X) where
  mul e e' := e'.trans e
  mul_assoc _ _ _ := rfl
  one := refl _
  one_mul _ := rfl
  mul_one _ := rfl
  inv := symm
  inv_mul_cancel := self_trans_symm
/-
**DilationEquiv.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：mul_def (e e' : X ≃ᵈ X) : e * e' = e'.trans e
参数：e e' : X ≃ᵈ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (e e' : X ≃ᵈ X) : e * e' = e'.trans e := rfl
/-
**DilationEquiv.one_def** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：one_def : (1 : X ≃ᵈ X) = refl X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : X ≃ᵈ X) = refl X := rfl
/-
**DilationEquiv.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：inv_def (e : X ≃ᵈ X) : e⁻¹ = e.symm
参数：e : X ≃ᵈ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (e : X ≃ᵈ X) : e⁻¹ = e.symm := rfl
/-
**DilationEquiv.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] (e e' : X ≃ᵈ X), ⇑(e * e') 
= ⇑e ∘ ⇑e'
参数：e e' : X ≃ᵈ X；e * e'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mul (e e' : X ≃ᵈ X) : ⇑(e * e') = e ∘ e' := rfl
/-
**DilationEquiv.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X], ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_one : ⇑(1 : X ≃ᵈ X) = id := rfl
/-
**DilationEquiv.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：coe_inv (e : X ≃ᵈ X) : ⇑(e⁻¹) = e.symm
参数：e : X ≃ᵈ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (e : X ≃ᵈ X) : ⇑(e⁻¹) = e.symm := rfl

/-- `Dilation.ratio` as a monoid homomorphism. -/
/-
**DilationEquiv.ratioHom** 是 Mathlib 中的一个定义，位于命名空间 `DilationEquiv`。
形式化陈述：ratioHom : (X ≃ᵈ X) ->* Real>=0 where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DilationEquiv.ratio_refl`：∀ {X : Type u_1} [inst : PseudoEMetricSpace X]
, Dilation.ratio (DilationEquiv.refl X) = 1

--- 原说明 ---
`Dilation.ratio` as a monoid homomorphism.
-/
noncomputable def ratioHom : (X ≃ᵈ X) →* ℝ≥0 where
  toFun := Dilation.ratio
  map_one' := ratio_refl
  map_mul' _ _ := (ratio_trans _ _).trans (mul_comm _ _)

@[simp]
/-
**DilationEquiv.ratio_inv** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：ratio_inv (e : X ≃ᵈ X) : ratio (e⁻¹) = (ratio e)⁻¹
参数：e : X ≃ᵈ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DilationEquiv.ratio_symm`：ratio_symm (e : X ≃ᵈ Y) : ratio e.symm = (rati
o e)⁻¹
-/
theorem ratio_inv (e : X ≃ᵈ X) : ratio (e⁻¹) = (ratio e)⁻¹ := ratio_symm e

@[simp]
/-
**DilationEquiv.ratio_pow** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：ratio_pow (e : X ≃ᵈ X) (n : Nat) : ratio (e ^ n) = ratio e ^ n
参数：e : X ≃ᵈ X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem ratio_pow (e : X ≃ᵈ X) (n : ℕ) : ratio (e ^ n) = ratio e ^ n :=
  ratioHom.map_pow _ _

@[simp]
/-
**DilationEquiv.ratio_zpow** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：ratio_zpow (e : X ≃ᵈ X) (n : Int) : ratio (e ^ n) = ratio e ^ n
参数：e : X ≃ᵈ X；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
-/
theorem ratio_zpow (e : X ≃ᵈ X) (n : ℤ) : ratio (e ^ n) = ratio e ^ n :=
  ratioHom.map_zpow _ _

/-- `DilationEquiv.toEquiv` as a monoid homomorphism. -/
@[simps]
/-
**DilationEquiv.toPerm** 是 Mathlib 中的一个定义，位于命名空间 `DilationEquiv`。
形式化陈述：toPerm : (X ≃ᵈ X) ->* Equiv.Perm X where toFun e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DilationEquiv.toEquiv` as a monoid homomorphism.
-/
def toPerm : (X ≃ᵈ X) →* Equiv.Perm X where
  toFun e := e.1
  map_mul' _ _ := rfl
  map_one' := rfl

@[norm_cast]
/-
**DilationEquiv.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `DilationEquiv`。
形式化陈述：coe_pow (e : X ≃ᵈ X) (n : Nat) : ⇑(e ^ n) = e^[n]
参数：e : X ≃ᵈ X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DilationEquiv.coe_toEquiv`：∀ {X : Type u_1} {Y : Type u_2} [inst : Pseud
oEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] (e : X ≃ᵈ Y),   ⇑e.toEquiv = ⇑e
· 使用定理 `DilationEquiv.toPerm_apply`：∀ {X : Type u_1} [inst : PseudoEMetricSpace 
X] (e : X ≃ᵈ X), DilationEquiv.toPerm e = e.toEquiv
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Equiv.Perm.coe_pow`：∀ {α : Type u_4} (f : Equiv.Perm α) (n : ℕ), ⇑(f ^ n
) = (⇑f)^[n]
-/
theorem coe_pow (e : X ≃ᵈ X) (n : ℕ) : ⇑(e ^ n) = e^[n] := by
  rw [← coe_toEquiv, ← toPerm_apply, map_pow, Equiv.Perm.coe_pow]; rfl

-- TODO: Once `IsometryEquiv` follows the `*EquivClass` pattern, replace this with an instance
-- of `DilationEquivClass` assuming `IsometryEquivClass`.
/-- Every isometry equivalence is a dilation equivalence of ratio `1`. -/
/-
**DilationEquiv._root_.IsometryEquiv.toDilationEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every isometry equivalence is a dilation equivalence of ratio `1`.
-/
def _root_.IsometryEquiv.toDilationEquiv (e : X ≃ᵢ Y) : X ≃ᵈ Y where
  edist_eq' := ⟨1, one_ne_zero, by simpa using! e.isometry⟩
  __ := e.toEquiv

@[simp]
/-
**DilationEquiv._root_.IsometryEquiv.toDilationEquiv_apply** 是 Mathlib 中的一个引理，位于
命名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsometryEquiv.toDilationEquiv_apply (e : X ≃ᵢ Y) (x : X) :
    e.toDilationEquiv x = e x :=
  rfl

@[simp]
/-
**DilationEquiv._root_.IsometryEquiv.toDilationEquiv_symm** 是 Mathlib 中的一个引理，位于命
名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsometryEquiv.toDilationEquiv_symm (e : X ≃ᵢ Y) :
    e.symm.toDilationEquiv = e.toDilationEquiv.symm :=
  rfl

@[simp]
/-
**DilationEquiv._root_.IsometryEquiv.coe_toDilationEquiv** 是 Mathlib 中的一个引理，位于命名
空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsometryEquiv.coe_toDilationEquiv (e : X ≃ᵢ Y) : ⇑e.toDilationEquiv = e :=
  rfl

@[simp]
/-
**DilationEquiv._root_.IsometryEquiv.coe_symm_toDilationEquiv** 是 Mathlib 中的一个引理
，位于命名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsometryEquiv.coe_symm_toDilationEquiv (e : X ≃ᵢ Y) :
    ⇑e.toDilationEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**DilationEquiv._root_.IsometryEquiv.toDilationEquiv_toDilation** 是 Mathlib 中的一个
引理，位于命名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsometryEquiv.toDilationEquiv_toDilation (e : X ≃ᵢ Y) :
    (e.toDilationEquiv.toDilation : X →ᵈ Y) = e.isometry.toDilation :=
  rfl

@[simp]
/-
**DilationEquiv._root_.IsometryEquiv.toDilationEquiv_ratio** 是 Mathlib 中的一个引理，位于
命名空间 `DilationEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsometryEquiv.toDilationEquiv_ratio (e : X ≃ᵢ Y) : ratio e.toDilationEquiv = 1 := by
  rw [← ratio_toDilation, IsometryEquiv.toDilationEquiv_toDilation, Isometry.toDilation_ratio]

/-- Reinterpret a `DilationEquiv` as a homeomorphism. -/
/-
**DilationEquiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `DilationEquiv`。
形式化陈述：toHomeomorph (e : X ≃ᵈ Y) : X ≃ₜ Y where continuous_toFun
参数：e : X ≃ᵈ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `DilationEquiv` as a homeomorphism.
-/
def toHomeomorph (e : X ≃ᵈ Y) : X ≃ₜ Y where
  continuous_toFun := Dilation.toContinuous e
  continuous_invFun := Dilation.toContinuous e.symm
  __ := e.toEquiv

@[simp]
/-
**DilationEquiv.toHomeomorph_symm** 是 Mathlib 中的一个引理，位于命名空间 `DilationEquiv`。
形式化陈述：toHomeomorph_symm (e : X ≃ᵈ Y) : e.symm.toHomeomorph = e.toHomeomorph.symm
参数：e : X ≃ᵈ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHomeomorph_symm (e : X ≃ᵈ Y) : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
/-
**DilationEquiv.coe_toHomeomorph** 是 Mathlib 中的一个引理，位于命名空间 `DilationEquiv`。
形式化陈述：coe_toHomeomorph (e : X ≃ᵈ Y) : ⇑e.toHomeomorph = e
参数：e : X ≃ᵈ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toHomeomorph (e : X ≃ᵈ Y) : ⇑e.toHomeomorph = e :=
  rfl

@[simp]
/-
**DilationEquiv.coe_symm_toHomeomorph** 是 Mathlib 中的一个引理，位于命名空间 `DilationEquiv`。
形式化陈述：coe_symm_toHomeomorph (e : X ≃ᵈ Y) : ⇑e.toHomeomorph.symm = e.symm
参数：e : X ≃ᵈ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symm_toHomeomorph (e : X ≃ᵈ Y) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

end PseudoEMetricSpace

section PseudoMetricSpace

variable {X Y F : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable [EquivLike F X Y] [DilationEquivClass F X Y]

@[simp]
/-
**DilationEquiv.map_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `DilationEquiv`。
形式化陈述：map_cobounded (e : F) : map e (cobounded X) = cobounded Y
参数：e : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Dilation.comap_cobounded`：comap_cobounded : Filter.comap f (cobounded β)
 = cobounded α
· 使用定理 `instDilationClassOfDilationEquivClass`：∀ (F : Type u_1) (X : outParam (T
ype u_2)) (Y : outParam (Type u_3)) [inst : PseudoEMetricSpace X]   [inst_1 : Ps
eudoEMetricSpace Y] [inst_2…
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
lemma map_cobounded (e : F) : map e (cobounded X) = cobounded Y := by
  rw [← Dilation.comap_cobounded e, map_comap_of_surjective (EquivLike.surjective e)]

end PseudoMetricSpace

end DilationEquiv

