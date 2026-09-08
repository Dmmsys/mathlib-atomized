/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The upper half plane

This file defines `UpperHalfPlane` to be the upper half plane in `ℂ`.

We define the notation `ℍ` for the upper half plane available in the locale
`UpperHalfPlane` so as not to conflict with the quaternions.
-/

@[expose] public section

noncomputable section

/-- The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace -/
@[ext]
/-
**UpperHalfPlane** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
-/
structure UpperHalfPlane where
  /-- Canonical embedding of the upper half-plane into `ℂ`. -/
  protected coe : ℂ
  coe_im_pos : 0 < coe.im

@[inherit_doc] scoped[UpperHalfPlane] notation "ℍ" => UpperHalfPlane

open UpperHalfPlane Complex

namespace UpperHalfPlane

attribute [coe] UpperHalfPlane.coe

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut ℍ ℂ := ⟨UpperHalfPlane.coe⟩

/-- Define `I := √-1` as an element of the upper half plane. -/
/-
**UpperHalfPlane.I** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：I : ℍ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `I := √-1` as an element of the upper half plane.
-/
def I : ℍ := ⟨Complex.I, by simp⟩

/-- Define the cube root of unity `ρ := (-1 + √-3) / 2` as an element of the upper half plane. -/
/-
**UpperHalfPlane.** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the cube root of unity `ρ := (-1 + √-3) / 2` as an element of the upper h
alf plane.
-/
def ρ : ℍ := ⟨⟨-1 / 2, Real.sqrt 3 / 2⟩, by positivity⟩
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ρ_sq : (ρ : ℂ) ^ 2 = -ρ - 1 := by
  simp [Complex.ext_iff, pow_two, ρ]
  grind
/-
**UpperHalfPlane.norm_** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_ρ : ‖(ρ : ℂ)‖ = 1 := by norm_num [norm_def, normSq, ← pow_two, ρ, div_pow]
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℍ := ⟨.I⟩
/-
**UpperHalfPlane.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {a b : UpperHalfPlane}, ↑a = ↑b ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `UpperHalfPlane.ext_iff`：∀ {x y : UpperHalfPlane}, x = y ↔ ↑x = ↑y
-/
@[simp, norm_cast] theorem coe_inj {a b : ℍ} : (a : ℂ) = b ↔ a = b := UpperHalfPlane.ext_iff.symm

@[deprecated (since := "2026-01-31")] alias ext_iff' := coe_inj
/-
**UpperHalfPlane.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_injective : Function.Injective UpperHalfPlane.coe
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
-/
theorem coe_injective : Function.Injective UpperHalfPlane.coe := fun _ _ ↦ UpperHalfPlane.ext
/-
**UpperHalfPlane.canLift** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
形式化陈述：canLift : CanLift Complex ℍ ((↑) : ℍ -> Complex) fun z => 0 < z.im where p
rf z hz
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance canLift : CanLift ℂ ℍ ((↑) : ℍ → ℂ) fun z => 0 < z.im where
  prf z hz := ⟨⟨z, hz⟩, rfl⟩
/-
**UpperHalfPlane.** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {P : ℍ → Prop} : (∀ z, P z) ↔ ∀ z hz, P ⟨z, hz⟩ :=
  ⟨fun h z hz ↦ h ⟨z, hz⟩, fun h z ↦ h z.1 z.2⟩
/-
**UpperHalfPlane.** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {P : ℍ → Prop} : (∃ z, P z) ↔ ∃ z hz, P ⟨z, hz⟩ :=
  ⟨fun ⟨⟨z, hz⟩, hP⟩ ↦ ⟨z, hz, hP⟩, fun ⟨z, hz, hP⟩ ↦ ⟨⟨z, hz⟩, hP⟩⟩

/-- Imaginary part -/
/-
**UpperHalfPlane.im** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：im (z : ℍ)
参数：z : ℍ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Imaginary part
-/
def im (z : ℍ) :=
  (z : ℂ).im

/-- Real part -/
/-
**UpperHalfPlane.re** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：re (z : ℍ)
参数：z : ℍ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Real part
-/
def re (z : ℍ) :=
  (z : ℂ).re

/-- Extensionality lemma in terms of `UpperHalfPlane.re` and `UpperHalfPlane.im`. -/
/-
**UpperHalfPlane.ext_re_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：ext_re_im {a b : ℍ} (hre : a.re = b.re) (him : a.im = b.im) : a = b
参数：hre : a.re = b.re；him : a.im = b.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w

--- 原说明 ---
Extensionality lemma in terms of `UpperHalfPlane.re` and `UpperHalfPlane.im`.
-/
theorem ext_re_im {a b : ℍ} (hre : a.re = b.re) (him : a.im = b.im) : a = b :=
  UpperHalfPlane.ext <| Complex.ext hre him

@[deprecated (since := "2026-01-29")]
alias ext' := ext_re_im

@[simp]
/-
**UpperHalfPlane.coe_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_im (z : ℍ) : (z : Complex).im = z.im
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_im (z : ℍ) : (z : ℂ).im = z.im :=
  rfl

@[simp]
/-
**UpperHalfPlane.coe_re** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_re (z : ℍ) : (z : Complex).re = z.re
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_re (z : ℍ) : (z : ℂ).re = z.re :=
  rfl

@[simp]
/-
**UpperHalfPlane.mk_re** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mk_re (z : Complex) (h : 0 < z.im) : (mk z h).re = z.re
参数：z : Complex；h : 0 < z.im。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_re (z : ℂ) (h : 0 < z.im) : (mk z h).re = z.re :=
  rfl

@[simp]
/-
**UpperHalfPlane.mk_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mk_im (z : Complex) (h : 0 < z.im) : (mk z h).im = z.im
参数：z : Complex；h : 0 < z.im。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_im (z : ℂ) (h : 0 < z.im) : (mk z h).im = z.im :=
  rfl
/-
**UpperHalfPlane.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_mk (z : Complex) (h : 0 < z.im) : (mk z h : Complex) = z
参数：z : Complex；h : 0 < z.im。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (z : ℂ) (h : 0 < z.im) : (mk z h : ℂ) = z :=
  rfl

@[simp]
/-
**UpperHalfPlane.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mk_coe (z : ℍ) (h : 0 < (z : Complex).im
参数：z : ℍ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (z : ℍ) (h : 0 < (z : ℂ).im := z.2) : mk z h = z :=
  rfl

@[simp]
/-
**UpperHalfPlane.I_im** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：I_im : I.im = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.I_im`：I_im : I.im = 1
-/
lemma I_im : I.im = 1 := Complex.I_im

@[simp]
/-
**UpperHalfPlane.I_re** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：I_re : I.re = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.I_re`：I_re : I.re = 0
-/
lemma I_re : I.re = 0 := Complex.I_re

@[simp, norm_cast]
/-
**UpperHalfPlane.coe_I** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_I : I = Complex.I
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_I : I = Complex.I := rfl

@[deprecated coe_mk (since := "2026-01-29")]
/-
**UpperHalfPlane.coe_mk_subtype** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_mk_subtype {z : Complex} (hz : 0 < z.im) : UpperHalfPlane.coe ⟨z, hz⟩ 
= z
参数：hz : 0 < z.im。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk_subtype {z : ℂ} (hz : 0 < z.im) :
    UpperHalfPlane.coe ⟨z, hz⟩ = z :=
  rfl
/-
**UpperHalfPlane.re_add_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：re_add_im (z : ℍ) : (z.re + z.im * Complex.I : Complex) = z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
-/
theorem re_add_im (z : ℍ) : (z.re + z.im * Complex.I : ℂ) = z :=
  Complex.re_add_im z
/-
**UpperHalfPlane.im_pos** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：im_pos (z : ℍ) : 0 < z.im
参数：z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
-/
theorem im_pos (z : ℍ) : 0 < z.im := z.coe_im_pos
/-
**UpperHalfPlane.im_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：im_ne_zero (z : ℍ) : z.im != 0
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
-/
theorem im_ne_zero (z : ℍ) : z.im ≠ 0 :=
  z.im_pos.ne'
/-
**UpperHalfPlane.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：ne_zero (z : ℍ) : (z : Complex) != 0
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
-/
theorem ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
  mt (congr_arg Complex.im) z.im_ne_zero
/-
**UpperHalfPlane.mem_slitPlane** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mem_slitPlane (z : ℍ) : (z : Complex) in Complex.slitPlane
参数：z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma mem_slitPlane (z : ℍ) : (z : ℂ) ∈ Complex.slitPlane := by
  simp [Complex.slitPlane, im_ne_zero z]

/-- Criterion for equality in terms of real part and norm. Useful when working with the
geometry of the fundamental domain. -/
/-
**UpperHalfPlane.eq_of_re_of_norm** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：eq_of_re_of_norm {τ τ' : ℍ} (hre : τ.re = τ'.re) (hnorm : ‖(τ : Complex)‖ 
= ‖(τ' : Complex)‖) : τ = τ'
参数：hre : τ.re = τ'.re；hnorm : ‖(τ : Complex)‖ = ‖(τ' : Complex)‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.sq_norm`：∀ (z : ℂ), ‖z‖ ^ 2 = Complex.normSq z
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `MonoidWithZeroHom.mk.congr_simp`：∀ {α : Type u_7} {β : Type u_8} [inst :
 MulZeroOneClass α] [inst_1 : MulZeroOneClass β]   (toZeroHom toZeroHom_1 : Zero
Hom α β) (e_toZeroHom…
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_left_inj₀`：pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b)
 (hn : n != 0) : a ^ n = b ^ n ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Criterion for equality in terms of real part and norm. Useful when working with 
the
geometry of the fundamental domain.
-/
lemma eq_of_re_of_norm {τ τ' : ℍ} (hre : τ.re = τ'.re) (hnorm : ‖(τ : ℂ)‖ = ‖(τ' : ℂ)‖) :
    τ = τ' := by
  apply_fun (· ^ 2) at hnorm
  simpa [UpperHalfPlane.ext_iff, Complex.ext_iff, hre, Complex.normSq, Complex.sq_norm,
    ← pow_two, pow_left_inj₀ τ.im_pos.le τ'.im_pos.le two_ne_zero] using hnorm

end UpperHalfPlane

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `UpperHalfPlane.im`. -/
@[positivity UpperHalfPlane.im _]
meta def evalUpperHalfPlaneIm : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(UpperHalfPlane.im $a) =>
    assertInstancesCommute
    pure (.positive q(@UpperHalfPlane.im_pos $a))
  | _, _, _ => throwError "not UpperHalfPlane.im"

/-- Extension for the `positivity` tactic: `UpperHalfPlane.coe`. -/
@[positivity UpperHalfPlane.coe _]
meta def evalUpperHalfPlaneCoe : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℂ), ~q(UpperHalfPlane.coe $a) =>
    assertInstancesCommute
    pure (.nonzero q(@UpperHalfPlane.ne_zero $a))
  | _, _, _ => throwError "not UpperHalfPlane.coe"

end Mathlib.Meta.Positivity

namespace UpperHalfPlane

/-
**UpperHalfPlane.normSq_pos** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：normSq_pos (z : ℍ) : 0 < Complex.normSq (z : Complex)
参数：z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.normSq_pos`：normSq_pos {z : Complex} : 0 < normSq z ↔ z != 0
· 使用定理 `UpperHalfPlane.ne_zero`：ne_zero (z : ℍ) : (z : Complex) != 0
-/
theorem normSq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by
  rw [Complex.normSq_pos]; exact z.ne_zero
/-
**UpperHalfPlane.normSq_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：normSq_ne_zero (z : ℍ) : Complex.normSq (z : Complex) != 0
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `UpperHalfPlane.normSq_pos`：normSq_pos (z : ℍ) : 0 < Complex.normSq (z : 
Complex)
-/
theorem normSq_ne_zero (z : ℍ) : Complex.normSq (z : ℂ) ≠ 0 :=
  (normSq_pos z).ne'
/-
**UpperHalfPlane.im_inv_neg_coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：im_inv_neg_coe_pos (z : ℍ) : 0 < (-z : Complex)⁻¹.im
参数：z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `Complex.inv_im`：inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.normSq_pos`：normSq_pos (z : ℍ) : 0 < Complex.normSq (z : 
Complex)
-/
theorem im_inv_neg_coe_pos (z : ℍ) : 0 < (-z : ℂ)⁻¹.im := by
  simpa [neg_div] using div_pos z.im_pos (normSq_pos z)
/-
**UpperHalfPlane.im_pnat_div_pos** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：im_pnat_div_pos (n : Nat) [NeZero n] (z : ℍ) : 0 < (-(n : Complex) / z).im
参数：n : Nat；z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `UpperHalfPlane.normSq_pos`：normSq_pos (z : ℍ) : 0 < Complex.normSq (z : 
Complex)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用引理 `Complex.div_im`：div_im (z w : Complex) : (z / w).im = z.im * w.re / norm
Sq w - z.re * w.im / normSq w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma im_pnat_div_pos (n : ℕ) [NeZero n] (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  suffices 0 < n * z.im / Complex.normSq z by simpa [Complex.div_im, neg_div]
  positivity [NeZero.ne n, z.normSq_pos]
/-
**UpperHalfPlane.ne_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：ne_ofReal (z : ℍ) (x : Real) : (z : Complex) != x
参数：z : ℍ；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma ne_ofReal (z : ℍ) (x : ℝ) : (z : ℂ) ≠ x :=
  ne_of_apply_ne Complex.im <| by simp [im_ne_zero]
/-
**UpperHalfPlane.ne_intCast** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：ne_intCast (z : ℍ) (n : Int) : (z : Complex) != n
参数：z : ℍ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.ne_ofReal`：ne_ofReal (z : ℍ) (x : Real) : (z : Complex) !
= x
-/
lemma ne_intCast (z : ℍ) (n : ℤ) : (z : ℂ) ≠ n := mod_cast ne_ofReal z n

@[deprecated (since := "2026-01-29")] alias ne_int := ne_intCast
/-
**UpperHalfPlane.ne_natCast** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：ne_natCast (z : ℍ) (n : Nat) : (z : Complex) != n
参数：z : ℍ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `UpperHalfPlane.ne_intCast`：ne_intCast (z : ℍ) (n : Int) : (z : Complex) 
!= n
-/
lemma ne_natCast (z : ℍ) (n : ℕ) : (z : ℂ) ≠ n := mod_cast ne_intCast z n

@[deprecated (since := "2026-01-29")] alias ne_nat := ne_natCast

section PosRealAction

/-
**UpperHalfPlane.posRealAction** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
形式化陈述：posRealAction : MulAction {x : Real // 0 < x} ℍ where smul x z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance posRealAction : MulAction {x : ℝ // 0 < x} ℍ where
  smul x z := mk ((x : ℝ) • (z : ℂ)) <| by simpa using mul_pos x.2 z.im_pos
  one_smul _ := UpperHalfPlane.ext <| one_smul _ _
  mul_smul x y z := UpperHalfPlane.ext <| mul_smul (x : ℝ) y (z : ℂ)

variable (x : {x : ℝ // 0 < x}) (z : ℍ)

@[simp]
/-
**UpperHalfPlane.coe_pos_real_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_pos_real_smul : ↑(x • z) = (x : Real) • (z : Complex)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pos_real_smul : ↑(x • z) = (x : ℝ) • (z : ℂ) :=
  rfl

@[simp]
/-
**UpperHalfPlane.pos_real_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：pos_real_im : (x • z).im = x * z.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
theorem pos_real_im : (x • z).im = x * z.im :=
  Complex.smul_im _ _

@[simp]
/-
**UpperHalfPlane.pos_real_re** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：pos_real_re : (x • z).re = x * z.re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
theorem pos_real_re : (x • z).re = x * z.re :=
  Complex.smul_re _ _
/-
**UpperHalfPlane.pos_real_smul_injective** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPla
ne`。
形式化陈述：pos_real_smul_injective (z : ℍ) : Function.Injective fun x : {x : Real // 
0 < x} => x • z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pos_real_smul_injective (z : ℍ) :
    Function.Injective fun x : {x : ℝ // 0 < x} ↦ x • z := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp_all [UpperHalfPlane.ext_iff, ne_zero]

end PosRealAction

section RealAddAction

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddAction ℝ ℍ where
  vadd x z := mk (x + z) <| by simpa using z.im_pos
  zero_vadd _ := by simp [HVAdd.hVAdd]
  add_vadd x y z := by simp [HVAdd.hVAdd, add_assoc]

variable (x : ℝ) (z : ℍ)

@[simp]
/-
**UpperHalfPlane.coe_vadd** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_vadd : ↑(x +ᵥ z) = (x + z : Complex)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vadd : ↑(x +ᵥ z) = (x + z : ℂ) :=
  rfl

@[simp]
/-
**UpperHalfPlane.vadd_re** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：vadd_re : (x +ᵥ z).re = x + z.re
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vadd_re : (x +ᵥ z).re = x + z.re :=
  rfl

@[simp]
/-
**UpperHalfPlane.vadd_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：vadd_im : (x +ᵥ z).im = z.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem vadd_im : (x +ᵥ z).im = z.im :=
  zero_add _

@[simp]
/-
**UpperHalfPlane.vadd_right_cancel_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：∀ {x y : ℝ} (z : UpperHalfPlane), x +ᵥ z = y +ᵥ z ↔ x = y
参数：z : UpperHalfPlane。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem vadd_right_cancel_iff {x y : ℝ} (z : ℍ) : x +ᵥ z = y +ᵥ z ↔ x = y := by
  simp [UpperHalfPlane.ext_iff]
/-
**UpperHalfPlane.vadd_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (z : UpperHalfPlane), Function.Injective fun x => x +ᵥ z
参数：z : UpperHalfPlane。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem vadd_left_injective (z : ℍ) : Function.Injective fun x : ℝ ↦ x +ᵥ z := by
  simp [Function.Injective]
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Infinite ℍ :=
  .of_injective _ <| UpperHalfPlane.vadd_left_injective I
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial ℍ := inferInstance

end RealAddAction

section upperHalfPlaneSet

/-- The upper half plane as a subset of `ℂ`.
This is convenient for taking derivatives of functions on the upper half plane. -/
/-
**UpperHalfPlane.upperHalfPlaneSet** 是 Mathlib 中的一个缩写定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：upperHalfPlaneSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper half plane as a subset of `ℂ`.
This is convenient for taking derivatives of functions on the upper half plane.
-/
abbrev upperHalfPlaneSet := {z : ℂ | 0 < z.im}

local notation "ℍₒ" => upperHalfPlaneSet
/-
**UpperHalfPlane.isOpen_upperHalfPlaneSet** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPl
ane`。
形式化陈述：isOpen_upperHalfPlaneSet : IsOpen ℍₒ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
lemma isOpen_upperHalfPlaneSet : IsOpen ℍₒ := isOpen_lt continuous_const Complex.continuous_im

@[simp]
/-
**UpperHalfPlane.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：range_coe : Set.range UpperHalfPlane.coe = ℍₒ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_coe : Set.range UpperHalfPlane.coe = ℍₒ := by
  ext; simp [UpperHalfPlane.exists]

end upperHalfPlaneSet

end UpperHalfPlane

