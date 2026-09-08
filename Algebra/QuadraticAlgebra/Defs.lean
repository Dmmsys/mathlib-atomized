/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Kenny Lau, Jiayang Hong
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic


/-!

# Quadratic Algebra

In this file we define the quadratic algebra `QuadraticAlgebra R a b` over a commutative ring `R`,
and define some algebraic structures on it.

## Main definitions

* `QuadraticAlgebra R a b`:
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b` in `R`.

## Tags

Quadratic algebra, quadratic extension

-/

@[expose] public section

universe u

/-- Quadratic algebra over a type with fixed coefficient where $i^2 = a + bi$, implemented as
a structure with two fields, `re` and `im`. When `R` is a commutative ring, this is isomorphic to
`R[X]/(X^2-b*X-a)`. -/
@[ext]
/-
**QuadraticAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → R → R → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quadratic algebra over a type with fixed coefficient where $i^2 = a + bi$, imple
mented as
a structure with two fields, `re` and `im`. When `R` is a commutative ring, this
 is isomorphic to
`R[X]/(X^2-b*X-a)`.
-/
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  /-- Real part of an element in quadratic algebra -/
  re : R
  /-- Imaginary part of an element in quadratic algebra -/
  im : R
deriving DecidableEq

initialize_simps_projections QuadraticAlgebra (as_prefix re, as_prefix im)

variable {R : Type*}
namespace QuadraticAlgebra

/-- The equivalence between quadratic algebra over `R` and `R × R`. -/
@[simps symm_apply]
/-
**QuadraticAlgebra.equivProd** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：equivProd (a b : R) : QuadraticAlgebra R a b ≃ R × R where toFun z
参数：a b : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between quadratic algebra over `R` and `R × R`.
-/
def equivProd (a b : R) : QuadraticAlgebra R a b ≃ R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

@[simp]
/-
**QuadraticAlgebra.mk_eta** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：mk_eta {a b} (z : QuadraticAlgebra R a b) : mk z.re z.im = z
参数：z : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eta {a b} (z : QuadraticAlgebra R a b) :
    mk z.re z.im = z := rfl

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton R] : Subsingleton (QuadraticAlgebra R a b) := (equivProd a b).subsingleton
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (QuadraticAlgebra R a b) := (equivProd a b).nontrivial

section Zero
variable [Zero R]

/-- The natural function `R → QuadraticAlgebra R a b`.

Note that, if `R` is a ring, you should use `algebraMap` instead of `C`. -/
/-
**QuadraticAlgebra.C** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：{R : Type u_1} → {a b : R} → [Zero R] → R → QuadraticAlgebra R a b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural function `R → QuadraticAlgebra R a b`.

Note that, if `R` is a ring, you should use `algebraMap` instead of `C`.
-/
protected def C (x : R) : QuadraticAlgebra R a b := ⟨x, 0⟩

@[simp]
/-
**QuadraticAlgebra.re_C** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：re_C : (.C r : QuadraticAlgebra R a b).re = r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_C : (.C r : QuadraticAlgebra R a b).re = r := rfl

@[simp]
/-
**QuadraticAlgebra.im_C** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：im_C : (.C r : QuadraticAlgebra R a b).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_C : (.C r : QuadraticAlgebra R a b).im = 0 := rfl
/-
**QuadraticAlgebra.C_injective** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_injective : Function.Injective (.C : R -> QuadraticAlgebra R a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem C_injective : Function.Injective (.C : R → QuadraticAlgebra R a b) :=
  fun _ _ h => congr_arg re h

@[simp]
/-
**QuadraticAlgebra.C_inj** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_inj {x y : R} : (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `QuadraticAlgebra.C_injective`：C_injective : Function.Injective (.C : R -
> QuadraticAlgebra R a b)
-/
theorem C_inj {x y : R} : (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y :=
  C_injective.eq_iff
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (QuadraticAlgebra R a b) := ⟨⟨0, 0⟩⟩
/-
**QuadraticAlgebra.re_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Zero R], QuadraticAlgebra.re 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_zero : (0 : QuadraticAlgebra R a b).re = 0 := rfl
/-
**QuadraticAlgebra.im_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Zero R], QuadraticAlgebra.im 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_zero : (0 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp]
/-
**QuadraticAlgebra.C_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_zero : (.C 0 : QuadraticAlgebra R a b) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_zero : (.C 0 : QuadraticAlgebra R a b) = 0 := rfl

@[simp]
/-
**QuadraticAlgebra.C_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_eq_zero_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticAlgebra.C_zero`：C_zero : (.C 0 : QuadraticAlgebra R a b) = 0
· 使用定理 `QuadraticAlgebra.C_inj`：C_inj {x y : R} : (.C x : QuadraticAlgebra R a b
) = .C y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem C_eq_zero_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0 := by
  rw [← C_zero, C_inj]
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (QuadraticAlgebra R a b) := ⟨0⟩

section One
variable [One R]

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (QuadraticAlgebra R a b) := ⟨⟨1, 0⟩⟩
/-
**QuadraticAlgebra.re_one** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Zero R] [inst_1 : One R], QuadraticAlge
bra.re 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem re_one : (1 : QuadraticAlgebra R a b).re = 1 := rfl
/-
**QuadraticAlgebra.im_one** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Zero R] [inst_1 : One R], QuadraticAlge
bra.im 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[scoped simp] theorem im_one : (1 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp]
/-
**QuadraticAlgebra.C_one** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_one : (.C 1 : QuadraticAlgebra R a b) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_one : (.C 1 : QuadraticAlgebra R a b) = 1 := rfl

@[simp]
/-
**QuadraticAlgebra.C_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_eq_one_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticAlgebra.C_one`：C_one : (.C 1 : QuadraticAlgebra R a b) = 1
· 使用定理 `QuadraticAlgebra.C_inj`：C_inj {x y : R} : (.C x : QuadraticAlgebra R a b
) = .C y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem C_eq_one_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1 := by
  rw [← C_one, C_inj]

end One

end Zero

section Add
variable [Add R]

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (QuadraticAlgebra R a b) where
  add z w := ⟨z.re + w.re, z.im + w.im⟩
/-
**QuadraticAlgebra.re_add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Add R] (z w : QuadraticAlgebra R a b), 
(z + w).re = z.re + w.re
参数：z w : QuadraticAlgebra R a b；z + w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_add (z w : QuadraticAlgebra R a b) :
    (z + w).re = z.re + w.re := rfl
/-
**QuadraticAlgebra.im_add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Add R] (z w : QuadraticAlgebra R a b), 
(z + w).im = z.im + w.im
参数：z w : QuadraticAlgebra R a b；z + w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_add (z w : QuadraticAlgebra R a b) :
    (z + w).im = z.im + w.im := rfl

@[simp]
/-
**QuadraticAlgebra.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：mk_add_mk (z w : QuadraticAlgebra R a b) : mk z.re z.im + mk w.re w.im = (
mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b)
参数：z w : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_add_mk (z w : QuadraticAlgebra R a b) :
    mk z.re z.im + mk w.re w.im = (mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b) := rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

@[simp]
/-
**QuadraticAlgebra.C_add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_add (x y : R) : (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem C_add (x y : R) : (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y := by
  ext <;> simp

end AddZeroClass

section Neg
variable [Neg R]

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (QuadraticAlgebra R a b) where neg z := ⟨-z.re, -z.im⟩
/-
**QuadraticAlgebra.re_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Neg R] (z : QuadraticAlgebra R a b), (-
z).re = -z.re
参数：z : QuadraticAlgebra R a b；-z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_neg (z : QuadraticAlgebra R a b) : (-z).re = -z.re := rfl
/-
**QuadraticAlgebra.im_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Neg R] (z : QuadraticAlgebra R a b), (-
z).im = -z.im
参数：z : QuadraticAlgebra R a b；-z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_neg (z : QuadraticAlgebra R a b) : (-z).im = -z.im := rfl

@[simp]
/-
**QuadraticAlgebra.neg_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：neg_mk (x y : R) : -(mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_mk (x y : R) :
    -(mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩ := rfl

end Neg

section AddGroup

@[simp]
/-
**QuadraticAlgebra.C_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_neg [NegZeroClass R] (x : R) : (.C (-x) : QuadraticAlgebra R a b) = -.C 
x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem C_neg [NegZeroClass R] (x : R) : (.C (-x) : QuadraticAlgebra R a b) = -.C x := by
  ext <;> simp
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Sub R] : Sub (QuadraticAlgebra R a b) where
  sub z w := ⟨z.re - w.re, z.im - w.im⟩
/-
**QuadraticAlgebra.re_sub** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Sub R] (z w : QuadraticAlgebra R a b), 
(z - w).re = z.re - w.re
参数：z w : QuadraticAlgebra R a b；z - w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).re = z.re - w.re := rfl
/-
**QuadraticAlgebra.im_sub** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Sub R] (z w : QuadraticAlgebra R a b), 
(z - w).im = z.im - w.im
参数：z w : QuadraticAlgebra R a b；z - w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).im = z.im - w.im := rfl

@[simp]
/-
**QuadraticAlgebra.mk_sub_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) : (mk x1 y1 : QuadraticAlgebra R a b) 
- mk x2 y2 = mk (x1 - x2) (y1 - y2)
参数：x1 y1 x2 y2 : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) - mk x2 y2 = mk (x1 - x2) (y1 - y2) := rfl

@[simp]
/-
**QuadraticAlgebra.C_sub** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_sub (r1 r2 : R) [SubNegZeroMonoid R] : (.C (r1 - r2) : QuadraticAlgebra 
R a b) = .C r1 - .C r2
参数：r1 r2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G], 0 - 0 = 0
-/
theorem C_sub (r1 r2 : R) [SubNegZeroMonoid R] :
    (.C (r1 - r2) : QuadraticAlgebra R a b) = .C r1 - .C r2 :=
  QuadraticAlgebra.ext rfl zero_sub_zero.symm

end AddGroup

section Mul
variable [Mul R] [Add R]

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (QuadraticAlgebra R a b) where
  mul z w := ⟨z.1 * w.1 + a * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2⟩
/-
**QuadraticAlgebra.re_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Mul R] [inst_1 : Add R] (z w : Quadrati
cAlgebra R a b),   (z * w).re = z.re * w.re + a * z.im * w.im
参数：z w : QuadraticAlgebra R a b；z * w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_mul (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + a * z.im * w.im := rfl
/-
**QuadraticAlgebra.im_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {a b : R} [inst : Mul R] [inst_1 : Add R] (z w : Quadrati
cAlgebra R a b),   (z * w).im = z.re * w.im + z.im * w.re + b * z.im * w.im
参数：z w : QuadraticAlgebra R a b；z * w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_mul (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + b * z.im * w.im := rfl

@[simp]
/-
**QuadraticAlgebra.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：mk_mul_mk (x1 y1 x2 y2 : R) : (mk x1 y1 : QuadraticAlgebra R a b) * mk x2 
y2 = mk (x1 * x2 + a * y1 * y2) (x1 * y2 + y1 * x2 + b * y1 * y2)
参数：x1 y1 x2 y2 : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) * mk x2 y2 =
    mk (x1 * x2 + a * y1 * y2) (x1 * y2 + y1 * x2 + b * y1 * y2) := rfl

end Mul

section SMul
variable [SMul S R] [SMul T R] (s : S)

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (QuadraticAlgebra R a b) where smul s z := ⟨s • z.re, s • z.im⟩
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  smul_assoc s t z := by ext <;> exact smul_assoc _ _ _
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  smul_comm s t z := by ext <;> exact smul_comm _ _ _
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul Sᵐᵒᵖ R] [IsCentralScalar S R] : IsCentralScalar S (QuadraticAlgebra R a b) where
  op_smul_eq_smul s z := by ext <;> exact op_smul_eq_smul _ _
/-
**QuadraticAlgebra.re_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {a b : R} [inst : SMul S R] (s : S) (z : Q
uadraticAlgebra R a b), (s • z).re = s • z.re
参数：s : S；z : QuadraticAlgebra R a b；s • z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).re = s • z.re := rfl
/-
**QuadraticAlgebra.im_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {a b : R} [inst : SMul S R] (s : S) (z : Q
uadraticAlgebra R a b), (s • z).im = s • z.im
参数：s : S；z : QuadraticAlgebra R a b；s • z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).im = s • z.im := rfl

@[simp]
/-
**QuadraticAlgebra.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：smul_mk (s : S) (x y : R) : s • (mk x y : QuadraticAlgebra R a b) = mk (s 
• x) (s • y)
参数：s : S；x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_mk (s : S) (x y : R) :
    s • (mk x y : QuadraticAlgebra R a b) = mk (s • x) (s • y) := rfl

end SMul

section MulAction

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]

end MulAction

@[simp]
/-
**QuadraticAlgebra.C_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) : (.C (s • r) : Quadra
ticAlgebra R a b) = s • .C r
参数：s : S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem C_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (.C (s • r) : QuadraticAlgebra R a b) = s • .C r :=
  QuadraticAlgebra.ext rfl (smul_zero _).symm
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid R] : AddMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_ <;> intros <;> rfl
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [AddMonoid R] [DistribMulAction S R] :
    DistribMulAction S (QuadraticAlgebra R a b) where
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid R] : AddCommMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addCommMonoid _ rfl ?_ ?_ <;> intros <;> rfl
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  add_smul r s x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup R] : AddGroup (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup R] : AddCommGroup (QuadraticAlgebra R a b) where

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne R]

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoidWithOne (QuadraticAlgebra R a b) where
  natCast n := .C n
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

@[simp]
/-
**QuadraticAlgebra.C_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_ofNat (n : Nat) [n.AtLeastTwo] : (.C (ofNat(n) : R) : QuadraticAlgebra R
 a b) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
-/
theorem C_ofNat (n : ℕ) [n.AtLeastTwo] :
    (.C (ofNat(n) : R) : QuadraticAlgebra R a b) = ofNat(n) := by
  ext <;> rfl

@[simp, norm_cast]
/-
**QuadraticAlgebra.re_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：re_natCast (n : Nat) : (n : QuadraticAlgebra R a b).re = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_natCast (n : ℕ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
/-
**QuadraticAlgebra.im_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：im_natCast (n : Nat) : (n : QuadraticAlgebra R a b).im = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_natCast (n : ℕ) : (n : QuadraticAlgebra R a b).im = 0 := rfl
/-
**QuadraticAlgebra.C_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_natCast (n : Nat) : .C (n : R) = (↑n : QuadraticAlgebra R a b)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_natCast (n : ℕ) : .C (n : R) = (↑n : QuadraticAlgebra R a b) := rfl

@[scoped simp]
/-
**QuadraticAlgebra.re_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：re_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re
 = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n) := rfl

@[scoped simp]
/-
**QuadraticAlgebra.im_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：im_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im
 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im = 0 := rfl

end AddCommMonoidWithOne

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroupWithOne (QuadraticAlgebra R a b) where
  intCast n := .C n
  intCast_ofNat n := by norm_cast
  intCast_negSucc n := by rw [Int.negSucc_eq, Int.cast_neg, C_neg]; norm_cast

@[simp, norm_cast]
/-
**QuadraticAlgebra.re_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：re_intCast (n : Int) : (n : QuadraticAlgebra R a b).re = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_intCast (n : ℤ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
/-
**QuadraticAlgebra.im_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：im_intCast (n : Int) : (n : QuadraticAlgebra R a b).im = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_intCast (n : ℤ) : (n : QuadraticAlgebra R a b).im = 0 := rfl
/-
**QuadraticAlgebra.C_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_intCast (n : Int) : .C (n : R) = (n : QuadraticAlgebra R a b)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_intCast (n : ℤ) : .C (n : R) = (n : QuadraticAlgebra R a b) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/-
**QuadraticAlgebra.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Quad
raticAlgebra`。
形式化陈述：instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (QuadraticAlgebr
a R a b) where left_distrib _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (QuadraticAlgebra R a b) where
  left_distrib _ _ _ := by ext <;> simp [mul_add] <;> abel
  right_distrib _ _ _ := by ext <;> simp [mul_add, add_mul] <;> abel
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
/-
**QuadraticAlgebra.C_mul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_mul_eq_smul (r : R) (x : QuadraticAlgebra R a b) : (.C r * x : Quadratic
Algebra R a b) = r • x
参数：r : R；x : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem C_mul_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (.C r * x : QuadraticAlgebra R a b) = r • x := by
  ext <;> simp

@[simp]
/-
**QuadraticAlgebra.C_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_mul (x y : R) : .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem C_mul (x y : R) : .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b) := by
  ext <;> simp

end NonUnitalNonAssocSemiring

section NonAssocSemiring
variable [NonAssocSemiring R]

/-
**QuadraticAlgebra.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlge
bra`。
形式化陈述：instNonAssocSemiring : NonAssocSemiring (QuadraticAlgebra R a b) where one
_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring : NonAssocSemiring (QuadraticAlgebra R a b) where
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[simp]
/-
**QuadraticAlgebra.nsmul_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：nsmul_mk (n : Nat) (x y : R) : (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n 
* x, n * y⟩
参数：n : Nat；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem nsmul_mk (n : ℕ) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end NonAssocSemiring

section Semiring
variable (a b) [Semiring R]

/-- `QuadraticAlgebra.re` as a `LinearMap` -/
@[simps]
/-
**QuadraticAlgebra.re** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：{R : Type u} → {a b : R} → QuadraticAlgebra R a b → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuadraticAlgebra.re` as a `LinearMap`
-/
def reₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.im` as a `LinearMap` -/
@[simps]
/-
**QuadraticAlgebra.im** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：{R : Type u} → {a b : R} → QuadraticAlgebra R a b → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuadraticAlgebra.im` as a `LinearMap`
-/
def imₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.equivTuple` as a `LinearEquiv` -/
/-
**QuadraticAlgebra.linearEquivTuple** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`
。
形式化陈述：linearEquivTuple : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 -> R) where .trans 
.symm finTwoArrowEquiv _ __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`QuadraticAlgebra.equivTuple` as a `LinearEquiv`
-/
def linearEquivTuple : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 → R) where
  __ := equivProd a b |>.trans <| finTwoArrowEquiv _ |>.symm
  map_add' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  map_smul' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩

@[simp]
/-
**QuadraticAlgebra.linearEquivTuple_apply** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticAl
gebra`。
形式化陈述：linearEquivTuple_apply (z : QuadraticAlgebra R a b) : (linearEquivTuple a 
b) z = ![z.re, z.im]
参数：z : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma linearEquivTuple_apply (z : QuadraticAlgebra R a b) :
    (linearEquivTuple a b) z = ![z.re, z.im] := rfl

@[simp]
/-
**QuadraticAlgebra.linearEquivTuple_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Quadra
ticAlgebra`。
形式化陈述：linearEquivTuple_symm_apply (x : Fin 2 -> R) : (linearEquivTuple a b).symm
 x = ⟨x 0, x 1⟩
参数：x : Fin 2 -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma linearEquivTuple_symm_apply (x : Fin 2 → R) :
    (linearEquivTuple a b).symm x = ⟨x 0, x 1⟩ := rfl

/-- `QuadraticAlgebra R a b` has a basis over `R` given by `1` and `i` -/
/-
**QuadraticAlgebra.basis** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：basis : Module.Basis (Fin 2) R (QuadraticAlgebra R a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuadraticAlgebra R a b` has a basis over `R` given by `1` and `i`
-/
noncomputable def basis : Module.Basis (Fin 2) R (QuadraticAlgebra R a b) :=
  .ofEquivFun <| linearEquivTuple a b

@[simp]
/-
**QuadraticAlgebra.basis_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`
。
形式化陈述：basis_repr_apply (x : QuadraticAlgebra R a b) : (basis a b).repr x = ![x.r
e, x.im]
参数：x : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basis_repr_apply (x : QuadraticAlgebra R a b) :
    (basis a b).repr x = ![x.re, x.im] := rfl
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite R (QuadraticAlgebra R a b) := .of_basis (basis a b)
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R (QuadraticAlgebra R a b) := .of_basis (basis a b)
/-
**QuadraticAlgebra.rank_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：rank_eq_two [StrongRankCondition R] : Module.rank R (QuadraticAlgebra R a 
b) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_eq_two [StrongRankCondition R] : Module.rank R (QuadraticAlgebra R a b) = 2 := by
  simp [rank_eq_card_basis (basis a b)]
/-
**QuadraticAlgebra.finrank_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：finrank_eq_two [StrongRankCondition R] : Module.finrank R (QuadraticAlgebr
a R a b) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuadraticAlgebra.rank_eq_two`：rank_eq_two [StrongRankCondition R] : Modu
le.rank R (QuadraticAlgebra R a b) = 2
· 使用定理 `Cardinal.toNat_ofNat`：toNat_ofNat (n : Nat) [n.AtLeastTwo] : Cardinal.to
Nat ofNat(n) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_eq_two [StrongRankCondition R] :
    Module.finrank R (QuadraticAlgebra R a b) = 2 := by
  simp [Module.finrank, rank_eq_two]

end Semiring

section CommSemiring
variable [CommSemiring R]

/-
**QuadraticAlgebra.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`
。
形式化陈述：instCommSemiring : CommSemiring (QuadraticAlgebra R a b) where mul_assoc _
 _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring : CommSemiring (QuadraticAlgebra R a b) where
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring S] [Algebra S R] : Algebra S (QuadraticAlgebra R a b) where
  algebraMap.toFun s := .C (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y := by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y := by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
/-
**QuadraticAlgebra.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩ := rfl
/-
**QuadraticAlgebra.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlge
bra`。
形式化陈述：algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ -> _).In
jective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `QuadraticAlgebra.mk.injEq`：∀ {R : Type u} {a b : R} (re im re_1 im_1 : R
),   ({ re := re, im := im } = { re := re_1, im := im_1 }) = (re = re_1 ∧ im = i
m_1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]

@[simp]
/-
**QuadraticAlgebra.algebraMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：algebraMap_inj {x y : R} : algebraMap R (QuadraticAlgebra R a b) x = algeb
raMap _ _ y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `QuadraticAlgebra.algebraMap_injective`：algebraMap_injective : (algebraMa
p R (QuadraticAlgebra R a b) : _ -> _).Injective
-/
theorem algebraMap_inj {x y : R} :
    algebraMap R (QuadraticAlgebra R a b) x = algebraMap _ _ y ↔ x = y :=
  algebraMap_injective.eq_iff

@[simp]
/-
**QuadraticAlgebra.algebraMap_re** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：algebraMap_re : (algebraMap R (QuadraticAlgebra R a b) r).re = r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_re : (algebraMap R (QuadraticAlgebra R a b) r).re = r := rfl

@[simp]
/-
**QuadraticAlgebra.algebraMap_im** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：algebraMap_im : (algebraMap R (QuadraticAlgebra R a b) r).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_im : (algebraMap R (QuadraticAlgebra R a b) r).im = 0 := rfl
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [Module S R] [Module.IsTorsionFree S R] :
    Module.IsTorsionFree S (QuadraticAlgebra R a b) :=
  (linearEquivTuple ..).injective.moduleIsTorsionFree _ (by simp)

@[simp]
/-
**QuadraticAlgebra.C_pow** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_pow (n : Nat) (r : R) : (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C 
r) ^ n
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem C_pow (n : ℕ) (r : R) : (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C r) ^ n :=
  (algebraMap R (QuadraticAlgebra R a b)).map_pow r n
/-
**QuadraticAlgebra.mul_C_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：mul_C_eq_smul (r : R) (x : QuadraticAlgebra R a b) : (x * .C r : Quadratic
Algebra R a b) = r • x
参数：r : R；x : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `QuadraticAlgebra.C_mul_eq_smul`：C_mul_eq_smul (r : R) (x : QuadraticAlge
bra R a b) : (.C r * x : QuadraticAlgebra R a b) = r • x
-/
theorem mul_C_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (x * .C r : QuadraticAlgebra R a b) = r • x := by
  rw [mul_comm, C_mul_eq_smul r x]

@[simp]
/-
**QuadraticAlgebra.C_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：C_eq_algebraMap : QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a
 b))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_eq_algebraMap : QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b)) := rfl
/-
**QuadraticAlgebra.smul_C** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：smul_C (r1 r2 : R) : r1 • (.C r2 : QuadraticAlgebra R a b) = .C (r1 * r2)
参数：r1 r2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticAlgebra.C_mul`：C_mul (x y : R) : .C (x * y) = (.C x * .C y : Qu
adraticAlgebra R a b)
· 使用定理 `QuadraticAlgebra.C_mul_eq_smul`：C_mul_eq_smul (r : R) (x : QuadraticAlge
bra R a b) : (.C r * x : QuadraticAlgebra R a b) = r • x
-/
theorem smul_C (r1 r2 : R) :
    r1 • (.C r2 : QuadraticAlgebra R a b) = .C (r1 * r2) := by rw [C_mul, C_mul_eq_smul]
/-
**QuadraticAlgebra.algebraMap_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebr
a`。
形式化陈述：algebraMap_dvd_iff {r : R} {z : QuadraticAlgebra R a b} : (algebraMap R (Q
uadraticAlgebra R a b) r) ∣ z ↔ r ∣ z.re ∧ r ∣ z.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_dvd_iff {r : R} {z : QuadraticAlgebra R a b} :
    (algebraMap R (QuadraticAlgebra R a b) r) ∣ z ↔ r ∣ z.re ∧ r ∣ z.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [QuadraticAlgebra.ext_iff, hr, hi, ← C_eq_algebraMap]

@[simp]
/-
**QuadraticAlgebra.algebraMap_dvd_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAl
gebra`。
形式化陈述：algebraMap_dvd_iff_dvd {z w : R} : algebraMap R (QuadraticAlgebra R a b) z
 ∣ algebraMap R (QuadraticAlgebra R a b) w ↔ z ∣ w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticAlgebra.algebraMap_dvd_iff`：algebraMap_dvd_iff {r : R} {z : Qua
draticAlgebra R a b} : (algebraMap R (QuadraticAlgebra R a b) r) ∣ z ↔ r ∣ z.re 
∧ r ∣ z.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem algebraMap_dvd_iff_dvd {z w : R} :
    algebraMap R (QuadraticAlgebra R a b) z ∣ algebraMap R (QuadraticAlgebra R a b) w ↔ z ∣ w := by
  rw [algebraMap_dvd_iff]
  simp

end CommSemiring

section CommRing

variable [CommRing R]

/-
**QuadraticAlgebra.instCommRing** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：{R : Type u_1} → {a b : R} → [CommRing R] → CommRing (QuadraticAlgebra R a
 b)
参数：QuadraticAlgebra R a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing : CommRing (QuadraticAlgebra R a b) where
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CharZero R] : CharZero (QuadraticAlgebra R a b) where
  cast_injective m n := by
    simp [QuadraticAlgebra.ext_iff]

@[simp]
/-
**QuadraticAlgebra.zsmul_val** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：zsmul_val (n : Int) (x y : R) : (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n
 * x, n * y⟩
参数：n : Int；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem zsmul_val (n : ℤ) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end CommRing

end QuadraticAlgebra

