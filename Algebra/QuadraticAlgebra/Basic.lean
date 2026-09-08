/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Defs
public import Mathlib.Algebra.Star.Unitary

import Mathlib.Tactic.FieldSimp

/-!
# Quadratic algebras: involution, norm, and trace.

Let `R` be a commutative ring. We define:

* `QuadraticAlgebra.star`: the quadratic involution

* `QuadraticAlgebra.norm`: the norm

* `QuadraticAlgebra.trace`: the trace, as an `R`-linear map

We prove:

* `QuadraticAlgebra.isUnit_iff_norm_isUnit`:
  `w : QuadraticAlgebra R a b` is a unit iff `w.norm` is a unit in `R`.

* `QuadraticAlgebra.norm_mem_nonZeroDivisors_iff`:
  `w : QuadraticAlgebra R a b` isn't a zero divisor iff
  `w.norm` isn't a zero divisor in `R`.

* If `K` is a field, and `∀ r, r ^ 2 ≠ a + b * r`, then `QuadraticAlgebra K a b` is a field.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {K R : Type*} {a b : R}

section omega

section

variable [Zero R] [One R]

/-- The representative of the root in the quadratic algebra -/
/-
**QuadraticAlgebra.omega** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：omega : QuadraticAlgebra R a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representative of the root in the quadratic algebra
-/
def omega : QuadraticAlgebra R a b :=
  ⟨0, 1⟩

/-- the canonical element `⟨0, 1⟩` in a quadratic algebra `QuadraticAlgebra R a b`. -/
scoped notation "ω" => omega

@[simp]
/-
**QuadraticAlgebra.omega_re** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：omega_re : (ω : QuadraticAlgebra R a b).re = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem omega_re : (ω : QuadraticAlgebra R a b).re = 0 :=
  rfl

@[simp]
/-
**QuadraticAlgebra.omega_im** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：omega_im : (ω : QuadraticAlgebra R a b).im = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem omega_im : (ω : QuadraticAlgebra R a b).im = 1 :=
  rfl

end

variable [CommSemiring R]

/-
**QuadraticAlgebra.omega_mul_omega_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlg
ebra`。
形式化陈述：omega_mul_omega_eq_mk : (ω : QuadraticAlgebra R a b) * ω = ⟨a, b⟩
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem omega_mul_omega_eq_mk : (ω : QuadraticAlgebra R a b) * ω = ⟨a, b⟩ := by
  ext <;> simp
/-
**QuadraticAlgebra.omega_mul_omega_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAl
gebra`。
形式化陈述：omega_mul_omega_eq_add : (ω : QuadraticAlgebra R a b) * ω = a • 1 + b • ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem omega_mul_omega_eq_add :
    (ω : QuadraticAlgebra R a b) * ω = a • 1 + b • ω := by
  ext <;> simp
/-
**QuadraticAlgebra.omega_mul_omega_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Quad
raticAlgebra`。
形式化陈述：omega_mul_omega_eq_algebraMap : (ω : QuadraticAlgebra R a b) * ω = algebra
Map R _ a + algebraMap R _ b * ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticAlgebra.omega_mul_omega_eq_add`：omega_mul_omega_eq_add : (ω : Q
uadraticAlgebra R a b) * ω = a • 1 + b • ω
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem omega_mul_omega_eq_algebraMap :
    (ω : QuadraticAlgebra R a b) * ω = algebraMap R _ a + algebraMap R _ b * ω := by
  simp [omega_mul_omega_eq_add, Algebra.algebraMap_eq_smul_one]

@[simp]
/-
**QuadraticAlgebra.omega_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：omega_mul_mk (x y : R) : (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x
 + b * y⟩
参数：x y : R。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem omega_mul_mk (x y : R) : (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x + b * y⟩ := by
  ext <;> simp

@[simp]
/-
**QuadraticAlgebra.omega_mul_algebraMap_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quadra
ticAlgebra`。
形式化陈述：omega_mul_algebraMap_mul_mk (n x y : R) : (ω : QuadraticAlgebra R a b) * a
lgebraMap _ _ n * ⟨x, y⟩ = ⟨a * n * y, n * x + n * b * y⟩
参数：n x y : R。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
-/
theorem omega_mul_algebraMap_mul_mk (n x y : R) :
    (ω : QuadraticAlgebra R a b) * algebraMap _ _ n * ⟨x, y⟩ = ⟨a * n * y, n * x + n * b * y⟩ := by
  ext <;> simp; ring
/-
**QuadraticAlgebra.mk_eq_add_smul_omega** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlge
bra`。
形式化陈述：mk_eq_add_smul_omega (x y : R) : (⟨x, y⟩ : QuadraticAlgebra R a b) = algeb
raMap _ _ x + y • ω
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mk_eq_add_smul_omega (x y : R) :
    (⟨x, y⟩ : QuadraticAlgebra R a b) = algebraMap _ _ x + y • ω := by
  ext <;> simp

variable {A : Type*} [Ring A] [Algebra R A]

set_option backward.isDefEq.respectTransparency false in
@[ext]
/-
**QuadraticAlgebra.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：algHom_ext {f g : QuadraticAlgebra R a b ->ₐ[R] A} (h : f ω = g ω) : f = g
参数：h : f ω = g ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticAlgebra.mk_eq_add_smul_omega`：mk_eq_add_smul_omega (x y : R) : 
(⟨x, y⟩ : QuadraticAlgebra R a b) = algebraMap _ _ x + y • ω
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algHom_ext {f g : QuadraticAlgebra R a b →ₐ[R] A}
    (h : f ω = g ω) : f = g := by
  ext ⟨x, y⟩
  simp [mk_eq_add_smul_omega, h]

set_option backward.isDefEq.respectTransparency false in
/-- The unique `AlgHom` from `QuadraticAlgebra R a b` to an `R`-algebra `A`,
constructed by replacing `ω` with the provided root.
Conversely, this associates to every algebra morphism `QuadraticAlgebra R a b →ₐ[R] A`
a value of `ω` in `A`. -/
@[simps]
/-
**QuadraticAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：lift : { u : A // u * u = a • 1 + b • u } ≃ (QuadraticAlgebra R a b ->ₐ[R]
 A) where toFun u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique `AlgHom` from `QuadraticAlgebra R a b` to an `R`-algebra `A`,
constructed by replacing `ω` with the provided root.
Conversely, this associates to every algebra morphism `QuadraticAlgebra R a b →ₐ
[R] A`
a value of `ω` in `A`.
-/
def lift : { u : A // u * u = a • 1 + b • u } ≃ (QuadraticAlgebra R a b →ₐ[R] A) where
  toFun u :=
    { toFun z := z.re • 1 + z.im • u
      map_zero' := by simp
      map_add' z w := by
        simp only [re_add, im_add, add_smul, ← add_assoc]
        congr 1
        simp only [add_assoc]
        congr 1
        rw [add_comm]
      map_one' := by simp
      map_mul' z w := by
        symm
        calc
          (z.re • (1 : A) + z.im • ↑u) * (w.re • 1 + w.im • ↑u) =
            (z.re * w.re) • (1 : A) + (z.re * w.im) • u +
              (z.im * w.re) • u + (z.im * w.im) • (u * u) := by
              simp only [mul_add, mul_one, add_mul, one_mul, ← add_assoc, smul_mul_smul]
              apply add_add_add_comm'
          _ = (z.re * w.re) • (1 : A) + (z.re * w.im + z.im * w.re) • u +
                (z.im * w.im) • (u * u) := by
              congr 1
              simp only [add_assoc]
              rw [← add_smul]
          _ = (z.re * w.re) • 1 + (z.re * w.im + z.im * w.re) • u +
                (z.im * w.im) • (a • 1 + b • u) := by
              simp [u.prop]
          _ = (z.re * w.re + a * z.im * w.im) • 1 +
                (z.re * w.im + z.im * w.re + b * z.im * w.im) • u := by
              simp only [smul_add]
              module
            _ = (z * w).re • 1 + (z * w).im • u := by
              simp
      commutes' r := by
        simp [← Algebra.algebraMap_eq_smul_one] }
  invFun f := ⟨f (ω), by
    simp [← map_mul, omega_mul_omega_eq_add]
    ⟩
  left_inv r := by
    simp
  right_inv f := by
    ext
    simp

end omega

section star

variable [CommRing R]

/-- Conjugation in `QuadraticAlgebra R a b`.
The conjugate of `x + y ω` is `x + y ω' = (x + b * y) - y ω`. -/
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugation in `QuadraticAlgebra R a b`.
The conjugate of `x + y ω` is `x + y ω' = (x + b * y) - y ω`.
-/
instance : Star (QuadraticAlgebra R a b) where
  star z := ⟨z.re + b * z.im, -z.im⟩

@[simp]
/-
**QuadraticAlgebra.star_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：star_mk (x y : R) : star (⟨x, y⟩ : QuadraticAlgebra R a b) = ⟨x + b * y, -
y⟩
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_mk (x y : R) :
    star (⟨x, y⟩ : QuadraticAlgebra R a b) = ⟨x + b * y, -y⟩ :=
  rfl

@[simp]
/-
**QuadraticAlgebra.re_star** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：re_star (z : QuadraticAlgebra R a b) : (star z).re = z.re + b * z.im
参数：z : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_star (z : QuadraticAlgebra R a b) :
    (star z).re = z.re + b * z.im :=
  rfl

@[simp]
/-
**QuadraticAlgebra.im_star** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：im_star (z : QuadraticAlgebra R a b) : (star z).im = -z.im
参数：z : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_star (z : QuadraticAlgebra R a b) :
    (star z).im = -z.im :=
  rfl
/-
**QuadraticAlgebra.mul_star** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：mul_star (x y : R) : (⟨x, y⟩ * star ⟨x, y⟩ : QuadraticAlgebra R a b) = (al
gebraMap _ _ x) * (algebraMap _ _ x) + (algebraMap _ _ b) * (algebraMap _ _ x) *
 (algebraMap _ _ y) - (algebraMap _ _ a) * (algebraMap _ _ y) * (algebraMap _ _ 
y)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 47 条，此处仅展示前 30 条）
-/
theorem mul_star (x y : R) :
    (⟨x, y⟩ * star ⟨x, y⟩ : QuadraticAlgebra R a b) = (algebraMap _ _ x) * (algebraMap _ _ x) +
      (algebraMap _ _ b) * (algebraMap _ _ x) * (algebraMap _ _ y) - (algebraMap _ _ a) *
      (algebraMap _ _ y) * (algebraMap _ _ y) := by
  ext <;> simp <;> ring
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarRing (QuadraticAlgebra R a b) where
  star_involutive _ := by
    refine QuadraticAlgebra.ext (by simp) (neg_neg _)
  star_mul a b := by ext <;>
    simp only [re_star, re_mul, im_mul, im_star, mul_neg, neg_mul, neg_neg] <;> ring
  star_add _ _ := QuadraticAlgebra.ext (by simp only [re_star, re_add, im_add]; ring) (neg_add _ _)

/-- `z - star z` is a multiple of the difference `ω - star ω`. -/
/-
**QuadraticAlgebra.sub_star** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：sub_star (z : QuadraticAlgebra R a b) : z - star z = z.im • (ω - star ω)
参数：z : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`z - star z` is a multiple of the difference `ω - star ω`.
-/
theorem sub_star (z : QuadraticAlgebra R a b) :
    z - star z = z.im • (ω - star ω) := by
  ext <;> simp <;> ring

end star

section norm

variable [CommRing R]

/-- the norm in a quadratic algebra, as a `MonoidHom`. -/
/-
**QuadraticAlgebra.norm** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm : QuadraticAlgebra R a b ->* R where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the norm in a quadratic algebra, as a `MonoidHom`.
-/
def norm : QuadraticAlgebra R a b →* R where
  toFun z := z.re * z.re + b * z.re * z.im - a * z.im * z.im
  map_mul' z w := by simp only [re_mul, im_mul]; ring
  map_one' := by simp
/-
**QuadraticAlgebra.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_def (z : QuadraticAlgebra R a b) : z.norm = z.re * z.re + b * z.re * 
z.im - a * z.im * z.im
参数：z : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (z : QuadraticAlgebra R a b) :
    z.norm = z.re * z.re + b * z.re * z.im - a * z.im * z.im :=
  rfl

@[simp]
/-
**QuadraticAlgebra.norm_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_zero : norm (0 : QuadraticAlgebra R a b) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_zero : norm (0 : QuadraticAlgebra R a b) = 0 := by simp [norm]

@[simp]
/-
**QuadraticAlgebra.norm_one** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_one : norm (1 : QuadraticAlgebra R a b) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_one : norm (1 : QuadraticAlgebra R a b) = 1 := by simp [norm]

@[simp]
/-
**QuadraticAlgebra.norm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_algebraMap (r : R) : norm (algebraMap R (QuadraticAlgebra R a b) r) =
 r ^ 2
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_algebraMap (r : R) : norm (algebraMap R (QuadraticAlgebra R a b) r) = r ^ 2 := by
  simp [norm_def, pow_two]

@[simp]
/-
**QuadraticAlgebra.norm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_natCast (n : Nat) : norm (n : QuadraticAlgebra R a b) = n ^ 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_natCast (n : ℕ) : norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [norm_def, pow_two]

@[simp]
/-
**QuadraticAlgebra.norm_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_intCast (n : Int) : norm (n : QuadraticAlgebra R a b) = n ^ 2
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_intCast (n : ℤ) : norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [norm_def, pow_two]
/-
**QuadraticAlgebra.algebraMap_norm_eq_mul_star** 是 Mathlib 中的一个定理，位于命名空间 `Quadra
ticAlgebra`。
形式化陈述：algebraMap_norm_eq_mul_star (z : QuadraticAlgebra R a b) : (algebraMap R _
 (norm z : R)) = z * star z
参数：z : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
（共 57 条，此处仅展示前 30 条）
-/
theorem algebraMap_norm_eq_mul_star (z : QuadraticAlgebra R a b) :
    (algebraMap R _ (norm z : R)) = z * star z := by
  ext <;> simp [norm, star, mul_comm] <;> ring

@[simp]
/-
**QuadraticAlgebra.norm_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_neg (x : QuadraticAlgebra R a b) : (-x).norm = x.norm
参数：x : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_neg (x : QuadraticAlgebra R a b) : (-x).norm = x.norm := by
  simp [norm]

@[simp]
/-
**QuadraticAlgebra.norm_star** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：norm_star (x : QuadraticAlgebra R a b) : (star x).norm = x.norm
参数：x : QuadraticAlgebra R a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 41 条，此处仅展示前 30 条）
-/
theorem norm_star (x : QuadraticAlgebra R a b) : (star x).norm = x.norm := by
  simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk, re_star, im_star, mul_neg, neg_mul, neg_neg,
    sub_left_inj]
  ring
/-
**QuadraticAlgebra.isUnit_iff_norm_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAl
gebra`。
形式化陈述：isUnit_iff_norm_isUnit {x : QuadraticAlgebra R a b} : IsUnit x ↔ IsUnit (x
.norm)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `QuadraticAlgebra.algebraMap_norm_eq_mul_star`：algebraMap_norm_eq_mul_sta
r (z : QuadraticAlgebra R a b) : (algebraMap R _ (norm z : R)) = z * star z
· 使用定理 `QuadraticAlgebra.C_eq_algebraMap`：C_eq_algebraMap : QuadraticAlgebra.C =
 (algebraMap R (QuadraticAlgebra R a b))
· 使用定理 `QuadraticAlgebra.C_mul`：C_mul (x y : R) : .C (x * y) = (.C x * .C y : Qu
adraticAlgebra R a b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticAlgebra.C_inj`：C_inj {x y : R} : (.C x : QuadraticAlgebra R a b
) = .C y ↔ x = y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem isUnit_iff_norm_isUnit {x : QuadraticAlgebra R a b} :
    IsUnit x ↔ IsUnit (x.norm) := by
  constructor
  · exact IsUnit.map norm
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← C_inj (R := R) (a := a) (b := b), C_mul, C_eq_algebraMap, algebraMap_norm_eq_mul_star,
      mul_assoc, map_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm, hr]

/-- An element of `QuadraticAlgebra R a b` has norm equal to `1`
if and only if it is contained in the submonoid of unitary elements. -/
/-
**QuadraticAlgebra.norm_eq_one_iff_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Quadra
ticAlgebra`。
形式化陈述：norm_eq_one_iff_mem_unitary {z : QuadraticAlgebra R a b} : z.norm = 1 ↔ z 
in unitary (QuadraticAlgebra R a b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitary.mem_iff_self_mul_star`：mem_iff_self_mul_star {U : R} : U in unit
ary R ↔ U * star U = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticAlgebra.algebraMap_norm_eq_mul_star`：algebraMap_norm_eq_mul_sta
r (z : QuadraticAlgebra R a b) : (algebraMap R _ (norm z : R)) = z * star z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticAlgebra.algebraMap_inj`：algebraMap_inj {x y : R} : algebraMap R
 (QuadraticAlgebra R a b) x = algebraMap _ _ y ↔ x = y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An element of `QuadraticAlgebra R a b` has norm equal to `1`
if and only if it is contained in the submonoid of unitary elements.
-/
theorem norm_eq_one_iff_mem_unitary {z : QuadraticAlgebra R a b} :
    z.norm = 1 ↔ z ∈ unitary (QuadraticAlgebra R a b) := by
  rw [Unitary.mem_iff_self_mul_star, ← algebraMap_norm_eq_mul_star]
  simp [← algebraMap_inj (R := R) (a := a) (b := b)]

alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary

/-- The kernel of the norm map on `QuadraticAlgebra R a b` equals
the submonoid of unitary elements. -/
/-
**QuadraticAlgebra.mker_norm_eq_unitary** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlge
bra`。
形式化陈述：mker_norm_eq_unitary : MonoidHom.mker (@norm R a b _) = unitary (Quadratic
Algebra R a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `QuadraticAlgebra.norm_eq_one_iff_mem_unitary`：norm_eq_one_iff_mem_unitar
y {z : QuadraticAlgebra R a b} : z.norm = 1 ↔ z in unitary (QuadraticAlgebra R a
 b)

--- 原说明 ---
The kernel of the norm map on `QuadraticAlgebra R a b` equals
the submonoid of unitary elements.
-/
theorem mker_norm_eq_unitary :
    MonoidHom.mker (@norm R a b _) = unitary (QuadraticAlgebra R a b) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

open nonZeroDivisors
/-
**QuadraticAlgebra.algebraMap_mem_nonZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 
`QuadraticAlgebra`。
形式化陈述：algebraMap_mem_nonZeroDivisors_iff {r : R} : algebraMap R (QuadraticAlgebr
a R a b) r in (QuadraticAlgebra R a b)⁰ ↔ r in R⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticAlgebra.algebraMap_inj`：algebraMap_inj {x y : R} : algebraMap R
 (QuadraticAlgebra R a b) x = algebraMap _ _ y ↔ x = y
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `QuadraticAlgebra.im_zero`：∀ {R : Type u_1} {a b : R} [inst : Zero R], Qu
adraticAlgebra.im 0 = 0
· 使用定理 `QuadraticAlgebra.re_zero`：∀ {R : Type u_1} {a b : R} [inst : Zero R], Qu
adraticAlgebra.re 0 = 0
· 使用定理 `QuadraticAlgebra.ext_iff`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgeb
ra R a b}, x = y ↔ x.re = y.re ∧ x.im = y.im
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem algebraMap_mem_nonZeroDivisors_iff {r : R} :
    algebraMap R (QuadraticAlgebra R a b) r ∈ (QuadraticAlgebra R a b)⁰ ↔ r ∈ R⁰ := by
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro H x hxr
    rw [← algebraMap_inj, map_zero]
    apply H
    rw [← map_mul, hxr, map_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff, re_zero, im_zero] at hz
    simp only [re_mul, algebraMap_re, algebraMap_im, mul_zero, add_zero, im_mul, zero_add] at hz
    simp [QuadraticAlgebra.ext_iff, re_zero, im_zero, h _ hz.left, h _ hz.right]
/-
**QuadraticAlgebra.star_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Quadratic
Algebra`。
形式化陈述：star_mem_nonZeroDivisors {z : QuadraticAlgebra R a b} (hz : z in (Quadrati
cAlgebra R a b)⁰) : star z in (QuadraticAlgebra R a b)⁰
参数：hz : z in (QuadraticAlgebra R a b)⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonZeroDivisors_iff_right`：mem_nonZeroDivisors_iff_right : r in M₀⁰ 
↔ forall x, x * r = 0 -> x = 0
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem star_mem_nonZeroDivisors {z : QuadraticAlgebra R a b}
    (hz : z ∈ (QuadraticAlgebra R a b)⁰) :
    star z ∈ (QuadraticAlgebra R a b)⁰ := by
  rw [mem_nonZeroDivisors_iff_right] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z, ← star_mul, mul_comm, hw, star_zero]
/-
**QuadraticAlgebra.star_mem_nonZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quadr
aticAlgebra`。
形式化陈述：star_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} : star z in (Qua
draticAlgebra R a b)⁰ ↔ z in (QuadraticAlgebra R a b)⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `QuadraticAlgebra.star_mem_nonZeroDivisors`：star_mem_nonZeroDivisors {z :
 QuadraticAlgebra R a b} (hz : z in (QuadraticAlgebra R a b)⁰) : star z in (Quad
raticAlgebra R a b)⁰
-/
theorem star_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    star z ∈ (QuadraticAlgebra R a b)⁰ ↔ z ∈ (QuadraticAlgebra R a b)⁰ := by
  refine ⟨fun h ↦ ?_, star_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact star_mem_nonZeroDivisors h
/-
**QuadraticAlgebra.norm_mem_nonZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quadr
aticAlgebra`。
形式化陈述：norm_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} : z.norm in R⁰ ↔
 z in (QuadraticAlgebra R a b)⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticAlgebra.C_mul_eq_smul`：C_mul_eq_smul (r : R) (x : QuadraticAlge
bra R a b) : (.C r * x : QuadraticAlgebra R a b) = r • x
· 使用定理 `QuadraticAlgebra.C_eq_algebraMap`：C_eq_algebraMap : QuadraticAlgebra.C =
 (algebraMap R (QuadraticAlgebra R a b))
· 使用定理 `QuadraticAlgebra.algebraMap_norm_eq_mul_star`：algebraMap_norm_eq_mul_sta
r (z : QuadraticAlgebra R a b) : (algebraMap R _ (norm z : R)) = z * star z
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `QuadraticAlgebra.algebraMap_mem_nonZeroDivisors_iff`：algebraMap_mem_nonZ
eroDivisors_iff {r : R} : algebraMap R (QuadraticAlgebra R a b) r in (QuadraticA
lgebra R a b)⁰ ↔ r in R⁰
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `QuadraticAlgebra.star_mem_nonZeroDivisors`：star_mem_nonZeroDivisors {z :
 QuadraticAlgebra R a b} (hz : z in (QuadraticAlgebra R a b)⁰) : star z in (Quad
raticAlgebra R a b)⁰
-/
theorem norm_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    z.norm ∈ R⁰ ↔ z ∈ (QuadraticAlgebra R a b)⁰ := by
  constructor
  · simp only [mem_nonZeroDivisors_iff_right]
    intro h w hw
    have : norm z • w = 0 := by
      rw [← C_mul_eq_smul, C_eq_algebraMap, algebraMap_norm_eq_mul_star, mul_comm, ← mul_assoc, hw,
        zero_mul]
    simp only [QuadraticAlgebra.ext_iff, re_smul, smul_eq_mul, mul_comm, re_zero, im_smul,
      im_zero] at this
    ext <;> simp [h _ this.left, h _ this.right]
  · intro hz
    rw [← algebraMap_mem_nonZeroDivisors_iff, algebraMap_norm_eq_mul_star]
    exact Submonoid.mul_mem _ hz (star_mem_nonZeroDivisors hz)

end norm

section trace

variable [CommRing R]

attribute [local grind =] re_add im_add im_star re_star re_smul im_smul RingHom.id_apply
  algebraMap_re algebraMap_im

/-- The trace in a quadratic algebra, as an `R`-linear map. -/
/-
**QuadraticAlgebra.trace** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticAlgebra`。
形式化陈述：trace : QuadraticAlgebra R a b ->ₗ[R] R where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trace in a quadratic algebra, as an `R`-linear map.
-/
def trace : QuadraticAlgebra R a b →ₗ[R] R where
  toFun z := 2 * z.re + b * z.im
  map_add' := by grind
  map_smul' := by grind [smul_eq_mul]

variable (z : QuadraticAlgebra R a b)
/-
**QuadraticAlgebra.trace_def** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：trace_def : trace z = 2 * z.re + b * z.im
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trace_def : trace z = 2 * z.re + b * z.im := rfl

@[simp]
/-
**QuadraticAlgebra.trace_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`
。
形式化陈述：trace_algebraMap (r : R) : trace (algebraMap R (QuadraticAlgebra R a b) r)
 = 2 * r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trace_algebraMap (r : R) :
    trace (algebraMap R (QuadraticAlgebra R a b) r) = 2 * r := by
  grind [trace_def]

@[simp]
/-
**QuadraticAlgebra.trace_natCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：trace_natCast (n : Nat) : trace (n : QuadraticAlgebra R a b) = 2 * n
参数：n : Nat。
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_natCast (n : ℕ) : trace (n : QuadraticAlgebra R a b) = 2 * n := by
  simp [trace_def, re_natCast, im_natCast]

@[simp]
/-
**QuadraticAlgebra.trace_intCast** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：trace_intCast (n : Int) : trace (n : QuadraticAlgebra R a b) = 2 * n
参数：n : Int。
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_intCast (n : ℤ) : trace (n : QuadraticAlgebra R a b) = 2 * n := by
  simp [trace_def, re_intCast, im_intCast]

@[simp]
/-
**QuadraticAlgebra.trace_omega** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：trace_omega : trace (ω : QuadraticAlgebra R a b) = b
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_omega : trace (ω : QuadraticAlgebra R a b) = b := by
  simp [trace_def]

@[simp]
/-
**QuadraticAlgebra.trace_one** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：trace_one : trace (1 : QuadraticAlgebra R a b) = 2
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_one : trace (1 : QuadraticAlgebra R a b) = 2 := by
  simp [trace_def]

@[simp]
/-
**QuadraticAlgebra.trace_star** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：trace_star : trace (star z) = trace z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trace_star : trace (star z) = trace z := by
  grind [trace_def]

/-- `z + star z` is the trace of `z`. -/
/-
**QuadraticAlgebra.algebraMap_trace_eq_add_star** 是 Mathlib 中的一个定理，位于命名空间 `Quadr
aticAlgebra`。
形式化陈述：algebraMap_trace_eq_add_star : algebraMap R (QuadraticAlgebra R a b) (trac
e z) = z + star z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y

--- 原说明 ---
`z + star z` is the trace of `z`.
-/
theorem algebraMap_trace_eq_add_star :
    algebraMap R (QuadraticAlgebra R a b) (trace z) = z + star z := by
  ext <;> grind [trace_def]

/-- The conjugate of `z` is `trace z - z`. -/
/-
**QuadraticAlgebra.star_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticAlgebra`。
形式化陈述：star_eq : star z = algebraMap R (QuadraticAlgebra R a b) (trace z) - z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticAlgebra.algebraMap_trace_eq_add_star`：algebraMap_trace_eq_add_s
tar : algebraMap R (QuadraticAlgebra R a b) (trace z) = z + star z
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b

--- 原说明 ---
The conjugate of `z` is `trace z - z`.
-/
theorem star_eq :
    star z = algebraMap R (QuadraticAlgebra R a b) (trace z) - z := by
  rw [algebraMap_trace_eq_add_star, add_sub_cancel_left]

/-- Every element of a quadratic algebra satisfies its characteristic equation. -/
/-
**QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`QuadraticAlgebra`。
形式化陈述：sq_sub_trace_smul_add_norm_eq_zero : z ^ 2 - trace z • z + algebraMap R _ 
(norm z) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `QuadraticAlgebra.algebraMap_trace_eq_add_star`：algebraMap_trace_eq_add_s
tar : algebraMap R (QuadraticAlgebra R a b) (trace z) = z + star z
· 使用定理 `QuadraticAlgebra.algebraMap_norm_eq_mul_star`：algebraMap_norm_eq_mul_sta
r (z : QuadraticAlgebra R a b) : (algebraMap R _ (norm z : R)) = z * star z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Every element of a quadratic algebra satisfies its characteristic equation.
-/
theorem sq_sub_trace_smul_add_norm_eq_zero :
    z ^ 2 - trace z • z + algebraMap R _ (norm z) = 0 := by
  rw [Algebra.smul_def, algebraMap_trace_eq_add_star, algebraMap_norm_eq_mul_star]; ring
/-
**QuadraticAlgebra.sq_eq_trace_smul_sub_norm** 是 Mathlib 中的一个定理，位于命名空间 `Quadrati
cAlgebra`。
形式化陈述：sq_eq_trace_smul_sub_norm : z ^ 2 = trace z • z - algebraMap R _ (norm z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero`：sq_sub_trace_smul_a
dd_norm_eq_zero : z ^ 2 - trace z • z + algebraMap R _ (norm z) = 0
-/
theorem sq_eq_trace_smul_sub_norm :
    z ^ 2 = trace z • z - algebraMap R _ (norm z) := by
  rw [← sub_eq_zero, ← sub_add, sq_sub_trace_smul_add_norm_eq_zero]

end trace

section field

variable [Field K] {a b : K} [Hab : Fact (∀ r, r ^ 2 ≠ a + b * r)]

/-
**QuadraticAlgebra.norm_eq_zero_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Quadratic
Algebra`。
形式化陈述：norm_eq_zero_iff_eq_zero {z : QuadraticAlgebra K a b} : norm z = 0 ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticAlgebra.ext`：∀ {R : Type u} {a b : R} {x y : QuadraticAlgebra R
 a b}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `QuadraticAlgebra.norm_def`：norm_def (z : QuadraticAlgebra R a b) : z.nor
m = z.re * z.re + b * z.re * z.im - a * z.im * z.im
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `QuadraticAlgebra.norm_zero`：norm_zero : norm (0 : QuadraticAlgebra R a b
) = 0
-/
lemma norm_eq_zero_iff_eq_zero {z : QuadraticAlgebra K a b} :
    norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [norm_def] at hz
    by_cases h : z.im = 0
    · simp [h] at hz
      aesop
    · exfalso
      rw [← pow_two, sub_eq_zero, ← eq_sub_iff_add_eq] at hz
      apply Hab.out (-z.re / z.im)
      grind
  · intro hz
    simp [hz]
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps] instance : NNRatCast (QuadraticAlgebra K a b) where nnratCast q := ⟨q, 0⟩
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps] instance : RatCast (QuadraticAlgebra K a b) where ratCast q := ⟨q, 0⟩
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps -isSimp, simps!] instance : Inv (QuadraticAlgebra K a b) where inv z := (norm z)⁻¹ • star z
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps -isSimp, simps!] instance : Div (QuadraticAlgebra K a b) where div w z := w * z⁻¹

/-- If `K` is a field and there is no `r : K` such that `r ^ 2 = a + b * r`,
then `QuadraticAlgebra K a b` is a field. -/
/-
**QuadraticAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K` is a field and there is no `r : K` such that `r ^ 2 = a + b * r`,
then `QuadraticAlgebra K a b` is a field.
-/
instance : Field (QuadraticAlgebra K a b) where
  inv_zero := by ext <;> simp
  mul_inv_cancel z hz := by
    rw [ne_eq, ← norm_eq_zero_iff_eq_zero] at hz
    simp only [inv_def, Algebra.mul_smul_comm]
    rw [← C_mul_eq_smul, C_eq_algebraMap, ← algebraMap_norm_eq_mul_star, ← map_mul,
      inv_mul_cancel₀ hz, map_one]
  nnratCast_def q := by ext <;> simp [sq]; field_simp; simp [NNRat.cast_def]
  ratCast_def q := by ext <;> simp [sq]; field_simp; simp [Rat.cast_def]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext <;> simp [NNRat.smul_def]
  qsmul_def q x := by ext <;> simp [Rat.smul_def]

end field

end QuadraticAlgebra

