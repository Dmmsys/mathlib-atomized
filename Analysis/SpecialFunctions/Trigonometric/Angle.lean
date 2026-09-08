/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Algebra.CharZero.Quotient
public import Mathlib.Topology.Instances.Sign
import Mathlib.Algebra.Order.Ring.Interval

/-!
# The type of angles

In this file we define `Real.Angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/

@[expose] public section


open Real

noncomputable section

namespace Real

/-- The type of angles -/
/-
**Real.Angle** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：Angle : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of angles
-/
def Angle : Type :=
  AddCircle (2 * π)
deriving NormedAddCommGroup, Inhabited

namespace Angle

/-- The canonical map from `ℝ` to the quotient `Angle`. -/
@[coe]
/-
**Real.Angle.coe** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：ℝ → Real.Angle
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `ℝ` to the quotient `Angle`.
-/
protected def coe (r : ℝ) : Angle := QuotientAddGroup.mk r
/-
**Real.Angle.** 是 Mathlib 中的一个实例，位于命名空间 `Real.Angle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ℝ Angle := ⟨Angle.coe⟩
/-
**Real.Angle.** 是 Mathlib 中的一个实例，位于命名空间 `Real.Angle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CircularOrder Real.Angle :=
  fast_instance% QuotientAddGroup.circularOrder (hp' := ⟨by simp [pi_pos]⟩)

@[continuity, fun_prop]
/-
**Real.Angle.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：continuous_coe : Continuous ((↑) : Real -> Angle)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
-/
theorem continuous_coe : Continuous ((↑) : ℝ → Angle) :=
  continuous_quotient_mk'

/-- Coercion `ℝ → Angle` as an additive homomorphism. -/
/-
**Real.Angle.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：coeHom : Real ->+ Angle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `ℝ → Angle` as an additive homomorphism.
-/
def coeHom : ℝ →+ Angle :=
  QuotientAddGroup.mk' _

@[simp]
/-
**Real.Angle.coe_coeHom** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_coeHom : (coeHom : Real -> Angle) = ((↑) : Real -> Angle)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeHom : (coeHom : ℝ → Angle) = ((↑) : ℝ → Angle) :=
  rfl

/-- An induction principle to deduce results for `Angle` from those for `ℝ`, used with
`induction θ using Real.Angle.induction_on`. -/
@[elab_as_elim]
/-
**Real.Angle.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ (x : ℝ), p ↑x) → p θ
参数：θ : Real.Angle；∀ (x : ℝ), p ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q

--- 原说明 ---
An induction principle to deduce results for `Angle` from those for `ℝ`, used wi
th
`induction θ using Real.Angle.induction_on`.
-/
protected theorem induction_on {p : Angle → Prop} (θ : Angle) (h : ∀ x : ℝ, p x) : p θ :=
  Quotient.inductionOn' θ h

@[simp]
/-
**Real.Angle.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_zero : ↑(0 : Real) = (0 : Angle)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ↑(0 : ℝ) = (0 : Angle) :=
  rfl

@[simp]
/-
**Real.Angle.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : Angle)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : Angle) :=
  rfl

@[simp]
/-
**Real.Angle.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : Angle) :=
  rfl

@[simp]
/-
**Real.Angle.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_sub (x y : Real) : ↑(x - y : Real) = (↑x - ↑y : Angle)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : Angle) :=
  rfl
/-
**Real.Angle.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) = n • (↑x : Angle)
参数：n : Nat；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = n • (↑x : Angle) :=
  rfl
/-
**Real.Angle.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_zsmul (z : Int) (x : Real) : ↑(z • x : Real) = z • (↑x : Angle)
参数：z : Int；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = z • (↑x : Angle) :=
  rfl
/-
**Real.Angle.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_eq_zero_iff {x : Real} : (x : Angle) = 0 ↔ exists n : Int, n • (2 * π)
 = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.coe_eq_zero_iff`：coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) =
 0 ↔ exists n : Int, n • p = x
-/
theorem coe_eq_zero_iff {x : ℝ} : (x : Angle) = 0 ↔ ∃ n : ℤ, n • (2 * π) = x :=
  AddCircle.coe_eq_zero_iff (2 * π)

@[simp, norm_cast]
/-
**Real.Angle.natCast_mul_eq_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：natCast_mul_eq_nsmul (x : Real) (n : Nat) : ↑((n : Real) * x) = n • (↑x : 
Angle)
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
theorem natCast_mul_eq_nsmul (x : ℝ) (n : ℕ) : ↑((n : ℝ) * x) = n • (↑x : Angle) := by
  simpa only [nsmul_eq_mul] using! coeHom.map_nsmul n x

@[simp, norm_cast]
/-
**Real.Angle.intCast_mul_eq_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：intCast_mul_eq_zsmul (x : Real) (n : Int) : ↑((n : Real) * x : Real) = n •
 (↑x : Angle)
参数：x : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
-/
theorem intCast_mul_eq_zsmul (x : ℝ) (n : ℤ) : ↑((n : ℝ) * x : ℝ) = n • (↑x : Angle) := by
  simpa only [zsmul_eq_mul] using! coeHom.map_zsmul n x

set_option backward.isDefEq.respectTransparency false in
/-
**Real.Angle.angle_eq_iff_two_pi_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：angle_eq_iff_two_pi_dvd_sub {ψ θ : Real} : (θ : Angle) = ψ ↔ exists k : In
t, θ - ψ = 2 * π * k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.coe.eq_1`：∀ (r : ℝ), ↑r = ↑r
· 使用定理 `QuotientAddGroup.eq`：∀ {α : Type u_1} [inst : AddGroup α] {s : AddSubgro
up α} {a b : α}, ↑a = ↑b ↔ -a + b ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddSubgroup.zmultiples_eq_closure`：∀ {G : Type u_1} [inst : AddGroup G] 
(g : G), AddSubgroup.zmultiples g = AddSubgroup.closure {g}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_eq_mul'`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ),
 n • a = a * ↑n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : Angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k := by
  simp only [eq_comm]
  rw [Angle.coe, Angle.coe, QuotientAddGroup.eq]
  simp only [AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]
/-
**Real.Angle.coe_two_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem coe_two_pi : ↑(2 * π : ℝ) = (0 : Angle) :=
  angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, Int.cast_one, mul_one]⟩

@[simp]
/-
**Real.Angle.neg_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：neg_coe_pi : -(π : Angle) = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_coe_pi : -(π : Angle) = π := by
  rw [← coe_neg, angle_eq_iff_two_pi_dvd_sub]
  use -1
  simp [two_mul, sub_eq_add_neg]

@[simp]
/-
**Real.Angle.two_nsmul_coe_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_coe_div_two (θ : Real) : (2 : Nat) • (↑(θ / 2) : Angle) = θ
参数：θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_nsmul`：coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) =
 n • (↑x : Angle)
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_nsmul, two_nsmul, add_halves]

@[simp]
/-
**Real.Angle.two_zsmul_coe_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_coe_div_two (θ : Real) : (2 : Int) • (↑(θ / 2) : Angle) = θ
参数：θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_zsmul`：coe_zsmul (z : Int) (x : Real) : ↑(z • x : Real) =
 z • (↑x : Angle)
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_zsmul, two_zsmul, add_halves]
/-
**Real.Angle.two_nsmul_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_neg_pi_div_two : (2 : Nat) • (↑(-π / 2) : Angle) = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_nsmul_coe_div_two`：two_nsmul_coe_div_two (θ : Real) : (2 
: Nat) • (↑(θ / 2) : Angle) = θ
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
-/
theorem two_nsmul_neg_pi_div_two : (2 : ℕ) • (↑(-π / 2) : Angle) = π := by
  rw [two_nsmul_coe_div_two, coe_neg, neg_coe_pi]
/-
**Real.Angle.two_zsmul_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_neg_pi_div_two : (2 : Int) • (↑(-π / 2) : Angle) = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.two_nsmul_neg_pi_div_two`：two_nsmul_neg_pi_div_two : (2 : Nat
) • (↑(-π / 2) : Angle) = π
-/
theorem two_zsmul_neg_pi_div_two : (2 : ℤ) • (↑(-π / 2) : Angle) = π := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_neg_pi_div_two]
/-
**Real.Angle.sub_coe_pi_eq_add_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sub_coe_pi_eq_add_coe_pi (θ : Angle) : θ - π = θ + π
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
-/
theorem sub_coe_pi_eq_add_coe_pi (θ : Angle) : θ - π = θ + π := by
  rw [sub_eq_add_neg, neg_coe_pi]

@[simp]
/-
**Real.Angle.two_nsmul_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_coe_pi : (2 : Nat) • (π : Angle) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.coe_two_pi`：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem two_nsmul_coe_pi : (2 : ℕ) • (π : Angle) = 0 := by simp [← natCast_mul_eq_nsmul]

@[simp]
/-
**Real.Angle.two_zsmul_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_coe_pi : (2 : Int) • (π : Angle) = 0
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
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Real.Angle.coe_two_pi`：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem two_zsmul_coe_pi : (2 : ℤ) • (π : Angle) = 0 := by simp [← intCast_mul_eq_zsmul]

@[simp, grind =]
/-
**Real.Angle.coe_pi_add_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_pi_add_coe_pi : (π : Real.Angle) + π = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.two_nsmul_coe_pi`：two_nsmul_coe_pi : (2 : Nat) • (π : Angle) 
= 0
-/
theorem coe_pi_add_coe_pi : (π : Real.Angle) + π = 0 := by rw [← two_nsmul, two_nsmul_coe_pi]
/-
**Real.Angle.zsmul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：zsmul_eq_iff {ψ θ : Angle} {z : Int} (hz : z != 0) : z • ψ = z • θ ↔ exist
s k : Fin z.natAbs, ψ = θ + (k : Nat) • (2 * π / z : Real)
参数：hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff`：zmultiples_zsmul_eq_zsmu
l_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : Int} (hz : z != 0) : z • ψ = z •
 θ ↔ exists k : Fin z.natAbs, ψ = θ …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem zsmul_eq_iff {ψ θ : Angle} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ) :=
  QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff hz
/-
**Real.Angle.nsmul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：nsmul_eq_iff {ψ θ : Angle} {n : Nat} (hz : n != 0) : n • ψ = n • θ ↔ exist
s k : Fin n, ψ = θ + (k : Nat) • (2 * π / n : Real)
参数：hz : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff`：zmultiples_nsmul_eq_nsmu
l_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : Nat} (hz : n != 0) : n • ψ = n •
 θ ↔ exists k : Fin n, ψ = θ + (k : …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem nsmul_eq_iff {ψ θ : Angle} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (2 * π / n : ℝ) :=
  QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hz
/-
**Real.Angle.two_zsmul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_eq_iff {ψ θ : Angle} : (2 : Int) • ψ = (2 : Int) • θ ↔ ψ = θ ∨ ψ
 = θ + ↑π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.zsmul_eq_iff`：zsmul_eq_iff {ψ θ : Angle} {z : Int} (hz : z !=
 0) : z • ψ = z • θ ↔ exists k : Fin z.natAbs, ψ = θ + (k : Nat) • (2 * π / z : 
Real)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Fin.exists_fin_two`：∀ {p : Fin 2 → Prop}, (∃ i, p i) ↔ p 0 ∨ p 1
· 使用定理 `Fin.val_zero`：∀ (n : ℕ) [inst : NeZero n], ↑0 = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.val_one`：∀ (n : ℕ), ↑1 = 1
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Int.cast_two`：cast_two : ((2 : Int) : R) = 2
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_zsmul_eq_iff {ψ θ : Angle} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  have : Int.natAbs 2 = 2 := rfl
  rw [zsmul_eq_iff two_ne_zero, this, Fin.exists_fin_two, Fin.val_zero,
    Fin.val_one, zero_smul, add_zero, one_smul, Int.cast_two,
    mul_div_cancel_left₀ (_ : ℝ) two_ne_zero]
/-
**Real.Angle.two_nsmul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) • ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ
 = θ + ↑π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem two_nsmul_eq_iff {ψ θ : Angle} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  simp_rw [← natCast_zsmul, Nat.cast_ofNat, two_zsmul_eq_iff]
/-
**Real.Angle.two_nsmul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_eq_zero_iff {θ : Angle} : (2 : Nat) • θ = 0 ↔ θ = 0 ∨ θ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.Angle.two_nsmul_eq_iff`：two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) 
• ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
-/
theorem two_nsmul_eq_zero_iff {θ : Angle} : (2 : ℕ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  convert! two_nsmul_eq_iff <;> simp
/-
**Real.Angle.two_nsmul_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_ne_zero_iff {θ : Angle} : (2 : Nat) • θ != 0 ↔ θ != 0 ∧ θ != π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Real.Angle.two_nsmul_eq_zero_iff`：two_nsmul_eq_zero_iff {θ : Angle} : (2
 : Nat) • θ = 0 ↔ θ = 0 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_nsmul_ne_zero_iff {θ : Angle} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← two_nsmul_eq_zero_iff]
/-
**Real.Angle.two_zsmul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_eq_zero_iff {θ : Angle} : (2 : Int) • θ = 0 ↔ θ = 0 ∨ θ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem two_zsmul_eq_zero_iff {θ : Angle} : (2 : ℤ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]
/-
**Real.Angle.two_zsmul_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_ne_zero_iff {θ : Angle} : (2 : Int) • θ != 0 ↔ θ != 0 ∧ θ != π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Real.Angle.two_zsmul_eq_zero_iff`：two_zsmul_eq_zero_iff {θ : Angle} : (2
 : Int) • θ = 0 ↔ θ = 0 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_zsmul_ne_zero_iff {θ : Angle} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← two_zsmul_eq_zero_iff]
/-
**Real.Angle.eq_neg_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0 ∨ θ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.two_nsmul_eq_zero_iff`：two_nsmul_eq_zero_iff {θ : Angle} : (2
 : Nat) • θ = 0 ↔ θ = 0 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0 ∨ θ = π := by
  rw [← add_eq_zero_iff_eq_neg, ← two_nsmul, two_nsmul_eq_zero_iff]
/-
**Real.Angle.ne_neg_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：ne_neg_self_iff {θ : Angle} : θ != -θ ↔ θ != 0 ∧ θ != π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.Angle.eq_neg_self_iff`：eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0
 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ne_neg_self_iff {θ : Angle} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← eq_neg_self_iff.not]
/-
**Real.Angle.neg_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：neg_eq_self_iff {θ : Angle} : -θ = θ ↔ θ = 0 ∨ θ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.Angle.eq_neg_self_iff`：eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0
 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neg_eq_self_iff {θ : Angle} : -θ = θ ↔ θ = 0 ∨ θ = π := by rw [eq_comm, eq_neg_self_iff]
/-
**Real.Angle.neg_ne_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：neg_ne_self_iff {θ : Angle} : -θ != θ ↔ θ != 0 ∧ θ != π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.Angle.neg_eq_self_iff`：neg_eq_self_iff {θ : Angle} : -θ = θ ↔ θ = 0
 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neg_ne_self_iff {θ : Angle} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← neg_eq_self_iff.not]
/-
**Real.Angle.two_nsmul_eq_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_eq_pi_iff {θ : Angle} : (2 : Nat) • θ = π ↔ θ = (π / 2 : Real) ∨
 θ = (-π / 2 : Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.Angle.coe_nsmul`：coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) =
 n • (↑x : Angle)
· 使用定理 `Real.Angle.two_nsmul_eq_iff`：two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) 
• ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Real.Angle.coe_sub`：coe_sub (x y : Real) : ↑(x - y : Real) = (↑x - ↑y : 
Angle)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Real.Angle.coe_two_pi`：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
-/
theorem two_nsmul_eq_pi_iff {θ : Angle} : (2 : ℕ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  have h : (π : Angle) = ((2 : ℕ) • (π / 2 : ℝ) :) := by rw [two_nsmul, add_halves]
  nth_rw 1 [h]
  rw [coe_nsmul, two_nsmul_eq_iff]
  apply iff_of_eq -- `congr` only works on `Eq`, so rewrite from `Iff` to `Eq`.
  congr
  rw [add_comm, ← coe_add, ← sub_eq_zero, ← coe_sub, neg_div, sub_neg_eq_add, add_assoc,
    add_halves, ← two_mul, coe_two_pi]
/-
**Real.Angle.two_zsmul_eq_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_eq_pi_iff {θ : Angle} : (2 : Int) • θ = π ↔ θ = (π / 2 : Real) ∨
 θ = (-π / 2 : Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.two_nsmul_eq_pi_iff`：two_nsmul_eq_pi_iff {θ : Angle} : (2 : N
at) • θ = π ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_zsmul_eq_pi_iff {θ : Angle} : (2 : ℤ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_eq_pi_iff]
/-
**Real.Angle.cos_eq_iff_coe_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_eq_iff_coe_eq_or_eq_neg {θ ψ : Real} : cos θ = cos ψ ↔ (θ : Angle) = ψ
 ∨ (θ : Angle) = -ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sin_eq_zero_iff`：sin_eq_zero_iff {x : Real} : sin x = 0 ↔ exists n 
: Int, (n : Real) * π = x
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.cos_sub_cos`：∀ (x y : ℝ), Real.cos x - Real.cos y = -2 * Real.sin (
(x + y) / 2) * Real.sin ((x - y) / 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `Real.Angle.coe_sub`：coe_sub (x y : Real) : ↑(x - y : Real) = (↑x - ↑y : 
Angle)
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.Angle.intCast_mul_eq_zsmul`：intCast_mul_eq_zsmul (x : Real) (n : In
t) : ↑((n : Real) * x : Real) = n • (↑x : Angle)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.Angle.coe_two_pi`：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
· 使用定理 `zsmul_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (n : ℤ), n • 0
 = 0
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
（共 35 条，此处仅展示前 30 条）
-/
theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} :
    cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ := by
  constructor
  · intro Hcos
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero,
      eq_false (two_ne_zero' ℝ), false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    · right
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), ← sub_eq_iff_eq_add] at hn
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc, intCast_mul_eq_zsmul,
        mul_comm, coe_two_pi, zsmul_zero]
    · left
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), eq_sub_iff_add_eq] at hn
      rw [← hn, coe_add, mul_assoc, intCast_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero,
        zero_add]
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' ℝ),
        mul_comm π _, sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
      mul_div_cancel_left₀ _ (two_ne_zero' ℝ), mul_comm π _, sin_int_mul_pi, mul_zero,
      zero_mul]
/-
**Real.Angle.sin_eq_iff_coe_eq_or_add_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angl
e`。
形式化陈述：sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : Real} : sin θ = sin ψ ↔ (θ : Angle) 
= ψ ∨ (θ : Angle) + ψ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.cos_eq_iff_coe_eq_or_eq_neg`：cos_eq_iff_coe_eq_or_eq_neg {θ ψ
 : Real} : cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cos_pi_div_two_sub`：cos_pi_div_two_sub (x : Real) : cos (π / 2 - x)
 = sin x
· 使用定理 `sub_right_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - b =
 a - c ↔ b = c
· 使用定理 `Real.Angle.coe_sub`：coe_sub (x y : Real) : ↑(x - y : Real) = (↑x - ↑y : 
Angle)
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Real.sin_sub_sin`：∀ (x y : ℝ), Real.sin x - Real.sin y = 2 * Real.sin ((
x - y) / 2) * Real.cos ((x + y) / 2)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.sin_int_mul_pi`：sin_int_mul_pi (n : Int) : sin (n * π) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
（共 33 条，此处仅展示前 30 条）
-/
theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : ℝ} :
    sin θ = sin ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) + ψ = π := by
  constructor
  · intro Hsin
    rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin
    rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h | h
    · left
      rw [coe_sub, coe_sub] at h
      exact sub_right_inj.1 h
    right
    rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub, sub_add_eq_add_sub, ← coe_add,
      add_halves, sub_sub, sub_eq_zero] at h
    exact h.symm
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' ℝ),
        mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assoc, mul_comm π _, ←
        mul_assoc] at H
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assoc 2 _ π,
      mul_div_cancel_left₀ _ (two_ne_zero' ℝ), cos_add_pi_div_two, sin_int_mul_pi, neg_zero,
      mul_zero]
/-
**Real.Angle.cos_sin_inj** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_sin_inj {θ ψ : Real} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (
θ : Angle) = ψ
参数：Hcos : cos θ = cos ψ；Hsin : sin θ = sin ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.cos_eq_iff_coe_eq_or_eq_neg`：cos_eq_iff_coe_eq_or_eq_neg {θ ψ
 : Real} : cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ
· 使用定理 `Real.Angle.sin_eq_iff_coe_eq_or_add_eq_pi`：sin_eq_iff_coe_eq_or_add_eq_p
i {θ ψ : Real} : sin θ = sin ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) + ψ = π
· 使用定理 `QuotientAddGroup.leftRel_apply`：∀ {α : Type u_1} [inst : AddGroup α] {s 
: AddSubgroup α} {x y : α}, (QuotientAddGroup.leftRel s) x y ↔ -x + y ∈ s
· 使用定理 `Quotient.exact'`：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Qu
otient.mk'' b -> s₁ a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `Int.add_mul_emod_self_right`：∀ (a b c : ℤ), (a + b * c) % c = a % c
（共 34 条，此处仅展示前 30 条）
-/
theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : Angle) = ψ := by
  rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc | hc; · exact hc
  rcases sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs | hs; · exact hs
  rw [eq_neg_iff_add_eq_zero, hs] at hc
  obtain ⟨n, hn⟩ : ∃ n, n • _ = _ := QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hc)
  rw [← neg_one_mul, add_zero, ← sub_eq_zero, zsmul_eq_mul, ← mul_assoc, ← sub_mul, mul_eq_zero,
    eq_false (ne_of_gt pi_pos), or_false, sub_neg_eq_add, ← Int.cast_zero, ← Int.cast_one,
    ← Int.cast_ofNat, ← Int.cast_mul, ← Int.cast_add, Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : ℤ) = 0 % (2 : ℤ) := congr_arg (· % (2 : ℤ)) hn
  rw [add_comm, Int.add_mul_emod_self_right] at this
  exact absurd this one_ne_zero

/-- The sine of a `Real.Angle`. -/
/-
**Real.Angle.sin** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：sin (θ : Angle) : Real
参数：θ : Angle。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sin_periodic`：sin_periodic : Function.Periodic sin (2 * π)

--- 原说明 ---
The sine of a `Real.Angle`.
-/
def sin (θ : Angle) : ℝ :=
  sin_periodic.lift θ

@[simp]
/-
**Real.Angle.sin_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sin_coe (x : ℝ) : sin (x : Angle) = Real.sin x :=
  rfl

@[continuity]
/-
**Real.Angle.continuous_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：continuous_sin : Continuous sin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.quotient_liftOn'`：Continuous.quotient_liftOn' {f : X -> Y} (h
 : Continuous f) (hs : forall a b, s a b -> f a = f b) : Continuous (fun x => Qu
otient.liftOn' x …
· 使用定理 `Real.continuous_sin`：continuous_sin : Continuous sin
· 使用定理 `Real.sin_periodic`：sin_periodic : Function.Periodic sin (2 * π)
-/
theorem continuous_sin : Continuous sin :=
  Real.continuous_sin.quotient_liftOn' _

/-- The cosine of a `Real.Angle`. -/
/-
**Real.Angle.cos** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：cos (θ : Angle) : Real
参数：θ : Angle。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.cos_periodic`：cos_periodic : Function.Periodic cos (2 * π)

--- 原说明 ---
The cosine of a `Real.Angle`.
-/
def cos (θ : Angle) : ℝ :=
  cos_periodic.lift θ

@[simp]
/-
**Real.Angle.cos_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cos_coe (x : ℝ) : cos (x : Angle) = Real.cos x :=
  rfl

@[continuity]
/-
**Real.Angle.continuous_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：continuous_cos : Continuous cos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.quotient_liftOn'`：Continuous.quotient_liftOn' {f : X -> Y} (h
 : Continuous f) (hs : forall a b, s a b -> f a = f b) : Continuous (fun x => Qu
otient.liftOn' x …
· 使用定理 `Real.continuous_cos`：continuous_cos : Continuous cos
· 使用定理 `Real.cos_periodic`：cos_periodic : Function.Periodic cos (2 * π)
-/
theorem continuous_cos : Continuous cos :=
  Real.continuous_cos.quotient_liftOn' _
/-
**Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.An
gle`。
形式化陈述：cos_eq_real_cos_iff_eq_or_eq_neg {θ : Angle} {ψ : Real} : cos θ = Real.cos
 ψ ↔ θ = ψ ∨ θ = -ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.Angle.cos_eq_iff_coe_eq_or_eq_neg`：cos_eq_iff_coe_eq_or_eq_neg {θ ψ
 : Real} : cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ
-/
theorem cos_eq_real_cos_iff_eq_or_eq_neg {θ : Angle} {ψ : ℝ} :
    cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction θ using Real.Angle.induction_on
  exact cos_eq_iff_coe_eq_or_eq_neg
/-
**Real.Angle.cos_eq_iff_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_eq_iff_eq_or_eq_neg {θ ψ : Angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg`：cos_eq_real_cos_iff_eq_or_e
q_neg {θ : Angle} {ψ : Real} : cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ
-/
theorem cos_eq_iff_eq_or_eq_neg {θ ψ : Angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction ψ using Real.Angle.induction_on
  exact cos_eq_real_cos_iff_eq_or_eq_neg
/-
**Real.Angle.sin_eq_real_sin_iff_eq_or_add_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real
.Angle`。
形式化陈述：sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : Angle} {ψ : Real} : sin θ = Real.
sin ψ ↔ θ = ψ ∨ θ + ψ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.Angle.sin_eq_iff_coe_eq_or_add_eq_pi`：sin_eq_iff_coe_eq_or_add_eq_p
i {θ ψ : Real} : sin θ = sin ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) + ψ = π
-/
theorem sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : Angle} {ψ : ℝ} :
    sin θ = Real.sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction θ using Real.Angle.induction_on
  exact sin_eq_iff_coe_eq_or_add_eq_pi
/-
**Real.Angle.sin_eq_iff_eq_or_add_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_eq_iff_eq_or_add_eq_pi {θ ψ : Angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ =
 π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.Angle.sin_eq_real_sin_iff_eq_or_add_eq_pi`：sin_eq_real_sin_iff_eq_o
r_add_eq_pi {θ : Angle} {ψ : Real} : sin θ = Real.sin ψ ↔ θ = ψ ∨ θ + ψ = π
-/
theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : Angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction ψ using Real.Angle.induction_on
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi

@[simp]
/-
**Real.Angle.sin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_zero : sin (0 : Angle) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_zero`：coe_zero : ↑(0 : Real) = (0 : Angle)
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
-/
theorem sin_zero : sin (0 : Angle) = 0 := by rw [← coe_zero, sin_coe, Real.sin_zero]
/-
**Real.Angle.sin_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_coe_pi : sin (π : Angle) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `Real.sin_pi`：sin_pi : sin π = 0
-/
theorem sin_coe_pi : sin (π : Angle) = 0 := by rw [sin_coe, Real.sin_pi]
/-
**Real.Angle.sin_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.sin_zero`：sin_zero : sin (0 : Angle) = 0
· 使用定理 `Real.Angle.sin_eq_iff_eq_or_add_eq_pi`：sin_eq_iff_eq_or_add_eq_pi {θ ψ :
 Angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π := by
  nth_rw 1 [← sin_zero]
  rw [sin_eq_iff_eq_or_add_eq_pi]
  simp
/-
**Real.Angle.sin_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_ne_zero_iff {θ : Angle} : sin θ != 0 ↔ θ != 0 ∧ θ != π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Real.Angle.sin_eq_zero_iff`：sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ 
= 0 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sin_ne_zero_iff {θ : Angle} : sin θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← sin_eq_zero_iff]

@[simp]
/-
**Real.Angle.sin_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_neg (θ : Angle) : sin (-θ) = -sin θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
-/
theorem sin_neg (θ : Angle) : sin (-θ) = -sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_neg _
/-
**Real.Angle.sin_antiperiodic** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_antiperiodic : Function.Antiperiodic sin (π : Angle)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.sin_antiperiodic`：sin_antiperiodic : Function.Antiperiodic sin π
-/
theorem sin_antiperiodic : Function.Antiperiodic sin (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.sin_antiperiodic _

@[simp]
/-
**Real.Angle.sin_add_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.sin_antiperiodic`：sin_antiperiodic : Function.Antiperiodic si
n (π : Angle)
-/
theorem sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ :=
  sin_antiperiodic θ

@[simp]
/-
**Real.Angle.sin_sub_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_sub_pi (θ : Angle) : sin (θ - π) = -sin θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β
} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodi
c f c → ∀ (x : α),…
· 使用定理 `Real.Angle.sin_antiperiodic`：sin_antiperiodic : Function.Antiperiodic si
n (π : Angle)
-/
theorem sin_sub_pi (θ : Angle) : sin (θ - π) = -sin θ :=
  sin_antiperiodic.sub_eq θ

@[simp]
/-
**Real.Angle.cos_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_zero : cos (0 : Angle) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_zero`：coe_zero : ↑(0 : Real) = (0 : Angle)
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
-/
theorem cos_zero : cos (0 : Angle) = 1 := by rw [← coe_zero, cos_coe, Real.cos_zero]
/-
**Real.Angle.cos_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_coe_pi : cos (π : Angle) = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `Real.cos_pi`：cos_pi : cos π = -1
-/
theorem cos_coe_pi : cos (π : Angle) = -1 := by rw [cos_coe, Real.cos_pi]

@[simp]
/-
**Real.Angle.cos_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_neg (θ : Angle) : cos (-θ) = cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.cos_neg`：cos_neg : cos (-x) = cos x
-/
theorem cos_neg (θ : Angle) : cos (-θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_neg _
/-
**Real.Angle.cos_antiperiodic** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_antiperiodic : Function.Antiperiodic cos (π : Angle)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.cos_antiperiodic`：cos_antiperiodic : Function.Antiperiodic cos π
-/
theorem cos_antiperiodic : Function.Antiperiodic cos (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.cos_antiperiodic _

@[simp]
/-
**Real.Angle.cos_add_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.cos_antiperiodic`：cos_antiperiodic : Function.Antiperiodic co
s (π : Angle)
-/
theorem cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ :=
  cos_antiperiodic θ

@[simp]
/-
**Real.Angle.cos_sub_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_sub_pi (θ : Angle) : cos (θ - π) = -cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β
} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodi
c f c → ∀ (x : α),…
· 使用定理 `Real.Angle.cos_antiperiodic`：cos_antiperiodic : Function.Antiperiodic co
s (π : Angle)
-/
theorem cos_sub_pi (θ : Angle) : cos (θ - π) = -cos θ :=
  cos_antiperiodic.sub_eq θ
/-
**Real.Angle.cos_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_eq_zero_iff {θ : Angle} : cos θ = 0 ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2
 : Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cos_pi_div_two`：cos_pi_div_two : cos (π / 2) = 0
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `Real.Angle.cos_eq_iff_eq_or_eq_neg`：cos_eq_iff_eq_or_eq_neg {θ ψ : Angle
} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cos_eq_zero_iff {θ : Angle} : cos θ = 0 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [← cos_pi_div_two, ← cos_coe, cos_eq_iff_eq_or_eq_neg, ← coe_neg, ← neg_div]
/-
**Real.Angle.sin_add** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_add (θ₁ θ₂ : Real.Angle) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * 
sin θ₂
参数：θ₁ θ₂ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.sin_add`：∀ (x y : ℝ), Real.sin (x + y) = Real.sin x * Real.cos y + 
Real.cos x * Real.sin y
-/
theorem sin_add (θ₁ θ₂ : Real.Angle) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact Real.sin_add _ _
/-
**Real.Angle.cos_add** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_add (θ₁ θ₂ : Real.Angle) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * 
sin θ₂
参数：θ₁ θ₂ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.cos_add`：∀ (x y : ℝ), Real.cos (x + y) = Real.cos x * Real.cos y - 
Real.sin x * Real.sin y
-/
theorem cos_add (θ₁ θ₂ : Real.Angle) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ := by
  induction θ₂ using Real.Angle.induction_on
  induction θ₁ using Real.Angle.induction_on
  exact Real.cos_add _ _
/-
**Real.Angle.sin_two_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_two_nsmul (θ : Angle) : sin (2 • θ) = 2 • (sin θ * cos θ)
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.sin_add`：sin_add (θ₁ θ₂ : Real.Angle) : sin (θ₁ + θ₂) = sin θ
₁ * cos θ₂ + cos θ₁ * sin θ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sin_two_nsmul (θ : Angle) : sin (2 • θ) = 2 • (sin θ * cos θ) := by
  simp [two_nsmul, two_mul, sin_add, mul_comm]

@[simp]
/-
**Real.Angle.cos_sq_add_sin_sq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_sq_add_sin_sq (θ : Real.Angle) : cos θ ^ 2 + sin θ ^ 2 = 1
参数：θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.cos_sq_add_sin_sq`：cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1
-/
theorem cos_sq_add_sin_sq (θ : Real.Angle) : cos θ ^ 2 + sin θ ^ 2 = 1 := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sq_add_sin_sq _
/-
**Real.Angle.sin_add_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_add_pi_div_two (θ : Angle) : sin (θ + ↑(π / 2)) = cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sin_add_pi_div_two`：sin_add_pi_div_two (x : Real) : sin (x + π / 2)
 = cos x
-/
theorem sin_add_pi_div_two (θ : Angle) : sin (θ + ↑(π / 2)) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_add_pi_div_two _
/-
**Real.Angle.sin_sub_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_sub_pi_div_two (θ : Angle) : sin (θ - ↑(π / 2)) = -cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sin_sub_pi_div_two`：sin_sub_pi_div_two (x : Real) : sin (x - π / 2)
 = -cos x
-/
theorem sin_sub_pi_div_two (θ : Angle) : sin (θ - ↑(π / 2)) = -cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_sub_pi_div_two _
/-
**Real.Angle.sin_pi_div_two_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_pi_div_two_sub (θ : Angle) : sin (↑(π / 2) - θ) = cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sin_pi_div_two_sub`：sin_pi_div_two_sub (x : Real) : sin (π / 2 - x)
 = cos x
-/
theorem sin_pi_div_two_sub (θ : Angle) : sin (↑(π / 2) - θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_pi_div_two_sub _
/-
**Real.Angle.cos_add_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_add_pi_div_two (θ : Angle) : cos (θ + ↑(π / 2)) = -sin θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.cos_add_pi_div_two`：cos_add_pi_div_two (x : Real) : cos (x + π / 2)
 = -sin x
-/
theorem cos_add_pi_div_two (θ : Angle) : cos (θ + ↑(π / 2)) = -sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_add_pi_div_two _
/-
**Real.Angle.cos_sub_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_sub_pi_div_two (θ : Angle) : cos (θ - ↑(π / 2)) = sin θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.cos_sub_pi_div_two`：cos_sub_pi_div_two (x : Real) : cos (x - π / 2)
 = sin x
-/
theorem cos_sub_pi_div_two (θ : Angle) : cos (θ - ↑(π / 2)) = sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sub_pi_div_two _
/-
**Real.Angle.cos_pi_div_two_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_pi_div_two_sub (θ : Angle) : cos (↑(π / 2) - θ) = sin θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.cos_pi_div_two_sub`：cos_pi_div_two_sub (x : Real) : cos (π / 2 - x)
 = sin x
-/
theorem cos_pi_div_two_sub (θ : Angle) : cos (↑(π / 2) - θ) = sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_pi_div_two_sub _
/-
**Real.Angle.abs_sin_eq_of_two_nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_sin_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • 
ψ) : |sin θ| = |sin ψ|
参数：h : (2 : Nat) • θ = (2 : Nat) • ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_nsmul_eq_iff`：two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) 
• ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `Real.Angle.sin_add_pi`：sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem abs_sin_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |sin θ| = |sin ψ| := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [sin_add_pi, abs_neg]
/-
**Real.Angle.abs_sin_eq_of_two_zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_sin_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • 
ψ) : |sin θ| = |sin ψ|
参数：h : (2 : Int) • θ = (2 : Int) • ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.abs_sin_eq_of_two_nsmul_eq`：abs_sin_eq_of_two_nsmul_eq {θ ψ :
 Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ) : |sin θ| = |sin ψ|
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
-/
theorem abs_sin_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |sin θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_sin_eq_of_two_nsmul_eq h
/-
**Real.Angle.abs_cos_eq_of_two_nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_cos_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • 
ψ) : |cos θ| = |cos ψ|
参数：h : (2 : Nat) • θ = (2 : Nat) • ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_nsmul_eq_iff`：two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) 
• ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `Real.Angle.cos_add_pi`：cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem abs_cos_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |cos θ| = |cos ψ| := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [cos_add_pi, abs_neg]
/-
**Real.Angle.abs_cos_eq_of_two_zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_cos_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • 
ψ) : |cos θ| = |cos ψ|
参数：h : (2 : Int) • θ = (2 : Int) • ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.abs_cos_eq_of_two_nsmul_eq`：abs_cos_eq_of_two_nsmul_eq {θ ψ :
 Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ) : |cos θ| = |cos ψ|
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
-/
theorem abs_cos_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |cos θ| = |cos ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_of_two_nsmul_eq h

@[simp]
/-
**Real.Angle.coe_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_toIcoMod (θ ψ : Real) : ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle)
参数：θ ψ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `toIcoMod_sub_self`：toIcoMod_sub_self (a b : α) : toIcoMod hp a b - b = -
toIcoDiv hp a b • p
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem coe_toIcoMod (θ ψ : ℝ) : ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIcoDiv two_pi_pos ψ θ, ?_⟩
  rw [toIcoMod_sub_self, zsmul_eq_mul, mul_comm]

@[simp]
/-
**Real.Angle.coe_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_toIocMod (θ ψ : Real) : ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle)
参数：θ ψ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `toIocMod_sub_self`：toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -
toIocDiv hp a b • p
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem coe_toIocMod (θ ψ : ℝ) : ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIocDiv two_pi_pos ψ θ, ?_⟩
  rw [toIocMod_sub_self, zsmul_eq_mul, mul_comm]

/-- Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`. -/
/-
**Real.Angle.toReal** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：toReal (θ : Angle) : Real
参数：θ : Angle。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π

--- 原说明 ---
Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
-/
def toReal (θ : Angle) : ℝ :=
  (toIocMod_periodic two_pi_pos (-π)).lift θ
/-
**Real.Angle.toReal_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_coe (θ : Real) : (θ : Angle).toReal = toIocMod two_pi_pos (-π) θ
参数：θ : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_coe (θ : ℝ) : (θ : Angle).toReal = toIocMod two_pi_pos (-π) θ :=
  rfl
/-
**Real.Angle.toReal_coe_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_coe_eq_self_iff {θ : Real} : (θ : Angle).toReal = θ ↔ -π < θ ∧ θ <=
 π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toReal_coe`：toReal_coe (θ : Real) : (θ : Angle).toReal = toIo
cMod two_pi_pos (-π) θ
· 使用定理 `toIocMod_eq_self`：toIocMod_eq_self : toIocMod hp a b = b ↔ b in Set.Ioc 
a (a + p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 43 条，此处仅展示前 30 条）
-/
theorem toReal_coe_eq_self_iff {θ : ℝ} : (θ : Angle).toReal = θ ↔ -π < θ ∧ θ ≤ π := by
  rw [toReal_coe, toIocMod_eq_self two_pi_pos]
  ring_nf
  rfl
/-
**Real.Angle.toReal_coe_eq_self_iff_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angl
e`。
形式化陈述：toReal_coe_eq_self_iff_mem_Ioc {θ : Real} : (θ : Angle).toReal = θ ↔ θ in 
Set.Ioc (-π) π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toReal_coe_eq_self_iff_mem_Ioc {θ : ℝ} : (θ : Angle).toReal = θ ↔ θ ∈ Set.Ioc (-π) π := by
  rw [toReal_coe_eq_self_iff, ← Set.mem_Ioc]

@[grind inj]
/-
**Real.Angle.toReal_injective** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_injective : Function.Injective toReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem toReal_injective : Function.Injective toReal := by
  intro θ ψ h
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  simpa [toReal_coe, toIocMod_eq_toIocMod, zsmul_eq_mul, mul_comm _ (2 * π), ←
    angle_eq_iff_two_pi_dvd_sub, eq_comm] using h

@[simp]
/-
**Real.Angle.toReal_inj** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ θ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Real.Angle.toReal_injective`：toReal_injective : Function.Injective toRea
l
-/
theorem toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ θ = ψ :=
  toReal_injective.eq_iff

@[simp, grind =]
/-
**Real.Angle.coe_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Real.Angle.coe_toIocMod`：coe_toIocMod (θ ψ : Real) : ↑(toIocMod two_pi_p
os ψ θ) = (θ : Angle)
-/
theorem coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ := by
  induction θ using Real.Angle.induction_on
  exact coe_toIocMod _ _
/-
**Real.Angle.neg_pi_lt_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：neg_pi_lt_toReal (θ : Angle) : -π < θ.toReal
参数：θ : Angle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `left_lt_toIocMod`：left_lt_toIocMod (a b : α) : a < toIocMod hp a b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
-/
theorem neg_pi_lt_toReal (θ : Angle) : -π < θ.toReal := by
  induction θ using Real.Angle.induction_on
  exact left_lt_toIocMod _ _ _
/-
**Real.Angle.toReal_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_le_pi (θ : Angle) : θ.toReal <= π
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 37 条，此处仅展示前 30 条）
-/
theorem toReal_le_pi (θ : Angle) : θ.toReal ≤ π := by
  induction θ using Real.Angle.induction_on
  convert! toIocMod_le_right two_pi_pos _ _
  ring
/-
**Real.Angle.abs_toReal_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_toReal_le_pi (θ : Angle) : |θ.toReal| <= π
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.Angle.neg_pi_lt_toReal`：neg_pi_lt_toReal (θ : Angle) : -π < θ.toRea
l
· 使用定理 `Real.Angle.toReal_le_pi`：toReal_le_pi (θ : Angle) : θ.toReal <= π
-/
theorem abs_toReal_le_pi (θ : Angle) : |θ.toReal| ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_toReal _).le, toReal_le_pi _⟩
/-
**Real.Angle.toReal_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_mem_Ioc (θ : Angle) : θ.toReal in Set.Ioc (-π) π
参数：θ : Angle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.neg_pi_lt_toReal`：neg_pi_lt_toReal (θ : Angle) : -π < θ.toRea
l
· 使用定理 `Real.Angle.toReal_le_pi`：toReal_le_pi (θ : Angle) : θ.toReal <= π
-/
theorem toReal_mem_Ioc (θ : Angle) : θ.toReal ∈ Set.Ioc (-π) π :=
  ⟨neg_pi_lt_toReal _, toReal_le_pi _⟩

@[simp]
/-
**Real.Angle.toIocMod_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toIocMod_toReal (θ : Angle) : toIocMod two_pi_pos (-π) θ.toReal = θ.toReal
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toReal_coe`：toReal_coe (θ : Real) : (θ : Angle).toReal = toIo
cMod two_pi_pos (-π) θ
· 使用定理 `toIocMod_toIocMod`：toIocMod_toIocMod (a₁ a₂ b : α) : toIocMod hp a₁ (toI
ocMod hp a₂ b) = toIocMod hp a₁ b
-/
theorem toIocMod_toReal (θ : Angle) : toIocMod two_pi_pos (-π) θ.toReal = θ.toReal := by
  induction θ using Real.Angle.induction_on
  rw [toReal_coe]
  exact toIocMod_toIocMod _ _ _ _

@[simp, grind =]
/-
**Real.Angle.toReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_zero : (0 : Angle).toReal = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_zero`：coe_zero : ↑(0 : Real) = (0 : Angle)
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem toReal_zero : (0 : Angle).toReal = 0 := by
  rw [← coe_zero, toReal_coe_eq_self_iff]
  exact ⟨Left.neg_neg_iff.2 Real.pi_pos, Real.pi_pos.le⟩

@[simp]
/-
**Real.Angle.toReal_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_eq_zero_iff {θ : Angle} : θ.toReal = 0 ↔ θ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `Real.Angle.toReal_inj`：toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ 
θ = ψ
-/
theorem toReal_eq_zero_iff {θ : Angle} : θ.toReal = 0 ↔ θ = 0 := by
  nth_rw 1 [← toReal_zero]
  exact toReal_inj

@[simp, grind =]
/-
**Real.Angle.toReal_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_pi : (π : Angle).toReal = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `Left.neg_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder 
α] [AddLeftStrictMono α] {a : α}, 0 < a → -a < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem toReal_pi : (π : Angle).toReal = π := by
  rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_lt_self Real.pi_pos, le_refl _⟩

@[simp]
/-
**Real.Angle.toReal_eq_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_eq_pi_iff {θ : Angle} : θ.toReal = π ↔ θ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_inj`：toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ 
θ = ψ
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toReal_eq_pi_iff {θ : Angle} : θ.toReal = π ↔ θ = π := by rw [← toReal_inj, toReal_pi]
/-
**Real.Angle.toReal_neg_eq_neg_toReal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angle`
。
形式化陈述：toReal_neg_eq_neg_toReal_iff {θ : Angle} : (-θ).toReal = -(θ.toReal) ↔ θ !
= π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Real.Angle.toReal_le_pi`：toReal_le_pi (θ : Angle) : θ.toReal <= π
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 52 条，此处仅展示前 30 条）
-/
lemma toReal_neg_eq_neg_toReal_iff {θ : Angle} : (-θ).toReal = -(θ.toReal) ↔ θ ≠ π := by
  nth_rw 1 [← coe_toReal θ, ← coe_neg, toReal_coe_eq_self_iff]
  constructor
  · rintro ⟨h, h'⟩ rfl
    simp at h
  · intro h
    rw [neg_lt_neg_iff]
    have h' : θ.toReal ≠ π := by simp [h]
    exact ⟨(toReal_le_pi θ).lt_of_ne h', by linarith [neg_pi_lt_toReal θ]⟩
/-
**Real.Angle.abs_toReal_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：∀ (θ : Real.Angle), |(-θ).toReal| = |θ.toReal|
参数：θ : Real.Angle；-θ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Real.Angle.toReal_neg_eq_neg_toReal_iff`：toReal_neg_eq_neg_toReal_iff {θ
 : Angle} : (-θ).toReal = -(θ.toReal) ↔ θ != π
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
@[simp] lemma abs_toReal_neg (θ : Angle) : |(-θ).toReal| = |θ.toReal| := by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp [toReal_neg_eq_neg_toReal_iff.2 h]
/-
**Real.Angle.pi_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：pi_ne_zero : (π : Angle) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Real.Angle.toReal_injective`：toReal_injective : Function.Injective toRea
l
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
-/
theorem pi_ne_zero : (π : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_pi, toReal_zero]
  exact Real.pi_ne_zero

@[simp, grind =]
/-
**Real.Angle.toReal_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_pi_div_two : ((π / 2 : Real) : Angle).toReal = π / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 66 条，此处仅展示前 30 条）
-/
theorem toReal_pi_div_two : ((π / 2 : ℝ) : Angle).toReal = π / 2 :=
  toReal_coe_eq_self_iff.2 <| by constructor <;> linarith [pi_pos]

@[simp]
/-
**Real.Angle.toReal_eq_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_eq_pi_div_two_iff {θ : Angle} : θ.toReal = π / 2 ↔ θ = (π / 2 : Rea
l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_inj`：toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ 
θ = ψ
· 使用定理 `Real.Angle.toReal_pi_div_two`：toReal_pi_div_two : ((π / 2 : Real) : Angl
e).toReal = π / 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toReal_eq_pi_div_two_iff {θ : Angle} : θ.toReal = π / 2 ↔ θ = (π / 2 : ℝ) := by
  rw [← toReal_inj, toReal_pi_div_two]

@[simp, grind =]
/-
**Real.Angle.toReal_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_neg_pi_div_two : ((-π / 2 : Real) : Angle).toReal = -π / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 66 条，此处仅展示前 30 条）
-/
theorem toReal_neg_pi_div_two : ((-π / 2 : ℝ) : Angle).toReal = -π / 2 :=
  toReal_coe_eq_self_iff.2 <| by constructor <;> linarith [pi_pos]

@[simp]
/-
**Real.Angle.toReal_eq_neg_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`
。
形式化陈述：toReal_eq_neg_pi_div_two_iff {θ : Angle} : θ.toReal = -π / 2 ↔ θ = (-π / 2
 : Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_inj`：toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ 
θ = ψ
· 使用定理 `Real.Angle.toReal_neg_pi_div_two`：toReal_neg_pi_div_two : ((-π / 2 : Rea
l) : Angle).toReal = -π / 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toReal_eq_neg_pi_div_two_iff {θ : Angle} : θ.toReal = -π / 2 ↔ θ = (-π / 2 : ℝ) := by
  rw [← toReal_inj, toReal_neg_pi_div_two]
/-
**Real.Angle.pi_div_two_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：pi_div_two_ne_zero : ((π / 2 : Real) : Angle) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Real.Angle.toReal_injective`：toReal_injective : Function.Injective toRea
l
· 使用定理 `Real.Angle.toReal_pi_div_two`：toReal_pi_div_two : ((π / 2 : Real) : Angl
e).toReal = π / 2
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem pi_div_two_ne_zero : ((π / 2 : ℝ) : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_pi_div_two, toReal_zero]
  exact div_ne_zero Real.pi_ne_zero two_ne_zero
/-
**Real.Angle.neg_pi_div_two_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：neg_pi_div_two_ne_zero : ((-π / 2 : Real) : Angle) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Real.Angle.toReal_injective`：toReal_injective : Function.Injective toRea
l
· 使用定理 `Real.Angle.toReal_neg_pi_div_two`：toReal_neg_pi_div_two : ((-π / 2 : Rea
l) : Angle).toReal = -π / 2
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem neg_pi_div_two_ne_zero : ((-π / 2 : ℝ) : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_neg_pi_div_two, toReal_zero]
  exact div_ne_zero (neg_ne_zero.2 Real.pi_ne_zero) two_ne_zero
/-
**Real.Angle.abs_toReal_coe_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_toReal_coe_eq_self_iff {θ : Real} : |(θ : Angle).toReal| = θ ↔ 0 <= θ 
∧ θ <= π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.Angle.abs_toReal_le_pi`：abs_toReal_le_pi (θ : Angle) : |θ.toReal| <
= π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Left.neg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem abs_toReal_coe_eq_self_iff {θ : ℝ} : |(θ : Angle).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
  ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h =>
    (toReal_coe_eq_self_iff.2 ⟨(Left.neg_neg_iff.2 Real.pi_pos).trans_le h.1, h.2⟩).symm ▸
      abs_eq_self.2 h.1⟩
/-
**Real.Angle.abs_toReal_neg_coe_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angl
e`。
形式化陈述：abs_toReal_neg_coe_eq_self_iff {θ : Real} : |(-θ : Angle).toReal| = θ ↔ 0 
<= θ ∧ θ <= π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.Angle.abs_toReal_le_pi`：abs_toReal_le_pi (θ : Angle) : |θ.toReal| <
= π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
-/
theorem abs_toReal_neg_coe_eq_self_iff {θ : ℝ} : |(-θ : Angle).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π := by
  refine ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h => ?_⟩
  by_cases hnegpi : θ = π; · simp [hnegpi, Real.pi_pos.le]
  rw [← coe_neg,
    toReal_coe_eq_self_iff.2
      ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi), (neg_nonpos.2 h.1).trans Real.pi_pos.le⟩,
    abs_neg, abs_eq_self.2 h.1]
/-
**Real.Angle.abs_toReal_eq_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`
。
形式化陈述：abs_toReal_eq_pi_div_two_iff {θ : Angle} : |θ.toReal| = π / 2 ↔ θ = (π / 2
 : Real) ∨ θ = (-π / 2 : Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_eq`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   0 ≤ b → (|a| = b ↔ a = b ∨ a = -b)
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Real.Angle.toReal_eq_pi_div_two_iff`：toReal_eq_pi_div_two_iff {θ : Angle
} : θ.toReal = π / 2 ↔ θ = (π / 2 : Real)
· 使用定理 `Real.Angle.toReal_eq_neg_pi_div_two_iff`：toReal_eq_neg_pi_div_two_iff {θ
 : Angle} : θ.toReal = -π / 2 ↔ θ = (-π / 2 : Real)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abs_toReal_eq_pi_div_two_iff {θ : Angle} :
    |θ.toReal| = π / 2 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [abs_eq (div_nonneg Real.pi_pos.le two_pos.le), ← neg_div, toReal_eq_pi_div_two_iff,
    toReal_eq_neg_pi_div_two_iff]
/-
**Real.Angle.nsmul_toReal_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：nsmul_toReal_eq_mul {n : Nat} (h : n != 0) {θ : Angle} : (n • θ).toReal = 
n * θ.toReal ↔ θ.toReal in Set.Ioc (-π / n) (π / n)
参数：h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Real.Angle.coe_nsmul`：coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) =
 n • (↑x : Angle)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nsmul_toReal_eq_mul {n : ℕ} (h : n ≠ 0) {θ : Angle} :
    (n • θ).toReal = n * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / n) (π / n) := by
  nth_rw 1 [← coe_toReal θ]
  have h' : 0 < (n : ℝ) := mod_cast Nat.pos_of_ne_zero h
  rw [← coe_nsmul, nsmul_eq_mul, toReal_coe_eq_self_iff, Set.mem_Ioc, div_lt_iff₀' h',
    le_div_iff₀' h']
/-
**Real.Angle.two_nsmul_toReal_eq_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_toReal_eq_two_mul {θ : Angle} : ((2 : Nat) • θ).toReal = 2 * θ.t
oReal ↔ θ.toReal in Set.Ioc (-π / 2) (π / 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.Angle.nsmul_toReal_eq_mul`：nsmul_toReal_eq_mul {n : Nat} (h : n != 
0) {θ : Angle} : (n • θ).toReal = n * θ.toReal ↔ θ.toReal in Set.Ioc (-π / n) (π
 / n)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
-/
theorem two_nsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) :=
  mod_cast nsmul_toReal_eq_mul two_ne_zero
/-
**Real.Angle.two_zsmul_toReal_eq_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_toReal_eq_two_mul {θ : Angle} : ((2 : Int) • θ).toReal = 2 * θ.t
oReal ↔ θ.toReal in Set.Ioc (-π / 2) (π / 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.two_nsmul_toReal_eq_two_mul`：two_nsmul_toReal_eq_two_mul {θ :
 Angle} : ((2 : Nat) • θ).toReal = 2 * θ.toReal ↔ θ.toReal in Set.Ioc (-π / 2) (
π / 2)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_zsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul]
/-
**Real.Angle.toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff** 是 Mathlib 中的一个定理，位于
命名空间 `Real.Angle`。
形式化陈述：toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : Real} {k : Int} : (θ : 
Angle).toReal = θ - 2 * k * π ↔ θ in Set.Ioc ((2 * k - 1 : Real) * π) ((2 * k + 
1) * π)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zsmul_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (n : ℤ), n • 0
 = 0
· 使用定理 `Real.Angle.coe_two_pi`：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
· 使用定理 `Real.Angle.coe_zsmul`：coe_zsmul (z : Int) (x : Real) : ↑(z • x : Real) =
 z • (↑x : Angle)
· 使用定理 `Real.Angle.coe_sub`：coe_sub (x y : Real) : ↑(x - y : Real) = (↑x - ↑y : 
Angle)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 61 条，此处仅展示前 30 条）
-/
theorem toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : ℝ} {k : ℤ} :
    (θ : Angle).toReal = θ - 2 * k * π ↔ θ ∈ Set.Ioc ((2 * k - 1 : ℝ) * π) ((2 * k + 1) * π) := by
  rw [← sub_zero (θ : Angle), ← zsmul_zero k, ← coe_two_pi, ← coe_zsmul, ← coe_sub, zsmul_eq_mul, ←
    mul_assoc, mul_comm (k : ℝ), toReal_coe_eq_self_iff, Set.mem_Ioc]
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩
/-
**Real.Angle.toReal_coe_eq_self_sub_two_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.A
ngle`。
形式化陈述：toReal_coe_eq_self_sub_two_pi_iff {θ : Real} : (θ : Angle).toReal = θ - 2 
* π ↔ θ in Set.Ioc π (3 * π)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_intCast`：isNat_intCast {R} [Ring R] (n : Int)
 (m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Real.Angle.toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff`：toReal_coe_eq_
self_sub_two_mul_int_mul_pi_iff {θ : Real} {k : Int} : (θ : Angle).toReal = θ - 
2 * k * π ↔ θ in Set.Ioc ((2 * k - 1 : Real) *…
-/
theorem toReal_coe_eq_self_sub_two_pi_iff {θ : ℝ} :
    (θ : Angle).toReal = θ - 2 * π ↔ θ ∈ Set.Ioc π (3 * π) := by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1 <;> norm_num
/-
**Real.Angle.toReal_coe_eq_self_add_two_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.A
ngle`。
形式化陈述：toReal_coe_eq_self_add_two_pi_iff {θ : Real} : (θ : Angle).toReal = θ + 2 
* π ↔ θ in Set.Ioc (-3 * π) (-π)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsInt.neg_to_eq`：∀ {α : Type u_1} [inst : Ring α] {
n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsInt a (Int.negOfNat n) → ↑n = a' → a =
 -a'
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isintCast`：isintCast {R} [Ring R] (n m : Int) : IsI
nt n m -> IsInt (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.Angle.toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff`：toReal_coe_eq_
self_sub_two_mul_int_mul_pi_iff {θ : Real} {k : Int} : (θ : Angle).toReal = θ - 
2 * k * π ↔ θ in Set.Ioc ((2 * k - 1 : Real) *…
-/
theorem toReal_coe_eq_self_add_two_pi_iff {θ : ℝ} :
    (θ : Angle).toReal = θ + 2 * π ↔ θ ∈ Set.Ioc (-3 * π) (-π) := by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1) using 2 <;> norm_num
/-
**Real.Angle.two_nsmul_toReal_eq_two_mul_sub_two_pi** 是 Mathlib 中的一个定理，位于命名空间 `R
eal.Angle`。
形式化陈述：two_nsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} : ((2 : Nat) • θ).toRea
l = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Real.Angle.coe_nsmul`：coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) =
 n • (↑x : Angle)
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Real.Angle.toReal_coe_eq_self_sub_two_pi_iff`：toReal_coe_eq_self_sub_two
_pi_iff {θ : Real} : (θ : Angle).toReal = θ - 2 * π ↔ θ in Set.Ioc π (3 * π)
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 77 条，此处仅展示前 30 条）
-/
theorem two_nsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul, two_nsmul, ← two_mul, toReal_coe_eq_self_sub_two_pi_iff, Set.mem_Ioc]
  exact
    ⟨fun h => by linarith, fun h =>
      ⟨(div_lt_iff₀' (zero_lt_two' ℝ)).1 h, by linarith [pi_pos, toReal_le_pi θ]⟩⟩
/-
**Real.Angle.two_zsmul_toReal_eq_two_mul_sub_two_pi** 是 Mathlib 中的一个定理，位于命名空间 `R
eal.Angle`。
形式化陈述：two_zsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} : ((2 : Int) • θ).toRea
l = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.two_nsmul_toReal_eq_two_mul_sub_two_pi`：two_nsmul_toReal_eq_t
wo_mul_sub_two_pi {θ : Angle} : ((2 : Nat) • θ).toReal = 2 * θ.toReal - 2 * π ↔ 
π / 2 < θ.toReal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_zsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul_sub_two_pi]
/-
**Real.Angle.two_nsmul_toReal_eq_two_mul_add_two_pi** 是 Mathlib 中的一个定理，位于命名空间 `R
eal.Angle`。
形式化陈述：two_nsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} : ((2 : Nat) • θ).toRea
l = 2 * θ.toReal + 2 * π ↔ θ.toReal <= -π / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Real.Angle.coe_nsmul`：coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) =
 n • (↑x : Angle)
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Real.Angle.toReal_coe_eq_self_add_two_pi_iff`：toReal_coe_eq_self_add_two
_pi_iff {θ : Real} : (θ : Angle).toReal = θ + 2 * π ↔ θ in Set.Ioc (-3 * π) (-π)
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 79 条，此处仅展示前 30 条）
-/
theorem two_nsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 := by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul, two_nsmul, ← two_mul, toReal_coe_eq_self_add_two_pi_iff, Set.mem_Ioc]
  refine
    ⟨fun h => by linarith, fun h =>
      ⟨by linarith [pi_pos, neg_pi_lt_toReal θ], (le_div_iff₀' (zero_lt_two' ℝ)).1 h⟩⟩
/-
**Real.Angle.two_zsmul_toReal_eq_two_mul_add_two_pi** 是 Mathlib 中的一个定理，位于命名空间 `R
eal.Angle`。
形式化陈述：two_zsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} : ((2 : Int) • θ).toRea
l = 2 * θ.toReal + 2 * π ↔ θ.toReal <= -π / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.two_nsmul_toReal_eq_two_mul_add_two_pi`：two_nsmul_toReal_eq_t
wo_mul_add_two_pi {θ : Angle} : ((2 : Nat) • θ).toReal = 2 * θ.toReal + 2 * π ↔ 
θ.toReal <= -π / 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_zsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul_add_two_pi]

@[simp, grind =]
/-
**Real.Angle.sin_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sin_toReal (θ : Angle) : Real.sin θ.toReal = sin θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
-/
theorem sin_toReal (θ : Angle) : Real.sin θ.toReal = sin θ := by
  conv_rhs => rw [← coe_toReal θ, sin_coe]

@[simp, grind =]
/-
**Real.Angle.cos_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：cos_toReal (θ : Angle) : Real.cos θ.toReal = cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
-/
theorem cos_toReal (θ : Angle) : Real.cos θ.toReal = cos θ := by
  conv_rhs => rw [← coe_toReal θ, cos_coe]
/-
**Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `
Real.Angle`。
形式化陈述：cos_nonneg_iff_abs_toReal_le_pi_div_two {θ : Angle} : 0 <= cos θ ↔ |θ.toRe
al| <= π / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.Angle.toReal_mem_Ioc`：toReal_mem_Ioc (θ : Angle) : θ.toReal in Set.
Ioc (-π) π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.cos_toReal`：cos_toReal (θ : Angle) : Real.cos θ.toReal = cos 
θ
· 使用定理 `Real.cos_abs`：cos_abs : cos |x| = cos x
-/
theorem cos_nonneg_iff_abs_toReal_le_pi_div_two {θ : Angle} : 0 ≤ cos θ ↔ |θ.toReal| ≤ π / 2 := by
  have : 0 < π / 2 := by positivity
  have := toReal_mem_Ioc θ
  rw [← cos_toReal, ← cos_abs]
  grind [cos_neg_of_pi_div_two_lt_of_lt, cos_nonneg_of_mem_Icc]
/-
**Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Rea
l.Angle`。
形式化陈述：cos_pos_iff_abs_toReal_lt_pi_div_two {θ : Angle} : 0 < cos θ ↔ |θ.toReal| 
< π / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two`：cos_nonneg_iff_abs_t
oReal_le_pi_div_two {θ : Angle} : 0 <= cos θ ↔ |θ.toReal| <= π / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₄`：contrapose_iff₄ {p q : Prop} 
: (p ↔ q) -> (¬ p ↔ ¬ q)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.Angle.abs_toReal_eq_pi_div_two_iff`：abs_toReal_eq_pi_div_two_iff {θ
 : Angle} : |θ.toReal| = π / 2 ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
· 使用定理 `Real.Angle.cos_eq_zero_iff`：cos_eq_zero_iff {θ : Angle} : cos θ = 0 ↔ θ 
= (π / 2 : Real) ∨ θ = (-π / 2 : Real)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cos_pos_iff_abs_toReal_lt_pi_div_two {θ : Angle} : 0 < cos θ ↔ |θ.toReal| < π / 2 := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, cos_nonneg_iff_abs_toReal_le_pi_div_two, ←
    and_congr_right]
  rintro -
  contrapose
  rw [@eq_comm ℝ 0, abs_toReal_eq_pi_div_two_iff, cos_eq_zero_iff]
/-
**Real.Angle.two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two** 是 Mathlib 中的一个引理，
位于命名空间 `Real.Angle`。
形式化陈述：two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toR
eal| < π / 2) (hψ : |ψ.toReal| < π / 2) : (2 : Nat) • θ = (2 : Nat) • ψ ↔ θ = ψ
参数：hθ : |θ.toReal| < π / 2；hψ : |ψ.toReal| < π / 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.cos_add_pi`：cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toReal| < π / 2)
    (hψ : |ψ.toReal| < π / 2) : (2 : ℕ) • θ = (2 : ℕ) • ψ ↔ θ = ψ := by
  suffices θ ≠ ψ + π by simp [this, two_nsmul_eq_iff]
  rintro rfl
  simp only [← cos_pos_iff_abs_toReal_lt_pi_div_two, cos_add_pi] at hθ hψ
  grind
/-
**Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two** 是 Mathlib 中的一个引理，
位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toR
eal| < π / 2) (hψ : |ψ.toReal| < π / 2) : (2 : Int) • θ = (2 : Int) • ψ ↔ θ = ψ
参数：hθ : |θ.toReal| < π / 2；hψ : |ψ.toReal| < π / 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Real.Angle.two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two`：two_nsmul_eq
_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toReal| < π / 2) (hψ 
: |ψ.toReal| < π / 2) : (2 : Nat) • θ = (2 : Nat…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toReal| < π / 2)
    (hψ : |ψ.toReal| < π / 2) : (2 : ℤ) • θ = (2 : ℤ) • ψ ↔ θ = ψ := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two hθ hψ]
/-
**Real.Angle.cos_neg_iff_pi_div_two_lt_abs_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Rea
l.Angle`。
形式化陈述：cos_neg_iff_pi_div_two_lt_abs_toReal {θ : Angle} : cos θ < 0 ↔ π / 2 < |θ.
toReal|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two`：cos_nonneg_iff_abs_t
oReal_le_pi_div_two {θ : Angle} : 0 <= cos θ ↔ |θ.toReal| <= π / 2
-/
theorem cos_neg_iff_pi_div_two_lt_abs_toReal {θ : Angle} : cos θ < 0 ↔ π / 2 < |θ.toReal| := by
  contrapose!; exact cos_nonneg_iff_abs_toReal_le_pi_div_two
/-
**Real.Angle.abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi** 是 Mathlib 中的一
个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle} (h : (2 
: Nat) • θ + (2 : Nat) • ψ = π) : |cos θ| = |sin ψ|
参数：h : (2 : Nat) • θ + (2 : Nat) • ψ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_nsmul_eq_iff`：two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) 
• ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α) (
n : ℕ), n • (a - b) = n • a - n • b
· 使用定理 `Real.Angle.two_nsmul_coe_div_two`：two_nsmul_coe_div_two (θ : Real) : (2 
: Nat) • (↑(θ / 2) : Angle) = θ
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.cos_pi_div_two_sub`：cos_pi_div_two_sub (θ : Angle) : cos (↑(π
 / 2) - θ) = sin θ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.Angle.cos_add_pi`：cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
theorem abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : |cos θ| = |sin ψ| := by
  rw [← eq_sub_iff_add_eq, ← two_nsmul_coe_div_two, ← nsmul_sub, two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl) <;> simp [cos_pi_div_two_sub]
/-
**Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi** 是 Mathlib 中的一
个定理，位于命名空间 `Real.Angle`。
形式化陈述：abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle} (h : (2 
: Int) • θ + (2 : Int) • ψ = π) : |cos θ| = |sin ψ|
参数：h : (2 : Int) • θ + (2 : Int) • ψ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi`：abs_cos_
eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle} (h : (2 : Nat) • θ + (
2 : Nat) • ψ = π) : |cos θ| = |sin ψ|
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
-/
theorem abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : |cos θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h

/-- The tangent of a `Real.Angle`. -/
/-
**Real.Angle.tan** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：tan (θ : Angle) : Real
参数：θ : Angle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tangent of a `Real.Angle`.
-/
def tan (θ : Angle) : ℝ :=
  sin θ / cos θ
/-
**Real.Angle.tan_eq_sin_div_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_eq_sin_div_cos (θ : Angle) : tan θ = sin θ / cos θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tan_eq_sin_div_cos (θ : Angle) : tan θ = sin θ / cos θ :=
  rfl

@[simp]
/-
**Real.Angle.tan_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.tan.eq_1`：∀ (θ : Real.Angle), θ.tan = θ.sin / θ.cos
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `Real.tan_eq_sin_div_cos`：∀ (x : ℝ), Real.tan x = Real.sin x / Real.cos x
-/
theorem tan_coe (x : ℝ) : tan (x : Angle) = Real.tan x := by
  rw [tan, sin_coe, cos_coe, Real.tan_eq_sin_div_cos]

@[simp]
/-
**Real.Angle.tan_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_zero : tan (0 : Angle) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_zero`：coe_zero : ↑(0 : Real) = (0 : Angle)
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `Real.tan_zero`：tan_zero : tan 0 = 0
-/
theorem tan_zero : tan (0 : Angle) = 0 := by rw [← coe_zero, tan_coe, Real.tan_zero]
/-
**Real.Angle.tan_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_coe_pi : tan (π : Angle) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `Real.tan_pi`：tan_pi : tan π = 0
-/
theorem tan_coe_pi : tan (π : Angle) = 0 := by rw [tan_coe, Real.tan_pi]
/-
**Real.Angle.tan_periodic** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_periodic : Function.Periodic tan (π : Angle)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `Real.tan_periodic`：tan_periodic : Function.Periodic tan π
-/
theorem tan_periodic : Function.Periodic tan (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  rw [← coe_add, tan_coe, tan_coe]
  exact Real.tan_periodic _

@[simp]
/-
**Real.Angle.tan_add_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_add_pi (θ : Angle) : tan (θ + π) = tan θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.tan_periodic`：tan_periodic : Function.Periodic tan (π : Angle
)
-/
theorem tan_add_pi (θ : Angle) : tan (θ + π) = tan θ :=
  tan_periodic θ

@[simp]
/-
**Real.Angle.tan_sub_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_sub_pi (θ : Angle) : tan (θ - π) = tan θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (x : α), f (x - c) = f x
· 使用定理 `Real.Angle.tan_periodic`：tan_periodic : Function.Periodic tan (π : Angle
)
-/
theorem tan_sub_pi (θ : Angle) : tan (θ - π) = tan θ :=
  tan_periodic.sub_eq θ

@[simp]
/-
**Real.Angle.tan_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_toReal (θ : Angle) : Real.tan θ.toReal = tan θ
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
-/
theorem tan_toReal (θ : Angle) : Real.tan θ.toReal = tan θ := by
  conv_rhs => rw [← coe_toReal θ, tan_coe]
/-
**Real.Angle.tan_eq_of_two_nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ) :
 tan θ = tan ψ
参数：h : (2 : Nat) • θ = (2 : Nat) • ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_nsmul_eq_iff`：two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) 
• ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `Real.Angle.tan_add_pi`：tan_add_pi (θ : Angle) : tan (θ + π) = tan θ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem tan_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) : tan θ = tan ψ := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · exact tan_add_pi _
/-
**Real.Angle.tan_eq_of_two_zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：tan_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • ψ) :
 tan θ = tan ψ
参数：h : (2 : Int) • θ = (2 : Int) • ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.tan_eq_of_two_nsmul_eq`：tan_eq_of_two_nsmul_eq {θ ψ : Angle} 
(h : (2 : Nat) • θ = (2 : Nat) • ψ) : tan θ = tan ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
-/
theorem tan_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) : tan θ = tan ψ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_of_two_nsmul_eq h
/-
**Real.Angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi** 是 Mathlib 中的一个定理，位于命名
空间 `Real.Angle`。
形式化陈述：tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle} (h : (2 : Nat) •
 θ + (2 : Nat) • ψ = π) : tan ψ = (tan θ)⁻¹
参数：h : (2 : Nat) • θ + (2 : Nat) • ψ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.coe_nsmul`：coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) =
 n • (↑x : Angle)
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `Real.tan_pi_div_two_sub`：tan_pi_div_two_sub (x : Real) : tan (π / 2 - x)
 = (tan x)⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
（共 32 条，此处仅展示前 30 条）
-/
theorem tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  rw [← smul_add, ← coe_add, ← coe_nsmul, two_nsmul, ← two_mul, angle_eq_iff_two_pi_dvd_sub] at h
  rcases h with ⟨k, h⟩
  rw [sub_eq_iff_eq_add, ← mul_inv_cancel_left₀ two_ne_zero π, mul_assoc, ← mul_add,
    mul_right_inj' (two_ne_zero' ℝ), ← eq_sub_iff_add_eq', mul_inv_cancel_left₀ two_ne_zero π,
    inv_mul_eq_div, mul_comm] at h
  rw [tan_coe, tan_coe, ← tan_pi_div_two_sub, h, add_sub_assoc, add_comm]
  exact Real.tan_periodic.int_mul _ _
/-
**Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi** 是 Mathlib 中的一个定理，位于命名
空间 `Real.Angle`。
形式化陈述：tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle} (h : (2 : Int) •
 θ + (2 : Int) • ψ = π) : tan ψ = (tan θ)⁻¹
参数：h : (2 : Int) • θ + (2 : Int) • ψ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi`：tan_eq_inv_of_tw
o_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle} (h : (2 : Nat) • θ + (2 : Nat) • ψ = π
) : tan ψ = (tan θ)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
-/
theorem tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h

/-- The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the
sign of the sine of the angle. -/
/-
**Real.Angle.sign** 是 Mathlib 中的一个定义，位于命名空间 `Real.Angle`。
形式化陈述：sign (θ : Angle) : SignType
参数：θ : Angle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle i
s strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It i
s defined as the
sign of the sine of the angle.
-/
def sign (θ : Angle) : SignType :=
  SignType.sign (sin θ)

@[simp, grind =]
/-
**Real.Angle.sign_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_zero : (0 : Angle).sign = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `Real.Angle.sin_zero`：sin_zero : sin (0 : Angle) = 0
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
-/
theorem sign_zero : (0 : Angle).sign = 0 := by
  rw [sign, sin_zero, _root_.sign_zero]

@[simp, grind =]
/-
**Real.Angle.sign_coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_coe_pi : (π : Angle).sign = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `Real.Angle.sin_coe_pi`：sin_coe_pi : sin (π : Angle) = 0
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
-/
theorem sign_coe_pi : (π : Angle).sign = 0 := by rw [sign, sin_coe_pi, _root_.sign_zero]

@[simp, grind =]
/-
**Real.Angle.sign_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sin_neg`：sin_neg (θ : Angle) : sin (-θ) = -sin θ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Left.sign_neg`：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) =
 -sign a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_neg (θ : Angle) : (-θ).sign = -θ.sign := by
  simp_rw [sign, sin_neg, Left.sign_neg]
/-
**Real.Angle.sign_antiperiodic** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_antiperiodic : Function.Antiperiodic sign (π : Angle)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `Real.Angle.sin_add_pi`：sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ
· 使用定理 `Left.sign_neg`：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) =
 -sign a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem sign_antiperiodic : Function.Antiperiodic sign (π : Angle) := fun θ => by
  rw [sign, sign, sin_add_pi, Left.sign_neg]

@[simp, grind =]
/-
**Real.Angle.sign_add_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.sign_antiperiodic`：sign_antiperiodic : Function.Antiperiodic 
sign (π : Angle)
-/
theorem sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign :=
  sign_antiperiodic θ

@[simp, grind =]
/-
**Real.Angle.sign_pi_add** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_pi_add (θ : Angle) : ((π : Angle) + θ).sign = -θ.sign
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Real.Angle.sign_add_pi`：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign
-/
theorem sign_pi_add (θ : Angle) : ((π : Angle) + θ).sign = -θ.sign := by rw [add_comm, sign_add_pi]

@[simp, grind =]
/-
**Real.Angle.sign_sub_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_sub_pi (θ : Angle) : (θ - π).sign = -θ.sign
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β
} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodi
c f c → ∀ (x : α),…
· 使用定理 `Real.Angle.sign_antiperiodic`：sign_antiperiodic : Function.Antiperiodic 
sign (π : Angle)
-/
theorem sign_sub_pi (θ : Angle) : (θ - π).sign = -θ.sign :=
  sign_antiperiodic.sub_eq θ

@[simp, grind =]
/-
**Real.Angle.sign_pi_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_pi_sub (θ : Angle) : ((π : Angle) - θ).sign = θ.sign
参数：θ : Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Antiperiodic.sub_eq'`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {c x : α} [inst : SubtractionCommMonoid α] [inst_1 : Neg β],   Function.Antip
eriodic f c → f (c …
· 使用定理 `Real.Angle.sign_antiperiodic`：sign_antiperiodic : Function.Antiperiodic 
sign (π : Angle)
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_pi_sub (θ : Angle) : ((π : Angle) - θ).sign = θ.sign := by
  simp [sign_antiperiodic.sub_eq']

@[grind =]
/-
**Real.Angle.sign_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `sign_eq_zero_iff`：sign_eq_zero_iff : sign a = 0 ↔ a = 0
· 使用定理 `Real.Angle.sin_eq_zero_iff`：sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ 
= 0 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π := by
  rw [sign, _root_.sign_eq_zero_iff, sin_eq_zero_iff]

@[grind =]
/-
**Real.Angle.sign_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_ne_zero_iff {θ : Angle} : θ.sign != 0 ↔ θ != 0 ∧ θ != π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Real.Angle.sign_eq_zero_iff`：sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔
 θ = 0 ∨ θ = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sign_ne_zero_iff {θ : Angle} : θ.sign ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← sign_eq_zero_iff]
/-
**Real.Angle.toReal_neg_iff_sign_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_neg_iff_sign_neg {θ : Angle} : θ.toReal < 0 ↔ θ.sign = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.sin_toReal`：sin_toReal (θ : Angle) : Real.sin θ.toReal = sin 
θ
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
-/
theorem toReal_neg_iff_sign_neg {θ : Angle} : θ.toReal < 0 ↔ θ.sign = -1 := by
  rw [sign, ← sin_toReal, sign_eq_neg_one_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]
/-
**Real.Angle.toReal_nonneg_iff_sign_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle
`。
形式化陈述：toReal_nonneg_iff_sign_nonneg {θ : Angle} : 0 <= θ.toReal ↔ 0 <= θ.sign
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem toReal_nonneg_iff_sign_nonneg {θ : Angle} : 0 ≤ θ.toReal ↔ 0 ≤ θ.sign := by
  simp only [sign, ← sin_toReal, sign_nonneg_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]

@[simp]
/-
**Real.Angle.sign_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_toReal {θ : Angle} (h : θ != π) : SignType.sign θ.toReal = θ.sign
参数：h : θ != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.toReal_neg_iff_sign_neg`：toReal_neg_iff_sign_neg {θ : Angle} 
: θ.toReal < 0 ↔ θ.sign = -1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.sin_toReal`：sin_toReal (θ : Angle) : Real.sin θ.toReal = sin 
θ
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `Real.sin_pos_of_pos_of_lt_pi`：sin_pos_of_pos_of_lt_pi {x : Real} (h0x : 
0 < x) (hxp : x < π) : 0 < sin x
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Real.Angle.toReal_le_pi`：toReal_le_pi (θ : Angle) : θ.toReal <= π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.Angle.toReal_eq_pi_iff`：toReal_eq_pi_iff {θ : Angle} : θ.toReal = π
 ↔ θ = π
-/
theorem sign_toReal {θ : Angle} (h : θ ≠ π) : SignType.sign θ.toReal = θ.sign := by
  rcases lt_trichotomy θ.toReal 0 with (ht | ht | ht)
  · simp [ht, toReal_neg_iff_sign_neg.1 ht]
  · simp [sign, ht, ← sin_toReal]
  · rw [sign, ← sin_toReal, sign_pos ht,
      sign_pos
        (sin_pos_of_pos_of_lt_pi ht ((toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)))]
/-
**Real.Angle.toReal_mem_Ioo_iff_sign_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angle`。
形式化陈述：toReal_mem_Ioo_iff_sign_pos {θ : Angle} : θ.toReal in Set.Ioo 0 π ↔ θ.sign
 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.sign_coe_pi`：sign_coe_pi : (π : Angle).sign = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.sign_toReal`：sign_toReal {θ : Angle} (h : θ != π) : SignType.
sign θ.toReal = θ.sign
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Real.Angle.toReal_le_pi`：toReal_le_pi (θ : Angle) : θ.toReal <= π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.Angle.toReal_eq_pi_iff`：toReal_eq_pi_iff {θ : Angle} : θ.toReal = π
 ↔ θ = π
-/
lemma toReal_mem_Ioo_iff_sign_pos {θ : Angle} :
    θ.toReal ∈ Set.Ioo 0 π ↔ θ.sign = 1 := by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp only [Set.mem_Ioo, ← sign_toReal h, sign_eq_one_iff, and_iff_left_iff_imp]
    exact fun _ ↦ (toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)
/-
**Real.Angle.coe_abs_toReal_of_sign_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle
`。
形式化陈述：coe_abs_toReal_of_sign_nonneg {θ : Angle} (h : 0 <= θ.sign) : ↑|θ.toReal| 
= θ
参数：h : 0 <= θ.sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `Real.Angle.toReal_nonneg_iff_sign_nonneg`：toReal_nonneg_iff_sign_nonneg 
{θ : Angle} : 0 <= θ.toReal ↔ 0 <= θ.sign
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
-/
theorem coe_abs_toReal_of_sign_nonneg {θ : Angle} (h : 0 ≤ θ.sign) : ↑|θ.toReal| = θ := by
  rw [abs_eq_self.2 (toReal_nonneg_iff_sign_nonneg.2 h), coe_toReal]
/-
**Real.Angle.neg_coe_abs_toReal_of_sign_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real.A
ngle`。
形式化陈述：neg_coe_abs_toReal_of_sign_nonpos {θ : Angle} (h : θ.sign <= 0) : -↑|θ.toR
eal| = θ
参数：h : θ.sign <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SignType.nonpos_iff`：nonpos_iff {a : SignType} : a <= 0 ↔ a = -1 ∨ a = 0
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.Angle.toReal_neg_iff_sign_neg`：toReal_neg_iff_sign_neg {θ : Angle} 
: θ.toReal < 0 ↔ θ.sign = -1
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用定理 `Real.Angle.sign_eq_zero_iff`：sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔
 θ = 0 ∨ θ = π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
-/
theorem neg_coe_abs_toReal_of_sign_nonpos {θ : Angle} (h : θ.sign ≤ 0) : -↑|θ.toReal| = θ := by
  rw [SignType.nonpos_iff] at h
  rcases h with (h | h)
  · rw [abs_of_neg (toReal_neg_iff_sign_neg.2 h), coe_neg, neg_neg, coe_toReal]
  · rw [sign_eq_zero_iff] at h
    rcases h with (rfl | rfl) <;> simp [abs_of_pos Real.pi_pos]
/-
**Real.Angle.eq_iff_sign_eq_and_abs_toReal_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.An
gle`。
形式化陈述：eq_iff_sign_eq_and_abs_toReal_eq {θ ψ : Angle} : θ = ψ ↔ θ.sign = ψ.sign ∧
 |θ.toReal| = |ψ.toReal|
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_iff_sign_eq_and_abs_toReal_eq {θ ψ : Angle} :
    θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.toReal| = |ψ.toReal| := by
  grind [toReal_neg_iff_sign_neg]
/-
**Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Ang
le`。
形式化陈述：eq_iff_abs_toReal_eq_of_sign_eq {θ ψ : Angle} (h : θ.sign = ψ.sign) : θ = 
ψ ↔ |θ.toReal| = |ψ.toReal|
参数：h : θ.sign = ψ.sign。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Real.Angle.eq_iff_sign_eq_and_abs_toReal_eq`：eq_iff_sign_eq_and_abs_toRe
al_eq {θ ψ : Angle} : θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.toReal| = |ψ.toReal|
-/
theorem eq_iff_abs_toReal_eq_of_sign_eq {θ ψ : Angle} (h : θ.sign = ψ.sign) :
    θ = ψ ↔ |θ.toReal| = |ψ.toReal| := by simpa [h] using @eq_iff_sign_eq_and_abs_toReal_eq θ ψ

@[simp]
/-
**Real.Angle.sign_coe_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_coe_pi_div_two : (↑(π / 2) : Angle).sign = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `sign_one`：sign_one : sign (1 : α) = 1
-/
theorem sign_coe_pi_div_two : (↑(π / 2) : Angle).sign = 1 := by
  rw [sign, sin_coe, sin_pi_div_two, sign_one]

@[simp]
/-
**Real.Angle.sign_coe_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_coe_neg_pi_div_two : (↑(-π / 2) : Angle).sign = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `Left.sign_neg`：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) =
 -sign a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sign_one`：sign_one : sign (1 : α) = 1
-/
theorem sign_coe_neg_pi_div_two : (↑(-π / 2) : Angle).sign = -1 := by
  rw [sign, sin_coe, neg_div, Real.sin_neg, sin_pi_div_two, Left.sign_neg, sign_one]
/-
**Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real.
Angle`。
形式化陈述：sign_coe_nonneg_of_nonneg_of_le_pi {θ : Real} (h0 : 0 <= θ) (hpi : θ <= π)
 : 0 <= (θ : Angle).sign
参数：h0 : 0 <= θ；hpi : θ <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `sign_nonneg_iff`：sign_nonneg_iff : 0 <= sign a ↔ 0 <= a
· 使用定理 `Real.sin_nonneg_of_nonneg_of_le_pi`：sin_nonneg_of_nonneg_of_le_pi {x : R
eal} (h0x : 0 <= x) (hxp : x <= π) : 0 <= sin x
-/
theorem sign_coe_nonneg_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    0 ≤ (θ : Angle).sign := by
  rw [sign, sign_nonneg_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
/-
**Real.Angle.sign_neg_coe_nonpos_of_nonneg_of_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `R
eal.Angle`。
形式化陈述：sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : Real} (h0 : 0 <= θ) (hpi : θ <
= π) : (-θ : Angle).sign <= 0
参数：h0 : 0 <= θ；hpi : θ <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign.eq_1`：∀ (θ : Real.Angle), θ.sign = SignType.sign θ.sin
· 使用定理 `sign_nonpos_iff`：sign_nonpos_iff : sign a <= 0 ↔ a <= 0
· 使用定理 `Real.Angle.sin_neg`：sin_neg (θ : Angle) : sin (-θ) = -sin θ
· 使用定理 `Left.neg_nonpos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sin_nonneg_of_nonneg_of_le_pi`：sin_nonneg_of_nonneg_of_le_pi {x : R
eal} (h0x : 0 <= x) (hxp : x <= π) : 0 <= sin x
-/
theorem sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    (-θ : Angle).sign ≤ 0 := by
  rw [sign, sign_nonpos_iff, sin_neg, Left.neg_nonpos_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
/-
**Real.Angle.sign_two_nsmul_eq_sign_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_two_nsmul_eq_sign_iff {θ : Angle} : ((2 : Nat) • θ).sign = θ.sign ↔ θ
 = π ∨ |θ.toReal| < π / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.Angle.sin_two_nsmul`：sin_two_nsmul (θ : Angle) : sin (2 • θ) = 2 • 
(sin θ * cos θ)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
theorem sign_two_nsmul_eq_sign_iff {θ : Angle} :
    ((2 : ℕ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  simp only [sign, sin_two_nsmul, nsmul_eq_mul, Nat.cast_ofNat, sign_mul, Nat.ofNat_pos, sign_pos,
    one_mul, mul_right_eq_self₀, _root_.sign_eq_zero_iff, sign_eq_one_iff, sin_eq_zero_iff,
    cos_pos_iff_abs_toReal_lt_pi_div_two]
  have : 0 < π / 2 := by positivity
  grind
/-
**Real.Angle.sign_two_zsmul_eq_sign_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_two_zsmul_eq_sign_iff {θ : Angle} : ((2 : Int) • θ).sign = θ.sign ↔ θ
 = π ∨ |θ.toReal| < π / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Real.Angle.sign_two_nsmul_eq_sign_iff`：sign_two_nsmul_eq_sign_iff {θ : A
ngle} : ((2 : Nat) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sign_two_zsmul_eq_sign_iff {θ : Angle} :
    ((2 : ℤ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  rw [two_zsmul, ← two_nsmul, sign_two_nsmul_eq_sign_iff]
/-
**Real.Angle.sign_two_nsmul_eq_neg_sign_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angl
e`。
形式化陈述：sign_two_nsmul_eq_neg_sign_iff {θ : Angle} : ((2 : Nat) • θ).sign = -θ.sig
n ↔ θ = 0 ∨ π / 2 < |θ.toReal|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Real.Angle.two_nsmul_coe_pi`：two_nsmul_coe_pi : (2 : Nat) • (π : Angle) 
= 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.Angle.sign_add_pi`：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Real.Angle.cos_add_pi`：cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.Angle.sign_two_nsmul_eq_sign_iff`：sign_two_nsmul_eq_sign_iff {θ : A
ngle} : ((2 : Nat) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2
-/
lemma sign_two_nsmul_eq_neg_sign_iff {θ : Angle} :
    ((2 : ℕ) • θ).sign = -θ.sign ↔ θ = 0 ∨ π / 2 < |θ.toReal| := by
  simpa [← cos_pos_iff_abs_toReal_lt_pi_div_two, ← cos_neg_iff_pi_div_two_lt_abs_toReal]
    using sign_two_nsmul_eq_sign_iff (θ := θ + π)
/-
**Real.Angle.sign_two_zsmul_eq_neg_sign_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angl
e`。
形式化陈述：sign_two_zsmul_eq_neg_sign_iff {θ : Angle} : ((2 : Int) • θ).sign = -θ.sig
n ↔ θ = 0 ∨ π / 2 < |θ.toReal|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用引理 `Real.Angle.sign_two_nsmul_eq_neg_sign_iff`：sign_two_nsmul_eq_neg_sign_if
f {θ : Angle} : ((2 : Nat) • θ).sign = -θ.sign ↔ θ = 0 ∨ π / 2 < |θ.toReal|
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sign_two_zsmul_eq_neg_sign_iff {θ : Angle} :
    ((2 : ℤ) • θ).sign = -θ.sign ↔ θ = 0 ∨ π / 2 < |θ.toReal| := by
  rw [two_zsmul, ← two_nsmul, sign_two_nsmul_eq_neg_sign_iff]
/-
**Real.Angle.eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 
`Real.Angle`。
形式化陈述：eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg (a b : Real.Angle) (h : (2 : Int)
 • a = (2 : Int) • b) (h_sign : a.sign = -b.sign) (h_ne : b.sign != 0) : a = b +
 π
参数：a b : Real.Angle；h : (2 : Int) • a = (2 : Int) • b；h_sign : a.sign = -b.sign；
h_ne : b.sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.two_zsmul_eq_iff`：two_zsmul_eq_iff {ψ θ : Angle} : (2 : Int) 
• ψ = (2 : Int) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg (a b : Real.Angle) (h : (2 : ℤ) • a = (2 : ℤ) • b)
    (h_sign : a.sign = -b.sign) (h_ne : b.sign ≠ 0) : a = b + π := by
  have h1 := Real.Angle.two_zsmul_eq_iff.mp h
  refine h1.resolve_left ?_
  rintro rfl
  simp only [SignType.self_eq_neg_iff] at h_sign
  rw [h_sign] at h_ne
  contradiction
/-
**Real.Angle.sub_ne_pi_of_sign_eq_of_sign_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rea
l.Angle`。
形式化陈述：sub_ne_pi_of_sign_eq_of_sign_ne_zero (a b : Real.Angle) (h_sign : a.sign =
 b.sign) (h_ne : b.sign != 0) : a - b != π
参数：a b : Real.Angle；h_sign : a.sign = b.sign；h_ne : b.sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.Angle.sign_add_pi`：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign
-/
theorem sub_ne_pi_of_sign_eq_of_sign_ne_zero (a b : Real.Angle) (h_sign : a.sign = b.sign)
    (h_ne : b.sign ≠ 0) : a - b ≠ π := by
  intro h
  have h' : a = b + π := by
    simp [← h]
  have h_sign' := h_sign
  rw [h', Real.Angle.sign_add_pi] at h_sign'
  simp only [SignType.neg_eq_self_iff] at h_sign'
  contradiction
/-
**Real.Angle.two_zsmul_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：two_zsmul_eq_iff_eq {a b : Real.Angle} (ha : a.sign != 0) (h : a.sign = b.
sign) : (2 : Int) • a = (2 : Int) • b ↔ a = b
参数：ha : a.sign != 0；h : a.sign = b.sign。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_zsmul_eq_iff`：two_zsmul_eq_iff {ψ θ : Angle} : (2 : Int) 
• ψ = (2 : Int) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.sign_add_pi`：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem two_zsmul_eq_iff_eq {a b : Real.Angle} (ha : a.sign ≠ 0) (h : a.sign = b.sign) :
    (2 : ℤ) • a = (2 : ℤ) • b ↔ a = b := by
  rw [Real.Angle.two_zsmul_eq_iff]
  constructor
  · intro h
    rcases h with h1 | h2
    · exact h1
    · have : a.sign = (b + π).sign := by aesop
      rw [Real.Angle.sign_add_pi] at this
      have := congr_arg (· = b.sign) this
      aesop
  · intro h
    aesop
/-
**Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq
** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angle`。
形式化陈述：abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq {θ ψ :
 Angle} (h : (2 : Nat) • (θ + ψ) = 0) (hs : θ.sign = ψ.sign) (h0 : θ.sign != 0) 
: |θ.toReal| + |ψ.toReal| = π
参数：h : (2 : Nat) • (θ + ψ) = 0；hs : θ.sign = ψ.sign；h0 : θ.sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.two_nsmul_eq_zero_iff`：two_nsmul_eq_zero_iff {θ : Angle} : (2
 : Nat) • θ = 0 ↔ θ = 0 ∨ θ = π
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `abs_eq`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   0 ≤ b → (|a| = b ↔ a = b ∨ a = -b)
· 使用定理 `Real.pi_nonneg`：pi_nonneg : 0 <= π
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.Angle.angle_eq_iff_two_pi_dvd_sub`：angle_eq_iff_two_pi_dvd_sub {ψ θ
 : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
· 使用引理 `IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo`：IsStrictOrderedRing.int_
mem_Icc_of_mul_mem_Ioo {r : R} (hr : 0 < r) {k m n : Int} (h : r * k in Set.Ioo 
(r * (m - 1 : Int)) (r * (n + 1 : In…
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Nat.castEmbedding_apply`：∀ {R : Type u_2} [inst : AddMonoidWithOne R] [i
nst_1 : CharZero R] (a : ℕ), Nat.castEmbedding a = ↑a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `addLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeft
CancelAdd G] (g h : G), (addLeftEmbedding g) h = g + h
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 37 条，此处仅展示前 30 条）
-/
lemma abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq {θ ψ : Angle}
    (h : (2 : ℕ) • (θ + ψ) = 0) (hs : θ.sign = ψ.sign) (h0 : θ.sign ≠ 0) :
    |θ.toReal| + |ψ.toReal| = π := by
  rcases two_nsmul_eq_zero_iff.mp h with h | h
  · simp_all [add_eq_zero_iff_eq_neg.mp h]
  rw [← coe_toReal θ, ← coe_toReal ψ, ← coe_add] at h
  suffices |θ.toReal + ψ.toReal| = π by grind [toReal_neg_iff_sign_neg, abs_add_eq_add_abs_iff]
  rw [abs_eq pi_nonneg]
  rcases angle_eq_iff_two_pi_dvd_sub.mp h with ⟨k, hk⟩
  rw [sub_eq_iff_eq_add] at hk
  have : k ∈ Finset.Icc (-1) 0 :=
    IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo two_pi_pos <| by grind [toReal_mem_Ioc]
  fin_cases this
  all_goals simp at hk; grind
/-
**Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq
** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angle`。
形式化陈述：abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq {θ ψ :
 Angle} (h : (2 : Int) • (θ + ψ) = 0) (hs : θ.sign = ψ.sign) (h0 : θ.sign != 0) 
: |θ.toReal| + |ψ.toReal| = π
参数：h : (2 : Int) • (θ + ψ) = 0；hs : θ.sign = ψ.sign；h0 : θ.sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_s
ign_eq`：abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq {θ ψ
 : Angle} (h : (2 : Nat) • (θ + ψ) = 0) (hs : θ.sign = ψ.sign) (h0 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
-/
lemma abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq {θ ψ : Angle}
    (h : (2 : ℤ) • (θ + ψ) = 0) (hs : θ.sign = ψ.sign) (h0 : θ.sign ≠ 0) :
    |θ.toReal| + |ψ.toReal| = π := by
  rw [two_zsmul, ← two_nsmul] at h
  exact abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq h hs h0
/-
**Real.Angle.toReal_add_of_sign_pos_sign_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real.Ang
le`。
形式化陈述：toReal_add_of_sign_pos_sign_neg {θ ψ : Angle} (hθ : θ.sign = 1) (hψ : ψ.si
gn = -1) : (θ + ψ).toReal = θ.toReal + ψ.toReal
参数：hθ : θ.sign = 1；hψ : ψ.sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff`：toReal_coe_eq_self_iff {θ : Real} : (
θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.Angle.coe_toReal`：coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ
-/
lemma toReal_add_of_sign_pos_sign_neg {θ ψ : Angle}
    (hθ : θ.sign = 1) (hψ : ψ.sign = -1) : (θ + ψ).toReal = θ.toReal + ψ.toReal := by
  suffices ((θ.toReal + ψ.toReal : ℝ) : Angle).toReal = θ.toReal + ψ.toReal by simpa using this
  rw [toReal_coe_eq_self_iff]
  grind [toReal_mem_Ioc, toReal_neg_iff_sign_neg, toReal_mem_Ioo_iff_sign_pos]
/-
**Real.Angle.toReal_add_of_sign_eq_neg_sign** 是 Mathlib 中的一个引理，位于命名空间 `Real.Angl
e`。
形式化陈述：toReal_add_of_sign_eq_neg_sign {θ ψ : Angle} (hψ : θ != π ∨ ψ != π) (hs : 
θ.sign = -ψ.sign) : (θ + ψ).toReal = θ.toReal + ψ.toReal
参数：hψ : θ != π ∨ ψ != π；hs : θ.sign = -ψ.sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SignType.trichotomy`：trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1
-/
lemma toReal_add_of_sign_eq_neg_sign {θ ψ : Angle} (hψ : θ ≠ π ∨ ψ ≠ π)
    (hs : θ.sign = -ψ.sign) : (θ + ψ).toReal = θ.toReal + ψ.toReal := by
  obtain (h | h | h) := ψ.sign.trichotomy
  all_goals grind [neg_neg, add_comm, toReal_add_of_sign_pos_sign_neg]
/-
**Real.Angle.toReal_add_eq_toReal_add_toReal** 是 Mathlib 中的一个引理，位于命名空间 `Real.Ang
le`。
形式化陈述：toReal_add_eq_toReal_add_toReal {θ ψ : Angle} (hθ : θ != π) (hψ : ψ != π) 
(hs : θ.sign != ψ.sign ∨ θ.sign = (θ + ψ).sign) : (θ + ψ).toReal = θ.toReal + ψ.
toReal
参数：hθ : θ != π；hψ : ψ != π；hs : θ.sign != ψ.sign ∨ θ.sign = (θ + ψ).sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SignType.trichotomy`：trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1
· 使用引理 `Real.Angle.toReal_add_of_sign_eq_neg_sign`：toReal_add_of_sign_eq_neg_sig
n {θ ψ : Angle} (hψ : θ != π ∨ ψ != π) (hs : θ.sign = -ψ.sign) : (θ + ψ).toReal 
= θ.toReal + ψ.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Real.Angle.toReal_neg_eq_neg_toReal_iff`：toReal_neg_eq_neg_toReal_iff {θ
 : Angle} : (-θ).toReal = -(θ.toReal) ↔ θ != π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma toReal_add_eq_toReal_add_toReal {θ ψ : Angle} (hθ : θ ≠ π) (hψ : ψ ≠ π)
    (hs : θ.sign ≠ ψ.sign ∨ θ.sign = (θ + ψ).sign) : (θ + ψ).toReal = θ.toReal + ψ.toReal := by
  obtain (hs | hs) := hs
  · obtain (h | h | h) := ψ.sign.trichotomy <;> obtain (h | h | h) := θ.sign.trichotomy
    all_goals grind [add_comm, toReal_add_of_sign_pos_sign_neg, sign_eq_zero_iff]
  · rw [← neg_neg θ.sign, ← sign_neg] at hs
    have := toReal_add_of_sign_eq_neg_sign (.inr <| by simpa [neg_eq_iff_eq_neg]) hs.symm
    simpa [toReal_neg_eq_neg_toReal_iff.mpr, hθ, ← sub_eq_add_neg, eq_sub_iff_add_eq', eq_comm]
/-
**Real.Angle.abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux** 是 Math
lib 中的一个引理，位于命名空间 `Real.Angle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux {θ ψ : Angle}
    (hθs : θ.sign = 1) (hψs : ψ.sign = 1)
    (hsa : (θ + ψ).sign ≠ 1) : |(θ + ψ).toReal| = 2 * π - (|θ.toReal| + |ψ.toReal|) := by
  rw [← toReal_mem_Ioo_iff_sign_pos] at hθs hψs
  have : ((θ + ψ).toReal : Angle) = ↑(θ.toReal + ψ.toReal) := by simp
  obtain ⟨k, hk⟩ := angle_eq_iff_two_pi_dvd_sub.mp this
  obtain (h | h) : (θ + ψ).toReal ≤ 0 ∨ θ + ψ = π := by
    have := (θ + ψ).sign.trichotomy
    grind [sign_eq_zero_iff, toReal_eq_zero_iff, toReal_neg_iff_sign_neg]
  · obtain rfl : k = -1 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos <| by
      grind [toReal_mem_Ioc]
    grind [abs_of_nonpos]
  · simp_all only [sign_coe_pi, ne_eq, zero_ne_one, not_false_eq_true, toReal_pi, coe_add,
      coe_toReal, pi_pos, abs_of_pos]
    obtain rfl : k = 0 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos (by grind)
    grind
/-
**Real.Angle.abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal** 是 Mathlib 
中的一个引理，位于命名空间 `Real.Angle`。
形式化陈述：abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal {θ ψ : Angle} (hs :
 θ.sign = ψ.sign) (hsa : θ.sign != (θ + ψ).sign) : |(θ + ψ).toReal| = 2 * π - (|
θ.toReal| + |ψ.toReal|)
参数：hs : θ.sign = ψ.sign；hsa : θ.sign != (θ + ψ).sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SignType.trichotomy`：trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.Angle.abs_toReal_neg`：∀ (θ : Real.Angle), |(-θ).toReal| = |θ.toReal
|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle.0.Real.An
gle.abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux`：∀ {θ ψ : Real.An
gle},   θ.sign = 1 → ψ.sign = 1 → (θ + ψ).sign ≠ 1 → |(θ + ψ).toReal| = 2 * Real
.pi - (|θ.toReal| + |ψ.toReal|)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal {θ ψ : Angle} (hs : θ.sign = ψ.sign)
    (hsa : θ.sign ≠ (θ + ψ).sign) : |(θ + ψ).toReal| = 2 * π - (|θ.toReal| + |ψ.toReal|) := by
  obtain h | h | h := θ.sign.trichotomy
  · obtain ⟨hθ', hψ'⟩ : (-θ).sign = 1 ∧ (-ψ).sign = 1 := by grind [sign_neg, neg_neg]
    have hsa' : (-θ + -ψ).sign ≠ 1 := by
      rwa [← hθ', ne_comm, ← neg_add, sign_neg, sign_neg, neg_injective.ne_iff]
    convert! abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux hθ' hψ' hsa' using 1
    all_goals simp [-neg_add_rev, ← neg_add, abs_toReal_neg]
  · grind [sign_eq_zero_iff, coe_pi_add_coe_pi]
  · exact abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux h (hs ▸ h) (h ▸ hsa.symm)
/-
**Real.Angle.continuousAt_sign** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：continuousAt_sign {θ : Angle} (h0 : θ != 0) (hpi : θ != π) : ContinuousAt 
sign θ
参数：h0 : θ != 0；hpi : θ != π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_sign_of_ne_zero`：continuousAt_sign_of_ne_zero {a : α} (h : 
a != 0) : ContinuousAt SignType.sign a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.Angle.sin_ne_zero_iff`：sin_ne_zero_iff {θ : Angle} : sin θ != 0 ↔ θ
 != 0 ∧ θ != π
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Real.Angle.continuous_sin`：continuous_sin : Continuous sin
-/
theorem continuousAt_sign {θ : Angle} (h0 : θ ≠ 0) (hpi : θ ≠ π) : ContinuousAt sign θ :=
  (continuousAt_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuousAt
/-
**Real.Angle._root_.ContinuousOn.angle_sign_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real
.Angle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousOn.angle_sign_comp {α : Type*} [TopologicalSpace α] {f : α → Angle}
    {s : Set α} (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π) :
    ContinuousOn (sign ∘ f) s := by
  refine (continuousOn_of_forall_continuousAt fun θ hθ => ?_).comp hf (Set.mapsTo_image f s)
  obtain ⟨z, hz, rfl⟩ := hθ
  exact continuousAt_sign (hs _ hz).1 (hs _ hz).2

/-- Suppose a function to angles is continuous on a connected set and never takes the values `0`
or `π` on that set. Then the values of the function on that set all have the same sign. -/
/-
**Real.Angle.sign_eq_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Real.Angle`。
形式化陈述：sign_eq_of_continuousOn {α : Type*} [TopologicalSpace α] {f : α -> Angle} 
{s : Set α} {x y : α} (hc : IsConnected s) (hf : ContinuousOn f s) (hs : forall 
z in s, f z != 0 ∧ f z != π) (hx : x in s) (hy : y in s) : (f y).sign = (f x).si
gn
参数：hc : IsConnected s；hf : ContinuousOn f s；hs : forall z in s, f z != 0 ∧ f z !
= π；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subsingleton`：IsPreconnected.subsingleton [TotallyDisconn
ectedSpace α] {s : Set α} (h : IsPreconnected s) : s.Subsingleton
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用定理 `instDiscreteTopologySignType`：DiscreteTopology SignType
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `ContinuousOn.angle_sign_comp`：∀ {α : Type u_1} [inst : TopologicalSpace 
α] {f : α → Real.Angle} {s : Set α},   ContinuousOn f s → (∀ z ∈ s, f z ≠ 0 ∧ f 
z ≠ ↑Real.pi) → Co…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
Suppose a function to angles is continuous on a connected set and never takes th
e values `0`
or `π` on that set. Then the values of the function on that set all have the sam
e sign.
-/
theorem sign_eq_of_continuousOn {α : Type*} [TopologicalSpace α] {f : α → Angle} {s : Set α}
    {x y : α} (hc : IsConnected s) (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π)
    (hx : x ∈ s) (hy : y ∈ s) : (f y).sign = (f x).sign :=
  (hc.image _ (hf.angle_sign_comp hs)).isPreconnected.subsingleton (Set.mem_image_of_mem _ hy)
    (Set.mem_image_of_mem _ hx)

end Angle

end Real

