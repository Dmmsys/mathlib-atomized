/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Half-planes in ℂ are open

We state that open left, right, upper and lower half-planes in the complex numbers are open sets,
where the bounding value of the real or imaginary part is given by a real or `EReal` `x`.
So this includes the full plane and the empty set for `x = ⊤`/`x = ⊥`.
-/

public section

namespace Complex

/-- An open left half-plane (with boundary real part given by an `EReal`) is an open set
in the complex plane. -/
/-
**Complex.isOpen_re_lt_EReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_re_lt_EReal (x : EReal) : IsOpen {z : Complex | z.re < x}
参数：x : EReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.continuous_coe_iff`：continuous_coe_iff {f : α -> Real} : (Continuo
us fun a => (f a : EReal)) ↔ Continuous f
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
An open left half-plane (with boundary real part given by an `EReal`) is an open
 set
in the complex plane.
-/
lemma isOpen_re_lt_EReal (x : EReal) : IsOpen {z : ℂ | z.re < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_re) continuous_const

/-- An open right half-plane (with boundary real part given by an `EReal`) is an open set
in the complex plane. -/
/-
**Complex.isOpen_re_gt_EReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_re_gt_EReal (x : EReal) : IsOpen {z : Complex | x < z.re}
参数：x : EReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.continuous_coe_iff`：continuous_coe_iff {f : α -> Real} : (Continuo
us fun a => (f a : EReal)) ↔ Continuous f
· 使用定理 `Complex.continuous_re`：Continuous Complex.re

--- 原说明 ---
An open right half-plane (with boundary real part given by an `EReal`) is an ope
n set
in the complex plane.
-/
lemma isOpen_re_gt_EReal (x : EReal) : IsOpen {z : ℂ | x < z.re} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_re

/-- An open lower half-plane (with boundary imaginary part given by an `EReal`) is an open set
in the complex plane. -/
/-
**Complex.isOpen_im_lt_EReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_im_lt_EReal (x : EReal) : IsOpen {z : Complex | z.im < x}
参数：x : EReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.continuous_coe_iff`：continuous_coe_iff {f : α -> Real} : (Continuo
us fun a => (f a : EReal)) ↔ Continuous f
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
An open lower half-plane (with boundary imaginary part given by an `EReal`) is a
n open set
in the complex plane.
-/
lemma isOpen_im_lt_EReal (x : EReal) : IsOpen {z : ℂ | z.im < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_im) continuous_const

/-- An open upper half-plane (with boundary imaginary part given by an `EReal`) is an open set
in the complex plane. -/
/-
**Complex.isOpen_im_gt_EReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_im_gt_EReal (x : EReal) : IsOpen {z : Complex | x < z.im}
参数：x : EReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.continuous_coe_iff`：continuous_coe_iff {f : α -> Real} : (Continuo
us fun a => (f a : EReal)) ↔ Continuous f
· 使用定理 `Complex.continuous_im`：Continuous Complex.im

--- 原说明 ---
An open upper half-plane (with boundary imaginary part given by an `EReal`) is a
n open set
in the complex plane.
-/
lemma isOpen_im_gt_EReal (x : EReal) : IsOpen {z : ℂ | x < z.im} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_im

/-- An open left half-plane is an open set in the complex plane. -/
/-
**Complex.isOpen_re_lt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_re_lt (x : Real) : IsOpen {z : Complex | z.re < x}
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.isOpen_re_lt_EReal`：isOpen_re_lt_EReal (x : EReal) : IsOpen {z :
 Complex | z.re < x}

--- 原说明 ---
An open left half-plane is an open set in the complex plane.
-/
lemma isOpen_re_lt (x : ℝ) : IsOpen {z : ℂ | z.re < x} := by
  simpa using isOpen_re_lt_EReal x

/-- An open right half-plane is an open set in the complex plane. -/
/-
**Complex.isOpen_re_gt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_re_gt (x : Real) : IsOpen {z : Complex | x < z.re}
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.isOpen_re_gt_EReal`：isOpen_re_gt_EReal (x : EReal) : IsOpen {z :
 Complex | x < z.re}

--- 原说明 ---
An open right half-plane is an open set in the complex plane.
-/
lemma isOpen_re_gt (x : ℝ) : IsOpen {z : ℂ | x < z.re} := by
  simpa using isOpen_re_gt_EReal x

/-- An open lower half-plane is an open set in the complex plane. -/
/-
**Complex.isOpen_im_lt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_im_lt (x : Real) : IsOpen {z : Complex | z.im < x}
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.isOpen_im_lt_EReal`：isOpen_im_lt_EReal (x : EReal) : IsOpen {z :
 Complex | z.im < x}

--- 原说明 ---
An open lower half-plane is an open set in the complex plane.
-/
lemma isOpen_im_lt (x : ℝ) : IsOpen {z : ℂ | z.im < x} := by
  simpa using isOpen_im_lt_EReal x

/-- An open upper half-plane is an open set in the complex plane. -/
/-
**Complex.isOpen_im_gt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isOpen_im_gt (x : Real) : IsOpen {z : Complex | x < z.im}
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.isOpen_im_gt_EReal`：isOpen_im_gt_EReal (x : EReal) : IsOpen {z :
 Complex | x < z.im}

--- 原说明 ---
An open upper half-plane is an open set in the complex plane.
-/
lemma isOpen_im_gt (x : ℝ) : IsOpen {z : ℂ | x < z.im} := by
  simpa using isOpen_im_gt_EReal x

end Complex

