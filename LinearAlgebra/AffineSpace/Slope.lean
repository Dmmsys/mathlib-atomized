/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Slope of a function

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some basic theorems about `slope`. The `slope` function naturally appears in the Mean
Value Theorem, and in the proof of the fact that a function with nonnegative second derivative on an
interval is convex on this interval.

## Tags

affine space, slope
-/

@[expose] public section

open AffineMap

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

/-- `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`. -/
/-
**slope** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：slope (f : k -> PE) (a b : k) : E
参数：f : k -> PE；a b : k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the i
nterval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`.
-/
def slope (f : k → PE) (a b : k) : E :=
  (b - a)⁻¹ • (f b -ᵥ f a)
/-
**slope_fun_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_fun_def (f : k -> PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a
)
参数：f : k -> PE。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem slope_fun_def (f : k → PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a) :=
  rfl
/-
**slope_def_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_def_field (f : k -> k) (a b : k) : slope f a b = (f b - f a) / (b - 
a)
参数：f : k -> k；a b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm
/-
**slope_fun_def_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_fun_def_field (f : k -> k) (a : k) : slope f a = fun b => (f b - f a
) / (b - a)
参数：f : k -> k；a : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem slope_fun_def_field (f : k → k) (a : k) : slope f a = fun b => (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm

@[simp]
/-
**slope_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_same (f : k -> PE) (a : k) : (slope f a a : E) = 0
参数：f : k -> PE；a : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `slope.eq_1`：∀ {k : Type u_1} {E : Type u_2} {PE : Type u_3} [inst : Fiel
d k] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module k E]   [inst_3 : AddTorso
…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 := by
  rw [slope, sub_self, inv_zero, zero_smul]
/-
**slope_def_module** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_def_module (f : k -> E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b -
 f a)
参数：f : k -> E；a b : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem slope_def_module (f : k → E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b - f a) :=
  rfl

@[simp]
/-
**sub_smul_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_smul_slope (f : k -> PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f 
a
参数：f : k -> PE；a b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `slope.eq_1`：∀ {k : Type u_1} {E : Type u_2} {PE : Type u_3} [inst : Fiel
d k] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module k E]   [inst_3 : AddTorso
…
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem sub_smul_slope (f : k → PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a := by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]
/-
**sub_smul_slope_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_smul_slope_vadd (f : k -> PE) (a b : k) : (b - a) • slope f a b +ᵥ f a
 = f b
参数：f : k -> PE；a b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul_slope`：sub_smul_slope (f : k -> PE) (a b : k) : (b - a) • slope
 f a b = f b -ᵥ f a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
-/
theorem sub_smul_slope_vadd (f : k → PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b := by
  rw [sub_smul_slope, vsub_vadd]

@[simp]
/-
**slope_vadd_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_vadd_const (f : k -> E) (c : PE) : (slope fun x => f x +ᵥ c) = slope
 f
参数：f : k -> E；c : PE。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem slope_vadd_const (f : k → E) (c : PE) : (slope fun x => f x +ᵥ c) = slope f := by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

@[simp]
/-
**slope_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_sub_smul (f : k -> E) {a b : k} (h : a != b) : slope (fun x => (x - 
a) • f x) a b = f b
参数：f : k -> E；h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem slope_sub_smul (f : k → E) {a b : k} (h : a ≠ b) :
    slope (fun x => (x - a) • f x) a b = f b := by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]
/-
**eq_of_slope_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_slope_eq_zero {f : k -> PE} {a b : k} (h : slope f a b = (0 : E)) : 
f a = f b
参数：h : slope f a b = (0 : E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_smul_slope_vadd`：sub_smul_slope_vadd (f : k -> PE) (a b : k) : (b - 
a) • slope f a b +ᵥ f a = f b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
-/
theorem eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b, h, smul_zero, zero_vadd]
/-
**AffineMap.slope_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.slope_comp {F PF : Type*} [AddCommGroup F] [Module k F] [AddTors
or F PF] (f : PE ->ᵃ[k] PF) (g : k -> PE) (a b : k) : slope (f ∘ g) a b = f.line
ar (slope g a b)
参数：f : PE ->ᵃ[k] PF；g : k -> PE；a b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AffineMap.slope_comp {F PF : Type*} [AddCommGroup F] [Module k F] [AddTorsor F PF]
    (f : PE →ᵃ[k] PF) (g : k → PE) (a b : k) : slope (f ∘ g) a b = f.linear (slope g a b) := by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]
/-
**LinearMap.slope_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.slope_comp {F : Type*} [AddCommGroup F] [Module k F] (f : E ->ₗ[
k] F) (g : k -> E) (a b : k) : slope (f ∘ g) a b = f (slope g a b)
参数：f : E ->ₗ[k] F；g : k -> E；a b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.slope_comp`：AffineMap.slope_comp {F PF : Type*} [AddCommGroup 
F] [Module k F] [AddTorsor F PF] (f : PE ->ᵃ[k] PF) (g : k -> PE) (a b : k) : sl
ope (f ∘ g…
-/
theorem LinearMap.slope_comp {F : Type*} [AddCommGroup F] [Module k F] (f : E →ₗ[k] F) (g : k → E)
    (a b : k) : slope (f ∘ g) a b = f (slope g a b) :=
  f.toAffineMap.slope_comp g a b
/-
**slope_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b a
参数：f : k -> PE；a b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `slope.eq_1`：∀ {k : Type u_1} {E : Type u_2} {PE : Type u_3} [inst : Fiel
d k] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module k E]   [inst_3 : AddTorso
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a := by
  rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]
/-
**slope_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : AddCommGroup E]
 [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun t => -f t) x y
 = -slope f x y
参数：f : k → E；x y : k；fun t => -f t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma slope_neg (f : k → E) (x y : k) : slope (fun t ↦ -f t) x y = -slope f x y := by
  simp only [slope_def_module, neg_sub_neg, ← smul_neg, neg_sub]
/-
**slope_neg_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : AddCommGroup E]
 [inst_2 : _root_.Module k E] (f : k → E),   slope (-f) = -slope f
参数：f : k → E；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
-/
@[simp] lemma slope_neg_fun (f : k → E) : slope (-f) = -slope f := by
  ext x y; exact slope_neg f x y
/-
**slope_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：slope_eq_zero_iff {f : k -> E} {a b : k} : slope f a b = 0 ↔ f a = f b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma slope_eq_zero_iff {f : k → E} {a b : k} : slope f a b = 0 ↔ f a = f b := by
  simp [slope, sub_eq_zero, eq_comm, or_iff_right_of_imp (congr_arg _)]

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `lineMap_slope_slope_sub_div_sub`. -/
/-
**sub_div_sub_smul_slope_add_sub_div_sub_smul_slope** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k -> PE) (a b c : k
) : ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slop
e f a c
参数：f : k -> PE；a b c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `slope_same`：slope_same (f : k -> PE) (a : k) : (slope f a a : E) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃

--- 原说明 ---
`slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This v
ersion
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients i
s `1`, so it is
actually an affine combination, see `lineMap_slope_slope_sub_div_sub`.
-/
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
    ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c := by
  by_cases hab : a = b
  · subst hab
    rw [sub_self, zero_div, zero_smul, zero_add]
    by_cases hac : a = c
    · simp [hac]
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_ne_zero.2 (Ne.symm hab)]
  rw [add_comm]
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hab), smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hbc),
    vsub_add_vsub_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`lineMap` to express this property. -/
/-
**lineMap_slope_slope_sub_div_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineMap_slope_slope_sub_div_sub (f : k -> PE) (a b c : k) (h : a != c) : l
ineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c
参数：f : k -> PE；a b c : k；h : a != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_div_sub_smul_slope_add_sub_div_sub_smul_slope`：sub_div_sub_smul_slop
e_add_sub_div_sub_smul_slope (f : k -> PE) (a b c : k) : ((b - a) / (c - a)) • s
lope f a b + ((c - b) / (c - a)) • slop…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
`slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This 
version uses
`lineMap` to express this property.
-/
theorem lineMap_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
    lineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c := by
  simp only [lineMap_apply_module, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
    add_left_inj]
  match_scalars
  field [sub_ne_zero.2 h.symm]

set_option backward.isDefEq.respectTransparency false in
/-- `slope f a b` is an affine combination of `slope f a (lineMap a b r)` and
`slope f (lineMap a b r) b`. We use `lineMap` to express this property. -/
/-
**lineMap_slope_lineMap_slope_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineMap_slope_lineMap_slope_lineMap (f : k -> PE) (a b r : k) : lineMap (s
lope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b
参数：f : k -> PE；a b r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `slope_same`：slope_same (f : k -> PE) (a : k) : (slope f a a : E) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_ring`：lineMap_apply_ring (a b c : k) : lineMap a
 b c = (1 - c) * a + c * b
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `lineMap_slope_slope_sub_div_sub`：lineMap_slope_slope_sub_div_sub (f : k 
-> PE) (a b c : k) (h : a != c) : lineMap (slope f a b) (slope f b c) ((c - b) /
 (c - a)) = slope f a…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
`slope f a b` is an affine combination of `slope f a (lineMap a b r)` and
`slope f (lineMap a b r) b`. We use `lineMap` to express this property.
-/
theorem lineMap_slope_lineMap_slope_lineMap (f : k → PE) (a b r : k) :
    lineMap (slope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b := by
  obtain rfl | hab : a = b ∨ a ≠ b := Classical.em _; · simp
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b]
  convert! lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  rw [lineMap_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]

section Order

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

/-
**slope_nonneg_iff_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：slope_nonneg_iff_of_le (hxy : x <= y) : 0 <= slope f x y ↔ f x <= f y
参数：hxy : x <= y。
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
· 使用定理 `slope_same`：slope_same (f : k -> PE) (a : k) : (slope f a a : E) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `vsub_eq_sub`：∀ {G : Type u_1} [inst : AddGroup G] (g₁ g₂ : G), g₁ -ᵥ g₂ 
= g₁ - g₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `slope.eq_1`：∀ {k : Type u_1} {E : Type u_2} {PE : Type u_3} [inst : Fiel
d k] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module k E]   [inst_3 : AddTorso
…
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma slope_nonneg_iff_of_le (hxy : x ≤ y) : 0 ≤ slope f x y ↔ f x ≤ f y := by
  by_cases hxeqy : x = y
  · simp [hxeqy]
  refine ⟨fun h ↦ ?_, fun h ↦ smul_nonneg (inv_nonneg.2 (sub_nonneg.2 hxy)) ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [slope, ← mul_smul, mul_inv_cancel₀ (mt sub_eq_zero.1 (Ne.symm hxeqy)), one_smul,
      vsub_eq_sub, sub_nonneg] at this
  · rwa [vsub_eq_sub, sub_nonneg]
/-
**MonotoneOn.slope_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.slope_nonneg {s : Set k} (hf : MonotoneOn f s) (hx : x in s) (h
y : y in s) : 0 <= slope f x y
参数：hf : MonotoneOn f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `slope_nonneg_iff_of_le`：slope_nonneg_iff_of_le (hxy : x <= y) : 0 <= slo
pe f x y ↔ f x <= f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
-/
lemma MonotoneOn.slope_nonneg {s : Set k} (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    0 ≤ slope f x y := by
  rcases le_total x y with hxy | hxy
  · exact (slope_nonneg_iff_of_le hxy).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_nonneg_iff_of_le hxy).mpr (hf hy hx hxy)
/-
**slope_nonpos_iff_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：slope_nonpos_iff_of_le (hxy : x <= y) : slope f x y <= 0 ↔ f y <= f x
参数：hxy : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg_fun`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 
: AddCommGroup E] [inst_2 : _root_.Module k E] (f : k → E),   slope (-f) = -slop
e f
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `slope_nonneg_iff_of_le`：slope_nonneg_iff_of_le (hxy : x <= y) : 0 <= slo
pe f x y ↔ f x <= f y
-/
lemma slope_nonpos_iff_of_le (hxy : x ≤ y) : slope f x y ≤ 0 ↔ f y ≤ f x := by
  simpa using slope_nonneg_iff_of_le (f := -f) hxy
/-
**AntitoneOn.slope_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.slope_nonpos {s : Set k} (hf : AntitoneOn f s) (hx : x in s) (h
y : y in s) : slope f x y <= 0
参数：hf : AntitoneOn f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `MonotoneOn.slope_nonneg`：MonotoneOn.slope_nonneg {s : Set k} (hf : Monot
oneOn f s) (hx : x in s) (hy : y in s) : 0 <= slope f x y
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma AntitoneOn.slope_nonpos {s : Set k} (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    slope f x y ≤ 0 := by
  simpa using hf.neg.slope_nonneg hx hy
/-
**slope_pos_iff_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：slope_pos_iff_of_le (hxy : x <= y) : 0 < slope f x y ↔ f x < f y
参数：hxy : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `slope_nonneg_iff_of_le`：slope_nonneg_iff_of_le (hxy : x <= y) : 0 <= slo
pe f x y ↔ f x <= f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma slope_pos_iff_of_le (hxy : x ≤ y) : 0 < slope f x y ↔ f x < f y := by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy, Ne, eq_comm, slope_eq_zero_iff]
/-
**StrictMonoOn.slope_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.slope_pos {s : Set k} (hf : StrictMonoOn f s) (hx : x in s) (
hy : y in s) (hxy : x != y) : 0 < slope f x y
参数：hf : StrictMonoOn f s；hx : x in s；hy : y in s；hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `slope_pos_iff_of_le`：slope_pos_iff_of_le (hxy : x <= y) : 0 < slope f x 
y ↔ f x < f y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
-/
lemma StrictMonoOn.slope_pos {s : Set k} (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : 0 < slope f x y := by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact (slope_pos_iff_of_le hxy.le).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_pos_iff_of_le hxy.le).mpr (hf hy hx hxy)
/-
**slope_neg_iff_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：slope_neg_iff_of_le (hxy : x <= y) : slope f x y < 0 ↔ f y < f x
参数：hxy : x <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg_fun`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 
: AddCommGroup E] [inst_2 : _root_.Module k E] (f : k → E),   slope (-f) = -slop
e f
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
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `slope_pos_iff_of_le`：slope_pos_iff_of_le (hxy : x <= y) : 0 < slope f x 
y ↔ f x < f y
-/
lemma slope_neg_iff_of_le (hxy : x ≤ y) : slope f x y < 0 ↔ f y < f x := by
  simpa using slope_pos_iff_of_le (f := -f) hxy
/-
**StrictAntiOn.slope_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.slope_neg {s : Set k} (hf : StrictAntiOn f s) (hx : x in s) (
hy : y in s) (hxy : x != y) : slope f x y < 0
参数：hf : StrictAntiOn f s；hx : x in s；hy : y in s；hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `StrictMonoOn.slope_pos`：StrictMonoOn.slope_pos {s : Set k} (hf : StrictM
onoOn f s) (hx : x in s) (hy : y in s) (hxy : x != y) : 0 < slope f x y
· 使用定理 `StrictAntiOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [ins
t_1 : Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]   [inst_4 : Preor
der β]…
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
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma StrictAntiOn.slope_neg {s : Set k} (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : slope f x y < 0 := by
  simpa using hf.neg.slope_pos hx hy hxy

end Order

