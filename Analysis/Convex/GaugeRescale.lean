/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.Convex
/-!
# "Gauge rescale" homeomorphism between convex sets

Given two convex von Neumann bounded neighbourhoods of the origin
in a real topological vector space,
we construct a homeomorphism `gaugeRescaleHomeomorph`
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.
-/

@[expose] public section

open Metric Bornology Filter Set
open scoped NNReal Topology Pointwise

noncomputable section

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The gauge rescale map `gaugeRescale s t` sends each point `x` to the point `y` on the same ray
that has the same gauge w.r.t. `t` as `x` has w.r.t. `s`.

The characteristic property is satisfied if `gauge t x ≠ 0`, see `gauge_gaugeRescale'`.
In particular, it is satisfied for all `x`,
provided that `t` is absorbent and von Neumann bounded. -/
/-
**gaugeRescale** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gaugeRescale (s t : Set E) (x : E) : E
参数：s t : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gauge rescale map `gaugeRescale s t` sends each point `x` to the point `y` o
n the same ray
that has the same gauge w.r.t. `t` as `x` has w.r.t. `s`.

The characteristic property is satisfied if `gauge t x ≠ 0`, see `gauge_gaugeRes
cale'`.
In particular, it is satisfied for all `x`,
provided that `t` is absorbent and von Neumann bounded.
-/
def gaugeRescale (s t : Set E) (x : E) : E := (gauge s x / gauge t x) • x
/-
**gaugeRescale_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeRescale_def (s t : Set E) (x : E) : gaugeRescale s t x = (gauge s x /
 gauge t x) • x
参数：s t : Set E；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gaugeRescale_def (s t : Set E) (x : E) :
    gaugeRescale s t x = (gauge s x / gauge t x) • x :=
  rfl
/-
**gaugeRescale_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] (s t
 : Set E), gaugeRescale s t 0 = 0
参数：s t : Set E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
@[simp] theorem gaugeRescale_zero (s t : Set E) : gaugeRescale s t 0 = 0 := smul_zero _
/-
**gaugeRescale_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeRescale_smul (s t : Set E) {c : Real} (hc : 0 <= c) (x : E) : gaugeRe
scale s t (c • x) = c • gaugeRescale s t x
参数：s t : Set E；hc : 0 <= c；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `gauge_smul_of_nonneg`：gauge_smul_of_nonneg [MulActionWithZero α E] [IsSc
alarTower α Real (Set E)] {s : Set E} {a : α} (ha : 0 <= a) (x : E) : gauge s (a
 • x) = a …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_div_mul_comm`：mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `div_self_mul_self`：div_self_mul_self (a : G₀) : a / a * a = a
-/
theorem gaugeRescale_smul (s t : Set E) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    gaugeRescale s t (c • x) = c • gaugeRescale s t x := by
  simp only [gaugeRescale, gauge_smul_of_nonneg hc, smul_smul, smul_eq_mul]
  rw [mul_div_mul_comm, mul_right_comm, div_self_mul_self]
/-
**gauge_gaugeRescale'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_gaugeRescale' (s : Set E) {t : Set E} {x : E} (hx : gauge t x != 0) 
: gauge t (gaugeRescale s t x) = gauge s x
参数：s : Set E；hx : gauge t x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gaugeRescale.eq_1`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] (s t : Set E) (x : E),   gaugeRescale s t x = (gauge s x / gaug
e t x) …
· 使用定理 `gauge_smul_of_nonneg`：gauge_smul_of_nonneg [MulActionWithZero α E] [IsSc
alarTower α Real (Set E)] {s : Set E} {a : α} (ha : 0 <= a) (x : E) : gauge s (a
 • x) = a …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
-/
theorem gauge_gaugeRescale' (s : Set E) {t : Set E} {x : E} (hx : gauge t x ≠ 0) :
    gauge t (gaugeRescale s t x) = gauge s x := by
  rw [gaugeRescale, gauge_smul_of_nonneg (div_nonneg (gauge_nonneg _) (gauge_nonneg _)),
    smul_eq_mul, div_mul_cancel₀ _ hx]
/-
**gauge_gaugeRescale_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_gaugeRescale_le (s t : Set E) (x : E) : gauge t (gaugeRescale s t x)
 <= gauge s x
参数：s t : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `gauge_zero`：gauge_zero : gauge s 0 = 0
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `gauge_gaugeRescale'`：gauge_gaugeRescale' (s : Set E) {t : Set E} {x : E}
 (hx : gauge t x != 0) : gauge t (gaugeRescale s t x) = gauge s x
-/
theorem gauge_gaugeRescale_le (s t : Set E) (x : E) :
    gauge t (gaugeRescale s t x) ≤ gauge s x := by
  by_cases hx : gauge t x = 0
  · simp [gaugeRescale, hx, gauge_nonneg]
  · exact (gauge_gaugeRescale' s hx).le

variable [TopologicalSpace E]

section
variable [T1Space E]

/-
**gaugeRescale_self_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeRescale_self_apply {s : Set E} (hsa : Absorbent Real s) (hsb : IsVonN
Bounded Real s) (x : E) : gaugeRescale s s x = x
参数：hsa : Absorbent Real s；hsb : IsVonNBounded Real s；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gaugeRescale_zero`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] (s t : Set E), gaugeRescale s t 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gaugeRescale.eq_1`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] (s t : Set E) (x : E),   gaugeRescale s t x = (gauge s x / gaug
e t x) …
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `gauge_pos`：gauge_pos (hs : Absorbent Real s) (hb : Bornology.IsVonNBound
ed Real s) : 0 < gauge s x ↔ x != 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem gaugeRescale_self_apply {s : Set E} (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s)
    (x : E) : gaugeRescale s s x = x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale, div_self, one_smul]
  exact ((gauge_pos hsa hsb).2 hx).ne'
/-
**gaugeRescale_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeRescale_self {s : Set E} (hsa : Absorbent Real s) (hsb : IsVonNBounde
d Real s) : gaugeRescale s s = id
参数：hsa : Absorbent Real s；hsb : IsVonNBounded Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `gaugeRescale_self_apply`：gaugeRescale_self_apply {s : Set E} (hsa : Abso
rbent Real s) (hsb : IsVonNBounded Real s) (x : E) : gaugeRescale s s x = x
-/
theorem gaugeRescale_self {s : Set E} (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s) :
    gaugeRescale s s = id :=
  funext <| gaugeRescale_self_apply hsa hsb
/-
**gauge_gaugeRescale** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_gaugeRescale (s : Set E) {t : Set E} (hta : Absorbent Real t) (htb :
 IsVonNBounded Real t) (x : E) : gauge t (gaugeRescale s t x) = gauge s x
参数：s : Set E；hta : Absorbent Real t；htb : IsVonNBounded Real t；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gaugeRescale_zero`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] (s t : Set E), gaugeRescale s t 0 = 0
· 使用定理 `gauge_zero`：gauge_zero : gauge s 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gauge_gaugeRescale'`：gauge_gaugeRescale' (s : Set E) {t : Set E} {x : E}
 (hx : gauge t x != 0) : gauge t (gaugeRescale s t x) = gauge s x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `gauge_pos`：gauge_pos (hs : Absorbent Real s) (hb : Bornology.IsVonNBound
ed Real s) : 0 < gauge s x ↔ x != 0
-/
theorem gauge_gaugeRescale (s : Set E) {t : Set E} (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t)
    (x : E) : gauge t (gaugeRescale s t x) = gauge s x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact gauge_gaugeRescale' s ((gauge_pos hta htb).2 hx).ne'
/-
**gaugeRescale_gaugeRescale** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeRescale_gaugeRescale {s t u : Set E} (hta : Absorbent Real t) (htb : 
IsVonNBounded Real t) (x : E) : gaugeRescale t u (gaugeRescale s t x) = gaugeRes
cale s u x
参数：hta : Absorbent Real t；htb : IsVonNBounded Real t；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gaugeRescale_zero`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] (s t : Set E), gaugeRescale s t 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gaugeRescale_def`：gaugeRescale_def (s t : Set E) (x : E) : gaugeRescale 
s t x = (gauge s x / gauge t x) • x
· 使用定理 `gaugeRescale_smul`：gaugeRescale_smul (s t : Set E) {c : Real} (hc : 0 <=
 c) (x : E) : gaugeRescale s t (c • x) = c • gaugeRescale s t x
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用定理 `gaugeRescale.eq_1`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] (s t : Set E) (x : E),   gaugeRescale s t x = (gauge s x / gaug
e t x) …
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `div_mul_div_cancel₀`：div_mul_div_cancel₀ (hb : b != 0) : a / b * (b / c)
 = a / c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `gauge_pos`：gauge_pos (hs : Absorbent Real s) (hb : Bornology.IsVonNBound
ed Real s) : 0 < gauge s x ↔ x != 0
-/
theorem gaugeRescale_gaugeRescale {s t u : Set E} (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t)
    (x : E) : gaugeRescale t u (gaugeRescale s t x) = gaugeRescale s u x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale_def s t x, gaugeRescale_smul, gaugeRescale, gaugeRescale, smul_smul,
    div_mul_div_cancel₀]
  exacts [((gauge_pos hta htb).2 hx).ne', div_nonneg (gauge_nonneg _) (gauge_nonneg _)]

/-- `gaugeRescale` bundled as an `Equiv`. -/
/-
**gaugeRescaleEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gaugeRescaleEquiv (s t : Set E) (hsa : Absorbent Real s) (hsb : IsVonNBoun
ded Real s) (hta : Absorbent Real t) (htb : IsVonNBounded Real t) : E ≃ E where 
toFun
参数：s t : Set E；hsa : Absorbent Real s；hsb : IsVonNBounded Real s；hta : Absorbent
 Real t；htb : IsVonNBounded Real t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`gaugeRescale` bundled as an `Equiv`.
-/
def gaugeRescaleEquiv (s t : Set E) (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s)
    (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t) : E ≃ E where
  toFun := gaugeRescale s t
  invFun := gaugeRescale t s
  left_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption
  right_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption

end

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s t : Set E}

/-
**mapsTo_gaugeRescale_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapsTo_gaugeRescale_interior (h₀ : t in 𝓝 0) (hc : Convex Real t) : MapsTo
 (gaugeRescale s t) (interior s) (interior t)
参数：h₀ : t in 𝓝 0；hc : Convex Real t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gauge_lt_one_iff_mem_interior`：gauge_lt_one_iff_mem_interior (hc : Conve
x Real s) (hs₀ : s in 𝓝 0) : gauge s x < 1 ↔ x in interior s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `gauge_gaugeRescale_le`：gauge_gaugeRescale_le (s t : Set E) (x : E) : gau
ge t (gaugeRescale s t x) <= gauge s x
· 使用定理 `interior_subset_gauge_lt_one`：interior_subset_gauge_lt_one (s : Set E) :
 interior s subseteq { x | gauge s x < 1 }
-/
theorem mapsTo_gaugeRescale_interior (h₀ : t ∈ 𝓝 0) (hc : Convex ℝ t) :
    MapsTo (gaugeRescale s t) (interior s) (interior t) := fun x hx ↦ by
  rw [← gauge_lt_one_iff_mem_interior] <;> try assumption
  exact (gauge_gaugeRescale_le _ _ _).trans_lt (interior_subset_gauge_lt_one _ hx)
/-
**mapsTo_gaugeRescale_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapsTo_gaugeRescale_closure {s t : Set E} (hsc : Convex Real s) (hs₀ : s i
n 𝓝 0) (htc : Convex Real t) (ht₀ : 0 in t) (hta : Absorbent Real t) : MapsTo (g
augeRescale s t) (closure s) (closure t)
参数：hsc : Convex Real s；hs₀ : s in 𝓝 0；htc : Convex Real t；ht₀ : 0 in t；hta : Abs
orbent Real t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_gauge_le_one`：mem_closure_of_gauge_le_one (hc : Convex Re
al s) (hs₀ : 0 in s) (ha : Absorbent Real s) (h : gauge s x <= 1) : x in closure
 s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `gauge_gaugeRescale_le`：gauge_gaugeRescale_le (s t : Set E) (x : E) : gau
ge t (gaugeRescale s t x) <= gauge s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `gauge_le_one_iff_mem_closure`：gauge_le_one_iff_mem_closure (hc : Convex 
Real s) (hs₀ : s in 𝓝 0) : gauge s x <= 1 ↔ x in closure s
-/
theorem mapsTo_gaugeRescale_closure {s t : Set E} (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (htc : Convex ℝ t) (ht₀ : 0 ∈ t) (hta : Absorbent ℝ t) :
    MapsTo (gaugeRescale s t) (closure s) (closure t) := fun _x hx ↦
  mem_closure_of_gauge_le_one htc ht₀ hta <| (gauge_gaugeRescale_le _ _ _).trans <|
    (gauge_le_one_iff_mem_closure hsc hs₀).2 hx

variable [T1Space E]
/-
**continuous_gaugeRescale** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_gaugeRescale {s t : Set E} (hs : Convex Real s) (hs₀ : s in 𝓝 0
) (ht : Convex Real t) (ht₀ : t in 𝓝 0) (htb : IsVonNBounded Real t) : Continuou
s (gaugeRescale s t)
参数：hs : Convex Real s；hs₀ : s in 𝓝 0；ht : Convex Real t；ht₀ : t in 𝓝 0；htb : IsV
onNBounded Real t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `gaugeRescale_zero`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _r
oot_.Module ℝ E] (s t : Set E), gaugeRescale s t 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_gauge_nhds_zero`：comap_gauge_nhds_zero (hb : Bornology.IsVonNBound
ed Real s) (h₀ : s in 𝓝 0) : comap (gauge s) (𝓝 0) = 𝓝 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `gauge_gaugeRescale`：gauge_gaugeRescale (s : Set E) {t : Set E} (hta : Ab
sorbent Real t) (htb : IsVonNBounded Real t) (x : E) : gauge t (gaugeRescale s t
 x) = ga…
· 使用定理 `tendsto_gauge_nhds_zero`：tendsto_gauge_nhds_zero (hs : s in 𝓝 0) : Tends
to (gauge s) (𝓝 0) (𝓝 0)
· 使用定理 `ContinuousAt.smul`：ContinuousAt.smul (hf : ContinuousAt f b) (hg : Conti
nuousAt g b) : ContinuousAt (f • g) b
· 使用定理 `ContinuousAt.div`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero
 G₀] [inst_1 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   [ContinuousMul G₀] {f 
g : α …
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuousAt_gauge`：continuousAt_gauge (hc : Convex Real s) (hs₀ : s in 
𝓝 0) : ContinuousAt (gauge s) x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `gauge_pos`：gauge_pos (hs : Absorbent Real s) (hb : Bornology.IsVonNBound
ed Real s) : 0 < gauge s x ↔ x != 0
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
-/
theorem continuous_gaugeRescale {s t : Set E} (hs : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (ht : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    Continuous (gaugeRescale s t) := by
  have hta : Absorbent ℝ t := absorbent_nhds_zero ht₀
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    simp only [tendsto_comap_iff, Function.comp_def, gauge_gaugeRescale _ hta htb]
    exact tendsto_gauge_nhds_zero hs₀
  · exact ((continuousAt_gauge hs hs₀).div (continuousAt_gauge ht ht₀)
      ((gauge_pos hta htb).2 hx).ne').smul continuousAt_id

/-- `gaugeRescale` bundled as a `Homeomorph`. -/
/-
**gaugeRescaleHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gaugeRescaleHomeomorph (s t : Set E) (hsc : Convex Real s) (hs₀ : s in 𝓝 0
) (hsb : IsVonNBounded Real s) (htc : Convex Real t) (ht₀ : t in 𝓝 0) (htb : IsV
onNBounded Real t) : E ≃ₜ E where toEquiv
参数：s t : Set E；hsc : Convex Real s；hs₀ : s in 𝓝 0；hsb : IsVonNBounded Real s；htc
 : Convex Real t；ht₀ : t in 𝓝 0；htb : IsVonNBounded Real t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A

--- 原说明 ---
`gaugeRescale` bundled as a `Homeomorph`.
-/
def gaugeRescaleHomeomorph (s t : Set E)
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) : E ≃ₜ E where
  toEquiv := gaugeRescaleEquiv s t (absorbent_nhds_zero hs₀) hsb (absorbent_nhds_zero ht₀) htb
  continuous_toFun := by apply continuous_gaugeRescale <;> assumption
  continuous_invFun := by apply continuous_gaugeRescale <;> assumption
/-
**image_gaugeRescaleHomeomorph_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_gaugeRescaleHomeomorph_interior {s t : Set E} (hsc : Convex Real s) 
(hs₀ : s in 𝓝 0) (hsb : IsVonNBounded Real s) (htc : Convex Real t) (ht₀ : t in 
𝓝 0) (htb : IsVonNBounded Real t) : gaugeRescaleHomeomorph s t hsc hs₀ hsb htc h
t₀ htb '' interior s = interior t
参数：hsc : Convex Real s；hs₀ : s in 𝓝 0；hsb : IsVonNBounded Real s；htc : Convex Re
al t；ht₀ : t in 𝓝 0；htb : IsVonNBounded Real t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `mapsTo_gaugeRescale_interior`：mapsTo_gaugeRescale_interior (h₀ : t in 𝓝 
0) (hc : Convex Real t) : MapsTo (gaugeRescale s t) (interior s) (interior t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_gaugeRescaleHomeomorph_interior {s t : Set E}
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' interior s = interior t :=
  Subset.antisymm (mapsTo_gaugeRescale_interior ht₀ htc).image_subset <| by
    rw [← Homeomorph.preimage_symm, ← image_subset_iff]
    exact (mapsTo_gaugeRescale_interior hs₀ hsc).image_subset
/-
**image_gaugeRescaleHomeomorph_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_gaugeRescaleHomeomorph_closure {s t : Set E} (hsc : Convex Real s) (
hs₀ : s in 𝓝 0) (hsb : IsVonNBounded Real s) (htc : Convex Real t) (ht₀ : t in 𝓝
 0) (htb : IsVonNBounded Real t) : gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht
₀ htb '' closure s = closure t
参数：hsc : Convex Real s；hs₀ : s in 𝓝 0；hsb : IsVonNBounded Real s；htc : Convex Re
al t；ht₀ : t in 𝓝 0；htb : IsVonNBounded Real t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `mapsTo_gaugeRescale_closure`：mapsTo_gaugeRescale_closure {s t : Set E} (
hsc : Convex Real s) (hs₀ : s in 𝓝 0) (htc : Convex Real t) (ht₀ : 0 in t) (hta 
: Absorbent Real …
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_gaugeRescaleHomeomorph_closure {s t : Set E}
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' closure s = closure t := by
  refine Subset.antisymm (mapsTo_gaugeRescale_closure hsc hs₀ htc
    (mem_of_mem_nhds ht₀) (absorbent_nhds_zero ht₀)).image_subset ?_
  rw [← Homeomorph.preimage_symm, ← image_subset_iff]
  exact (mapsTo_gaugeRescale_closure htc ht₀ hsc
    (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀)).image_subset

/-- Given two convex bounded sets in a topological vector space with nonempty interiors,
there exists a homeomorphism of the ambient space
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.

In particular, if both `s` and `t` are open set or both `s` and `t` are closed sets,
then `e` maps `s` to `t`. -/
/-
**exists_homeomorph_image_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_homeomorph_image_eq {s t : Set E} (hsc : Convex Real s) (hsne : (in
terior s).Nonempty) (hsb : IsVonNBounded Real s) (hst : Convex Real t) (htne : (
interior t).Nonempty) (htb : IsVonNBounded Real t) : exists e : E ≃ₜ E, e '' int
erior s = interior t ∧ e '' closure s = closure t ∧ e '' frontier s = frontier t
参数：hsc : Convex Real s；hsne : (interior s).Nonempty；hsb : IsVonNBounded Real s；h
st : Convex Real t；htne : (interior t).Nonempty；htb : IsVonNBounded Real t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_vadd`：∀ {α : Type u_2} {G : Type u_4} [inst : TopologicalSpace 
α] [inst_1 : AddGroup G] [inst_2 : AddAction G α]   [ContinuousConstVAdd G α] (c
 : …
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `image_gaugeRescaleHomeomorph_interior`：image_gaugeRescaleHomeomorph_inte
rior {s t : Set E} (hsc : Convex Real s) (hs₀ : s in 𝓝 0) (hsb : IsVonNBounded R
eal s) (htc : Convex Real t…
· 使用定理 `vadd_neg_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), g +ᵥ -g +ᵥ a = a
· 使用定理 `closure_vadd`：∀ {α : Type u_2} {G : Type u_4} [inst : TopologicalSpace α
] [inst_1 : AddGroup G] [inst_2 : AddAction G α]   [ContinuousConstVAdd G α] (c 
: …
· 使用定理 `image_gaugeRescaleHomeomorph_closure`：image_gaugeRescaleHomeomorph_closu
re {s t : Set E} (hsc : Convex Real s) (hs₀ : s in 𝓝 0) (hsb : IsVonNBounded Rea
l s) (htc : Convex Real t)…
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h

--- 原说明 ---
Given two convex bounded sets in a topological vector space with nonempty interi
ors,
there exists a homeomorphism of the ambient space
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.

In particular, if both `s` and `t` are open set or both `s` and `t` are closed s
ets,
then `e` maps `s` to `t`.
-/
theorem exists_homeomorph_image_eq {s t : Set E}
    (hsc : Convex ℝ s) (hsne : (interior s).Nonempty) (hsb : IsVonNBounded ℝ s)
    (hst : Convex ℝ t) (htne : (interior t).Nonempty) (htb : IsVonNBounded ℝ t) :
    ∃ e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t ∧
      e '' frontier s = frontier t := by
  rsuffices ⟨e, h₁, h₂⟩ : ∃ e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t
  · refine ⟨e, h₁, h₂, ?_⟩
    simp_rw [← closure_sdiff_interior, image_sdiff e.injective, h₁, h₂]
  rcases hsne with ⟨x, hx⟩
  rcases htne with ⟨y, hy⟩
  set h : E ≃ₜ E := by
    apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
      simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
  refine ⟨.trans (.addLeft (-x)) <| h.trans <| .addLeft y, ?_, ?_⟩
  · calc
      (fun a ↦ y + h (-x + a)) '' interior s = y +ᵥ h '' interior (-x +ᵥ s) := by
        simp_rw [interior_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_interior, interior_vadd, vadd_neg_vadd]
  · calc
      (fun a ↦ y + h (-x + a)) '' closure s = y +ᵥ h '' closure (-x +ᵥ s) := by
        simp_rw [closure_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_closure, closure_vadd, vadd_neg_vadd]

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `s` is a convex bounded set with a nonempty interior in a real normed space,
then there is a homeomorphism of the ambient space to itself
that sends the interior of `s` to the unit open ball
and the closure of `s` to the unit closed ball. -/
/-
**exists_homeomorph_image_interior_closure_frontier_eq_unitBall** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：exists_homeomorph_image_interior_closure_frontier_eq_unitBall {s : Set E} 
(hc : Convex Real s) (hne : (interior s).Nonempty) (hb : IsBounded s) : exists h
 : E ≃ₜ E, h '' interior s = ball 0 1 ∧ h '' closure s = closedBall 0 1 ∧ h '' f
rontier s = sphere 0 1
参数：hc : Convex Real s；hne : (interior s).Nonempty；hb : IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `frontier_ball`：frontier_ball (x : E) {r : Real} (hr : r != 0) : frontier
 (ball x r) = sphere x r
· 使用定理 `exists_homeomorph_image_eq`：exists_homeomorph_image_eq {s t : Set E} (hs
c : Convex Real s) (hsne : (interior s).Nonempty) (hsb : IsVonNBounded Real s) (
hst : Convex Rea…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NormedSpace.isVonNBounded_of_isBounded`：isVonNBounded_of_isBounded {s : 
Set E} (h : Bornology.IsBounded s) : Bornology.IsVonNBounded 𝕜 s
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `NormedSpace.isVonNBounded_ball`：isVonNBounded_ball (r : Real) : Bornolog
y.IsVonNBounded 𝕜 (Metric.ball (0 : E) r)

--- 原说明 ---
If `s` is a convex bounded set with a nonempty interior in a real normed space,
then there is a homeomorphism of the ambient space to itself
that sends the interior of `s` to the unit open ball
and the closure of `s` to the unit closed ball.
-/
theorem exists_homeomorph_image_interior_closure_frontier_eq_unitBall {s : Set E}
    (hc : Convex ℝ s) (hne : (interior s).Nonempty) (hb : IsBounded s) :
    ∃ h : E ≃ₜ E, h '' interior s = ball 0 1 ∧ h '' closure s = closedBall 0 1 ∧
      h '' frontier s = sphere 0 1 := by
  simpa [isOpen_ball.interior_eq, closure_ball, frontier_ball]
    using exists_homeomorph_image_eq hc hne (NormedSpace.isVonNBounded_of_isBounded _ hb)
    (convex_ball 0 1) (by simp [isOpen_ball.interior_eq]) (NormedSpace.isVonNBounded_ball _ _ _)
