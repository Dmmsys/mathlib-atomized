/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Basic

/-!
# (Semi)normed groups: basic theory

We prove basic properties of (semi)normed groups.

## Tags

normed group
-/

@[expose] public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b c d : E} {r r₁ r₂ : ℝ}

@[to_additive]
/-
**dist_eq_norm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ * b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedGroup E] (x 
y : E), dist x y = ‖x⁻¹ * y‖
-/
theorem dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ * b‖ :=
  SeminormedGroup.dist_eq _ _

@[to_additive]
/-
**dist_eq_norm_inv_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹ * a‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
-/
theorem dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹ * a‖ := by
  rw [dist_comm, dist_eq_norm_inv_mul]

@[to_additive of_forall_le_norm]
/-
**DiscreteTopology.of_forall_le_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : forall x : E, x !
= 1 -> r <= ‖x‖) : DiscreteTopology E
参数：hpos : 0 < r；hr : forall x : E, x != 1 -> r <= ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DiscreteTopology.of_forall_le_dist`：DiscreteTopology.of_forall_le_dist {
α} [PseudoMetricSpace α] {r : Real} (hpos : 0 < r) (hr : Pairwise (r <= dist · ·
 : α -> α -> Prop)) : Di…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
-/
lemma DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : ∀ x : E, x ≠ 1 → r ≤ ‖x‖) :
    DiscreteTopology E :=
  .of_forall_le_dist hpos fun x y hne ↦ by
    simp only [dist_eq_norm_inv_mul]
    exact hr _ (by simpa [inv_mul_eq_one] using hne)

@[to_additive (attr := simp)]
/-
**dist_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_one_right (a : E) : dist a 1 = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul'`：dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹
 * a‖
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem dist_one_right (a : E) : dist a 1 = ‖a‖ := by rw [dist_eq_norm_inv_mul', inv_one, one_mul]

@[to_additive]
/-
**inseparable_one_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_one_iff_norm {a : E} : Inseparable a 1 ↔ ‖a‖ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.inseparable_iff`：Metric.inseparable_iff {x y : α} : Inseparable x
 y ↔ dist x y = 0
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inseparable_one_iff_norm {a : E} : Inseparable a 1 ↔ ‖a‖ = 0 := by
  rw [Metric.inseparable_iff, dist_one_right]

@[to_additive]
/-
**dist_one_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_one_left (a : E) : dist 1 a = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
-/
lemma dist_one_left (a : E) : dist 1 a = ‖a‖ := by rw [dist_comm, dist_one_right]

@[to_additive (attr := simp)]
/-
**dist_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_one : dist (1 : E) = norm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `dist_one_left`：dist_one_left (a : E) : dist 1 a = ‖a‖
-/
lemma dist_one : dist (1 : E) = norm := funext dist_one_left

@[to_additive]
/-
**norm_div_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dist_one`：dist_one : dist (1 : E) = norm
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `dist_eq_norm_inv_mul'`：dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹
 * a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖ := by
  rw [← dist_one, dist_eq_norm_inv_mul, dist_eq_norm_inv_mul']
  simp

@[to_additive (attr := simp) norm_neg]
/-
**norm_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `norm_div_rev`：norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖
-/
theorem norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖ := by simpa using norm_div_rev 1 a

@[to_additive (attr := simp) norm_abs_zsmul]
/-
**norm_zpow_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_zpow_abs (a : E) (n : Int) : ‖a ^ |n|‖ = ‖a ^ n‖
参数：a : E；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
-/
theorem norm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖ = ‖a ^ n‖ := by
  rcases le_total 0 n with hn | hn <;> simp [hn, abs_of_nonneg, abs_of_nonpos]

@[to_additive (attr := simp) norm_natAbs_smul]
/-
**norm_pow_natAbs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_pow_natAbs (a : E) (n : Int) : ‖a ^ n.natAbs‖ = ‖a ^ n‖
参数：a : E；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `norm_zpow_abs`：norm_zpow_abs (a : E) (n : Int) : ‖a ^ |n|‖ = ‖a ^ n‖
-/
theorem norm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖ = ‖a ^ n‖ := by
  rw [← zpow_natCast, ← Int.abs_eq_natAbs, norm_zpow_abs]

@[to_additive norm_isUnit_zsmul]
/-
**norm_zpow_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_zpow_isUnit (a : E) {n : Int} (hn : IsUnit n) : ‖a ^ n‖ = ‖a‖
参数：a : E；hn : IsUnit n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pow_natAbs`：norm_pow_natAbs (a : E) (n : Int) : ‖a ^ n.natAbs‖ = ‖a
 ^ n‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.isUnit_iff_natAbs_eq`：isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem norm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖ = ‖a‖ := by
  rw [← norm_pow_natAbs, Int.isUnit_iff_natAbs_eq.mp hn, pow_one]

@[simp]
/-
**norm_units_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : Intˣ) (a : E) : ‖
n • a‖ = ‖a‖
参数：n : Intˣ；a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_isUnit_zsmul`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E
) {n : ℤ}, IsUnit n → ‖n • a‖ = ‖a‖
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem norm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖ = ‖a‖ :=
  norm_isUnit_zsmul a n.isUnit

open scoped symmDiff in
@[to_additive]
/-
**dist_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_mulIndicator (s t : Set α) (f : α -> E) (x : α) : dist (s.mulIndicato
r f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖
参数：s t : Set α；f : α -> E；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Set.apply_mulIndicator_symmDiff`：apply_mulIndicator_symmDiff {g : G -> β
} (hg : forall x, g x⁻¹ = g x) (s t : Set α) (f : α -> G) (x : α) : g (mulIndica
tor (s ∆ t) f x) = g …
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem dist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖ := by
  rw [dist_eq_norm_inv_mul, Set.apply_mulIndicator_symmDiff norm_inv']
  simp only [Set.mulIndicator, mul_ite, mul_one]
  split_ifs <;> simp

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le /-- **Triangle inequality** for the norm. -/]
/-
**norm_mul_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z

--- 原说明 ---
**Triangle inequality** for the norm.
-/
theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_inv_mul] using dist_triangle a⁻¹ 1 b

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le_of_le /-- **Triangle inequality** for the norm. -/]
/-
**norm_mul_le_of_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_mul_le_of_le' (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂) : ‖a₁ * a₂‖ <= r₁ +
 r₂
参数：h₁ : ‖a₁‖ <= r₁；h₂ : ‖a₂‖ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
**Triangle inequality** for the norm.
-/
theorem norm_mul_le_of_le' (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ + r₂ :=
  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₃_le /-- **Triangle inequality** for the norm. -/]
/-
**norm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClass α] (a b : 
α), ‖a * b‖ = ‖a‖ * ‖b‖
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormMulClass.norm_mul`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : Mul α}
 [self : NormMulClass α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖

--- 原说明 ---
**Triangle inequality** for the norm.
-/
lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₄_le /-- **Triangle inequality** for the norm. -/]
/-
**norm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClass α] (a b : 
α), ‖a * b‖ = ‖a‖ * ‖b‖
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormMulClass.norm_mul`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : Mul α}
 [self : NormMulClass α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖

--- 原说明 ---
**Triangle inequality** for the norm.
-/
lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
  norm_mul_le_of_le' norm_mul₃_le' le_rfl

@[to_additive]
/-
**norm_div_le_norm_div_add_norm_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_div_le_norm_div_add_norm_div (a b c : E) : ‖a / c‖ <= ‖a / b‖ + ‖b / 
c‖
参数：a b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
lemma norm_div_le_norm_div_add_norm_div (a b c : E) : ‖a / c‖ ≤ ‖a / b‖ + ‖b / c‖ := by
  simpa using norm_mul_le' (a / b) (b / c)

@[to_additive]
/-
**norm_le_norm_div_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_le_norm_div_add (a b : E) : ‖a‖ <= ‖a / b‖ + ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `norm_div_le_norm_div_add_norm_div`：norm_div_le_norm_div_add_norm_div (a 
b c : E) : ‖a / c‖ <= ‖a / b‖ + ‖b / c‖
-/
lemma norm_le_norm_div_add (a b : E) : ‖a‖ ≤ ‖a / b‖ + ‖b‖ := by
  simpa only [div_one] using norm_div_le_norm_div_add_norm_div a b 1

@[to_additive (attr := simp) norm_nonneg]
/-
**norm_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_nonneg' (a : E) : 0 <= ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
  rw [← dist_one_right]
  exact dist_nonneg

attribute [bound] norm_nonneg
attribute [grind .] norm_nonneg

@[to_additive (attr := simp) abs_norm]
/-
**abs_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_norm' (z : E) : |‖z‖| = ‖z‖
参数：z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _

@[to_additive (attr := simp) norm_zero]
/-
**norm_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_one' : ‖(1 : E)‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
-/
theorem norm_one' : ‖(1 : E)‖ = 0 := by rw [← dist_one_right, dist_self]

@[to_additive]
/-
**ne_one_of_norm_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_one_of_norm_ne_zero : ‖a‖ != 0 -> a != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_one_of_norm_ne_zero : ‖a‖ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact norm_one'

@[to_additive (attr := nontriviality) norm_of_subsingleton]
/-
**norm_of_subsingleton'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_of_subsingleton' [Subsingleton E] (a : E) : ‖a‖ = 0
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
-/
theorem norm_of_subsingleton' [Subsingleton E] (a : E) : ‖a‖ = 0 := by
  rw [Subsingleton.elim a 1, norm_one']

@[to_additive zero_lt_one_add_norm_sq]
/-
**zero_lt_one_add_norm_sq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ‖x‖ ^ 2
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
-/
theorem zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ‖x‖ ^ 2 := by
  positivity

@[to_additive]
/-
**norm_div_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_div_le (a b : E) : ‖a / b‖ <= ‖a‖ + ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
theorem norm_div_le (a b : E) : ‖a / b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [div_eq_mul_inv] using norm_mul_le' a b⁻¹

attribute [bound] norm_sub_le

@[to_additive]
/-
**norm_div_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_div_le_of_le {r₁ r₂ : Real} (H₁ : ‖a₁‖ <= r₁) (H₂ : ‖a₂‖ <= r₂) : ‖a₁
 / a₂‖ <= r₁ + r₂
参数：H₁ : ‖a₁‖ <= r₁；H₂ : ‖a₂‖ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_div_le`：norm_div_le (a b : E) : ‖a / b‖ <= ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem norm_div_le_of_le {r₁ r₂ : ℝ} (H₁ : ‖a₁‖ ≤ r₁) (H₂ : ‖a₂‖ ≤ r₂) : ‖a₁ / a₂‖ ≤ r₁ + r₂ :=
  (norm_div_le a₁ a₂).trans <| add_le_add H₁ H₂

@[to_additive dist_le_norm_add_norm]
/-
**dist_le_norm_add_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_norm_add_norm' (a b : E) : dist a b <= ‖a‖ + ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
theorem dist_le_norm_add_norm' (a b : E) : dist a b ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_inv_mul] using norm_mul_le' a⁻¹ b

@[to_additive]
/-
**abs_norm_sub_norm_le_norm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_norm_sub_norm_le_norm_inv_mul (a b : E) : |‖a‖ - ‖b‖| <= ‖a⁻¹ * b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `abs_dist_sub_le`：abs_dist_sub_le (x y z : α) : |dist x z - dist y z| <= 
dist x y
-/
theorem abs_norm_sub_norm_le_norm_inv_mul (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a⁻¹ * b‖ := by
  simpa [dist_eq_norm_inv_mul] using abs_dist_sub_le a b 1

@[to_additive]
/-
**norm_sub_norm_le_norm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_norm_le_norm_inv_mul (a b : E) : ‖a‖ - ‖b‖ <= ‖a⁻¹ * b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `abs_norm_sub_norm_le_norm_inv_mul`：abs_norm_sub_norm_le_norm_inv_mul (a 
b : E) : |‖a‖ - ‖b‖| <= ‖a⁻¹ * b‖
-/
theorem norm_sub_norm_le_norm_inv_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a⁻¹ * b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le_norm_inv_mul a b)

@[to_additive (attr := bound)]
/-
**norm_sub_le_norm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ <= ‖a * b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
theorem norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a * b‖ := by
  simpa using norm_mul_le' (a * b) (b⁻¹)

@[to_additive]
/-
**dist_norm_norm_le_norm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_norm_norm_le_norm_inv_mul (a b : E) : dist ‖a‖ ‖b‖ <= ‖a⁻¹ * b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_norm_sub_norm_le_norm_inv_mul`：abs_norm_sub_norm_le_norm_inv_mul (a 
b : E) : |‖a‖ - ‖b‖| <= ‖a⁻¹ * b‖
-/
theorem dist_norm_norm_le_norm_inv_mul (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a⁻¹ * b‖ :=
  abs_norm_sub_norm_le_norm_inv_mul a b

@[to_additive]
/-
**norm_le_norm_add_norm_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_norm_add_norm_div' (u v : E) : ‖u‖ <= ‖v‖ + ‖u / v‖
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
theorem norm_le_norm_add_norm_div' (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u / v‖ := by
  rw [add_comm]
  refine (norm_mul_le' _ _).trans_eq' ?_
  rw [div_mul_cancel]

@[to_additive]
/-
**norm_le_norm_add_norm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_norm_add_norm_inv_mul (u v : E) : ‖u‖ <= ‖v‖ + ‖u⁻¹ * v‖
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Group._zpow_trick_one`：_zpow_trick_one {G : Type*} [Group
 G] (a b : G) (m : Int) : a * b * b ^ m = a * b ^ (m + 1)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_le_norm_add_norm_inv_mul (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u⁻¹ * v‖ := by
  rw [add_comm, ← norm_inv' v, ← norm_inv' u]
  refine (norm_mul_le' _ _).trans_eq' ?_
  group

@[to_additive]
/-
**norm_le_norm_add_norm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_norm_add_norm_div (u v : E) : ‖v‖ <= ‖u‖ + ‖u / v‖
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_div_rev`：norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖
· 使用定理 `norm_le_norm_add_norm_div'`：norm_le_norm_add_norm_div' (u v : E) : ‖u‖ <
= ‖v‖ + ‖u / v‖
-/
theorem norm_le_norm_add_norm_div (u v : E) : ‖v‖ ≤ ‖u‖ + ‖u / v‖ := by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u

alias norm_le_insert' := norm_le_norm_add_norm_sub'
alias norm_le_insert := norm_le_norm_add_norm_sub

@[to_additive]
/-
**norm_le_mul_norm_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_mul_norm_add (u v : E) : ‖u‖ <= ‖u * v‖ + ‖v‖
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
· 使用定理 `norm_div_le`：norm_div_le (a b : E) : ‖a / b‖ <= ‖a‖ + ‖b‖
-/
theorem norm_le_mul_norm_add (u v : E) : ‖u‖ ≤ ‖u * v‖ + ‖v‖ :=
  calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ ≤ ‖u * v‖ + ‖v‖ := norm_div_le _ _

/-- An analogue of `norm_le_mul_norm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `norm_le_add_norm_add` for the addition from the left. -/]
/-
**norm_le_mul_norm_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_mul_norm_add' (u v : E) : ‖v‖ <= ‖u * v‖ + ‖u‖
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
An analogue of `norm_le_mul_norm_add` for the multiplication from the left.
-/
theorem norm_le_mul_norm_add' (u v : E) : ‖v‖ ≤ ‖u * v‖ + ‖u‖ :=
  calc
    ‖v‖ = ‖u⁻¹ * (u * v)‖ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ ≤ ‖u⁻¹‖ + ‖u * v‖ := norm_mul_le' u⁻¹ (u * v)
    _ = ‖u * v‖ + ‖u‖ := by rw [norm_inv', add_comm]

@[to_additive]
/-
**norm_mul_eq_norm_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x * y‖ = ‖y‖
参数：y : E；h : ‖x‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `norm_le_mul_norm_add'`：norm_le_mul_norm_add' (u v : E) : ‖v‖ <= ‖u * v‖ 
+ ‖u‖
-/
lemma norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x * y‖ = ‖y‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add' x y

@[to_additive]
/-
**norm_mul_eq_norm_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x * y‖ = ‖x‖
参数：x : E；h : ‖y‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
· 使用定理 `norm_le_mul_norm_add`：norm_le_mul_norm_add (u v : E) : ‖u‖ <= ‖u * v‖ + 
‖v‖
-/
lemma norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x * y‖ = ‖x‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add x y

@[to_additive]
/-
**norm_div_eq_norm_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_div_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x / y‖ = ‖y‖
参数：y : E；h : ‖x‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `norm_mul_eq_norm_right`：norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ 
= 0) : ‖x * y‖ = ‖y‖
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
-/
lemma norm_div_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x / y‖ = ‖y‖ := by
  rw [div_eq_mul_inv, norm_mul_eq_norm_right _ h, norm_inv']

@[to_additive]
/-
**norm_div_eq_norm_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_div_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x / y‖ = ‖x‖
参数：x : E；h : ‖y‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `norm_mul_eq_norm_left`：norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 
0) : ‖x * y‖ = ‖x‖
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
-/
lemma norm_div_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x / y‖ = ‖x‖ := by
  rw [div_eq_mul_inv, norm_mul_eq_norm_left]
  rwa [norm_inv']

@[to_additive]
/-
**ball_eq_norm_inv_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_eq_norm_inv_mul_lt (y : E) (ε : Real) : ball y ε = { x | ‖x⁻¹ * y‖ < 
ε }
参数：y : E；ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ball_eq_norm_inv_mul_lt (y : E) (ε : ℝ) : ball y ε = { x | ‖x⁻¹ * y‖ < ε } :=
  Set.ext fun a => by simp [dist_eq_norm_inv_mul]

@[to_additive]
/-
**ball_one_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_one_eq (r : Real) : ball (1 : E) r = { x | ‖x‖ < r }
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ball_one_eq (r : ℝ) : ball (1 : E) r = { x | ‖x‖ < r } :=
  Set.ext fun a => by simp

@[to_additive]
/-
**mem_ball_iff_norm_inv_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_ball_iff_norm_inv_mul_lt : b in ball a r ↔ ‖b⁻¹ * a‖ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball_iff_norm_inv_mul_lt : b ∈ ball a r ↔ ‖b⁻¹ * a‖ < r := by
  rw [mem_ball, dist_eq_norm_inv_mul]

@[to_additive]
/-
**mem_ball_iff_norm_inv_mul_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_ball_iff_norm_inv_mul_lt' : b in ball a r ↔ ‖a⁻¹ * b‖ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball'`：mem_ball' : y in ball x ε ↔ dist x y < ε
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball_iff_norm_inv_mul_lt' : b ∈ ball a r ↔ ‖a⁻¹ * b‖ < r := by
  rw [mem_ball', dist_eq_norm_inv_mul]

@[to_additive]
/-
**mem_ball_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_ball_one_iff : a in ball (1 : E) r ↔ ‖a‖ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ‖a‖ < r := by rw [mem_ball, dist_one_right]

@[to_additive]
/-
**mem_closedBall_iff_norm_inv_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closedBall_iff_norm_inv_mul_le : b in closedBall a r ↔ ‖b⁻¹ * a‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall_iff_norm_inv_mul_le : b ∈ closedBall a r ↔ ‖b⁻¹ * a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm_inv_mul]

@[to_additive]
/-
**mem_closedBall_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closedBall_one_iff : a in closedBall (1 : E) r ↔ ‖a‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall_one_iff : a ∈ closedBall (1 : E) r ↔ ‖a‖ ≤ r := by
  rw [mem_closedBall, dist_one_right]

@[to_additive]
/-
**mem_closedBall_iff_norm_inv_mul_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closedBall_iff_norm_inv_mul_le' : b in closedBall a r ↔ ‖a⁻¹ * b‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall'`：mem_closedBall' : y in closedBall x ε ↔ dist x y
 <= ε
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall_iff_norm_inv_mul_le' : b ∈ closedBall a r ↔ ‖a⁻¹ * b‖ ≤ r := by
  rw [mem_closedBall', dist_eq_norm_inv_mul]

@[to_additive norm_le_of_mem_closedBall]
/-
**norm_le_of_mem_closedBall'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_of_mem_closedBall' (h : b in closedBall a r) : ‖b‖ <= ‖a‖ + r
参数：h : b in closedBall a r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_le_norm_add_norm_inv_mul`：norm_le_norm_add_norm_inv_mul (u v : E) :
 ‖u‖ <= ‖v‖ + ‖u⁻¹ * v‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closedBall_iff_norm_inv_mul_le`：mem_closedBall_iff_norm_inv_mul_le :
 b in closedBall a r ↔ ‖b⁻¹ * a‖ <= r
-/
theorem norm_le_of_mem_closedBall' (h : b ∈ closedBall a r) : ‖b‖ ≤ ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans (by simp [mem_closedBall_iff_norm_inv_mul_le.1 h])

@[to_additive norm_le_norm_add_const_of_dist_le]
/-
**norm_le_norm_add_const_of_dist_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_norm_add_const_of_dist_le' : dist a b <= r -> ‖a‖ <= ‖b‖ + r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_le_of_mem_closedBall'`：norm_le_of_mem_closedBall' (h : b in closedB
all a r) : ‖b‖ <= ‖a‖ + r
-/
theorem norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r :=
  norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]
/-
**norm_lt_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_lt_of_mem_ball' (h : b in ball a r) : ‖b‖ < ‖a‖ + r
参数：h : b in ball a r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `norm_le_norm_add_norm_inv_mul`：norm_le_norm_add_norm_inv_mul (u v : E) :
 ‖u‖ <= ‖v‖ + ‖u⁻¹ * v‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_iff_norm_inv_mul_lt`：mem_ball_iff_norm_inv_mul_lt : b in ball a
 r ↔ ‖b⁻¹ * a‖ < r
-/
theorem norm_lt_of_mem_ball' (h : b ∈ ball a r) : ‖b‖ < ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans_lt (by simp [mem_ball_iff_norm_inv_mul_lt.1 h])

@[to_additive]
/-
**norm_div_sub_norm_div_le_norm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ <= ‖u / 
v‖
参数：u v w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ ≤ ‖u / v‖ := by
  simpa using norm_mul_le' (u / v) (v / w)

@[to_additive norm_add_sub_norm_sub_le_two_mul]
/-
**norm_mul_sub_norm_div_le_two_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_mul_sub_norm_div_le_two_mul {E : Type*} [SeminormedGroup E] (u v : E)
 : ‖u * v‖ - ‖u / v‖ <= 2 * ‖v‖
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `norm_mul₃_le'`：norm_mul₃_le' : ‖a * b * c‖ <= ‖a‖ + ‖b‖ + ‖c‖
-/
lemma norm_mul_sub_norm_div_le_two_mul {E : Type*} [SeminormedGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * ‖v‖ := by
  simpa [-tsub_le_iff_right, tsub_le_iff_left, two_mul, add_assoc]
    using norm_mul₃_le' (a := (u / v)) (b := v) (c := v)

@[to_additive norm_add_sub_norm_sub_le_two_mul_min]
/-
**norm_mul_sub_norm_div_le_two_mul_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_mul_sub_norm_div_le_two_mul_min {E : Type*} [SeminormedCommGroup E] (
u v : E) : ‖u * v‖ - ‖u / v‖ <= 2 * min ‖u‖ ‖v‖
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_min_of_nonneg`：mul_min_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * min b c = min (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `norm_div_rev`：norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `norm_mul_sub_norm_div_le_two_mul`：norm_mul_sub_norm_div_le_two_mul {E : 
Type*} [SeminormedGroup E] (u v : E) : ‖u * v‖ - ‖u / v‖ <= 2 * ‖v‖
-/
lemma norm_mul_sub_norm_div_le_two_mul_min {E : Type*} [SeminormedCommGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * min ‖u‖ ‖v‖ := by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ (norm_mul_sub_norm_div_le_two_mul u v)
  rw [norm_div_rev, mul_comm]
  exact norm_mul_sub_norm_div_le_two_mul _ _

-- Higher priority to fire before `mem_sphere`.
@[to_additive]
/-
**mem_sphere_iff_norm_inv_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_sphere_iff_norm_inv_mul_eq : b in sphere a r ↔ ‖b⁻¹ * a‖ = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sphere_iff_norm_inv_mul_eq : b ∈ sphere a r ↔ ‖b⁻¹ * a‖ = r := by
  simp [dist_eq_norm_inv_mul]

@[to_additive] -- `simp` can prove this
/-
**mem_sphere_one_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_sphere_one_iff_norm : a in sphere (1 : E) r ↔ ‖a‖ = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ‖a‖ = r := by simp

@[to_additive (attr := simp) norm_eq_of_mem_sphere]
/-
**norm_eq_of_mem_sphere'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ‖(x : E)‖ = r
参数：x : sphere (1 : E) r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_sphere_one_iff_norm`：mem_sphere_one_iff_norm : a in sphere (1 : E) r
 ↔ ‖a‖ = r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ‖(x : E)‖ = r :=
  mem_sphere_one_iff_norm.mp x.2

@[to_additive]
/-
**ne_one_of_mem_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_one_of_mem_sphere (hr : r != 0) (x : sphere (1 : E) r) : (x : E) != 1
参数：hr : r != 0；x : sphere (1 : E) r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_one_of_norm_ne_zero`：ne_one_of_norm_ne_zero : ‖a‖ != 0 -> a != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_of_mem_sphere'`：norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : 
‖(x : E)‖ = r
-/
theorem ne_one_of_mem_sphere (hr : r ≠ 0) (x : sphere (1 : E) r) : (x : E) ≠ 1 :=
  ne_one_of_norm_ne_zero <| by rwa [norm_eq_of_mem_sphere' x]

@[to_additive ne_zero_of_mem_unit_sphere]
/-
**ne_one_of_mem_unit_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) != 1
参数：x : sphere (1 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_one_of_mem_sphere`：ne_one_of_mem_sphere (hr : r != 0) (x : sphere (1 
: E) r) : (x : E) != 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) ≠ 1 :=
  ne_one_of_mem_sphere one_ne_zero _

variable (E)

/-- The norm of a seminormed group as a group seminorm. -/
@[to_additive /-- The norm of a seminormed group as an additive group seminorm. -/]
/-
**normGroupSeminorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normGroupSeminorm : GroupSeminorm E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖

--- 原说明 ---
The norm of a seminormed group as a group seminorm.
-/
def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩

@[to_additive (attr := simp)]
/-
**coe_normGroupSeminorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_normGroupSeminorm : ⇑(normGroupSeminorm E) = norm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_normGroupSeminorm : ⇑(normGroupSeminorm E) = norm :=
  rfl

variable {E}

@[to_additive]
/-
**NormedGroup.tendsto_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedGroup.tendsto_nhds_one {f : α -> E} {l : Filter α} : Tendsto f l (𝓝 
1) ↔ forall ε > 0, forallᶠ x in l, ‖f x‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem NormedGroup.tendsto_nhds_one {f : α → E} {l : Filter α} :
    Tendsto f l (𝓝 1) ↔ ∀ ε > 0, ∀ᶠ x in l, ‖f x‖ < ε :=
  Metric.tendsto_nhds.trans <| by simp only [dist_one_right]

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.tendsto_nhds_one := NormedGroup.tendsto_nhds_one

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.tendsto_nhds_zero := NormedAddGroup.tendsto_nhds_zero

@[to_additive]
/-
**NormedGroup.tendsto_nhds_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedGroup.tendsto_nhds_nhds {f : E -> F} {x : E} {y : F} : Tendsto f (𝓝 
x) (𝓝 y) ↔ forall ε > 0, exists δ > 0, forall x', ‖x'⁻¹ * x‖ < δ -> ‖(f x')⁻¹ * 
y‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem NormedGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x'⁻¹ * x‖ < δ → ‖(f x')⁻¹ * y‖ < ε := by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_inv_mul]

@[to_additive]
/-
**NormedGroup.nhds_basis_norm_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedGroup.nhds_basis_norm_lt (x : E) : (𝓝 x).HasBasis (fun ε : Real => 0
 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε }
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
-/
theorem NormedGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε } := by
  simp_rw [← ball_eq_norm_inv_mul_lt]
  exact Metric.nhds_basis_ball

@[to_additive]
/-
**NormedGroup.nhds_one_basis_norm_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedGroup.nhds_one_basis_norm_lt : (𝓝 (1 : E)).HasBasis (fun ε : Real =>
 0 < ε) fun ε => { y | ‖y‖ < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NormedGroup.nhds_basis_norm_lt`：NormedGroup.nhds_basis_norm_lt (x : E) :
 (𝓝 x).HasBasis (fun ε : Real => 0 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε }
-/
theorem NormedGroup.nhds_one_basis_norm_lt :
    (𝓝 (1 : E)).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y‖ < ε } := by
  convert! NormedGroup.nhds_basis_norm_lt (1 : E) using 1
  simp

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.nhds_one_basis_norm_lt := NormedGroup.nhds_one_basis_norm_lt

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.nhds_zero_basis_norm_lt := NormedAddGroup.nhds_zero_basis_norm_lt

@[to_additive]
/-
**NormedGroup.uniformity_basis_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedGroup.uniformity_basis_dist : (𝓤 E).HasBasis (fun ε : Real => 0 < ε)
 fun ε => { p : E × E | ‖p.fst⁻¹ * p.snd‖ < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
theorem NormedGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst⁻¹ * p.snd‖ < ε } := by
  convert Metric.uniformity_basis_dist (α := E)
  simp [dist_eq_norm_inv_mul]

open Finset

variable [FunLike 𝓕 E F]

section NNNorm

-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SeminormedGroup.toNNNorm : NNNorm E :=
  ⟨fun a => .mk ‖a‖ (norm_nonneg' a)⟩

@[to_additive (attr := simp, norm_cast) coe_nnnorm]
/-
**coe_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_nnnorm' (a : E) : (‖a‖₊ : Real) = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nnnorm' (a : E) : (‖a‖₊ : ℝ) = ‖a‖ := rfl

@[to_additive (attr := simp) coe_comp_nnnorm]
/-
**coe_comp_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_comp_nnnorm' : (toReal : Real>=0 -> Real) ∘ (nnnorm : E -> Real>=0) = 
norm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp_nnnorm' : (toReal : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm :=
  rfl

@[to_additive (attr := simp) norm_toNNReal]
/-
**norm_toNNReal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
theorem norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊ :=
  @Real.toNNReal_coe ‖a‖₊

@[to_additive (attr := simp) toReal_enorm]
/-
**toReal_enorm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toReal_enorm' (x : E) : ‖x‖ₑ.toReal = ‖x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toReal_enorm' (x : E) : ‖x‖ₑ.toReal = ‖x‖ := by simp [enorm]

@[to_additive (attr := simp) ofReal_norm]
/-
**ofReal_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.ofReal_eq_coe_nnreal`：ofReal_eq_coe_nnreal {x : Real} (h : 0 <= 
x) : ENNReal.ofReal x = ofNNReal (NNReal.mk x h)
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
lemma ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := ENNReal.ofReal_eq_coe_nnreal _

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm := ofReal_norm

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm' := ofReal_norm'

@[to_additive enorm_eq_iff_norm_eq]
/-
**enorm'_eq_iff_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : SeminormedGroup E] [inst_1 : Semin
ormedGroup F] {x : E} {y : F},   ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.toNNReal_eq_toNNReal_iff`：toNNReal_eq_toNNReal_iff {r p : Real} (hr
 : 0 <= r) (hp : 0 <= p) : toNNReal r = toNNReal p ↔ r = p
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
-/
theorem enorm'_eq_iff_norm_eq {x : E} {y : F} : ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h ↦ ?_, fun h ↦ by congr⟩
  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)

@[to_additive enorm_le_iff_norm_le]
/-
**enorm'_le_iff_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : SeminormedGroup E] [inst_1 : Semin
ormedGroup F] {x : E} {y : F},   ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖ ≤ ‖y‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
theorem enorm'_le_iff_norm_le {x : E} {y : F} : ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖ ≤ ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h ↦ ?_, fun h ↦ by gcongr⟩
  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
  exact h

@[to_additive]
/-
**nndist_eq_nnnorm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_eq_nnnorm_inv_mul (a b : E) : nndist a b = ‖a⁻¹ * b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
-/
theorem nndist_eq_nnnorm_inv_mul (a b : E) : nndist a b = ‖a⁻¹ * b‖₊ :=
  NNReal.eq <| dist_eq_norm_inv_mul _ _

@[to_additive (attr := simp) nnnorm_neg]
/-
**nnnorm_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
-/
theorem nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inv' a

@[to_additive (attr := simp)]
/-
**nndist_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_one_right (a : E) : nndist a 1 = ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_eq_nnnorm_inv_mul`：nndist_eq_nnnorm_inv_mul (a b : E) : nndist a 
b = ‖a⁻¹ * b‖₊
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `nnnorm_inv'`：nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_one_right (a : E) : nndist a 1 = ‖a‖₊ := by
  simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]
/-
**edist_one_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：edist_one_right (a : E) : edist a 1 = ‖a‖ₑ
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `nndist_one_right`：nndist_one_right (a : E) : nndist a 1 = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_one_right (a : E) : edist a 1 = ‖a‖ₑ := by simp [edist_nndist, nndist_one_right, enorm]

@[to_additive (attr := simp) nnnorm_zero]
/-
**nnnorm_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_one' : ‖(1 : E)‖₊ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
-/
theorem nnnorm_one' : ‖(1 : E)‖₊ = 0 := NNReal.eq norm_one'

@[to_additive]
/-
**ne_one_of_nnnorm_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ != 0 -> a != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `nnnorm_one'`：nnnorm_one' : ‖(1 : E)‖₊ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]
/-
**nnnorm_mul_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_mul_le' (a b : E) : ‖a * b‖₊ <= ‖a‖₊ + ‖b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
theorem nnnorm_mul_le' (a b : E) : ‖a * b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_mul_le' a b

@[to_additive norm_nsmul_le]
/-
**norm_pow_le_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_5} [inst : SeminormedGroup E] {a : E} {n : ℕ}, ‖a ^ n‖ ≤ ↑n 
* ‖a‖
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_pow_le_mul_norm : ∀ {n : ℕ}, ‖a ^ n‖ ≤ n * ‖a‖
  | 0 => by simp
  | n + 1 => by simpa [pow_succ, add_mul] using norm_mul_le_of_le' norm_pow_le_mul_norm le_rfl

@[to_additive nnnorm_nsmul_le]
/-
**nnnorm_pow_le_mul_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_pow_le_mul_norm {n : Nat} : ‖a ^ n‖₊ <= n * ‖a‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `norm_pow_le_mul_norm`：∀ {E : Type u_5} [inst : SeminormedGroup E] {a : E
} {n : ℕ}, ‖a ^ n‖ ≤ ↑n * ‖a‖
-/
lemma nnnorm_pow_le_mul_norm {n : ℕ} : ‖a ^ n‖₊ ≤ n * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using! norm_pow_le_mul_norm

@[to_additive (attr := simp) nnnorm_abs_zsmul]
/-
**nnnorm_zpow_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_zpow_abs (a : E) (n : Int) : ‖a ^ |n|‖₊ = ‖a ^ n‖₊
参数：a : E；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_zpow_abs`：norm_zpow_abs (a : E) (n : Int) : ‖a ^ |n|‖ = ‖a ^ n‖
-/
theorem nnnorm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_zpow_abs a n

@[to_additive (attr := simp) nnnorm_natAbs_smul]
/-
**nnnorm_pow_natAbs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_pow_natAbs (a : E) (n : Int) : ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊
参数：a : E；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_pow_natAbs`：norm_pow_natAbs (a : E) (n : Int) : ‖a ^ n.natAbs‖ = ‖a
 ^ n‖
-/
theorem nnnorm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_pow_natAbs a n

@[to_additive nnnorm_isUnit_zsmul]
/-
**nnnorm_zpow_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_zpow_isUnit (a : E) {n : Int} (hn : IsUnit n) : ‖a ^ n‖₊ = ‖a‖₊
参数：a : E；hn : IsUnit n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_zpow_isUnit`：norm_zpow_isUnit (a : E) {n : Int} (hn : IsUnit n) : ‖
a ^ n‖ = ‖a‖
-/
theorem nnnorm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_zpow_isUnit a hn

@[simp]
/-
**nnnorm_units_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : Intˣ) (a : E) :
 ‖n • a‖₊ = ‖a‖₊
参数：n : Intˣ；a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_isUnit_zsmul`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E
) {n : ℤ}, IsUnit n → ‖n • a‖ = ‖a‖
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem nnnorm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_isUnit_zsmul a n.isUnit

@[to_additive (attr := simp)]
/-
**nndist_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_one_left (a : E) : nndist 1 a = ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_eq_nnnorm_inv_mul`：nndist_eq_nnnorm_inv_mul (a b : E) : nndist a 
b = ‖a⁻¹ * b‖₊
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_one_left (a : E) : nndist 1 a = ‖a‖₊ := by simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]
/-
**edist_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_one_left (a : E) : edist 1 a = ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `nndist_one_left`：nndist_one_left (a : E) : nndist 1 a = ‖a‖₊
-/
theorem edist_one_left (a : E) : edist 1 a = ‖a‖₊ := by
  rw [edist_nndist, nndist_one_left]

open scoped symmDiff in
@[to_additive]
/-
**nndist_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_mulIndicator (s t : Set α) (f : α -> E) (x : α) : nndist (s.mulIndi
cator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊
参数：s t : Set α；f : α -> E；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_mulIndicator`：dist_mulIndicator (s t : Set α) (f : α -> E) (x : α) 
: dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖
-/
theorem nndist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ :=
  NNReal.eq <| dist_mulIndicator s t f x

@[to_additive]
/-
**nnnorm_div_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_div_le (a b : E) : ‖a / b‖₊ <= ‖a‖₊ + ‖b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `norm_div_le`：norm_div_le (a b : E) : ‖a / b‖ <= ‖a‖ + ‖b‖
-/
theorem nnnorm_div_le (a b : E) : ‖a / b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_div_le _ _

@[to_additive]
/-
**enorm_div_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_div_le : ‖a / b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nnnorm_div_le`：nnnorm_div_le (a b : E) : ‖a / b‖₊ <= ‖a‖₊ + ‖b‖₊
-/
lemma enorm_div_le : ‖a / b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  simpa [enorm, ← ENNReal.coe_add] using nnnorm_div_le a b

@[to_additive]
/-
**nndist_nnnorm_nnnorm_le_nnnorm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_nnnorm_nnnorm_le_nnnorm_inv_mul (a b : E) : nndist ‖a‖₊ ‖b‖₊ <= ‖a⁻
¹ * b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `dist_norm_norm_le_norm_inv_mul`：dist_norm_norm_le_norm_inv_mul (a b : E)
 : dist ‖a‖ ‖b‖ <= ‖a⁻¹ * b‖
-/
theorem nndist_nnnorm_nnnorm_le_nnnorm_inv_mul (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a⁻¹ * b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le_norm_inv_mul a b

@[to_additive]
/-
**nnnorm_le_nnnorm_add_nnnorm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ‖b‖₊ <= ‖a‖₊ + ‖a / b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_le_norm_add_norm_div`：norm_le_norm_add_norm_div (u v : E) : ‖v‖ <= 
‖u‖ + ‖u / v‖
-/
theorem nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ‖b‖₊ ≤ ‖a‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div _ _

@[to_additive]
/-
**nnnorm_le_nnnorm_add_nnnorm_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ‖a‖₊ <= ‖b‖₊ + ‖a / b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_le_norm_add_norm_div'`：norm_le_norm_add_norm_div' (u v : E) : ‖u‖ <
= ‖v‖ + ‖u / v‖
-/
theorem nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ‖a‖₊ ≤ ‖b‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div' _ _

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]
/-
**nnnorm_le_mul_nnnorm_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_le_mul_nnnorm_add (a b : E) : ‖a‖₊ <= ‖a * b‖₊ + ‖b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_le_mul_norm_add`：norm_le_mul_norm_add (u v : E) : ‖u‖ <= ‖u * v‖ + 
‖v‖
-/
theorem nnnorm_le_mul_nnnorm_add (a b : E) : ‖a‖₊ ≤ ‖a * b‖₊ + ‖b‖₊ :=
  norm_le_mul_norm_add _ _

/-- An analogue of `nnnorm_le_mul_nnnorm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `nnnorm_le_add_nnnorm_add` for the addition from the left. -/]
/-
**nnnorm_le_mul_nnnorm_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_le_mul_nnnorm_add' (a b : E) : ‖b‖₊ <= ‖a * b‖₊ + ‖a‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_le_mul_norm_add'`：norm_le_mul_norm_add' (u v : E) : ‖v‖ <= ‖u * v‖ 
+ ‖u‖

--- 原说明 ---
An analogue of `nnnorm_le_mul_nnnorm_add` for the multiplication from the left.
-/
theorem nnnorm_le_mul_nnnorm_add' (a b : E) : ‖b‖₊ ≤ ‖a * b‖₊ + ‖a‖₊ :=
  norm_le_mul_norm_add' _ _

@[to_additive]
/-
**nnnorm_mul_eq_nnnorm_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_mul_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x * y‖₊ = ‖y‖
₊
参数：y : E；h : ‖x‖₊ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `norm_mul_eq_norm_right`：norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ 
= 0) : ‖x * y‖ = ‖y‖
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma nnnorm_mul_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x * y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
/-
**nnnorm_mul_eq_nnnorm_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_mul_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x * y‖₊ = ‖x‖₊
参数：x : E；h : ‖y‖₊ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `norm_mul_eq_norm_left`：norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 
0) : ‖x * y‖ = ‖x‖
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma nnnorm_mul_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x * y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_left _ <| congr_arg NNReal.toReal h

@[to_additive]
/-
**nnnorm_div_eq_nnnorm_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_div_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x / y‖₊ = ‖y‖
₊
参数：y : E；h : ‖x‖₊ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `norm_div_eq_norm_right`：norm_div_eq_norm_right {x : E} (y : E) (h : ‖x‖ 
= 0) : ‖x / y‖ = ‖y‖
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma nnnorm_div_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x / y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_div_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
/-
**nnnorm_div_eq_nnnorm_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_div_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x / y‖₊ = ‖x‖₊
参数：x : E；h : ‖y‖₊ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `norm_div_eq_norm_left`：norm_div_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 
0) : ‖x / y‖ = ‖x‖
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma nnnorm_div_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x / y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_div_eq_norm_left _ <| congr_arg NNReal.toReal h

/-- The nonnegative norm seen as an `ENNReal` and then as a `Real` is equal to the norm. -/
@[to_additive toReal_coe_nnnorm /-- The nonnegative norm seen as an `ENNReal` and
then as a `Real` is equal to the norm. -/]
/-
**toReal_coe_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toReal_coe_nnnorm' (a : E) : (‖a‖₊ : Real>=0∞).toReal = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_coe_nnnorm' (a : E) : (‖a‖₊ : ℝ≥0∞).toReal = ‖a‖ := rfl

open scoped symmDiff in
@[to_additive]
/-
**edist_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_mulIndicator (s t : Set α) (f : α -> E) (x : α) : edist (s.mulIndica
tor f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊
参数：s t : Set α；f : α -> E；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `nndist_mulIndicator`：nndist_mulIndicator (s t : Set α) (f : α -> E) (x :
 α) : nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f
 x‖₊
-/
theorem edist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    edist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ := by
  rw [edist_nndist, nndist_mulIndicator]

@[to_additive nontrivialTopology_iff_exists_nnnorm_ne_zero]
/-
**nontrivialTopology_iff_exists_nnnorm_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivialTopology_iff_exists_nnnorm_ne_zero' : NontrivialTopology E ↔ exi
sts x : E, ‖x‖₊ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nndist_eq_nnnorm_inv_mul`：nndist_eq_nnnorm_inv_mul (a b : E) : nndist a 
b = ‖a⁻¹ * b‖₊
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `nnnorm_inv'`：nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊
-/
theorem nontrivialTopology_iff_exists_nnnorm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖₊ ≠ 0 := by
  simp_rw [TopologicalSpace.nontrivial_iff_exists_not_inseparable, Metric.inseparable_iff_nndist,
    nndist_eq_nnnorm_inv_mul]
  exact ⟨fun ⟨x, y, hxy⟩ => ⟨_, hxy⟩, fun ⟨x, hx⟩ => ⟨x, 1, by simpa using hx⟩⟩

@[to_additive indiscreteTopology_iff_forall_nnnorm_eq_zero]
/-
**indiscreteTopology_iff_forall_nnnorm_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indiscreteTopology_iff_forall_nnnorm_eq_zero' : IndiscreteTopology E ↔ for
all x : E, ‖x‖₊ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `nontrivialTopology_iff_exists_nnnorm_ne_zero'`：nontrivialTopology_iff_ex
ists_nnnorm_ne_zero' : NontrivialTopology E ↔ exists x : E, ‖x‖₊ != 0
-/
theorem indiscreteTopology_iff_forall_nnnorm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖₊ = 0 := by
  simpa using nontrivialTopology_iff_exists_nnnorm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_nnnorm_ne_zero]
/-
**exists_nnnorm_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nnnorm_ne_zero' [NontrivialTopology E] : exists x : E, ‖x‖₊ != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nontrivialTopology_iff_exists_nnnorm_ne_zero'`：nontrivialTopology_iff_ex
ists_nnnorm_ne_zero' : NontrivialTopology E ↔ exists x : E, ‖x‖₊ != 0
-/
theorem exists_nnnorm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖₊ ≠ 0 :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]
/-
**IndiscreteTopology.nnnorm_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IndiscreteTopology.nnnorm_eq_zero' [IndiscreteTopology E] : forall x : E, 
‖x‖₊ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `indiscreteTopology_iff_forall_nnnorm_eq_zero'`：indiscreteTopology_iff_fo
rall_nnnorm_eq_zero' : IndiscreteTopology E ↔ forall x : E, ‖x‖₊ = 0
-/
theorem IndiscreteTopology.nnnorm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖₊ = 0 :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_nnnorm_ne_zero]
  NontrivialTopology.of_exists_nnnorm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_nnnorm_eq_zero]
  IndiscreteTopology.of_forall_nnnorm_eq_zero'

@[to_additive nontrivialTopology_iff_exists_norm_ne_zero]
/-
**nontrivialTopology_iff_exists_norm_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivialTopology_iff_exists_norm_ne_zero' : NontrivialTopology E ↔ exist
s x : E, ‖x‖ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nontrivialTopology_iff_exists_norm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖ ≠ 0 := by
  simp [nontrivialTopology_iff_exists_nnnorm_ne_zero', ← NNReal.ne_iff]

@[to_additive indiscreteTopology_iff_forall_norm_eq_zero]
/-
**indiscreteTopology_iff_forall_norm_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indiscreteTopology_iff_forall_norm_eq_zero' : IndiscreteTopology E ↔ foral
l x : E, ‖x‖ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `nontrivialTopology_iff_exists_norm_ne_zero'`：nontrivialTopology_iff_exis
ts_norm_ne_zero' : NontrivialTopology E ↔ exists x : E, ‖x‖ != 0
-/
theorem indiscreteTopology_iff_forall_norm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖ = 0 := by
  simpa using nontrivialTopology_iff_exists_norm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_norm_ne_zero]
/-
**exists_norm_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_norm_ne_zero' [NontrivialTopology E] : exists x : E, ‖x‖ != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nontrivialTopology_iff_exists_norm_ne_zero'`：nontrivialTopology_iff_exis
ts_norm_ne_zero' : NontrivialTopology E ↔ exists x : E, ‖x‖ != 0
-/
theorem exists_norm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖ ≠ 0 :=
  nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]
/-
**IndiscreteTopology.norm_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IndiscreteTopology.norm_eq_zero' [IndiscreteTopology E] : forall x : E, ‖x
‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `indiscreteTopology_iff_forall_norm_eq_zero'`：indiscreteTopology_iff_fora
ll_norm_eq_zero' : IndiscreteTopology E ↔ forall x : E, ‖x‖ = 0
-/
theorem IndiscreteTopology.norm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖ = 0 :=
  indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_norm_ne_zero]
  NontrivialTopology.of_exists_norm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_norm_eq_zero]
  IndiscreteTopology.of_forall_norm_eq_zero'

end NNNorm

section ENorm

@[to_additive (attr := simp) enorm_zero]
/-
**enorm_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E] : ‖(1 : 
E)‖ₑ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ESeminormedMonoid.enorm_zero`：∀ {E : Type u_8} {inst : TopologicalSpace 
E} [self : ESeminormedMonoid E], ‖1‖ₑ = 0
-/
lemma enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E] : ‖(1 : E)‖ₑ = 0 := by
  rw [ESeminormedMonoid.enorm_zero]

@[to_additive exists_enorm_lt]
/-
**exists_enorm_lt'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_enorm_lt' (E : Type*) [TopologicalSpace E] [ESeminormedMonoid E] [h
bot : NeBot (𝓝[!=] (1 : E))] {c : Real>=0∞} (hc : c != 0) : exists x != (1 : E),
 ‖x‖ₑ < c
参数：E : Type*；𝓝[!=] (1 : E)；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.frequently_iff_neBot`：frequently_iff_neBot {l : Filter α} {p : α 
-> Prop} : (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x})
· 使用定理 `Filter.Tendsto.eventually_lt_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `ContinuousENorm.continuous_enorm`：∀ {E : Type u_8} {inst : TopologicalSp
ace E} [self : ContinuousENorm E], Continuous enorm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_one'`：enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMono
id E] : ‖(1 : E)‖ₑ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_enorm_lt' (E : Type*) [TopologicalSpace E] [ESeminormedMonoid E]
    [hbot : NeBot (𝓝[≠] (1 : E))] {c : ℝ≥0∞} (hc : c ≠ 0) : ∃ x ≠ (1 : E), ‖x‖ₑ < c :=
  frequently_iff_neBot.mpr hbot |>.and_eventually
    (ContinuousENorm.continuous_enorm.tendsto' 1 0 (by simp) |>.eventually_lt_const hc.bot_lt)
    |>.exists

@[to_additive (attr := simp) enorm_neg]
/-
**enorm_inv'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_inv'`：nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ := by simp [enorm]

@[to_additive]
/-
**edist_eq_enorm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_eq_enorm_inv_mul (a b : E) : edist a b = ‖a⁻¹ * b‖ₑ
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用引理 `ofReal_norm'`：ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ
-/
theorem edist_eq_enorm_inv_mul (a b : E) : edist a b = ‖a⁻¹ * b‖ₑ := by
  rw [edist_dist, dist_eq_norm_inv_mul, ofReal_norm']

@[deprecated (since := "2026-02-11")] alias edist_one_eq_enorm := edist_one_right

@[deprecated (since := "2026-02-11")] alias edist_zero_eq_enorm := edist_zero_right

@[to_additive]
/-
**enorm_div_rev** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_div_rev {E : Type*} [SeminormedGroup E] (a b : E) : ‖a / b‖ₑ = ‖b / 
a‖ₑ
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `enorm_inv'`：enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
lemma enorm_div_rev {E : Type*} [SeminormedGroup E] (a b : E) : ‖a / b‖ₑ = ‖b / a‖ₑ := by
  rw [← enorm_inv', inv_div]

@[to_additive]
/-
**mem_eball_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_eball_one_iff {r : Real>=0∞} : a in eball 1 r ↔ ‖a‖ₑ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用引理 `edist_one_right`：edist_one_right (a : E) : edist a 1 = ‖a‖ₑ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eball_one_iff {r : ℝ≥0∞} : a ∈ eball 1 r ↔ ‖a‖ₑ < r := by
  rw [Metric.mem_eball, edist_one_right]

@[deprecated (since := "2026-01-24")]
alias mem_emetric_ball_zero_iff := mem_eball_zero_iff

@[to_additive existing, deprecated (since := "2026-01-24")]
alias mem_emetric_ball_one_iff := mem_eball_one_iff

end ENorm

section ESeminormedMonoid

variable {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E]

@[to_additive enorm_add_le]
/-
**enorm_mul_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_mul_le' (a b : E) : ‖a * b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ESeminormedMonoid.enorm_mul_le`：∀ {E : Type u_8} {inst : TopologicalSpac
e E} [self : ESeminormedMonoid E] (x y : E), ‖x * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ
-/
lemma enorm_mul_le' (a b : E) : ‖a * b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := ESeminormedMonoid.enorm_mul_le a b

@[to_additive enorm_add_le_of_le]
/-
**enorm_mul_le_of_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_mul_le_of_le' {r₁ r₂ : Real>=0∞} {a₁ a₂ : E} (h₁ : ‖a₁‖ₑ <= r₁) (h₂ 
: ‖a₂‖ₑ <= r₂) : ‖a₁ * a₂‖ₑ <= r₁ + r₂
参数：h₁ : ‖a₁‖ₑ <= r₁；h₂ : ‖a₂‖ₑ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `enorm_mul_le'`：enorm_mul_le' (a b : E) : ‖a * b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem enorm_mul_le_of_le' {r₁ r₂ : ℝ≥0∞} {a₁ a₂ : E}
    (h₁ : ‖a₁‖ₑ ≤ r₁) (h₂ : ‖a₂‖ₑ ≤ r₂) : ‖a₁ * a₂‖ₑ ≤ r₁ + r₂ :=
  (enorm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

@[to_additive enorm_add₃_le]
/-
**enorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : Mul α] [NormM
ulClass α] (a b : α), ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_mul₃_le' {a b c : E} : ‖a * b * c‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ :=
  enorm_mul_le_of_le' (enorm_mul_le' _ _) le_rfl

@[to_additive enorm_add₄_le]
/-
**enorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : Mul α] [NormM
ulClass α] (a b : α), ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_mul₄_le' {a b c d : E} : ‖a * b * c * d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ :=
  enorm_mul_le_of_le' enorm_mul₃_le' le_rfl

end ESeminormedMonoid

section ENormedMonoid

variable {E : Type*} [TopologicalSpace E] [ENormedMonoid E]

@[to_additive (attr := simp) enorm_eq_zero]
/-
**enorm_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_eq_zero' {a : E} : ‖a‖ₑ = 0 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma enorm_eq_zero' {a : E} : ‖a‖ₑ = 0 ↔ a = 1 := by
  simp [ENormedMonoid.enorm_eq_zero]

@[to_additive enorm_ne_zero]
/-
**enorm_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_ne_zero' {a : E} : ‖a‖ₑ != 0 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `enorm_eq_zero'`：enorm_eq_zero' {a : E} : ‖a‖ₑ = 0 ↔ a = 1
-/
lemma enorm_ne_zero' {a : E} : ‖a‖ₑ ≠ 0 ↔ a ≠ 1 :=
  enorm_eq_zero'.ne

@[to_additive (attr := simp) enorm_pos]
/-
**enorm_pos'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_pos' {a : E} : 0 < ‖a‖ₑ ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `enorm_ne_zero'`：enorm_ne_zero' {a : E} : ‖a‖ₑ != 0 ↔ a != 1
-/
lemma enorm_pos' {a : E} : 0 < ‖a‖ₑ ↔ a ≠ 1 :=
  pos_iff_ne_zero.trans enorm_ne_zero'

end ENormedMonoid

open Set in
@[to_additive]
/-
**SeminormedGroup.disjoint_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SeminormedGroup.disjoint_nhds (x : E) (f : Filter E) : Disjoint (𝓝 x) f ↔ 
exists δ > 0, forallᶠ y in f, δ <= ‖y⁻¹ * x‖
参数：x : E；f : Filter E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `NormedGroup.nhds_basis_norm_lt`：NormedGroup.nhds_basis_norm_lt (x : E) :
 (𝓝 x).HasBasis (fun ε : Real => 0 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma SeminormedGroup.disjoint_nhds (x : E) (f : Filter E) :
    Disjoint (𝓝 x) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y⁻¹ * x‖ := by
  simp [NormedGroup.nhds_basis_norm_lt x |>.disjoint_iff_left, compl_ofPred, eventually_iff]

@[to_additive]
/-
**SeminormedGroup.disjoint_nhds_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SeminormedGroup.disjoint_nhds_one (f : Filter E) : Disjoint (𝓝 1) f ↔ exis
ts δ > 0, forallᶠ y in f, δ <= ‖y‖
参数：f : Filter E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用引理 `SeminormedGroup.disjoint_nhds`：SeminormedGroup.disjoint_nhds (x : E) (f 
: Filter E) : Disjoint (𝓝 x) f ↔ exists δ > 0, forallᶠ y in f, δ <= ‖y⁻¹ * x‖
-/
lemma SeminormedGroup.disjoint_nhds_one (f : Filter E) :
    Disjoint (𝓝 1) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y‖ := by
  simpa using disjoint_nhds 1 f

end SeminormedGroup

section Induced

variable (E F)
variable [FunLike 𝓕 E F]

-- See note [reducible non-instances]
/-- A group homomorphism from a `Group` to a `SeminormedGroup` induces a `SeminormedGroup`
/-
**on** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddGroup` structure on the domain. -/]
/-
**SeminormedGroup.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E 
F] (f : 𝓕) : SeminormedGroup E
参数：f : 𝓕。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  fast_instance% { PseudoMetricSpace.induced f toPseudoMetricSpace with
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_mul, map_inv, ← dist_eq_norm_inv_mul]; rfl }

-- See note [reducible non-instances]
/-- A group homomorphism from a `CommGroup` to a `SeminormedGroup` induces a
`SeminormedCommGroup` structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddCommGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddCommGroup` structure on the domain. -/]
/-
**SeminormedCommGroup.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedCommGroup.induced [CommGroup E] [SeminormedGroup F] [MonoidHomCl
ass 𝓕 E F] (f : 𝓕) : SeminormedCommGroup E
参数：f : 𝓕。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev SeminormedCommGroup.induced
    [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  fast_instance% { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `Group` to a `NormedGroup` induces a `NormedGroup`
/-
**on** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on the domain. -/
@[to_additive /-- An injective group homomorphism from an `AddGroup` to a
`NormedAddGroup` induces a `NormedAddGroup` structure on the domain. -/]
/-
**NormedGroup.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedGroup.induced [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 
𝓕) (h : Injective f) : NormedGroup E
参数：f : 𝓕；h : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev NormedGroup.induced
    [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  fast_instance% { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `CommGroup` to a `NormedGroup` induces a
`NormedCommGroup` structure on the domain. -/
@[to_additive /-- An injective group homomorphism from a `CommGroup` to a
`NormedCommGroup` induces a `NormedCommGroup` structure on the domain. -/]
/-
**NormedCommGroup.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E 
F] (f : 𝓕) (h : Injective f) : NormedCommGroup E
参数：f : 𝓕；h : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  fast_instance% { SeminormedCommGroup.induced E F f, MetricSpace.induced f h _ with }

end Induced

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive]
/-
**dist_eq_norm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul'`：dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹
 * a‖
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖ := by
  rw [dist_eq_norm_inv_mul', div_eq_inv_mul]

@[to_additive]
/-
**dist_eq_norm_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖ := by
  rw [dist_eq_norm_inv_mul, div_eq_inv_mul]

alias dist_eq_norm := dist_eq_norm_sub

alias dist_eq_norm' := dist_eq_norm_sub'

@[to_additive]
/-
**norm_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
-/
theorem norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖ := by
  rw [← dist_eq_norm_inv_mul, dist_eq_norm_div]

@[to_additive abs_norm_sub_norm_le]
/-
**abs_norm_sub_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| <= ‖a / b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `abs_norm_sub_norm_le_norm_inv_mul`：abs_norm_sub_norm_le_norm_inv_mul (a 
b : E) : |‖a‖ - ‖b‖| <= ‖a⁻¹ * b‖
· 使用定理 `norm_inv_mul`：norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖
-/
theorem abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a / b‖ :=
  (abs_norm_sub_norm_le_norm_inv_mul a b).trans_eq (norm_inv_mul a b)

@[to_additive norm_sub_norm_le]
/-
**norm_sub_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_norm_le' (a b : E) : ‖a‖ - ‖b‖ <= ‖a / b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `abs_norm_sub_norm_le'`：abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| <= 
‖a / b‖
-/
theorem norm_sub_norm_le' (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a / b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive dist_norm_norm_le]
/-
**dist_norm_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ <= ‖a / b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_norm_sub_norm_le'`：abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| <= 
‖a / b‖
-/
theorem dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a / b‖ :=
  abs_norm_sub_norm_le' a b

@[to_additive nndist_nnnorm_nnnorm_le]
/-
**nndist_nnnorm_nnnorm_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_nnnorm_nnnorm_le' (a b : E) : nndist ‖a‖₊ ‖b‖₊ <= ‖a / b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `dist_norm_norm_le'`：dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ <= ‖a / 
b‖
-/
theorem nndist_nnnorm_nnnorm_le' (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a / b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le' a b

@[to_additive]
/-
**nndist_eq_nnnorm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
-/
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊ :=
  NNReal.eq <| dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive]
/-
**edist_eq_enorm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_eq_enorm_div (a b : E) : edist a b = ‖a / b‖ₑ
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用引理 `ofReal_norm'`：ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ
-/
theorem edist_eq_enorm_div (a b : E) : edist a b = ‖a / b‖ₑ := by
  rw [edist_dist, dist_eq_norm_div, ofReal_norm']

@[to_additive]
/-
**dist_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by
  simp_rw [dist_eq_norm_inv_mul, ← norm_inv' (x⁻¹ * y⁻¹), mul_inv, inv_inv]
/-
**norm_multiset_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) : ‖m.
sum‖ <= (m.map fun x => ‖x‖).sum
参数：m : Multiset E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_sum_of_subadditive`：∀ {α : Type u_2} {β : Type u_3} [inst : 
AddCommMonoid α] [inst_1 : AddCommMonoid β] [inst_2 : Preorder β]   [IsOrderedAd
dMonoid β] (f : α → …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
-/
theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
    ‖m.sum‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.le_sum_of_subadditive norm norm_zero.le norm_add_le

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
/-
**enorm_multisetSum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_multisetSum_le (m : Multiset ε) : ‖m.sum‖ₑ <= (m.map fun x => ‖x‖ₑ).
sum
参数：m : Multiset ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_sum_of_subadditive`：∀ {α : Type u_2} {β : Type u_3} [inst : 
AddCommMonoid α] [inst_1 : AddCommMonoid β] [inst_2 : Preorder β]   [IsOrderedAd
dMonoid β] (f : α → …
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `enorm_add_le`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESe
minormedAddMonoid E] (a b : E), ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
-/
theorem enorm_multisetSum_le (m : Multiset ε) :
    ‖m.sum‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le

@[to_additive existing]
/-
**norm_multiset_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ <= (m.map fun x => ‖x‖).
sum
参数：m : Multiset E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0)
 (h_mul : forall (a b : α), f (a * b) <= f a + f b) : f m.prod <= (m.map f).sum
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.apply_prod_le_sum_map _ norm_one'.le norm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε] in
@[to_additive existing]
/-
**enorm_multisetProd_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_multisetProd_le (m : Multiset ε) : ‖m.prod‖ₑ <= (m.map fun x => ‖x‖ₑ
).sum
参数：m : Multiset ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0)
 (h_mul : forall (a b : α), f (a * b) <= f a + f b) : f m.prod <= (m.map f).sum
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `enorm_one'`：enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMono
id E] : ‖(1 : E)‖ₑ = 0
· 使用引理 `enorm_mul_le'`：enorm_mul_le' (a b : E) : ‖a * b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
-/
theorem enorm_multisetProd_le (m : Multiset ε) :
    ‖m.prod‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.apply_prod_le_sum_map _ enorm_one'.le enorm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
@[bound]
/-
**enorm_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_sum_le (s : Finset ι) (f : ι -> ε) : ‖∑ i in s, f i‖ₑ <= ∑ i in s, ‖
f i‖ₑ
参数：s : Finset ι；f : ι -> ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive`：∀ {ι : Type u_1} {M : Type u_4} {N : Type 
u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preorder N]  
 [IsOrderedAddMono…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `enorm_add_le`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESe
minormedAddMonoid E] (a b : E), ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
-/
theorem enorm_sum_le (s : Finset ι) (f : ι → ε) :
    ‖∑ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le f

@[bound]
/-
**norm_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι -> E) : ‖
∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
参数：s : Finset ι；f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive`：∀ {ι : Type u_1} {M : Type u_4} {N : Type 
u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preorder N]  
 [IsOrderedAddMono…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
-/
theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.le_sum_of_subadditive norm norm_zero.le norm_add_le f

@[to_additive existing]
/-
**enorm_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_prod_le (s : Finset ι) (f : ι -> ε) : ‖∏ i in s, f i‖ₑ <= ∑ i in s, 
‖f i‖ₑ
参数：s : Finset ι；f : ι -> ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_prod_le_sum_apply`：apply_prod_le_sum_apply (h_one : g 1 <= 
0) (h_mul : forall (a b : α), g (a * b) <= g a + g b) : g (∏ x in s, f x) <= ∑ x
 in s, g (f x)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `enorm_one'`：enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMono
id E] : ‖(1 : E)‖ₑ = 0
· 使用引理 `enorm_mul_le'`：enorm_mul_le' (a b : E) : ‖a * b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
-/
theorem enorm_prod_le (s : Finset ι) (f : ι → ε) : ‖∏ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.apply_prod_le_sum_apply _ enorm_one'.le enorm_mul_le'

@[to_additive existing]
/-
**norm_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_prod_le (s : Finset ι) (f : ι -> E) : ‖∏ i in s, f i‖ <= ∑ i in s, ‖f
 i‖
参数：s : Finset ι；f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_prod_le_sum_apply`：apply_prod_le_sum_apply (h_one : g 1 <= 
0) (h_mul : forall (a b : α), g (a * b) <= g a + g b) : g (∏ x in s, f x) <= ∑ x
 in s, g (f x)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `norm_mul_le'`：norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖
-/
theorem norm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.apply_prod_le_sum_apply _ norm_one'.le norm_mul_le'

@[to_additive]
/-
**enorm_prod_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_prod_le_of_le (s : Finset ι) {f : ι -> ε} {n : ι -> Real>=0∞} (h : f
orall b in s, ‖f b‖ₑ <= n b) : ‖∏ b in s, f b‖ₑ <= ∑ b in s, n b
参数：s : Finset ι；h : forall b in s, ‖f b‖ₑ <= n b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `enorm_prod_le`：enorm_prod_le (s : Finset ι) (f : ι -> ε) : ‖∏ i in s, f 
i‖ₑ <= ∑ i in s, ‖f i‖ₑ
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
-/
theorem enorm_prod_le_of_le (s : Finset ι) {f : ι → ε} {n : ι → ℝ≥0∞} (h : ∀ b ∈ s, ‖f b‖ₑ ≤ n b) :
    ‖∏ b ∈ s, f b‖ₑ ≤ ∑ b ∈ s, n b :=
  (enorm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
/-
**norm_prod_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_prod_le_of_le (s : Finset ι) {f : ι -> E} {n : ι -> Real} (h : forall
 b in s, ‖f b‖ <= n b) : ‖∏ b in s, f b‖ <= ∑ b in s, n b
参数：s : Finset ι；h : forall b in s, ‖f b‖ <= n b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_prod_le`：norm_prod_le (s : Finset ι) (f : ι -> E) : ‖∏ i in s, f i‖
 <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem norm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ‖f b‖ ≤ n b) :
    ‖∏ b ∈ s, f b‖ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
/-
**dist_prod_prod_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_prod_prod_le_of_le (s : Finset ι) {f a : ι -> E} {d : ι -> Real} (h :
 forall b in s, dist (f b) (a b) <= d b) : dist (∏ b in s, f b) (∏ b in s, a b) 
<= ∑ b in s, d b
参数：s : Finset ι；h : forall b in s, dist (f b) (a b) <= d b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_inv_distrib`：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x
)⁻¹) = (∏ x in s, f x)⁻¹
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `norm_prod_le_of_le`：norm_prod_le_of_le (s : Finset ι) {f : ι -> E} {n : 
ι -> Real} (h : forall b in s, ‖f b‖ <= n b) : ‖∏ b in s, f b‖ <= ∑ b in s, n b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι → E} {d : ι → ℝ}
    (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, d b := by
  simp_rw [dist_eq_norm_inv_mul] at h
  rw [dist_eq_norm_inv_mul, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  exact norm_prod_le_of_le s h

@[to_additive]
/-
**dist_prod_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_prod_prod_le (s : Finset ι) (f a : ι -> E) : dist (∏ b in s, f b) (∏ 
b in s, a b) <= ∑ b in s, dist (f b) (a b)
参数：s : Finset ι；f a : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_prod_prod_le_of_le`：dist_prod_prod_le_of_le (s : Finset ι) {f a : ι
 -> E} {d : ι -> Real} (h : forall b in s, dist (f b) (a b) <= d b) : dist (∏ b 
in s, f b) (∏…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem dist_prod_prod_le (s : Finset ι) (f a : ι → E) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive ball_eq]
/-
**ball_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_eq' (y : E) (ε : Real) : ball y ε = { x | ‖x / y‖ < ε }
参数：y : E；ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_eq_norm_inv_mul_lt`：ball_eq_norm_inv_mul_lt (y : E) (ε : Real) : ba
ll y ε = { x | ‖x⁻¹ * y‖ < ε }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_inv_mul`：norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_eq' (y : E) (ε : ℝ) : ball y ε = { x | ‖x / y‖ < ε } := by
  simp_rw [ball_eq_norm_inv_mul_lt, norm_inv_mul]

@[to_additive mem_ball_iff_norm]
/-
**mem_ball_iff_norm''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_ball_iff_norm'' : b in ball a r ↔ ‖b / a‖ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball_iff_norm'' : b ∈ ball a r ↔ ‖b / a‖ < r := by
  rw [mem_ball, dist_eq_norm_div]

@[to_additive mem_ball_iff_norm']
/-
**mem_ball_iff_norm'''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_ball_iff_norm''' : b in ball a r ↔ ‖a / b‖ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball'`：mem_ball' : y in ball x ε ↔ dist x y < ε
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball_iff_norm''' : b ∈ ball a r ↔ ‖a / b‖ < r := by
  rw [mem_ball', dist_eq_norm_div]

/-- A scaled ball is a ball. -/
@[to_additive setOf_sub_mem_ball_eq_ball /-- A translated ball is a ball. -/]
/-
**setOf_div_mem_ball_eq_ball''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOf_div_mem_ball_eq_ball'' : {x | x / a in ball 1 r} = Metric.ball a r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_ball_iff_norm''`：mem_ball_iff_norm'' : b in ball a r ↔ ‖b / a‖ < r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A scaled ball is a ball.
-/
theorem setOf_div_mem_ball_eq_ball'' :
    {x | x / a ∈ ball 1 r} = Metric.ball a r := by
  ext x
  rw [mem_ball_iff_norm'']
  simp

@[to_additive mem_closedBall_iff_norm]
/-
**mem_closedBall_iff_norm''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closedBall_iff_norm'' : b in closedBall a r ↔ ‖b / a‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall_iff_norm'' : b ∈ closedBall a r ↔ ‖b / a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm_div]

@[to_additive mem_closedBall_iff_norm']
/-
**mem_closedBall_iff_norm'''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closedBall_iff_norm''' : b in closedBall a r ↔ ‖a / b‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall'`：mem_closedBall' : y in closedBall x ε ↔ dist x y
 <= ε
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall_iff_norm''' : b ∈ closedBall a r ↔ ‖a / b‖ ≤ r := by
  rw [mem_closedBall', dist_eq_norm_div]

/-- A scaled closed ball is a closed ball. -/
@[to_additive setOf_sub_mem_closedBall_eq_closedBall
  /-- A translated closed ball is a closed ball. -/]
/-
**setOf_div_mem_closedBall_eq_closedBall''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOf_div_mem_closedBall_eq_closedBall'' : {x | x / a in closedBall 1 r} =
 Metric.closedBall a r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closedBall_iff_norm''`：mem_closedBall_iff_norm'' : b in closedBall a
 r ↔ ‖b / a‖ <= r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem setOf_div_mem_closedBall_eq_closedBall'' :
    {x | x / a ∈ closedBall 1 r} = Metric.closedBall a r := by
  ext x
  rw [mem_closedBall_iff_norm'']
  simp

-- Higher priority to fire before `mem_sphere`.
@[to_additive (attr := simp high) mem_sphere_iff_norm]
/-
**mem_sphere_iff_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_sphere_iff_norm' : b in sphere a r ↔ ‖b / a‖ = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sphere_iff_norm' : b ∈ sphere a r ↔ ‖b / a‖ = r := by simp [dist_eq_norm_div]

/-- A scaled sphere is a sphere. -/
@[to_additive setOf_sub_mem_sphere_eq_sphere /-- A translated sphere is a sphere. -/]
/-
**setOf_div_mem_sphere_eq_sphere''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOf_div_mem_sphere_eq_sphere'' : {x | x / a in sphere 1 r} = Metric.sphe
re a r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_sphere_iff_norm'`：mem_sphere_iff_norm' : b in sphere a r ↔ ‖b / a‖ =
 r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A scaled sphere is a sphere.
-/
theorem setOf_div_mem_sphere_eq_sphere'' :
    {x | x / a ∈ sphere 1 r} = Metric.sphere a r := by
  ext x
  rw [mem_sphere_iff_norm']
  simp

@[to_additive]
/-
**mul_mem_ball_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_ball_iff_norm : a * b in ball a r ↔ ‖b‖ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_ball_iff_norm''`：mem_ball_iff_norm'' : b in ball a r ↔ ‖b / a‖ < r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ‖b‖ < r := by
  rw [mem_ball_iff_norm'']
  simp

@[to_additive]
/-
**mul_mem_closedBall_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_closedBall_iff_norm : a * b in closedBall a r ↔ ‖b‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closedBall_iff_norm''`：mem_closedBall_iff_norm'' : b in closedBall a
 r ↔ ‖b / a‖ <= r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_mem_closedBall_iff_norm : a * b ∈ closedBall a r ↔ ‖b‖ ≤ r := by
  rw [mem_closedBall_iff_norm'']
  simp

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_ball`.
@[to_additive (attr := simp high)]
/-
**preimage_mul_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_mul_ball (a b : E) (r : Real) : (b * ·) ⁻¹' ball a r = ball (a / 
b) r
参数：a b : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_mul_ball (a b : E) (r : ℝ) : (b * ·) ⁻¹' ball a r = ball (a / b) r := by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_ball, div_eq_mul_inv, mul_comm, mul_assoc]

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_closedBall`.
@[to_additive (attr := simp high)]
/-
**preimage_mul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_mul_closedBall (a b : E) (r : Real) : (b * ·) ⁻¹' closedBall a r 
= closedBall (a / b) r
参数：a b : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_mul_closedBall (a b : E) (r : ℝ) :
    (b * ·) ⁻¹' closedBall a r = closedBall (a / b) r := by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_closedBall, div_eq_mul_inv, mul_comm, mul_assoc]

@[to_additive (attr := simp)]
/-
**preimage_mul_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_mul_sphere (a b : E) (r : Real) : (b * ·) ⁻¹' sphere a r = sphere
 (a / b) r
参数：a b : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_mul_sphere (a b : E) (r : ℝ) : (b * ·) ⁻¹' sphere a r = sphere (a / b) r := by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]

@[to_additive]
/-
**pow_mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_mem_closedBall {n : Nat} (h : a in closedBall b r) : a ^ n in closedBa
ll (b ^ n) (n • r)
参数：h : a in closedBall b r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_pow_le_mul_norm`：∀ {E : Type u_5} [inst : SeminormedGroup E] {a : E
} {n : ℕ}, ‖a ^ n‖ ≤ ↑n * ‖a‖
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
theorem pow_mem_closedBall {n : ℕ} (h : a ∈ closedBall b r) :
    a ^ n ∈ closedBall (b ^ n) (n • r) := by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine norm_pow_le_mul_norm.trans ?_
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg

@[to_additive]
/-
**pow_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_mem_ball {n : Nat} (hn : 0 < n) (h : a in ball b r) : a ^ n in ball (b
 ^ n) (n • r)
参数：hn : 0 < n；h : a in ball b r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `norm_pow_le_mul_norm`：∀ {E : Type u_5} [inst : SeminormedGroup E] {a : E
} {n : ℕ}, ‖a ^ n‖ ≤ ↑n * ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
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
（共 65 条，此处仅展示前 30 条）
-/
theorem pow_mem_ball {n : ℕ} (hn : 0 < n) (h : a ∈ ball b r) : a ^ n ∈ ball (b ^ n) (n • r) := by
  simp only [mem_ball, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine lt_of_le_of_lt norm_pow_le_mul_norm ?_
  replace hn : 0 < (n : ℝ) := by norm_cast
  rw [nsmul_eq_mul]
  nlinarith

@[to_additive]
/-
**mul_mem_closedBall_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_closedBall_mul_iff {c : E} : a * c in closedBall (b * c) r ↔ a in 
closedBall b r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `mul_mul_inv_mul_cancel`：mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻
¹ * c) = a * c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_mem_closedBall_mul_iff {c : E} : a * c ∈ closedBall (b * c) r ↔ a ∈ closedBall b r := by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]
/-
**mul_mem_ball_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_ball_mul_iff {c : E} : a * c in ball (b * c) r ↔ a in ball b r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `mul_mul_inv_mul_cancel`：mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻
¹ * c) = a * c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_mem_ball_mul_iff {c : E} : a * c ∈ ball (b * c) r ↔ a ∈ ball b r := by
  simp only [mem_ball, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]
/-
**smul_closedBall''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_closedBall'' : a • closedBall b r = closedBall (a • b) r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_closedBall'' : a • closedBall b r = closedBall (a • b) r := by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
/-
**smul_ball''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_ball'' : a • ball b r = ball (a • b) r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_ball'' : a • ball b r = ball (a • b) r := by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
/-
**nnnorm_multiset_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ <= (m.map fun x => ‖x
‖₊).sum
参数：m : Multiset E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_multiset_sum`：coe_multiset_sum (s : Multiset Real>=0) : ((s.s
um : Real>=0) : Real) = (s.map (↑)).sum
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `norm_multiset_prod_le`：norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖
 <= (m.map fun x => ‖x‖).sum
-/
theorem nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ ≤ (m.map fun x => ‖x‖₊).sum :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]
/-
**nnnorm_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_prod_le (s : Finset ι) (f : ι -> E) : ‖∏ a in s, f a‖₊ <= ∑ a in s,
 ‖f a‖₊
参数：s : Finset ι；f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `norm_prod_le`：norm_prod_le (s : Finset ι) (f : ι -> E) : ‖∏ i in s, f i‖
 <= ∑ i in s, ‖f i‖
-/
theorem nnnorm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact norm_prod_le _ _

@[to_additive]
/-
**nnnorm_prod_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_prod_le_of_le (s : Finset ι) {f : ι -> E} {n : ι -> Real>=0} (h : f
orall b in s, ‖f b‖₊ <= n b) : ‖∏ b in s, f b‖₊ <= ∑ b in s, n b
参数：s : Finset ι；h : forall b in s, ‖f b‖₊ <= n b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `norm_prod_le_of_le`：norm_prod_le_of_le (s : Finset ι) {f : ι -> E} {n : 
ι -> Real} (h : forall b in s, ‖f b‖ <= n b) : ‖∏ b in s, f b‖ <= ∑ b in s, n b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
-/
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ‖f b‖₊ ≤ n b) :
    ‖∏ b ∈ s, f b‖₊ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le_of_le s h).trans_eq (NNReal.coe_sum ..).symm

@[to_additive]
/-
**NormedCommGroup.tendsto_nhds_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedCommGroup.tendsto_nhds_nhds {f : E -> F} {x : E} {y : F} : Tendsto f
 (𝓝 x) (𝓝 y) ↔ forall ε > 0, exists δ > 0, forall x', ‖x' / x‖ < δ -> ‖f x' / y‖
 < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_inv_mul`：norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖
· 使用定理 `NormedGroup.tendsto_nhds_nhds`：NormedGroup.tendsto_nhds_nhds {f : E -> F
} {x : E} {y : F} : Tendsto f (𝓝 x) (𝓝 y) ↔ forall ε > 0, exists δ > 0, forall x
', ‖x'⁻¹ * x‖ < δ -…
-/
theorem NormedCommGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x' / x‖ < δ → ‖f x' / y‖ < ε := by
  simpa [norm_inv_mul] using NormedGroup.tendsto_nhds_nhds (f := f) (x := x) (y := y)

@[to_additive]
/-
**NormedCommGroup.nhds_basis_norm_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedCommGroup.nhds_basis_norm_lt (x : E) : (𝓝 x).HasBasis (fun ε : Real 
=> 0 < ε) fun ε => { y | ‖y / x‖ < ε }
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_inv_mul`：norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖
· 使用定理 `NormedGroup.nhds_basis_norm_lt`：NormedGroup.nhds_basis_norm_lt (x : E) :
 (𝓝 x).HasBasis (fun ε : Real => 0 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε }
-/
theorem NormedCommGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y / x‖ < ε } := by
  simpa [norm_inv_mul] using NormedGroup.nhds_basis_norm_lt x

@[to_additive]
/-
**NormedCommGroup.uniformity_basis_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedCommGroup.uniformity_basis_dist : (𝓤 E).HasBasis (fun ε : Real => 0 
< ε) fun ε => { p : E × E | ‖p.fst / p.snd‖ < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_inv_mul`：norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖
· 使用定理 `NormedGroup.uniformity_basis_dist`：NormedGroup.uniformity_basis_dist : (
𝓤 E).HasBasis (fun ε : Real => 0 < ε) fun ε => { p : E × E | ‖p.fst⁻¹ * p.snd‖ <
 ε }
-/
theorem NormedCommGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst / p.snd‖ < ε } := by
  simpa [norm_inv_mul] using NormedGroup.uniformity_basis_dist (E := E)

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

@[to_additive (attr := simp) norm_le_zero_iff]
/-
**norm_le_zero_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_le_zero_iff' : ‖a‖ <= 0 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `dist_le_zero`：dist_le_zero {x y : γ} : dist x y <= 0 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_le_zero_iff' : ‖a‖ ≤ 0 ↔ a = 1 := by rw [← dist_one_right, dist_le_zero]

@[to_additive (attr := simp) norm_pos_iff]
/-
**norm_pos_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_pos_iff' : 0 < ‖a‖ ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `norm_le_zero_iff'`：norm_le_zero_iff' : ‖a‖ <= 0 ↔ a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_pos_iff' : 0 < ‖a‖ ↔ a ≠ 1 := by rw [← not_le, norm_le_zero_iff']

@[to_additive (attr := simp) norm_eq_zero]
/-
**norm_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_eq_zero' : ‖a‖ = 0 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用引理 `norm_le_zero_iff'`：norm_le_zero_iff' : ‖a‖ <= 0 ↔ a = 1
-/
lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'

@[to_additive norm_ne_zero_iff]
/-
**norm_ne_zero_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_ne_zero_iff' : ‖a‖ != 0 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `norm_eq_zero'`：norm_eq_zero' : ‖a‖ = 0 ↔ a = 1
-/
lemma norm_ne_zero_iff' : ‖a‖ ≠ 0 ↔ a ≠ 1 := norm_eq_zero'.not

@[to_additive]
/-
**norm_div_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_eq_zero'`：norm_eq_zero' : ‖a‖ = 0 ↔ a = 1
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b := by rw [norm_eq_zero', div_eq_one]

@[to_additive]
/-
**norm_div_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_div_pos_iff : 0 < ‖a / b‖ ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `norm_div_eq_zero_iff`：norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b
-/
theorem norm_div_pos_iff : 0 < ‖a / b‖ ↔ a ≠ b := by
  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
  exact norm_div_eq_zero_iff.not

@[to_additive eq_of_norm_sub_le_zero]
/-
**eq_of_norm_div_le_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_norm_div_le_zero (h : ‖a / b‖ <= 0) : a = b
参数：h : ‖a / b‖ <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
· 使用引理 `norm_le_zero_iff'`：norm_le_zero_iff' : ‖a‖ <= 0 ↔ a = 1
-/
theorem eq_of_norm_div_le_zero (h : ‖a / b‖ ≤ 0) : a = b := by
  rwa [← div_eq_one, ← norm_le_zero_iff']

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff

attribute [to_additive] eq_of_norm_div_eq_zero

@[to_additive]
/-
**eq_one_or_norm_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
theorem eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖ := by
  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt

@[to_additive]
/-
**eq_one_or_nnnorm_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_or_nnnorm_pos (a : E) : a = 1 ∨ 0 < ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_one_or_norm_pos`：eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖
-/
theorem eq_one_or_nnnorm_pos (a : E) : a = 1 ∨ 0 < ‖a‖₊ :=
  eq_one_or_norm_pos a

@[to_additive (attr := simp) nnnorm_eq_zero]
/-
**nnnorm_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `coe_nnnorm'`：coe_nnnorm' (a : E) : (‖a‖₊ : Real) = ‖a‖
· 使用引理 `norm_eq_zero'`：norm_eq_zero' : ‖a‖ = 0 ↔ a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1 := by
  rw [← NNReal.coe_eq_zero, coe_nnnorm', norm_eq_zero']

@[to_additive nnnorm_ne_zero_iff]
/-
**nnnorm_ne_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_ne_zero_iff' : ‖a‖₊ != 0 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `nnnorm_eq_zero'`：nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1
-/
theorem nnnorm_ne_zero_iff' : ‖a‖₊ ≠ 0 ↔ a ≠ 1 :=
  nnnorm_eq_zero'.not

@[to_additive (attr := simp) nnnorm_pos]
/-
**nnnorm_pos'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_pos' : 0 < ‖a‖₊ ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `nnnorm_ne_zero_iff'`：nnnorm_ne_zero_iff' : ‖a‖₊ != 0 ↔ a != 1
-/
lemma nnnorm_pos' : 0 < ‖a‖₊ ↔ a ≠ 1 := pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive /-- The norm of a normed group as an additive group norm. -/]
/-
**normGroupNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normGroupNorm : GroupNorm E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of a normed group as a group norm.
-/
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero'.1 }

@[simp]
/-
**coe_normGroupNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_normGroupNorm : ⇑(normGroupNorm E) = norm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_normGroupNorm : ⇑(normGroupNorm E) = norm :=
  rfl

end NormedGroup

section NormedAddGroup

variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

/-! Some relations with `HasCompactSupport` -/

/-
**hasCompactSupport_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasCompactSupport_norm_iff : (HasCompactSupport fun x => ‖f x‖) ↔ HasCompa
ctSupport f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasCompactSupport_comp_left`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u
_5} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {g : β → γ
} {f : α → β}, (∀…
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0

--- 原说明 ---
Some relations with `HasCompactSupport`
-/
theorem hasCompactSupport_norm_iff : (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f :=
  hasCompactSupport_comp_left norm_eq_zero

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff

end NormedAddGroup

/-! ### `positivity` extensions -/

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: multiplicative norms are always nonnegative, and positive
on non-one inputs. -/
@[positivity ‖_‖]
meta def evalMulNorm : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedGroup_E ← synthInstanceQ q(SeminormedGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 1` assumption
    let o : Option (Q(NormedGroup $E) × Q($a ≠ 1)) ← do
      let .some normedGroup_E ← trySynthInstanceQ q(NormedGroup $E) | pure none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 1) | pure none
      pure <| some (normedGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff'.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg' $a)
  | _, _, _ => throwError "not `‖·‖`"

/-- Extension for the `positivity` tactic: additive norms are always nonnegative, and positive
on non-zero inputs. -/
@[positivity ‖_‖]
meta def evalAddNorm : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedAddGroup_E ← synthInstanceQ q(SeminormedAddGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 0` assumption
    let o : Option (Q(NormedAddGroup $E) × Q($a ≠ 0)) ← do
      let .some normedAddGroup_E ← trySynthInstanceQ q(NormedAddGroup $E) | pure none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 0) | pure none
      pure <| some (normedAddGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedAddGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg $a)
  | _, _, _ => throwError "not `‖·‖`"

end Mathlib.Meta.Positivity

