/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.Positivity

/-!
# Chebyshev polynomials over the reals: some extremal properties

* Chebyshev polynomials have largest leading coefficient,
following proof in https://math.stackexchange.com/a/978145/1277
* Chebyshev polynomials maximize iterated derivatives at 1 and beyond

## Main statements

* leadingCoeff_le_of_forall_abs_le_one: If `P` is a real polynomial of degree at most `n` and
  `|P (x)| ≤ 1` for all `x ∈ [-1, 1]` then the leading coefficient of `P` is at most `2 ^ (n - 1)`
* leadingCoeff_eq_iff_of_forall_abs_le_one: When `n ≥ 2`, equality holds iff `P = T_n`
* eval_iterate_derivative_le_of_forall_abs_le_one: If `P` is a real polynomial of degree at most `n`
  and `|P (x)| ≤ 1` for all `x ∈ [-1, 1]` then for all `x ≥ 1`, `P ^ (k) (x) ≤ T_n ^ (k)(x)`
* eval_iterate_derivative_eq_iff_of_forall_abs_le_one: If `0 < k ≤ n` then equality holds iff
  `P = T_n`

## Implementation

We describe the proof for the leading coefficient; the proof for iterated derivatives uses a
similar approach.

By monotonicity of `2 ^ (n - 1)`, we can assume that `P` has degree exactly `n`.
Using Lagrange interpolation, we can give a formula for the leading coefficient of `P`
as a linear combination of the values of `P` on the Chebyshev nodes (sumNodes_eq_coeff).
The Chebyshev polynomial `T_n` has value `±1` on the nodes, with the same signs as the
coefficients of the linear combination (negOnePow_mul_leadingCoeffC_pos).
Since `|P (x)| ≤ 1` on the nodes, this implies that the leading coefficient of `P` is bounded
by that of `T_n`, which is known to equal `2 ^ (n - 1)`.
Moreover, equality holds iff `P` and `T_n` agree on the nodes, which implies that they coincide.
-/
@[expose] public section
namespace Polynomial.Chebyshev

open Polynomial Real

/-- For `n ≠ 0` and `i ≤ n`, `node n i` is one of the extremal points of the Chebyshev `T`
polynomial over the interval `[-1, 1]`. -/
/-
**Polynomial.Chebyshev.node** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：node (n i : Nat) : Real
参数：n i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `n ≠ 0` and `i ≤ n`, `node n i` is one of the extremal points of the Chebysh
ev `T`
polynomial over the interval `[-1, 1]`.
-/
noncomputable def node (n i : ℕ) : ℝ := cos (i * π / n)
/-
**Polynomial.Chebyshev.node_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Chebysh
ev`。
形式化陈述：node_eq_one {n : Nat} : node n 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma node_eq_one {n : ℕ} : node n 0 = 1 := by simp [node]
/-
**Polynomial.Chebyshev.node_eq_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Che
byshev`。
形式化陈述：node_eq_neg_one {n : Nat} (hn : n != 0) : node n n = -1
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.cos_pi`：cos_pi : cos π = -1
-/
lemma node_eq_neg_one {n : ℕ} (hn : n ≠ 0) : node n n = -1 := by
  have : n * π / n = π := by aesop
  simp [node, this]
/-
**Polynomial.Chebyshev.node_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Chebys
hev`。
形式化陈述：node_mem_Icc {n i : Nat} : node n i in Set.Icc (-1) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Real.neg_one_le_cos`：neg_one_le_cos : -1 <= cos x
· 使用定理 `Real.cos_le_one`：cos_le_one : cos x <= 1
-/
lemma node_mem_Icc {n i : ℕ} : node n i ∈ Set.Icc (-1) 1 :=
  Set.mem_Icc.mpr ⟨neg_one_le_cos _, cos_le_one _⟩
/-
**Polynomial.Chebyshev.eval_T_real_node** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Ch
ebyshev`。
形式化陈述：eval_T_real_node {n i : Nat} (hi : i in Finset.Iic n) : (T Real n).eval (n
ode n i) = (-1) ^ i
参数：hi : i in Finset.Iic n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Polynomial.Chebyshev.T_zero`：T_zero : T R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
（共 54 条，此处仅展示前 30 条）
-/
lemma eval_T_real_node {n i : ℕ} (hi : i ∈ Finset.Iic n) :
    (T ℝ n).eval (node n i) = (-1) ^ i := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [show i = 0 by grind]
  have : (n : ℤ) * (i * π / n) = i * π := by norm_cast; field
  rw [node, T_real_cos, this, cos_nat_mul_pi]
/-
**Polynomial.Chebyshev.strictAntiOn_node** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.C
hebyshev`。
形式化陈述：strictAntiOn_node (n : Nat) : StrictAntiOn (node n ·) (Finset.range (n + 1
))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `StrictAntiOn.comp_strictMonoOn`：StrictAntiOn.comp_strictMonoOn (hg : Str
ictAntiOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g
 ∘ f) s
· 使用定理 `Real.strictAntiOn_cos`：strictAntiOn_cos : StrictAntiOn cos (Icc 0 π)
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用引理 `StrictMono.mul_const`：StrictMono.mul_const [MulPosStrictMono M₀] (hf : S
trictMono f) (ha : 0 < a) : StrictMono fun x => f x * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
（共 40 条，此处仅展示前 30 条）
-/
lemma strictAntiOn_node (n : ℕ) :
    StrictAntiOn (node n ·) (Finset.range (n + 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine strictAntiOn_cos.comp_strictMonoOn ?_ (fun x hx => Set.mem_Icc.mpr ⟨by positivity, ?_⟩)
  · apply StrictMono.strictMonoOn
    exact StrictMono.mul_const
      (StrictMono.mul_const Nat.strictMono_cast (by positivity)) (by positivity)
  rw [Finset.mem_coe, Finset.mem_range_succ_iff] at hx
  rw [mul_div_assoc]
  nth_rewrite 2 [← mul_div_cancel₀ π (Nat.cast_ne_zero.mpr hn)]
  gcongr
/-
**Polynomial.Chebyshev.node_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：node_lt {n i j : Nat} (hj : j <= n) (hij : i < j) : node n j < node n i
参数：hj : j <= n；hij : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.Chebyshev.strictAntiOn_node`：strictAntiOn_node (n : Nat) : St
rictAntiOn (node n ·) (Finset.range (n + 1))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
-/
lemma node_lt {n i j : ℕ} (hj : j ≤ n) (hij : i < j) :
    node n j < node n i :=
  strictAntiOn_node n (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr (by grind)))
    (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hj)) hij
/-
**Polynomial.Chebyshev.zero_lt_prod_node_sub_node** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial.Chebyshev`。
形式化陈述：zero_lt_prod_node_sub_node {n i : Nat} (hi : i <= n) : 0 < (-1) ^ i * ∏ j 
in (Finset.range (n + 1)).erase i, (node n i - node n j)
参数：hi : i <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.erase_singleton`：erase_singleton (a : α) : ({a} : Finset α).erase
 a = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos_of_neg_of_neg`：mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosSt
rictMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a b : R} (ha : a < 0) 
(hb : b < 0…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 46 条，此处仅展示前 30 条）
-/
lemma zero_lt_prod_node_sub_node {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i * ∏ j ∈ (Finset.range (n + 1)).erase i, (node n i - node n j) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.le_zero.mp hi]
  have h₁ : 0 < ∏ j ∈ Finset.range i, ((-1) * (node n i - node n j)) :=
    Finset.prod_pos (fun j hj => mul_pos_of_neg_of_neg neg_one_lt_zero <| sub_neg.mpr <|
    node_lt hi (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at h₁
  have h₂ : 0 < ∏ j ∈ Finset.Ioc i n, (node n i - node n j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr <|
      node_lt (Finset.mem_Ioc.mp hj).2 (Finset.mem_Ioc.mp hj).1)
  have union : (Finset.range (n + 1)).erase i = (Finset.range i) ∪ Finset.Ioc i n := by grind
  have disjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by grind [Finset.disjoint_iff_ne]
  rw [union, Finset.prod_union disjoint, ← mul_assoc]
  exact mul_pos h₁ h₂
/-
**Polynomial.Chebyshev.negOnePow_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Ch
ebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma negOnePow_mul_le {α : ℝ} {i : ℕ} (hα : |α| ≤ 1) : (-1) ^ i * α ≤ 1 := by
  apply le_of_abs_le
  rwa [abs_mul, abs_neg_one_pow, one_mul]
/-
**Polynomial.Chebyshev.negOnePow_mul_negOnePow_mul_cancel** 是 Mathlib 中的一个引理，位于命
名空间 `Polynomial.Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma negOnePow_mul_negOnePow_mul_cancel {α β : ℝ} {i : ℕ} :
    ((-1) ^ i * α) * ((-1) ^ i * β) = α * β := calc
  _ = ((-1) ^ i * (-1) ^ i) * α * β := by ring
  _ = α * β := by simp [← mul_pow]

/-- For a polynomial `P` and coefficient function `c`, `sumNodes n c P` is a linear combination
of `P` evaluated at the `n`'th order Chebyshev nodes, with coefficients taken from `c`. -/
/-
**Polynomial.Chebyshev.sumNodes** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Chebyshev`
。
形式化陈述：sumNodes (n : Nat) (c : Nat -> Real) (P : Real[X])
参数：n : Nat；c : Nat -> Real；P : Real[X]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a polynomial `P` and coefficient function `c`, `sumNodes n c P` is a linear 
combination
of `P` evaluated at the `n`'th order Chebyshev nodes, with coefficients taken fr
om `c`.
-/
noncomputable def sumNodes (n : ℕ) (c : ℕ → ℝ) (P : ℝ[X]) := ∑ i ≤ n, P.eval (node n i) * (c i)
/-
**Polynomial.Chebyshev.sumNodes_le_sumNodes_T** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：sumNodes_le_sumNodes_T {n : Nat} {c : Nat -> Real} (hcnonneg : forall i <=
 n, 0 <= (-1) ^ i * (c i)) {P : Real[X]} (hPbnd : forall x in Set.Icc (-1) 1, |P
.eval x| <= 1) : sumNodes n c P <= sumNodes n c (T Real n)
参数：hcnonneg : forall i <= n, 0 <= (-1) ^ i * (c i)；hPbnd : forall x in Set.Icc (
-1) 1, |P.eval x| <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.sumNodes.eq_1`：∀ (n : ℕ) (c : ℕ → ℝ) (P : Polynomia
l ℝ),   Polynomial.Chebyshev.sumNodes n c P = ∑ i ≤ n, Polynomial.eval (Polynomi
al.Chebyshev.node n i) P…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.negOnePow_mul_negOnePow_mul_cancel`：∀ {α β : ℝ} {i : 
ℕ}, (-1) ^ i * α * ((-1) ^ i * β) = α * β
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.negOnePow_mul_le`：∀ {α : ℝ} {i : ℕ}, |α| ≤ 1 → (-1) ^
 i * α ≤ 1
· 使用引理 `Polynomial.Chebyshev.node_mem_Icc`：node_mem_Icc {n i : Nat} : node n i i
n Set.Icc (-1) 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用引理 `Polynomial.Chebyshev.eval_T_real_node`：eval_T_real_node {n i : Nat} (hi 
: i in Finset.Iic n) : (T Real n).eval (node n i) = (-1) ^ i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem sumNodes_le_sumNodes_T {n : ℕ} {c : ℕ → ℝ}
    (hcnonneg : ∀ i ≤ n, 0 ≤ (-1) ^ i * (c i))
    {P : ℝ[X]} (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    sumNodes n c P ≤ sumNodes n c (T ℝ n) := by
  rw [sumNodes, sumNodes]
  refine Finset.sum_le_sum (fun i hi => ?_)
  calc
    P.eval (node n i) * (c i) =
      ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * (c i)) :=
      negOnePow_mul_negOnePow_mul_cancel.symm
    _ ≤ 1 * ((-1) ^ i * (c i)) := by
      gcongr
      · exact (hcnonneg i (Finset.mem_Iic.mp hi))
      · exact (negOnePow_mul_le (hPbnd _ node_mem_Icc))
    _ = (T ℝ n).eval (node n i) * (c i) := by
      rw [eval_T_real_node hi, one_mul]
/-
**Polynomial.Chebyshev.sumNodes_eq_sumNodes_T_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Chebyshev`。
形式化陈述：sumNodes_eq_sumNodes_T_iff {n : Nat} {c : Nat -> Real} (hcpos : forall i <
= n, 0 < (-1) ^ i * (c i)) {P : Real[X]} (hPdeg : P.degree <= n) (hPbnd : forall
 x in Set.Icc (-1) 1, |P.eval x| <= 1) : (sumNodes n c P = sumNodes n c (T Real 
n)) ↔ P = T Real n
参数：hcpos : forall i <= n, 0 < (-1) ^ i * (c i)；hPdeg : P.degree <= n；hPbnd : for
all x in Set.Icc (-1) 1, |P.eval x| <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_of_degrees_lt_of_eval_finset_eq`：eq_of_degrees_lt_of_eval_
finset_eq (degree_f_lt : f.degree < #s) (degree_g_lt : g.degree < #s) (eval_fg :
 forall x in s, f.eval x = g.eval x…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用引理 `StrictAntiOn.injOn`：StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn
 f
· 使用引理 `Polynomial.Chebyshev.strictAntiOn_node`：strictAntiOn_node (n : Nat) : St
rictAntiOn (node n ·) (Finset.range (n + 1))
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.Chebyshev.degree_T`：degree_T [IsDomain R] [NeZero (2 : R)] (n
 : Int) : (T R n).degree = n.natAbs
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Polynomial.Chebyshev.sumNodes.eq_1`：∀ (n : ℕ) (c : ℕ → ℝ) (P : Polynomia
l ℝ),   Polynomial.Chebyshev.sumNodes n c P = ∑ i ≤ n, Polynomial.eval (Polynomi
al.Chebyshev.node n i) P…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Polynomial.Chebyshev.eval_T_real_node`：eval_T_real_node {n i : Nat} (hi 
: i in Finset.Iic n) : (T Real n).eval (node n i) = (-1) ^ i
（共 46 条，此处仅展示前 30 条）
-/
theorem sumNodes_eq_sumNodes_T_iff {n : ℕ} {c : ℕ → ℝ}
    (hcpos : ∀ i ≤ n, 0 < (-1) ^ i * (c i))
    {P : ℝ[X]} (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    (sumNodes n c P = sumNodes n c (T ℝ n)) ↔ P = T ℝ n := by
  refine ⟨fun h => ?_, by intro h; rw [h]⟩
  rw [sumNodes, sumNodes] at h
  apply eq_of_degrees_lt_of_eval_finset_eq ((Finset.range (n + 1)).image (node n ·))
  · apply lt_of_le_of_lt hPdeg
    rw [Nat.cast_lt, Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  · rw [degree_T, Int.natAbs_natCast, Nat.cast_lt,
      Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  replace h := ge_of_eq h
  contrapose! h
  obtain ⟨x, hx, hPx⟩ := h
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  replace hi := Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hi)
  suffices ∑ i ≤ n, ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * c i) <
      ∑ i ≤ n, ((-1) ^ i * (T ℝ n).eval (node n i)) * ((-1) ^ i * c i) by
    simpa [negOnePow_mul_negOnePow_mul_cancel]
  have h_le {i : ℕ} (hi : i ∈ Finset.Iic n) :
    (-1) ^ i * P.eval (node n i) * ((-1) ^ i * c i) ≤
    (-1) ^ i * (T ℝ n).eval (node n i) * ((-1) ^ i * c i) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hcpos i (Finset.mem_Iic.mp hi)))
    rw [eval_T_real_node hi, ← neg_pow', neg_neg, one_pow]
    exact negOnePow_mul_le (hPbnd _ node_mem_Icc)
  refine Finset.sum_lt_sum (fun i hi => h_le hi) ⟨i, hi, lt_of_le_of_ne (h_le hi) ?_⟩
  have := ne_of_lt (hcpos i (Finset.mem_Iic.mp hi))
  grind => ring

/-- Coefficients use to reproduce the leading coefficient of a polynomial given its values on the
Chebyshev nodes. -/
/-
**Polynomial.Chebyshev.leadingCoeffC** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Cheby
shev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coefficients use to reproduce the leading coefficient of a polynomial given its 
values on the
Chebyshev nodes.
-/
private noncomputable def leadingCoeffC (n i : ℕ) :=
  (∏ j ∈ (Finset.range (n + 1)).erase i, (node n i - node n j))⁻¹
/-
**Polynomial.Chebyshev.sumNodes_eq_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.C
hebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sumNodes_eq_coeff {n : ℕ} {P : ℝ[X]} (hP : P.degree ≤ n) :
    sumNodes n (leadingCoeffC n) P = P.coeff n := by
  simp_rw [sumNodes, leadingCoeffC]
  have : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    grw [hP]
    norm_cast
    simp
  convert! (Lagrange.coeff_eq_sum (strictAntiOn_node n).injOn this).symm using 2
  · exact Eq.symm (Nat.range_succ_eq_Iic n)
  · simp
/-
**Polynomial.Chebyshev.sumNodes_T_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheby
shev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sumNodes_T_eq (n : ℕ) :
    sumNodes n (leadingCoeffC n) (T ℝ n) = 2 ^ (n - 1) := by
  rw [sumNodes_eq_coeff (by simp)]
  trans (T ℝ n).leadingCoeff
  · simp [leadingCoeff]
  · simp
/-
**Polynomial.Chebyshev.negOnePow_mul_leadingCoeffC_pos** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial.Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem negOnePow_mul_leadingCoeffC_pos {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i * leadingCoeffC n i := by
  have := inv_pos_of_pos <| zero_lt_prod_node_sub_node hi
  rwa [mul_inv, ← inv_pow, inv_neg_one] at this
/-
**Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial.Chebyshev`。
形式化陈述：coeff_le_of_forall_abs_le_one {n : Nat} {P : Real[X]} (hPdeg : P.degree <=
 n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) : P.coeff n <= 2 ^ (n 
- 1)
参数：hPdeg : P.degree <= n；hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.sumNodes_eq_coeff`：∀ {n : ℕ} {P : Polynomial ℝ},   P.
degree ≤ ↑n → Polynomial.Chebyshev.sumNodes n (Polynomial.Chebyshev.leadingCoeff
C✝ n) P = P.coeff n
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.sumNodes_T_eq`：∀ (n : ℕ),   Polynomial.Chebyshev.sumN
odes n (Polynomial.Chebyshev.leadingCoeffC✝ n) (Polynomial.Chebyshev.T ℝ ↑n) = 2
 ^ (n - 1)
· 使用定理 `Polynomial.Chebyshev.sumNodes_le_sumNodes_T`：sumNodes_le_sumNodes_T {n :
 Nat} {c : Nat -> Real} (hcnonneg : forall i <= n, 0 <= (-1) ^ i * (c i)) {P : R
eal[X]} (hPbnd : forall x in Set.…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.negOnePow_mul_leadingCoeffC_pos`：∀ {n i : ℕ}, i ≤ n →
 0 < (-1) ^ i * Polynomial.Chebyshev.leadingCoeffC✝ n i
-/
theorem coeff_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.coeff n ≤ 2 ^ (n - 1) := by
  convert! sumNodes_le_sumNodes_T (fun i hi => le_of_lt <| negOnePow_mul_leadingCoeffC_pos hi) hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]
/-
**Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial.Chebyshev`。
形式化陈述：leadingCoeff_le_of_forall_abs_le_one {n : Nat} {P : Real[X]} (hPdeg : P.de
gree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) : P.leadingCoef
f <= 2 ^ (n - 1)
参数：hPdeg : P.degree <= n；hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithBot.coe_le`：∀ {α : Type u_1} {a b : α} [inst : LE α] {o : Option α},
 b ∈ o → (↑a ≤ o ↔ a ≤ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one`：coeff_le_of_forall_a
bs_le_one {n : Nat} {P : Real[X]} (hPdeg : P.degree <= n) (hPbnd : forall x in S
et.Icc (-1) 1, |P.eval x| <= 1) : P.coef…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.sub_le_sub_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n - k ≤ m - k
-/
theorem leadingCoeff_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.leadingCoeff ≤ 2 ^ (n - 1) := by
  by_cases P = 0
  case pos hP => simp [hP]
  case neg hP =>
    lift P.degree to ℕ using degree_ne_bot.mpr hP with d hd
    replace hPdeg : d ≤ n := (WithBot.coe_le rfl).mp hPdeg
    rw [leadingCoeff, natDegree_eq_of_degree_eq_some hd.symm]
    grw [coeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd, hPdeg]
    norm_num
/-
**Polynomial.Chebyshev.coeff_eq_iff_of_forall_abs_le_one** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial.Chebyshev`。
形式化陈述：coeff_eq_iff_of_forall_abs_le_one {n : Nat} {P : Real[X]} (hPdeg : P.degre
e <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) : P.coeff n = 2 ^ 
(n - 1) ↔ P = T Real n
参数：hPdeg : P.degree <= n；hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.sumNodes_eq_coeff`：∀ {n : ℕ} {P : Polynomial ℝ},   P.
degree ≤ ↑n → Polynomial.Chebyshev.sumNodes n (Polynomial.Chebyshev.leadingCoeff
C✝ n) P = P.coeff n
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.sumNodes_T_eq`：∀ (n : ℕ),   Polynomial.Chebyshev.sumN
odes n (Polynomial.Chebyshev.leadingCoeffC✝ n) (Polynomial.Chebyshev.T ℝ ↑n) = 2
 ^ (n - 1)
· 使用定理 `Polynomial.Chebyshev.sumNodes_eq_sumNodes_T_iff`：sumNodes_eq_sumNodes_T_
iff {n : Nat} {c : Nat -> Real} (hcpos : forall i <= n, 0 < (-1) ^ i * (c i)) {P
 : Real[X]} (hPdeg : P.degree <= n) (…
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.negOnePow_mul_leadingCoeffC_pos`：∀ {n i : ℕ}, i ≤ n →
 0 < (-1) ^ i * Polynomial.Chebyshev.leadingCoeffC✝ n i
-/
theorem coeff_eq_iff_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.coeff n = 2 ^ (n - 1) ↔ P = T ℝ n := by
  convert! sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_leadingCoeffC_pos hi) hPdeg hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]
/-
**Polynomial.Chebyshev.leadingCoeff_eq_iff_of_forall_abs_le_one** 是 Mathlib 中的一个
定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：leadingCoeff_eq_iff_of_forall_abs_le_one {n : Nat} {P : Real[X]} (hn : 2 <
= n) (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 
1) : P.leadingCoeff = 2 ^ (n - 1) ↔ P = T Real n
参数：hn : 2 <= n；hPdeg : P.degree <= n；hPbnd : forall x in Set.Icc (-1) 1, |P.eval
 x| <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Chebyshev.coeff_eq_iff_of_forall_abs_le_one`：coeff_eq_iff_of_
forall_abs_le_one {n : Nat} {P : Real[X]} (hPdeg : P.degree <= n) (hPbnd : foral
l x in Set.Icc (-1) 1, |P.eval x| <= 1) : P.…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`：leadingCoeff_
le_of_forall_abs_le_one {n : Nat} {P : Real[X]} (hPdeg : P.degree <= n) (hPbnd :
 forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `pow_lt_pow_right₀`：pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m <
 a ^ n
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 36 条，此处仅展示前 30 条）
-/
theorem leadingCoeff_eq_iff_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]} (hn : 2 ≤ n)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.leadingCoeff = 2 ^ (n - 1) ↔ P = T ℝ n := by
  refine ⟨fun hP => ?_, fun hP => by simp [hP]⟩
  apply (coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).mp
  suffices hPdeg' : n ≤ P.degree by
    replace hPdeg' : P.degree = n := eq_of_le_of_ge hPdeg hPdeg'
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some hPdeg'] at hP
  lift P.degree to ℕ with d hd
  · contrapose! hP
    rw [degree_eq_bot.mp hP, leadingCoeff_zero]
    positivity
  replace hP := ge_of_eq hP
  contrapose! hP
  have : d - 1 < n - 1 := by grind [Nat.cast_withBot, WithBot.coe_le_coe, WithBot.coe_lt_coe]
  calc P.leadingCoeff ≤ 2 ^ (d - 1) := leadingCoeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd
  _ < 2 ^ (n - 1) := by gcongr; norm_num

/-- Coefficients used to compute the iterated derivative of a polynomial given its values on the
Chebyshev nodes. -/
/-
**Polynomial.Chebyshev.iterateDerivativeC** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.
Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coefficients used to compute the iterated derivative of a polynomial given its v
alues on the
Chebyshev nodes.
-/
private noncomputable def iterateDerivativeC (n k : ℕ) (x : ℝ) (i : ℕ) :=
    k.factorial * (∏ j ∈ (Finset.range (n + 1)).erase i, ((node n i) - (node n j)))⁻¹ *
    ∑ t ∈ ((Finset.range (n + 1)).erase i).powersetCard (n - k), ∏ a ∈ t, (x - node n a)
/-
**Polynomial.Chebyshev.sumNodes_eq_eval_iterate_derivative** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial.Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sumNodes_eq_eval_iterate_derivative {n k : ℕ} (hk : k ≤ n) (x : ℝ)
    {P : ℝ[X]} (hP : P.degree ≤ n) :
    sumNodes n (iterateDerivativeC n k x) P = (derivative^[k] P).eval x := by
  simp_rw [sumNodes, iterateDerivativeC]
  have h₁ : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]; grw [hP]; norm_cast; simp
  convert!
    (Lagrange.eval_iterate_derivative_eq_sum (strictAntiOn_node n).injOn h₁
        (show k < _ by simp [hk]) x).symm
  rw [Finset.mul_sum]
  grind [Nat.range_succ_eq_Iic, Nat.card_Iic]
/-
**Polynomial.Chebyshev.negOnePow_mul_iterateDerivativeC_nonneg** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial.Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem negOnePow_mul_iterateDerivativeC_nonneg
    {n k i : ℕ} (hi : i ≤ n) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (-1) ^ i * iterateDerivativeC n k x i := by
  rw [iterateDerivativeC, ← mul_assoc]
  refine mul_nonneg ?_ (Finset.sum_nonneg' ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
    exact le_of_lt <| mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k)
      (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t => Finset.prod_nonneg (fun a _ => by grind [show node n a ≤ 1 from cos_le_one _])
/-
**Polynomial.Chebyshev.negOnePow_mul_iterateDerivativeC_pos** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial.Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem negOnePow_mul_iterateDerivativeC_pos
    {n k i : ℕ} (hk₁ : 0 < k) (hk₂ : k ≤ n) (hi : i ≤ n) {x : ℝ} (hx : 1 ≤ x) :
    0 < (-1) ^ i * iterateDerivativeC n k x i := by
  rw [iterateDerivativeC, ← mul_assoc]
  refine mul_pos ?_ (Finset.sum_pos' ?_ ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
    exact mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k) (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t _ => Finset.prod_nonneg (fun a _ => by grind [show node n a ≤ 1 from cos_le_one _])
  · have : ∃ s ⊆ (Finset.range (n + 1)).erase i, s.card = n - k ∧ 0 ∉ s := by
      by_cases 1 ≤ i ∧ i ≤ n - k
      case neg => exact ⟨Finset.Icc 1 (n - k), by grind, by grind [Nat.card_Icc], by simp⟩
      case pos => exact ⟨(Finset.Icc 1 (n - k + 1)).erase i, by grind, by grind [Nat.card_Icc],
        by simp⟩
    obtain ⟨s, hs, hscard, hsn⟩ := this
    refine ⟨s, by simp [hs, hscard], Finset.prod_pos (fun a ha => ?_)⟩
    grind [show node n a < 1 by rw [← node_eq_one (n := n)]; exact node_lt (by grind) (by grind)]
/-
**Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one** 是 Mathl
ib 中的一个定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：eval_iterate_derivative_le_of_forall_abs_le_one {n : Nat} {P : Real[X]} {k
 : Nat} {x : Real} (hx : 1 <= x) (hPdeg : P.degree <= n) (hPbnd : forall x in Se
t.Icc (-1) 1, |P.eval x| <= 1) : (derivative^[k] P).eval x <= (derivative^[k] (T
 Real n)).eval x
参数：hx : 1 <= x；hPdeg : P.degree <= n；hPbnd : forall x in Set.Icc (-1) 1, |P.eval
 x| <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.iterate_derivative_eq_zero_of_degree_lt`：iterate_derivative_e
q_zero_of_degree_lt {k : Nat} {P : R[X]} (h : P.degree < k) : derivative^[k] P =
 0
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Chebyshev.degree_T`：degree_T [IsDomain R] [NeZero (2 : R)] (n
 : Int) : (T R n).degree = n.natAbs
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.sumNodes_eq_eval_iterate_derivative`：∀ {n k : ℕ},   k
 ≤ n →     ∀ (x : ℝ) {P : Polynomial ℝ},       P.degree ≤ ↑n →         Polynomia
l.Chebyshev.sumNodes n (Polynomial.Chebyshev…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.Chebyshev.sumNodes_le_sumNodes_T`：sumNodes_le_sumNodes_T {n :
 Nat} {c : Nat -> Real} (hcnonneg : forall i <= n, 0 <= (-1) ^ i * (c i)) {P : R
eal[X]} (hPbnd : forall x in Set.…
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.negOnePow_mul_iterateDerivativeC_nonneg`：∀ {n k i : ℕ
}, i ≤ n → ∀ {x : ℝ}, 1 ≤ x → 0 ≤ (-1) ^ i * Polynomial.Chebyshev.iterateDerivat
iveC✝ n k x i
-/
theorem eval_iterate_derivative_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    {k : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    (derivative^[k] P).eval x ≤ (derivative^[k] (T ℝ n)).eval x := by
  by_cases! hk : n < k
  · rw [iterate_derivative_eq_zero_of_degree_lt (by grw [hPdeg]; simpa),
      iterate_derivative_eq_zero_of_degree_lt (by simp [hk])]
  convert!
    sumNodes_le_sumNodes_T (fun i hi => negOnePow_mul_iterateDerivativeC_nonneg hi hx) hPbnd using 1
  · rw [sumNodes_eq_eval_iterate_derivative hk x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk x (le_of_eq (degree_T ℝ n))]
/-
**Polynomial.Chebyshev.eval_iterate_derivative_eq_iff_of_bounded** 是 Mathlib 中的一
个定理，位于命名空间 `Polynomial.Chebyshev`。
形式化陈述：eval_iterate_derivative_eq_iff_of_bounded {n : Nat} {P : Real[X]} {k : Nat
} (hk₁ : 0 < k) (hk₂ : k <= n) {x : Real} (hx : 1 <= x) (hPdeg : P.degree <= n) 
(hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) : (derivative^[k] P).eval 
x = (derivative^[k] (T Real n)).eval x ↔ P = T Real n
参数：hk₁ : 0 < k；hk₂ : k <= n；hx : 1 <= x；hPdeg : P.degree <= n；hPbnd : forall x i
n Set.Icc (-1) 1, |P.eval x| <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.sumNodes_eq_eval_iterate_derivative`：∀ {n k : ℕ},   k
 ≤ n →     ∀ (x : ℝ) {P : Polynomial ℝ},       P.degree ≤ ↑n →         Polynomia
l.Chebyshev.sumNodes n (Polynomial.Chebyshev…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.Chebyshev.degree_T`：degree_T [IsDomain R] [NeZero (2 : R)] (n
 : Int) : (T R n).degree = n.natAbs
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.Chebyshev.sumNodes_eq_sumNodes_T_iff`：sumNodes_eq_sumNodes_T_
iff {n : Nat} {c : Nat -> Real} (hcpos : forall i <= n, 0 < (-1) ^ i * (c i)) {P
 : Real[X]} (hPdeg : P.degree <= n) (…
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extre
mal.0.Polynomial.Chebyshev.negOnePow_mul_iterateDerivativeC_pos`：∀ {n k i : ℕ}, 
  0 < k → k ≤ n → i ≤ n → ∀ {x : ℝ}, 1 ≤ x → 0 < (-1) ^ i * Polynomial.Chebyshev
.iterateDerivativeC✝ n k x i
-/
theorem eval_iterate_derivative_eq_iff_of_bounded {n : ℕ} {P : ℝ[X]}
    {k : ℕ} (hk₁ : 0 < k) (hk₂ : k ≤ n) {x : ℝ} (hx : 1 ≤ x)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    (derivative^[k] P).eval x = (derivative^[k] (T ℝ n)).eval x ↔ P = T ℝ n := by
  convert!
    sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_iterateDerivativeC_pos hk₁ hk₂ hi hx)
      hPdeg hPbnd using 2
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x (le_of_eq (degree_T ℝ n))]

end Polynomial.Chebyshev

