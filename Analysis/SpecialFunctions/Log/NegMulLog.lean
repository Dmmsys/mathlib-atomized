/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Convex.Deriv

/-!
# The functions `x ↦ x * log x` and `x ↦ - x * log x`

The purpose of this file is to record basic analytic properties of
- `x ↦ x * log x`, called `mul_log` in theorem statements
- `x ↦ - x * log x`, named `negMulLog`, which is notably used in the theory of Shannon entropy.

## Main definitions

* `negMulLog`: the function `x ↦ - x * log x` from `ℝ` to `ℝ`.

-/

@[expose] public section

open scoped Topology

namespace Real

section mulLog

/-
**Real.self_sub_one_lt_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：self_sub_one_lt_mul_log {x : Real} (h0 : 0 <= x) (h1 : x != 1) : x - 1 < x
 * x.log
参数：h0 : 0 <= x；h1 : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 93 条，此处仅展示前 30 条）
-/
lemma self_sub_one_lt_mul_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≠ 1) : x - 1 < x * x.log := by
  by_cases hx_pos : 0 < x
  · nlinarith [Real.log_inv x, Real.log_lt_sub_one_of_pos (inv_pos.mpr hx_pos) (by aesop),
      mul_inv_cancel₀ hx_pos.ne']
  · cases lt_or_eq_of_le h0 <;> aesop
/-
**Real.self_sub_one_le_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：self_sub_one_le_mul_log {x : Real} (h0 : 0 <= x) : x - 1 <= x * x.log
参数：h0 : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.self_sub_one_lt_mul_log`：self_sub_one_lt_mul_log {x : Real} (h0 : 0
 <= x) (h1 : x != 1) : x - 1 < x * x.log
-/
lemma self_sub_one_le_mul_log {x : ℝ} (h0 : 0 ≤ x) : x - 1 ≤ x * x.log := by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (self_sub_one_lt_mul_log h0 h1)

@[fun_prop]
/-
**Real.continuous_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：continuous_mul_log : Continuous fun x => x * log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Real.continuousAt_log`：continuousAt_log (hx : x != 0) : ContinuousAt log
 x
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
· 使用引理 `tendsto_log_mul_self_nhdsLT_zero`：tendsto_log_mul_self_nhdsLT_zero : Fil
ter.Tendsto (fun x => log x * x) (𝓝[<] 0) (𝓝 0)
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `tendsto_log_mul_rpow_nhdsGT_zero`：tendsto_log_mul_rpow_nhdsGT_zero {r : 
Real} (hr : 0 < r) : Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0)
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
（共 36 条，此处仅展示前 30 条）
-/
lemma continuous_mul_log : Continuous fun x ↦ x * log x := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain hx | rfl := ne_or_eq x 0
  · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [ContinuousAt, zero_mul]
  simp_rw [mul_comm _ (log _)]
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 ∪ {0} := by ext; simp [em]
  rw [this, nhdsWithin_union, nhdsWithin_union]
  simp only [nhdsWithin_singleton, Filter.tendsto_sup]
  refine ⟨⟨tendsto_log_mul_self_nhdsLT_zero, ?_⟩, ?_⟩
  · simpa only [rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  · convert! tendsto_pure_nhds (fun x ↦ log x * x) 0
    simp

@[fun_prop]
/-
**Real.Continuous.mul_log** 是 Mathlib 中的一个定理，位于命名空间 `Real.Continuous`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {f : α → ℝ}, Continuous f → C
ontinuous fun a => f a * Real.log (f a)
参数：f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `Real.continuous_mul_log`：continuous_mul_log : Continuous fun x => x * lo
g x
-/
lemma Continuous.mul_log {α : Type*} [TopologicalSpace α] {f : α → ℝ} (hf : Continuous f) :
    Continuous fun a ↦ f a * log (f a) := continuous_mul_log.comp hf
/-
**Real.differentiableOn_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：differentiableOn_mul_log : DifferentiableOn Real (fun x => x * log x) {0}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mul`：DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s)
 (hb : DifferentiableOn 𝕜 b s) : DifferentiableOn 𝕜 (a * b) s
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `Real.differentiableOn_log`：differentiableOn_log : DifferentiableOn Real 
log {0}ᶜ
-/
lemma differentiableOn_mul_log : DifferentiableOn ℝ (fun x ↦ x * log x) {0}ᶜ :=
  differentiable_id.differentiableOn.mul differentiableOn_log
/-
**Real.deriv_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv_mul_log {x : Real} (hx : x != 0) : deriv (fun x => x * log x) x = lo
g x + 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.deriv_log'`：deriv_log' : deriv log = Inv.inv
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deriv_mul_log {x : ℝ} (hx : x ≠ 0) : deriv (fun x ↦ x * log x) x = log x + 1 := by
  simp [hx]
/-
**Real.hasDerivAt_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_mul_log {x : Real} (hx : x != 0) : HasDerivAt (fun x => x * log
 x) (log x + 1) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.deriv_mul_log`：deriv_mul_log {x : Real} (hx : x != 0) : deriv (fun 
x => x * log x) x = log x + 1
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_deriv_iff`：hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x 
↔ DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用引理 `Real.differentiableOn_mul_log`：differentiableOn_mul_log : Differentiable
On Real (fun x => x * log x) {0}ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma hasDerivAt_mul_log {x : ℝ} (hx : x ≠ 0) : HasDerivAt (fun x ↦ x * log x) (log x + 1) x := by
  rw [← deriv_mul_log hx, hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_mul_log ?_
  simp [hx]

@[simp]
/-
**Real.rightDeriv_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rightDeriv_mul_log {x : Real} (hx : x != 0) : derivWithin (fun x => x * lo
g x) (Set.Ioi x) x = log x + 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用引理 `Real.hasDerivAt_mul_log`：hasDerivAt_mul_log {x : Real} (hx : x != 0) : H
asDerivAt (fun x => x * log x) (log x + 1) x
· 使用定理 `uniqueDiffWithinAt_Ioi`：uniqueDiffWithinAt_Ioi (a : Real) : UniqueDiffWi
thinAt Real (Ioi a) a
-/
lemma rightDeriv_mul_log {x : ℝ} (hx : x ≠ 0) :
    derivWithin (fun x ↦ x * log x) (Set.Ioi x) x = log x + 1 :=
  (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

@[simp]
/-
**Real.leftDeriv_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：leftDeriv_mul_log {x : Real} (hx : x != 0) : derivWithin (fun x => x * log
 x) (Set.Iio x) x = log x + 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用引理 `Real.hasDerivAt_mul_log`：hasDerivAt_mul_log {x : Real} (hx : x != 0) : H
asDerivAt (fun x => x * log x) (log x + 1) x
· 使用定理 `uniqueDiffWithinAt_Iio`：uniqueDiffWithinAt_Iio (a : Real) : UniqueDiffWi
thinAt Real (Iio a) a
-/
lemma leftDeriv_mul_log {x : ℝ} (hx : x ≠ 0) :
    derivWithin (fun x ↦ x * log x) (Set.Iio x) x = log x + 1 :=
  (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

open Filter in
/-
**Real.tendsto_deriv_mul_log_nhdsWithin_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma tendsto_deriv_mul_log_nhdsWithin_zero :
    Tendsto (deriv (fun x ↦ x * log x)) (𝓝[>] 0) atBot := by
  have : (deriv (fun x ↦ x * log x)) =ᶠ[𝓝[>] 0] (fun x ↦ log x + 1) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro x hx
    rw [Set.mem_Ioi] at hx
    exact deriv_mul_log hx.ne'
  simp only [tendsto_congr' this, tendsto_atBot_add_const_right, tendsto_log_nhdsGT_zero]

open Filter in
/-
**Real.tendsto_deriv_mul_log_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_deriv_mul_log_atTop : Tendsto (fun x => deriv (fun x => x * log x)
 x) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Real.deriv_mul_log`：deriv_mul_log {x : Real} (hx : x != 0) : deriv (fun 
x => x * log x) x = log x + 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Tendsto.atTop_add`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : LinearOrder α]   [IsOrderedAdd
Monoid α] [Ord…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma tendsto_deriv_mul_log_atTop :
    Tendsto (fun x ↦ deriv (fun x ↦ x * log x) x) atTop atTop := by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun _ hx ↦ deriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

open Filter in
/-
**Real.tendsto_rightDeriv_mul_log_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_rightDeriv_mul_log_atTop : Tendsto (fun x => derivWithin (fun x =>
 x * log x) (Set.Ioi x) x) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Real.rightDeriv_mul_log`：rightDeriv_mul_log {x : Real} (hx : x != 0) : d
erivWithin (fun x => x * log x) (Set.Ioi x) x = log x + 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Tendsto.atTop_add`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : LinearOrder α]   [IsOrderedAdd
Monoid α] [Ord…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma tendsto_rightDeriv_mul_log_atTop :
    Tendsto (fun x ↦ derivWithin (fun x ↦ x * log x) (Set.Ioi x) x) atTop atTop := by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun _ hx ↦ rightDeriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

/-- At `x=0`, `(fun x ↦ x * log x)` is not differentiable
(but note that it is continuous, see `continuous_mul_log`). -/
/-
**Real.not_DifferentiableAt_log_mul_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_DifferentiableAt_log_mul_zero : ¬ DifferentiableAt Real (fun x => x * 
log x) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi`：not_differentiabl
eWithinAt_of_deriv_tendsto_atBot_Ioi (f : Real -> Real) {a : Real} (hf : Tendsto
 (deriv f) (𝓝[>] a) atBot) : ¬ Differentiab…
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.NegMulLog.0.Real.tendsto_
deriv_mul_log_nhdsWithin_zero`：Filter.Tendsto (deriv fun x => x * Real.log x) (n
hdsWithin 0 (Set.Ioi 0)) Filter.atBot
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x

--- 原说明 ---
At `x=0`, `(fun x ↦ x * log x)` is not differentiable
(but note that it is continuous, see `continuous_mul_log`).
-/
lemma not_DifferentiableAt_log_mul_zero :
    ¬ DifferentiableAt ℝ (fun x ↦ x * log x) 0 := fun h ↦
  (not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (fun x : ℝ ↦ x * log x) (a := 0))
    tendsto_deriv_mul_log_nhdsWithin_zero
    (h.differentiableWithinAt (s := Set.Ioi 0))

/-- Not differentiable, hence `deriv` has junk value zero. -/
/-
**Real.deriv_mul_log_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv_mul_log_zero : deriv (fun x => x * log x) 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用引理 `Real.not_DifferentiableAt_log_mul_zero`：not_DifferentiableAt_log_mul_zer
o : ¬ DifferentiableAt Real (fun x => x * log x) 0

--- 原说明 ---
Not differentiable, hence `deriv` has junk value zero.
-/
lemma deriv_mul_log_zero : deriv (fun x ↦ x * log x) 0 = 0 :=
  deriv_zero_of_not_differentiableAt not_DifferentiableAt_log_mul_zero
/-
**Real.not_continuousAt_deriv_mul_log_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：not_continuousAt_deriv_mul_log_zero : ¬ ContinuousAt (deriv (fun (x : Real
) => x * log x)) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_continuousAt_of_tendsto`：not_continuousAt_of_tendsto {f : X -> Y} {l
₁ : Filter X} {l₂ : Filter Y} {x : X} (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l
₁ <= 𝓝 x) (hl₂ : …
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.NegMulLog.0.Real.tendsto_
deriv_mul_log_nhdsWithin_zero`：Filter.Tendsto (deriv fun x => x * Real.log x) (n
hdsWithin 0 (Set.Ioi 0)) Filter.atBot
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_continuousAt_deriv_mul_log_zero :
    ¬ ContinuousAt (deriv (fun (x : ℝ) ↦ x * log x)) 0 :=
  not_continuousAt_of_tendsto tendsto_deriv_mul_log_nhdsWithin_zero nhdsWithin_le_nhds (by simp)
/-
**Real.deriv2_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv2_mul_log (x : Real) : deriv^[2] (fun x => x * log x) x = x⁻¹
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用引理 `Real.not_continuousAt_deriv_mul_log_zero`：not_continuousAt_deriv_mul_log
_zero : ¬ ContinuousAt (deriv (fun (x : Real) => x * log x)) 0
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_ne_nhds`：eventually_ne_nhds [T1Space X] {a b : X} (h : a != b
) : forallᶠ x in 𝓝 a, x != b
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Real.deriv_mul_log`：deriv_mul_log {x : Real} (hx : x != 0) : deriv (fun 
x => x * log x) x = log x + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `deriv_add_const`：deriv_add_const (c : F) : deriv (fun y => f y + c) x = 
deriv f x
· 使用定理 `Real.deriv_log`：deriv_log (x : Real) : deriv log x = x⁻¹
-/
lemma deriv2_mul_log (x : ℝ) : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases hx : x = 0
  · rw [hx, inv_zero]
    exact deriv_zero_of_not_differentiableAt
      (fun h ↦ not_continuousAt_deriv_mul_log_zero h.continuousAt)
  · suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ x * log x) y = log y + 1 by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_add_const, deriv_log x]
    filter_upwards [eventually_ne_nhds hx] with y hy using deriv_mul_log hy
/-
**Real.strictConvexOn_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：strictConvexOn_mul_log : StrictConvexOn Real (Set.Ici (0 : Real)) (fun x =
> x * log x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConvexOn_of_deriv2_pos`：strictConvexOn_of_deriv2_pos {D : Set Real
} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf'' : forall
 x in interior D, …
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `Real.continuous_mul_log`：continuous_mul_log : Continuous fun x => x * lo
g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.deriv2_mul_log`：deriv2_mul_log (x : Real) : deriv^[2] (fun x => x *
 log x) x = x⁻¹
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
-/
lemma strictConvexOn_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_mul_log]
  positivity
/-
**Real.convexOn_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：convexOn_mul_log : ConvexOn Real (Set.Ici (0 : Real)) (fun x => x * log x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.convexOn`：StrictConvexOn.convexOn {s : Set E} {f : E -> β
} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f
· 使用引理 `Real.strictConvexOn_mul_log`：strictConvexOn_mul_log : StrictConvexOn Rea
l (Set.Ici (0 : Real)) (fun x => x * log x)
-/
lemma convexOn_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) :=
  strictConvexOn_mul_log.convexOn
/-
**Real.mul_log_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：mul_log_nonneg {x : Real} (hx : 1 <= x) : 0 <= x * log x
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
-/
lemma mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)
/-
**Real.mul_log_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：mul_log_pos {x : Real} (hx : 1 < x) : 0 < x * log x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
-/
lemma mul_log_pos {x : ℝ} (hx : 1 < x) : 0 < x * log x :=
  mul_pos (zero_lt_one.trans hx) (log_pos hx)
/-
**Real.mul_log_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：mul_log_nonpos {x : Real} (hx₀ : 0 <= x) (hx₁ : x <= 1) : x * log x <= 0
参数：hx₀ : 0 <= x；hx₁ : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.log_nonpos`：log_nonpos (hx : 0 <= x) (h'x : x <= 1) : log x <= 0
-/
lemma mul_log_nonpos {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : x * log x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hx₀ (log_nonpos hx₀ hx₁)
/-
**Real.mul_log_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：mul_log_neg {x : Real} (hx₀ : 0 < x) (hx₁ : x < 1) : x * log x < 0
参数：hx₀ : 0 < x；hx₁ : x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
-/
lemma mul_log_neg {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : x * log x < 0 :=
    mul_neg_of_pos_of_neg  hx₀ (log_neg hx₀ hx₁)

end mulLog

section negMulLog

/-- The function `x ↦ - x * log x` from `ℝ` to `ℝ`. -/
/-
**Real.negMulLog** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：negMulLog (x : Real) : Real
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `x ↦ - x * log x` from `ℝ` to `ℝ`.
-/
noncomputable def negMulLog (x : ℝ) : ℝ := - x * log x
/-
**Real.negMulLog_def** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：negMulLog_def : negMulLog = fun x => - x * log x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma negMulLog_def : negMulLog = fun x ↦ - x * log x := rfl
/-
**Real.negMulLog_eq_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：negMulLog_eq_neg : negMulLog = fun x => -(x * log x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma negMulLog_eq_neg : negMulLog = fun x ↦ -(x * log x) := by simp [negMulLog_def]
/-
**Real.negMulLog_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Real.negMulLog 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma negMulLog_zero : negMulLog (0 : ℝ) = 0 := by simp [negMulLog]
/-
**Real.negMulLog_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Real.negMulLog 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma negMulLog_one : negMulLog (1 : ℝ) = 0 := by simp [negMulLog]
/-
**Real.negMulLog_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：negMulLog_nonneg {x : Real} (h1 : 0 <= x) (h2 : x <= 1) : 0 <= negMulLog x
参数：h1 : 0 <= x；h2 : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Real.negMulLog_eq_neg`：negMulLog_eq_neg : negMulLog = fun x => -(x * log
 x)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Real.mul_log_nonpos`：mul_log_nonpos {x : Real} (hx₀ : 0 <= x) (hx₁ : x <
= 1) : x * log x <= 0
-/
lemma negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x := by
  simpa only [negMulLog_eq_neg, neg_nonneg] using mul_log_nonpos h1 h2
/-
**Real.negMulLog_mul** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：negMulLog_mul (x y : Real) : negMulLog (x * y) = y * negMulLog x + x * neg
MulLog y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 40 条，此处仅展示前 30 条）
-/
lemma negMulLog_mul (x y : ℝ) : negMulLog (x * y) = y * negMulLog x + x * negMulLog y := by
  simp only [negMulLog, neg_mul]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [log_mul hx hy]
  ring
/-
**Real.continuous_negMulLog** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Continuous Real.negMulLog
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.negMulLog_eq_neg`：negMulLog_eq_neg : negMulLog = fun x => -(x * log
 x)
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `Real.continuous_mul_log`：continuous_mul_log : Continuous fun x => x * lo
g x
-/
@[fun_prop] lemma continuous_negMulLog : Continuous negMulLog := by
  simpa only [negMulLog_eq_neg] using continuous_mul_log.fun_neg
/-
**Real.differentiableOn_negMulLog** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：differentiableOn_negMulLog : DifferentiableOn Real negMulLog {0}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.negMulLog_eq_neg`：negMulLog_eq_neg : negMulLog = fun x => -(x * log
 x)
· 使用定理 `DifferentiableOn.neg`：DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) 
: DifferentiableOn 𝕜 (-f) s
· 使用引理 `Real.differentiableOn_mul_log`：differentiableOn_mul_log : Differentiable
On Real (fun x => x * log x) {0}ᶜ
-/
lemma differentiableOn_negMulLog : DifferentiableOn ℝ negMulLog {0}ᶜ := by
  simpa only [negMulLog_eq_neg] using! differentiableOn_mul_log.neg
/-
**Real.differentiableAt_negMulLog_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：differentiableAt_negMulLog_iff {x : Real} : DifferentiableAt Real negMulLo
g x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.not_DifferentiableAt_log_mul_zero`：not_DifferentiableAt_log_mul_zer
o : ¬ DifferentiableAt Real (fun x => x * log x) 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Real.differentiableOn_negMulLog`：differentiableOn_negMulLog : Differenti
ableOn Real negMulLog {0}ᶜ
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma differentiableAt_negMulLog_iff {x : ℝ} : DifferentiableAt ℝ negMulLog x ↔ x ≠ 0 := by
  constructor
  · unfold negMulLog
    intro h eq0
    simp only [neg_mul, differentiableAt_fun_neg_iff, eq0] at h
    exact not_DifferentiableAt_log_mul_zero h
  · intro hx
    have : x ∈ ({0} : Set ℝ)ᶜ := by
      simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_true]
    have := differentiableOn_negMulLog x this
    apply DifferentiableWithinAt.differentiableAt (s := {0}ᶜ) <;>
    simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_true,
      compl_singleton_mem_nhds_iff]

@[fun_prop] alias ⟨_, differentiableAt_negMulLog⟩ := differentiableAt_negMulLog_iff
/-
**Real.deriv_negMulLog** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv_negMulLog {x : Real} (hx : x != 0) : deriv negMulLog x = - log x - 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.negMulLog_eq_neg`：negMulLog_eq_neg : negMulLog = fun x => -(x * log
 x)
· 使用定理 `deriv.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Ty
pe v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F} {
x :…
· 使用引理 `Real.deriv_mul_log`：deriv_mul_log {x : Real} (hx : x != 0) : deriv (fun 
x => x * log x) x = log x + 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
-/
lemma deriv_negMulLog {x : ℝ} (hx : x ≠ 0) : deriv negMulLog x = - log x - 1 := by
  rw [negMulLog_eq_neg, deriv.fun_neg, deriv_mul_log hx]
  ring
/-
**Real.hasDerivAt_negMulLog** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_negMulLog {x : Real} (hx : x != 0) : HasDerivAt negMulLog (- lo
g x - 1) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.deriv_negMulLog`：deriv_negMulLog {x : Real} (hx : x != 0) : deriv n
egMulLog x = - log x - 1
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_deriv_iff`：hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x 
↔ DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用引理 `Real.differentiableOn_negMulLog`：differentiableOn_negMulLog : Differenti
ableOn Real negMulLog {0}ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma hasDerivAt_negMulLog {x : ℝ} (hx : x ≠ 0) : HasDerivAt negMulLog (- log x - 1) x := by
  rw [← deriv_negMulLog hx, hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_negMulLog ?_
  simp [hx]
/-
**Real.deriv2_negMulLog** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv2_negMulLog (x : Real) : deriv^[2] negMulLog x = -x⁻¹
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.negMulLog_eq_neg`：negMulLog_eq_neg : negMulLog = fun x => -(x * log
 x)
· 使用引理 `Real.deriv2_mul_log`：deriv2_mul_log (x : Real) : deriv^[2] (fun x => x *
 log x) x = x⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `deriv.fun_neg'`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : T
ype v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F},
 (de…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma deriv2_negMulLog (x : ℝ) : deriv^[2] negMulLog x = -x⁻¹ := by
  rw [negMulLog_eq_neg]
  have h := deriv2_mul_log
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, deriv.fun_neg',
    Function.comp_apply] at h ⊢
  rw [h]
/-
**Real.strictConcaveOn_negMulLog** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：strictConcaveOn_negMulLog : StrictConcaveOn Real (Set.Ici (0 : Real)) negM
ulLog
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.negMulLog_eq_neg`：negMulLog_eq_neg : negMulLog = fun x => -(x * log
 x)
· 使用定理 `StrictConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst
 : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : 
AddCommG…
· 使用引理 `Real.strictConvexOn_mul_log`：strictConvexOn_mul_log : StrictConvexOn Rea
l (Set.Ici (0 : Real)) (fun x => x * log x)
-/
lemma strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog := by
  simpa only [negMulLog_eq_neg] using! strictConvexOn_mul_log.neg
/-
**Real.concaveOn_negMulLog** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：concaveOn_negMulLog : ConcaveOn Real (Set.Ici (0 : Real)) negMulLog
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConcaveOn.concaveOn`：StrictConcaveOn.concaveOn {s : Set E} {f : E 
-> β} (hf : StrictConcaveOn 𝕜 s f) : ConcaveOn 𝕜 s f
· 使用引理 `Real.strictConcaveOn_negMulLog`：strictConcaveOn_negMulLog : StrictConcav
eOn Real (Set.Ici (0 : Real)) negMulLog
-/
lemma concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog :=
  strictConcaveOn_negMulLog.concaveOn
/-
**Real.negMulLog_lt_one_sub_self** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：negMulLog_lt_one_sub_self {x : Real} (h0 : 0 <= x) (h1 : x != 1) : x.negMu
lLog < 1 - x
参数：h0 : 0 <= x；h1 : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 45 条，此处仅展示前 30 条）
-/
lemma negMulLog_lt_one_sub_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≠ 1) : x.negMulLog < 1 - x := by
  unfold negMulLog
  linarith [self_sub_one_lt_mul_log h0 h1]
/-
**Real.negMulLog_le_one_sub_self** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：negMulLog_le_one_sub_self {x : Real} (h0 : 0 <= x) : x.negMulLog <= 1 - x
参数：h0 : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.negMulLog_one`：Real.negMulLog 1 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.negMulLog_lt_one_sub_self`：negMulLog_lt_one_sub_self {x : Real} (h0
 : 0 <= x) (h1 : x != 1) : x.negMulLog < 1 - x
-/
lemma negMulLog_le_one_sub_self {x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x :=by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (negMulLog_lt_one_sub_self h0 h1)

end negMulLog

end Real

