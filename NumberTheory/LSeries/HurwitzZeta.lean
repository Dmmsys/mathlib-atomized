/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Hurwitz zeta function

This file gives the definition and properties of the following two functions:

* The **Hurwitz zeta function**, which is the meromorphic continuation to all `s ∈ ℂ` of the
  function defined for `1 < re s` by the series

  `∑' n, 1 / (n + a) ^ s`

  for a parameter `a ∈ ℝ`, with the sum taken over all `n` such that `n + a > 0`;

* the related sum, which we call the "**exponential zeta function**" (does it have a standard name?)

  `∑' n : ℕ, exp (2 * π * I * n * a) / n ^ s`.

## Main definitions and results

* `hurwitzZeta`: the Hurwitz zeta function (defined to be periodic in `a` with period 1)
* `expZeta`: the exponential zeta function
* `hasSum_hurwitzZeta_of_one_lt_re` and `hasSum_expZeta_of_one_lt_re`:
  relation to Dirichlet series for `1 < re s`
* ` hurwitzZeta_residue_one` shows that the residue at `s = 1` equals `1`
* `differentiableAt_hurwitzZeta` and `differentiableAt_expZeta`: analyticity away from `s = 1`
* `hurwitzZeta_one_sub` and `expZeta_one_sub`: functional equations `s ↔ 1 - s`.
-/

@[expose] public section

open Set Real Complex Filter Topology

namespace HurwitzZeta

/-!
## The Hurwitz zeta function
-/

/-- The Hurwitz zeta function, which is the meromorphic continuation of
`∑ (n : ℕ), 1 / (n + a) ^ s` if `0 ≤ a ≤ 1`. See `hasSum_hurwitzZeta_of_one_lt_re` for the relation
to the Dirichlet series in the convergence range. -/
/-
**HurwitzZeta.hurwitzZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZeta (a : UnitAddCircle) (s : Complex)
参数：a : UnitAddCircle；s : Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hurwitz zeta function, which is the meromorphic continuation of
`∑ (n : ℕ), 1 / (n + a) ^ s` if `0 ≤ a ≤ 1`. See `hasSum_hurwitzZeta_of_one_lt_r
e` for the relation
to the Dirichlet series in the convergence range.
-/
noncomputable def hurwitzZeta (a : UnitAddCircle) (s : ℂ) :=
  hurwitzZetaEven a s + hurwitzZetaOdd a s
/-
**HurwitzZeta.hurwitzZetaEven_eq** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaEven_eq (a : UnitAddCircle) (s : Complex) : hurwitzZetaEven a s
 = (hurwitzZeta a s + hurwitzZeta (-a) s) / 2
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HurwitzZeta.hurwitzZetaEven_neg`：hurwitzZetaEven_neg (a : UnitAddCircle)
 (s : Complex) : hurwitzZetaEven (-a) s = hurwitzZetaEven a s
· 使用引理 `HurwitzZeta.hurwitzZetaOdd_neg`：hurwitzZetaOdd_neg (a : UnitAddCircle) (
s : Complex) : hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 55 条，此处仅展示前 30 条）
-/
lemma hurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaEven a s = (hurwitzZeta a s + hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf
/-
**HurwitzZeta.hurwitzZetaOdd_eq** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaOdd_eq (a : UnitAddCircle) (s : Complex) : hurwitzZetaOdd a s =
 (hurwitzZeta a s - hurwitzZeta (-a) s) / 2
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HurwitzZeta.hurwitzZetaEven_neg`：hurwitzZetaEven_neg (a : UnitAddCircle)
 (s : Complex) : hurwitzZetaEven (-a) s = hurwitzZetaEven a s
· 使用引理 `HurwitzZeta.hurwitzZetaOdd_neg`：hurwitzZetaOdd_neg (a : UnitAddCircle) (
s : Complex) : hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 57 条，此处仅展示前 30 条）
-/
lemma hurwitzZetaOdd_eq (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaOdd a s = (hurwitzZeta a s - hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

/-- The Hurwitz zeta function is differentiable away from `s = 1`. -/
/-
**HurwitzZeta.differentiableAt_hurwitzZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZet
a`。
形式化陈述：differentiableAt_hurwitzZeta (a : UnitAddCircle) {s : Complex} (hs : s != 
1) : DifferentiableAt Complex (hurwitzZeta a) s
参数：a : UnitAddCircle；hs : s != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.add`：DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f + g) x
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZetaEven`：differentiableAt_hurwitzZe
taEven (a : UnitAddCircle) {s : Complex} (hs' : s != 1) : DifferentiableAt Compl
ex (hurwitzZetaEven a) s
· 使用引理 `HurwitzZeta.differentiable_hurwitzZetaOdd`：differentiable_hurwitzZetaOdd
 (a : UnitAddCircle) : Differentiable Complex (hurwitzZetaOdd a)

--- 原说明 ---
The Hurwitz zeta function is differentiable away from `s = 1`.
-/
lemma differentiableAt_hurwitzZeta (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (hurwitzZeta a) s :=
  (differentiableAt_hurwitzZetaEven a hs).add (differentiable_hurwitzZetaOdd a s)

/-- Formula for `hurwitzZeta s` as a Dirichlet series in the convergence range. We
restrict to `a ∈ Icc 0 1` to simplify the statement. -/
/-
**HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `Hurwitz
Zeta`。
形式化陈述：hasSum_hurwitzZeta_of_one_lt_re {a : Real} (ha : a in Icc 0 1) {s : Comple
x} (hs : 1 < re s) : HasSum (fun n : Nat => 1 / (n + a : Complex) ^ s) (hurwitzZ
eta a s)
参数：ha : a in Icc 0 1；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `hurwitzZeta s` as a Dirichlet series in the convergence range. We
restrict to `a ∈ Icc 0 1` to simplify the statement.
-/
lemma hasSum_hurwitzZeta_of_one_lt_re {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ 1 / (n + a : ℂ) ^ s) (hurwitzZeta a s) := by
  convert!
    (hasSum_nat_hurwitzZetaEven_of_mem_Icc ha hs).add (hasSum_nat_hurwitzZetaOdd_of_mem_Icc ha hs)
    using 1
  ext1 n
  -- plain `ring_nf` works here, but the following is faster:
  apply show ∀ (x y : ℂ), x = (x + y) / 2 + (x - y) / 2 by intros; ring

/-- The residue of the Hurwitz zeta function at `s = 1` is `1`. -/
/-
**HurwitzZeta.hurwitzZeta_residue_one** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZeta_residue_one (a : UnitAddCircle) : Tendsto (fun s => (s - 1) * 
hurwitzZeta a s) (𝓝[!=] 1) (𝓝 1)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HurwitzZeta.hurwitzZetaEven_residue_one`：hurwitzZetaEven_residue_one (a 
: UnitAddCircle) : Tendsto (fun s => (s - 1) * hurwitzZetaEven a s) (𝓝[!=] 1) (𝓝
 1)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The residue of the Hurwitz zeta function at `s = 1` is `1`.
-/
lemma hurwitzZeta_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * hurwitzZeta a s) (𝓝[≠] 1) (𝓝 1) := by
  simp only [hurwitzZeta, mul_add, (by simp : 𝓝 (1 : ℂ) = 𝓝 (1 + (1 - 1) * hurwitzZetaOdd a 1))]
  refine (hurwitzZetaEven_residue_one a).add ((Tendsto.mul ?_ ?_).mono_left nhdsWithin_le_nhds)
  exacts [tendsto_id.sub_const _, (differentiable_hurwitzZetaOdd a).continuous.tendsto _]
/-
**HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div** 是 Mathlib 中的一个引理，位于命名空间
 `HurwitzZeta`。
形式化陈述：differentiableAt_hurwitzZeta_sub_one_div (a : UnitAddCircle) : Differentia
bleAt Complex (fun s => hurwitzZeta a s - 1 / (s - 1) / GammaReal s) 1
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a + b - c = a - c + b
· 使用定理 `DifferentiableAt.add`：DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f + g) x
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div`：differentiable
At_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) : DifferentiableAt Complex (f
un s => hurwitzZetaEven a s - 1 / (s - 1) / Ga…
· 使用引理 `HurwitzZeta.differentiable_hurwitzZetaOdd`：differentiable_hurwitzZetaOdd
 (a : UnitAddCircle) : Differentiable Complex (hurwitzZetaOdd a)
-/
lemma differentiableAt_hurwitzZeta_sub_one_div (a : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s) 1 := by
  simp only [hurwitzZeta, add_sub_right_comm]
  exact (differentiableAt_hurwitzZetaEven_sub_one_div a).add (differentiable_hurwitzZetaOdd a 1)

/-- Expression for `hurwitzZeta a 1` as a limit. (Mathematically `hurwitzZeta a 1` is
undefined, but our construction assigns some value to it; this lemma is mostly of interest for
determining what that value is). -/
/-
**HurwitzZeta.tendsto_hurwitzZeta_sub_one_div_nhds_one** 是 Mathlib 中的一个引理，位于命名空间
 `HurwitzZeta`。
形式化陈述：tendsto_hurwitzZeta_sub_one_div_nhds_one (a : UnitAddCircle) : Tendsto (fu
n s => hurwitzZeta a s - 1 / (s - 1) / GammaReal s) (𝓝 1) (𝓝 (hurwitzZeta a 1))
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a + b - c = a - c + b
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one`：tendsto_hurwit
zZetaEven_sub_one_div_nhds_one (a : UnitAddCircle) : Tendsto (fun s => hurwitzZe
taEven a s - 1 / (s - 1) / GammaReal s) (𝓝 1) …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `HurwitzZeta.differentiable_hurwitzZetaOdd`：differentiable_hurwitzZetaOdd
 (a : UnitAddCircle) : Differentiable Complex (hurwitzZetaOdd a)

--- 原说明 ---
Expression for `hurwitzZeta a 1` as a limit. (Mathematically `hurwitzZeta a 1` i
s
undefined, but our construction assigns some value to it; this lemma is mostly o
f interest for
determining what that value is).
-/
lemma tendsto_hurwitzZeta_sub_one_div_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s) (𝓝 1) (𝓝 (hurwitzZeta a 1)) := by
  simp only [hurwitzZeta, add_sub_right_comm]
  refine (tendsto_hurwitzZetaEven_sub_one_div_nhds_one a).add
    (differentiable_hurwitzZetaOdd a 1).continuousAt.tendsto

/-- The difference of two Hurwitz zeta functions is differentiable everywhere. -/
/-
**HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta** 是 Mathlib 中的一个引理，位于命名
空间 `HurwitzZeta`。
形式化陈述：differentiable_hurwitzZeta_sub_hurwitzZeta (a b : UnitAddCircle) : Differe
ntiable Complex (fun s => hurwitzZeta a s - hurwitzZeta b s)
参数：a b : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `Differentiable.add`：Differentiable.add (hf : Differentiable 𝕜 f) (hg : D
ifferentiable 𝕜 g) : Differentiable 𝕜 (f + g)
· 使用引理 `HurwitzZeta.differentiable_hurwitzZetaEven_sub_hurwitzZetaEven`：differen
tiable_hurwitzZetaEven_sub_hurwitzZetaEven (a b : UnitAddCircle) : Differentiabl
e Complex (fun s => hurwitzZetaEven a s - hurwitzZet…
· 使用定理 `Differentiable.sub`：Differentiable.sub (hf : Differentiable 𝕜 f) (hg : D
ifferentiable 𝕜 g) : Differentiable 𝕜 (f - g)
· 使用引理 `HurwitzZeta.differentiable_hurwitzZetaOdd`：differentiable_hurwitzZetaOdd
 (a : UnitAddCircle) : Differentiable Complex (hurwitzZetaOdd a)

--- 原说明 ---
The difference of two Hurwitz zeta functions is differentiable everywhere.
-/
lemma differentiable_hurwitzZeta_sub_hurwitzZeta (a b : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZeta a s - hurwitzZeta b s) := by
  simp only [hurwitzZeta, add_sub_add_comm]
  refine (differentiable_hurwitzZetaEven_sub_hurwitzZetaEven a b).add (.sub ?_ ?_)
  all_goals apply differentiable_hurwitzZetaOdd

/-!
## The exponential zeta function
-/

/-- Meromorphic continuation of the series `∑' (n : ℕ), exp (2 * π * I * a * n) / n ^ s`.  See
`hasSum_expZeta_of_one_lt_re` for the relation to the Dirichlet series. -/
/-
**HurwitzZeta.expZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：expZeta (a : UnitAddCircle) (s : Complex)
参数：a : UnitAddCircle；s : Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Meromorphic continuation of the series `∑' (n : ℕ), exp (2 * π * I * a * n) / n 
^ s`.  See
`hasSum_expZeta_of_one_lt_re` for the relation to the Dirichlet series.
-/
noncomputable def expZeta (a : UnitAddCircle) (s : ℂ) :=
  cosZeta a s + I * sinZeta a s
/-
**HurwitzZeta.cosZeta_eq** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosZeta_eq (a : UnitAddCircle) (s : Complex) : cosZeta a s = (expZeta a s 
+ expZeta (-a) s) / 2
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.expZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZeta.exp
Zeta a s = HurwitzZeta.cosZeta a s + Complex.I * HurwitzZeta.sinZeta a s
· 使用引理 `HurwitzZeta.cosZeta_neg`：cosZeta_neg (a : UnitAddCircle) (s : Complex) :
 cosZeta (-a) s = cosZeta a s
· 使用引理 `HurwitzZeta.sinZeta_neg`：sinZeta_neg (a : UnitAddCircle) (s : Complex) :
 sinZeta (-a) s = -sinZeta a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
（共 60 条，此处仅展示前 30 条）
-/
lemma cosZeta_eq (a : UnitAddCircle) (s : ℂ) :
    cosZeta a s = (expZeta a s + expZeta (-a) s) / 2 := by
  rw [expZeta, expZeta, cosZeta_neg, sinZeta_neg]
  ring_nf
/-
**HurwitzZeta.sinZeta_eq** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：sinZeta_eq (a : UnitAddCircle) (s : Complex) : sinZeta a s = (expZeta a s 
- expZeta (-a) s) / (2 * I)
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.expZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZeta.exp
Zeta a s = HurwitzZeta.cosZeta a s + Complex.I * HurwitzZeta.sinZeta a s
· 使用引理 `HurwitzZeta.cosZeta_neg`：cosZeta_neg (a : UnitAddCircle) (s : Complex) :
 cosZeta (-a) s = cosZeta a s
· 使用引理 `HurwitzZeta.sinZeta_neg`：sinZeta_neg (a : UnitAddCircle) (s : Complex) :
 sinZeta (-a) s = -sinZeta a s
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
（共 76 条，此处仅展示前 30 条）
-/
lemma sinZeta_eq (a : UnitAddCircle) (s : ℂ) :
    sinZeta a s = (expZeta a s - expZeta (-a) s) / (2 * I) := by
  rw [expZeta, expZeta, cosZeta_neg, sinZeta_neg]
  field
/-
**HurwitzZeta.hasSum_expZeta_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：hasSum_expZeta_of_one_lt_re (a : Real) {s : Complex} (hs : 1 < re s) : Has
Sum (fun n : Nat => cexp (2 * π * I * a * n) / n ^ s) (expZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasSum.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f g : β → α} {a b : α}   {L : SummationFilter β} [Co
…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HurwitzZeta.hasSum_nat_cosZeta`：hasSum_nat_cosZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Nat => Real.cos (2 * π * a * n) / (n : Com
plex) ^ s) (cosZeta …
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `HurwitzZeta.hasSum_nat_sinZeta`：hasSum_nat_sinZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Nat => Real.sin (2 * π * a * n) / (n : Com
plex) ^ s) (sinZeta …
-/
lemma hasSum_expZeta_of_one_lt_re (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ cexp (2 * π * I * a * n) / n ^ s) (expZeta a s) := by
  convert! (hasSum_nat_cosZeta a hs).add ((hasSum_nat_sinZeta a hs).mul_left I) using 1
  ext1 n
  simp only [mul_right_comm _ I, ← cos_add_sin_I, push_cast]
  rw [add_div, mul_div, mul_comm _ I]
/-
**HurwitzZeta.differentiableAt_expZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：differentiableAt_expZeta (a : UnitAddCircle) (s : Complex) (hs : s != 1 ∨ 
a != 0) : DifferentiableAt Complex (expZeta a) s
参数：a : UnitAddCircle；s : Complex；hs : s != 1 ∨ a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.add`：DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f + g) x
· 使用引理 `HurwitzZeta.differentiableAt_cosZeta`：differentiableAt_cosZeta (a : Unit
AddCircle) {s : Complex} (hs' : s != 1 ∨ a != 0) : DifferentiableAt Complex (cos
Zeta a) s
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用引理 `HurwitzZeta.differentiableAt_sinZeta`：differentiableAt_sinZeta (a : Unit
AddCircle) : Differentiable Complex (sinZeta a)
-/
lemma differentiableAt_expZeta (a : UnitAddCircle) (s : ℂ) (hs : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (expZeta a) s := by
  apply DifferentiableAt.add
  · exact differentiableAt_cosZeta a hs
  · apply (differentiableAt_const _).mul (differentiableAt_sinZeta a s)

/-- If `a ≠ 0` then the exponential zeta function is analytic everywhere. -/
/-
**HurwitzZeta.differentiable_expZeta_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Hurwi
tzZeta`。
形式化陈述：differentiable_expZeta_of_ne_zero {a : UnitAddCircle} (ha : a != 0) : Diff
erentiable Complex (expZeta a)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HurwitzZeta.differentiableAt_expZeta`：differentiableAt_expZeta (a : Unit
AddCircle) (s : Complex) (hs : s != 1 ∨ a != 0) : DifferentiableAt Complex (expZ
eta a) s

--- 原说明 ---
If `a ≠ 0` then the exponential zeta function is analytic everywhere.
-/
lemma differentiable_expZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
    Differentiable ℂ (expZeta a) :=
  (differentiableAt_expZeta a · (Or.inr ha))

/-- Reformulation of `hasSum_expZeta_of_one_lt_re` using `LSeriesHasSum`. -/
/-
**HurwitzZeta.LSeriesHasSum_exp** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：LSeriesHasSum_exp (a : Real) {s : Complex} (hs : 1 < re s) : LSeriesHasSum
 (cexp <| 2 * π * I * a * ·) s (expZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.hasSum_expZeta_of_one_lt_re`：hasSum_expZeta_of_one_lt_re (a 
: Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Nat => cexp (2 * π * I *
 a * n) / n ^ s) (expZeta a s…
· 使用引理 `LSeries.term_of_ne_zero'`：term_of_ne_zero' {s : Complex} (hs : s != 0) (
f : Nat -> Complex) (n : Nat) : term f s n = f n / n ^ s
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0

--- 原说明 ---
Reformulation of `hasSum_expZeta_of_one_lt_re` using `LSeriesHasSum`.
-/
lemma LSeriesHasSum_exp (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (cexp <| 2 * π * I * a * ·) s (expZeta a s) :=
  (hasSum_expZeta_of_one_lt_re a hs).congr_fun
    (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

/-!
## The functional equation
-/

/-
**HurwitzZeta.hurwitzZeta_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZeta_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Na
t), s != -n) (hs' : a != 0 ∨ s != 1) : hurwitzZeta a (1 - s) = (2 * π) ^ (-s) * 
Gamma s * (exp (-π * I * s / 2) * expZeta a s + exp (π * I * s / 2) * expZeta (-
a) s)
参数：a : UnitAddCircle；hs : forall (n : Nat), s != -n；hs' : a != 0 ∨ s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.hurwitzZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ),   HurwitzZe
ta.hurwitzZeta a s = HurwitzZeta.hurwitzZetaEven a s + HurwitzZeta.hurwitzZetaOd
d a s
· 使用引理 `HurwitzZeta.hurwitzZetaEven_one_sub`：hurwitzZetaEven_one_sub (a : UnitAd
dCircle) {s : Complex} (hs : forall (n : Nat), s != -n) (hs' : a != 0 ∨ s != 1) 
: hurwitzZetaEven a (1 - …
· 使用引理 `HurwitzZeta.hurwitzZetaOdd_one_sub`：hurwitzZetaOdd_one_sub (a : UnitAddC
ircle) {s : Complex} (hs : forall (n : Nat), s != -n) : hurwitzZetaOdd a (1 - s)
 = 2 * (2 * π) ^ (-s) * …
· 使用定理 `HurwitzZeta.expZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZeta.exp
Zeta a s = HurwitzZeta.cosZeta a s + Complex.I * HurwitzZeta.sinZeta a s
· 使用定理 `Complex.cos.eq_1`：∀ (z : ℂ), Complex.cos z = (Complex.exp (z * Complex.I
) + Complex.exp (-z * Complex.I)) / 2
· 使用定理 `Complex.sin.eq_1`：∀ (z : ℂ), Complex.sin z = (Complex.exp (-z * Complex.
I) - Complex.exp (z * Complex.I)) * Complex.I / 2
· 使用引理 `HurwitzZeta.sinZeta_neg`：sinZeta_neg (a : UnitAddCircle) (s : Complex) :
 sinZeta (-a) s = -sinZeta a s
· 使用引理 `HurwitzZeta.cosZeta_neg`：cosZeta_neg (a : UnitAddCircle) (s : Complex) :
 cosZeta (-a) s = cosZeta a s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
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
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
## The functional equation
-/
lemma hurwitzZeta_one_sub (a : UnitAddCircle) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : a ≠ 0 ∨ s ≠ 1) :
    hurwitzZeta a (1 - s) = (2 * π) ^ (-s) * Gamma s *
    (exp (-π * I * s / 2) * expZeta a s + exp (π * I * s / 2) * expZeta (-a) s) := by
  rw [hurwitzZeta, hurwitzZetaEven_one_sub a hs hs', hurwitzZetaOdd_one_sub a hs,
    expZeta, expZeta, Complex.cos, Complex.sin, sinZeta_neg, cosZeta_neg]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring,
    show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : ℂ) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf

/-- Functional equation for the exponential zeta function. -/
/-
**HurwitzZeta.expZeta_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：expZeta_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), 
s != 1 - n) : expZeta a (1 - s) = (2 * π) ^ (-s) * Gamma s * (exp (π * I * s / 2
) * hurwitzZeta a s + exp (-π * I * s / 2) * hurwitzZeta (-a) s)
参数：a : UnitAddCircle；hs : forall (n : Nat), s != 1 - n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
Functional equation for the exponential zeta function.
-/
lemma expZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ 1 - n) :
    expZeta a (1 - s) = (2 * π) ^ (-s) * Gamma s *
    (exp (π * I * s / 2) * hurwitzZeta a s + exp (-π * I * s / 2) * hurwitzZeta (-a) s) := by
  have hs' (n : ℕ) : s ≠ -↑n := by
    convert! hs (n + 1) using 1
    push_cast
    ring
  rw [expZeta, cosZeta_one_sub a hs, sinZeta_one_sub a hs', hurwitzZeta, hurwitzZeta,
    hurwitzZetaEven_neg, hurwitzZetaOdd_neg, Complex.cos, Complex.sin]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring,
    show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : ℂ) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf
  rw [I_sq]
  ring_nf

end HurwitzZeta

