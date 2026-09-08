/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Hadamard three-lines Theorem

In this file we present a proof of Hadamard's three-lines Theorem.

## Main result

- `norm_le_interp_of_mem_verticalClosedStrip` :
  Hadamard three-line theorem: If `f` is a bounded function, continuous on
  `re ⁻¹' [l, u]` and differentiable on `re ⁻¹' (l, u)`, then for
  `M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})`, that is `M(x)` is the supremum of the absolute value
  of `f` along the vertical lines `re z = x`, we have that `∀ z ∈ re ⁻¹' [l, u]` the inequality
  `‖f(z)‖ ≤ M(0) ^ (1 - ((z.re - l) / (u - l))) * M(1) ^ ((z.re - l) / (u - l))` holds.
  This can be seen to be equivalent to the statement
  that `log M(re z)` is a convex function on `[0, 1]`.

- `norm_le_interp_of_mem_verticalClosedStrip'` :
  Variant of the above lemma in simpler terms. In particular, it makes no mention of the helper
  functions defined in this file.

## Main definitions

- `Complex.HadamardThreeLines.verticalStrip` :
    The vertical strip defined by : `re ⁻¹' Ioo a b`

- `Complex.HadamardThreeLines.verticalClosedStrip` :
    The vertical strip defined by : `re ⁻¹' Icc a b`

- `Complex.HadamardThreeLines.sSupNormIm` :
    The supremum function on vertical lines defined by : `sSup {|f(z)| : z.re = x}`

- `Complex.HadamardThreeLines.interpStrip` :
    The interpolation between the `sSupNormIm` on the edges of the vertical strip `re⁻¹ [0, 1]`.

- `Complex.HadamardThreeLines.interpStrip` :
    The interpolation between the `sSupNormIm` on the edges of any vertical strip.

- `Complex.HadamardThreeLines.invInterpStrip` :
    Inverse of the interpolation between the `sSupNormIm` on the edges of the
    vertical strip `re⁻¹ [0, 1]`.

- `Complex.HadamardThreeLines.F` :
    Function defined by `f` times `invInterpStrip`. Convenient form for proofs.

## Note

The proof follows from Phragmén-Lindelöf when both frontiers are not everywhere zero.
We then use a limit argument to cover the case when either of the sides are `0`.
-/

@[expose] public section


open Set Filter Function Complex Topology

namespace Complex
namespace HadamardThreeLines

/-- The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b`. -/
/-
**Complex.HadamardThreeLines.verticalStrip** 是 Mathlib 中的一个定义，位于命名空间 `Complex.Ha
damardThreeLines`。
形式化陈述：verticalStrip (a : Real) (b : Real) : Set Complex
参数：a : Real；b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈
 Ioo a b`.
-/
def verticalStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Ioo a b

/-- The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b`. -/
/-
**Complex.HadamardThreeLines.verticalClosedStrip** 是 Mathlib 中的一个定义，位于命名空间 `Comp
lex.HadamardThreeLines`。
形式化陈述：verticalClosedStrip (a : Real) (b : Real) : Set Complex
参数：a : Real；b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈
 Icc a b`.
-/
def verticalClosedStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Icc a b

/-- The supremum of the norm of `f` on imaginary lines. (Fixed real part)
This is also known as the function `M` -/
/-
**Complex.HadamardThreeLines.sSupNormIm** 是 Mathlib 中的一个定义，位于命名空间 `Complex.Hadam
ardThreeLines`。
形式化陈述：sSupNormIm {E : Type*} [NormedAddCommGroup E] (f : Complex -> E) (x : Real
) : Real
参数：f : Complex -> E；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of the norm of `f` on imaginary lines. (Fixed real part)
This is also known as the function `M`
-/
noncomputable def sSupNormIm {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (x : ℝ) : ℝ :=
  sSup ((norm ∘ f) '' re ⁻¹' {x})

section invInterpStrip

variable {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) (z : ℂ)

/--
The inverse of the interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the inverse of the right side of the target inequality:
`|f(z)| ≤ |M(0) ^ (1-z)| * |M(1) ^ z|`.

Shifting this by a positive epsilon allows us to prove the case when either of the boundaries
is zero. -/
/-
**Complex.HadamardThreeLines.invInterpStrip** 是 Mathlib 中的一个定义，位于命名空间 `Complex.H
adamardThreeLines`。
形式化陈述：invInterpStrip (ε : Real) : Complex
参数：ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of the interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the inverse of the right side of the target inequality:
`|f(z)| ≤ |M(0) ^ (1-z)| * |M(1) ^ z|`.

Shifting this by a positive epsilon allows us to prove the case when either of t
he boundaries
is zero.
-/
noncomputable def invInterpStrip (ε : ℝ) : ℂ :=
  (ε + sSupNormIm f 0) ^ (z - 1) * (ε + sSupNormIm f 1) ^ (-z)

/-- A function useful for the proofs steps. We will aim to show that it is bounded by 1. -/
/-
**Complex.HadamardThreeLines.F** 是 Mathlib 中的一个定义，位于命名空间 `Complex.HadamardThreeL
ines`。
形式化陈述：F [NormedSpace Complex E] (ε : Real)
参数：ε : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function useful for the proofs steps. We will aim to show that it is bounded b
y 1.
-/
noncomputable def F [NormedSpace ℂ E] (ε : ℝ) := fun z ↦ invInterpStrip f z ε • f z

/-- `sSup` of `norm` is nonneg applied to the image of `f` on the vertical line `re z = x` -/
/-
**Complex.HadamardThreeLines.sSupNormIm_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x.HadamardThreeLines`。
形式化陈述：sSupNormIm_nonneg (x : Real) : 0 <= sSupNormIm f x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sSup_nonneg`：sSup_nonneg (hs : forall x in s, 0 <= x) : 0 <= sSup s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`sSup` of `norm` is nonneg applied to the image of `f` on the vertical line `re 
z = x`
-/
lemma sSupNormIm_nonneg (x : ℝ) : 0 ≤ sSupNormIm f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

/-- `sSup` of `norm` translated by `ε > 0` is positive applied to the image of `f` on the
vertical line `re z = x` -/
/-
**Complex.HadamardThreeLines.sSupNormIm_eps_pos** 是 Mathlib 中的一个引理，位于命名空间 `Compl
ex.HadamardThreeLines`。
形式化陈述：sSupNormIm_eps_pos {ε : Real} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm
 f x
参数：hε : ε > 0；x : Real。
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
· 使用定理 `Mathlib.Tactic.Linarith.sub_nonpos_of_le`：sub_nonpos_of_le [IsOrderedRin
g α] {a b : α} : a <= b -> a - b <= 0
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
`sSup` of `norm` translated by `ε > 0` is positive applied to the image of `f` o
n the
vertical line `re z = x`
-/
lemma sSupNormIm_eps_pos {ε : ℝ} (hε : ε > 0) (x : ℝ) : 0 < ε + sSupNormIm f x := by
  linarith [sSupNormIm_nonneg f x]

/-- Useful rewrite for the absolute value of `invInterpStrip` -/
/-
**Complex.HadamardThreeLines.norm_invInterpStrip** 是 Mathlib 中的一个引理，位于命名空间 `Comp
lex.HadamardThreeLines`。
形式化陈述：norm_invInterpStrip {ε : Real} (hε : ε > 0) : ‖invInterpStrip f z ε‖ = (ε 
+ sSupNormIm f 0) ^ (z.re - 1) * (ε + sSupNormIm f 1) ^ (-z.re)
参数：hε : ε > 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_eps_pos`：sSupNormIm_eps_pos {ε : R
eal} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Useful rewrite for the absolute value of `invInterpStrip`
-/
lemma norm_invInterpStrip {ε : ℝ} (hε : ε > 0) :
    ‖invInterpStrip f z ε‖ =
    (ε + sSupNormIm f 0) ^ (z.re - 1) * (ε + sSupNormIm f 1) ^ (-z.re) := by
  simp only [invInterpStrip, norm_mul]
  repeat rw [← ofReal_add]
  repeat rw [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _]
  simp

/-- The function `invInterpStrip` is `diffContOnCl`. -/
/-
**Complex.HadamardThreeLines.diffContOnCl_invInterpStrip** 是 Mathlib 中的一个引理，位于命名
空间 `Complex.HadamardThreeLines`。
形式化陈述：diffContOnCl_invInterpStrip {ε : Real} (hε : ε > 0) : DiffContOnCl Complex
 (fun z => invInterpStrip f z ε) (verticalStrip 0 1)
参数：hε : ε > 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `Differentiable.mul`：Differentiable.mul (ha : Differentiable 𝕜 a) (hb : D
ifferentiable 𝕜 b) : Differentiable 𝕜 (a * b)
· 使用定理 `Differentiable.const_cpow`：Differentiable.const_cpow (hf : Differentiabl
e Complex f) (h0 : c != 0 ∨ forall x, f x != 0) : Differentiable Complex (fun x 
=> c ^ f x)
· 使用定理 `Differentiable.sub_const`：Differentiable.sub_const (hf : Differentiable 
𝕜 f) (c : F) : Differentiable 𝕜 fun y => f y - c
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_eps_pos`：sSupNormIm_eps_pos {ε : R
eal} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm f x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Differentiable.neg`：Differentiable.neg (h : Differentiable 𝕜 f) : Differ
entiable 𝕜 (-f)

--- 原说明 ---
The function `invInterpStrip` is `diffContOnCl`.
-/
lemma diffContOnCl_invInterpStrip {ε : ℝ} (hε : ε > 0) :
    DiffContOnCl ℂ (fun z ↦ invInterpStrip f z ε) (verticalStrip 0 1) := by
  apply Differentiable.diffContOnCl
  apply Differentiable.mul
  · apply Differentiable.const_cpow (Differentiable.sub_const differentiable_id 1) _
    left
    rw [← ofReal_add, ofReal_ne_zero]
    simp only [ne_eq, ne_of_gt (sSupNormIm_eps_pos f hε 0), not_false_eq_true]
  · apply Differentiable.const_cpow (Differentiable.neg differentiable_id)
    apply Or.inl
    rw [← ofReal_add, ofReal_ne_zero]
    exact (ne_of_gt (sSupNormIm_eps_pos f hε 1))

/-- If `f` is bounded on the unit vertical strip, then `f` is bounded by `sSupNormIm` there. -/
/-
**Complex.HadamardThreeLines.norm_le_sSupNormIm** 是 Mathlib 中的一个引理，位于命名空间 `Compl
ex.HadamardThreeLines`。
形式化陈述：norm_le_sSupNormIm (f : Complex -> E) (z : Complex) (hD : z in verticalClo
sedStrip 0 1) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) : ‖f z‖ <=
 sSupNormIm f (z.re)
参数：f : Complex -> E；z : Complex；hD : z in verticalClosedStrip 0 1；hB : BddAbove 
((norm ∘ f) '' verticalClosedStrip 0 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
If `f` is bounded on the unit vertical strip, then `f` is bounded by `sSupNormIm
` there.
-/
lemma norm_le_sSupNormIm (f : ℂ → E) (z : ℂ) (hD : z ∈ verticalClosedStrip 0 1)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ ≤ sSupNormIm f (z.re) := by
  refine le_csSup ?_ ?_
  · revert hB; gcongr
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (norm ∘ f)
    simp only [mem_preimage, mem_singleton]

/-- Alternative version of `norm_le_sSupNormIm` with a strict inequality and a positive `ε`. -/
/-
**Complex.HadamardThreeLines.norm_lt_sSupNormIm_eps** 是 Mathlib 中的一个引理，位于命名空间 `C
omplex.HadamardThreeLines`。
形式化陈述：norm_lt_sSupNormIm_eps (f : Complex -> E) (ε : Real) (hε : ε > 0) (z : Com
plex) (hD : z in verticalClosedStrip 0 1) (hB : BddAbove ((norm ∘ f) '' vertical
ClosedStrip 0 1)) : ‖f z‖ < ε + sSupNormIm f (z.re)
参数：f : Complex -> E；ε : Real；hε : ε > 0；z : Complex；hD : z in verticalClosedStri
p 0 1；hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_add_of_pos_of_le`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddRightStrictMono α] {a b c : α},   0 < a → b ≤ c → b < a + c
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
· 使用引理 `Complex.HadamardThreeLines.norm_le_sSupNormIm`：norm_le_sSupNormIm (f : C
omplex -> E) (z : Complex) (hD : z in verticalClosedStrip 0 1) (hB : BddAbove ((
norm ∘ f) '' verticalClosedStrip 0 …

--- 原说明 ---
Alternative version of `norm_le_sSupNormIm` with a strict inequality and a posit
ive `ε`.
-/
lemma norm_lt_sSupNormIm_eps (f : ℂ → E) (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hD : z ∈ verticalClosedStrip 0 1) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ < ε + sSupNormIm f (z.re) :=
  lt_add_of_pos_of_le hε (norm_le_sSupNormIm f z hD hB)

variable [NormedSpace ℂ E]

set_option backward.isDefEq.respectTransparency.types false in
/-- When the function `f` is bounded above on a vertical strip, then so is `F`. -/
/-
**Complex.HadamardThreeLines.F_BddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Complex.Hadam
ardThreeLines`。
形式化陈述：F_BddAbove (f : Complex -> E) (ε : Real) (hε : ε > 0) (hB : BddAbove ((nor
m ∘ f) '' verticalClosedStrip 0 1)) : BddAbove ((norm ∘ (F f ε)) '' verticalClos
edStrip 0 1)
参数：f : Complex -> E；ε : Real；hε : ε > 0；hB : BddAbove ((norm ∘ f) '' verticalClo
sedStrip 0 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_eps_pos`：sSupNormIm_eps_pos {ε : R
eal} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm f x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Real.rpow_le_one_of_one_le_of_nonpos`：rpow_le_one_of_one_le_of_nonpos {x
 z : Real} (hx : 1 <= x) (hz : z <= 0) : x ^ z <= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge (hx0 : 0 <
 x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
When the function `f` is bounded above on a vertical strip, then so is `F`.
-/
lemma F_BddAbove (f : ℂ → E) (ε : ℝ) (hε : ε > 0)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    BddAbove ((norm ∘ (F f ε)) '' verticalClosedStrip 0 1) := by
  -- Rewriting goal
  simp only [F, comp_apply, invInterpStrip]
  rw [bddAbove_def] at *
  rcases hB with ⟨B, hB⟩
  -- Using bound
  use ((max 1 ((ε + sSupNormIm f 0) ^ (-(1 : ℝ)))) * max 1 ((ε + sSupNormIm f 1) ^ (-(1 : ℝ)))) * B
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro z hset
  specialize hB (‖f z‖) (by simpa [image_congr, mem_image, comp_apply] using ⟨z, hset, rfl⟩)
  -- Proof that the bound is correct
  simp only [norm_smul, norm_mul, ← ofReal_add]
  gcongr
    -- Bounding individual terms
  · by_cases hM0_one : 1 ≤ ε + sSupNormIm f 0
    -- `1 ≤ sSupNormIm f 0`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re, Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
    -- `0 < sSupNormIm f 0 < 1`
    · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re]
      apply Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 0) (le_of_lt hM0_one) _
      simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
  · by_cases hM1_one : 1 ≤ ε + sSupNormIm f 1
    -- `1 ≤ sSupNormIm f 1`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_one_of_one_le_of_nonpos
        hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
    -- `0 < sSupNormIm f 1 < 1`
    · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 1)
        (le_of_lt hM1_one) (neg_le_neg_iff.mpr hset.2)]

/-- Proof that `F` is bounded by one on the edges. -/
/-
**Complex.HadamardThreeLines.F_edge_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Complex.Ha
damardThreeLines`。
形式化陈述：F_edge_le_one (f : Complex -> E) (ε : Real) (hε : ε > 0) (z : Complex) (hB
 : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z in re ⁻¹' {0, 1}) :
 ‖F f ε z‖ <= 1
参数：f : Complex -> E；ε : Real；hε : ε > 0；z : Complex；hB : BddAbove ((norm ∘ f) ''
 verticalClosedStrip 0 1)；hz : z in re ⁻¹' {0, 1}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用引理 `Complex.HadamardThreeLines.norm_invInterpStrip`：norm_invInterpStrip {ε :
 Real} (hε : ε > 0) : ‖invInterpStrip f z ε‖ = (ε + sSupNormIm f 0) ^ (z.re - 1)
 * (ε + sSupNormIm f 1) ^ (-z.re)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `inv_mul_le_iff₀`：inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * 
a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_eps_pos`：sSupNormIm_eps_pos {ε : R
eal} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Complex.HadamardThreeLines.norm_lt_sSupNormIm_eps`：norm_lt_sSupNormIm_ep
s (f : Complex -> E) (ε : Real) (hε : ε > 0) (z : Complex) (hD : z in verticalCl
osedStrip 0 1) (hB : BddAbove ((norm ∘ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Proof that `F` is bounded by one on the edges.
-/
lemma F_edge_le_one (f : ℂ → E) (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z ∈ re ⁻¹' {0, 1}) :
    ‖F f ε z‖ ≤ 1 := by
  simp only [F, norm_smul, norm_invInterpStrip f z hε]
  rcases hz with hz0 | hz1
  -- `z.re = 0`
  · simp only [hz0, zero_sub, Real.rpow_neg_one, neg_zero, Real.rpow_zero, mul_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 0)]
    rw [← hz0]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
  -- `z.re = 1`
  · rw [mem_singleton_iff] at hz1
    simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 1), mul_one]
    rw [← hz1]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]
/-
**Complex.HadamardThreeLines.norm_mul_invInterpStrip_le_one_of_mem_verticalClose
dStrip** 是 Mathlib 中的一个定理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip (f : Complex -> 
E) (ε : Real) (hε : 0 < ε) (z : Complex) (hd : DiffContOnCl Complex f (verticalS
trip 0 1)) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z in ve
rticalClosedStrip 0 1) : ‖F f ε z‖ <= 1
参数：f : Complex -> E；ε : Real；hε : 0 < ε；z : Complex；hd : DiffContOnCl Complex f 
(verticalStrip 0 1)；hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)；hz : z
 in verticalClosedStrip 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PhragmenLindelof.vertical_strip`：vertical_strip (hfd : DiffContOnCl Comp
lex f (re ⁻¹' Ioo a b)) (hB : exists c < π / (b - a), exists B, f =O[comap (_roo
t_.abs ∘ im) atTop ⊓ …
· 使用定理 `DiffContOnCl.smul`：smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [Norme
dAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {f : E ->
 F} {s …
· 使用引理 `Complex.HadamardThreeLines.diffContOnCl_invInterpStrip`：diffContOnCl_inv
InterpStrip {ε : Real} (hε : ε > 0) : DiffContOnCl Complex (fun z => invInterpSt
rip f z ε) (verticalStrip 0 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `Complex.HadamardThreeLines.F_BddAbove`：F_BddAbove (f : Complex -> E) (ε 
: Real) (hε : ε > 0) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) : B
ddAbove ((norm ∘ (F f ε)) '…
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
（共 35 条，此处仅展示前 30 条）
-/
theorem norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip (f : ℂ → E) (ε : ℝ) (hε : 0 < ε)
    (z : ℂ) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F f ε z‖ ≤ 1 := by
  apply PhragmenLindelof.vertical_strip
    (DiffContOnCl.smul (diffContOnCl_invInterpStrip f hε) hd) _
    (fun x hx ↦ F_edge_le_one f ε hε x hB (Or.inl hx))
    (fun x hx ↦ F_edge_le_one f ε hε x hB (Or.inr hx)) hz.1 hz.2
  use 0
  rw [sub_zero, div_one]
  refine ⟨ Real.pi_pos, ?_⟩
  obtain ⟨BF, hBF⟩ := F_BddAbove f ε hε hB
  simp only [comp_apply, mem_upperBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hBF
  use BF
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro x hx
  simpa using! (hBF x ((preimage_mono Ioo_subset_Icc_self) hx)).trans
    ((le_of_lt (lt_add_one BF)).trans (Real.add_one_le_exp BF))

end invInterpStrip

-----

variable {E : Type*} [NormedAddCommGroup E] (f : ℂ → E)

/--
The interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the right side of the target inequality:
`|f(z)| ≤ |M(0) ^ (1-z)| * |M(1) ^ z|`.

Note that if `sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0` then the power is not continuous
since `0 ^ 0 = 1`. Hence the use of `ite`. -/
/-
**Complex.HadamardThreeLines.interpStrip** 是 Mathlib 中的一个定义，位于命名空间 `Complex.Hada
mardThreeLines`。
形式化陈述：interpStrip (z : Complex) : Complex
参数：z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the right side of the target inequality:
`|f(z)| ≤ |M(0) ^ (1-z)| * |M(1) ^ z|`.

Note that if `sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0` then the power is not con
tinuous
since `0 ^ 0 = 1`. Hence the use of `ite`.
-/
noncomputable def interpStrip (z : ℂ) : ℂ :=
  if sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    then 0
    else sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z

/-- Rewrite for `InterpStrip` when `0 < sSupNormIm f 0` and `0 < sSupNormIm f 1`. -/
/-
**Complex.HadamardThreeLines.interpStrip_eq_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Co
mplex.HadamardThreeLines`。
形式化陈述：interpStrip_eq_of_pos (z : Complex) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sS
upNormIm f 1) : interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z
参数：z : Complex；h0 : 0 < sSupNormIm f 0；h1 : 0 < sSupNormIm f 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rewrite for `InterpStrip` when `0 < sSupNormIm f 0` and `0 < sSupNormIm f 1`.
-/
lemma interpStrip_eq_of_pos (z : ℂ) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1) :
    interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z := by
  simp only [ne_of_gt h0, ne_of_gt h1, interpStrip, if_false, or_false]

/-- Rewrite for `InterpStrip` when `0 = sSupNormIm f 0` or `0 = sSupNormIm f 1`. -/
/-
**Complex.HadamardThreeLines.interpStrip_eq_of_zero** 是 Mathlib 中的一个引理，位于命名空间 `C
omplex.HadamardThreeLines`。
形式化陈述：interpStrip_eq_of_zero (z : Complex) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm 
f 1 = 0) : interpStrip f z = 0
参数：z : Complex；h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
Rewrite for `InterpStrip` when `0 = sSupNormIm f 0` or `0 = sSupNormIm f 1`.
-/
lemma interpStrip_eq_of_zero (z : ℂ) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0) :
    interpStrip f z = 0 :=
  if_pos h

/-- Rewrite for `InterpStrip` on the open vertical strip. -/
/-
**Complex.HadamardThreeLines.interpStrip_eq_of_mem_verticalStrip** 是 Mathlib 中的一
个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：interpStrip_eq_of_mem_verticalStrip (z : Complex) (hz : z in verticalStrip
 0 1) : interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z
参数：z : Complex；hz : z in verticalStrip 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.HadamardThreeLines.interpStrip_eq_of_zero`：interpStrip_eq_of_zer
o (z : Complex) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0) : interpStrip f z 
= 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_nonneg`：sSupNormIm_nonneg (x : Rea
l) : 0 <= sSupNormIm f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用引理 `Complex.HadamardThreeLines.interpStrip_eq_of_pos`：interpStrip_eq_of_pos 
(z : Complex) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1) : interpStrip 
f z = sSupNormIm f 0 ^ (1 - z) * sSupN…

--- 原说明 ---
Rewrite for `InterpStrip` on the open vertical strip.
-/
lemma interpStrip_eq_of_mem_verticalStrip (z : ℂ) (hz : z ∈ verticalStrip 0 1) :
    interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z := by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  · rw [interpStrip_eq_of_zero _ z h]
    rcases h with h0 | h1
    · simp only [h0, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ne_eq, true_and, ofReal_eq_zero]
      left
      rw [sub_eq_zero, eq_comm]
      simp only [Complex.ext_iff, one_re, ne_of_lt hz.2, false_and, not_false_eq_true]
    · simp only [h1, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq, true_and]
      right
      rw [eq_comm]
      simp only [Complex.ext_iff, zero_re, ne_of_lt hz.1, false_and, not_false_eq_true]
  · replace h : (0 < sSupNormIm f 0) ∧ (0 < sSupNormIm f 1) :=
      ⟨(lt_of_le_of_ne (sSupNormIm_nonneg f 0) (ne_comm.mp h.1)),
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) (ne_comm.mp h.2))⟩
    exact interpStrip_eq_of_pos f z h.1 h.2
/-
**Complex.HadamardThreeLines.diffContOnCl_interpStrip** 是 Mathlib 中的一个引理，位于命名空间 
`Complex.HadamardThreeLines`。
形式化陈述：diffContOnCl_interpStrip : DiffContOnCl Complex (interpStrip f) (verticalS
trip 0 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.HadamardThreeLines.interpStrip_eq_of_zero`：interpStrip_eq_of_zer
o (z : Complex) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0) : interpStrip f z 
= 0
· 使用定理 `diffContOnCl_const`：diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ :
 E => c) s
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用引理 `Complex.HadamardThreeLines.interpStrip_eq_of_pos`：interpStrip_eq_of_pos 
(z : Complex) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1) : interpStrip 
f z = sSupNormIm f 0 ^ (1 - z) * sSupN…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_nonneg`：sSupNormIm_nonneg (x : Rea
l) : 0 <= sSupNormIm f x
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用定理 `DifferentiableAt.const_cpow`：DifferentiableAt.const_cpow (hf : Different
iableAt Complex f x) (h0 : c != 0 ∨ f x != 0) : DifferentiableAt Complex (fun x 
=> c ^ f x) x
· 使用定理 `DifferentiableAt.const_sub`：DifferentiableAt.const_sub (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => c - f y) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
lemma diffContOnCl_interpStrip :
    DiffContOnCl ℂ (interpStrip f) (verticalStrip 0 1) := by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  -- Case everywhere 0
  · eta_expand; simp_rw [interpStrip_eq_of_zero f _ h]; exact diffContOnCl_const
  -- Case nowhere 0
  · rcases h with ⟨h0, h1⟩
    rw [ne_comm] at h0 h1
    apply Differentiable.diffContOnCl
    intro z
    eta_expand
    simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
      (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
    refine DifferentiableAt.mul ?_ ?_
    · apply DifferentiableAt.const_cpow (DifferentiableAt.const_sub differentiableAt_id 1) _
      left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]
    · refine DifferentiableAt.const_cpow ?_ ?_
      · apply differentiableAt_id
      · left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]

/-- The correct generalization of `interpStrip` to produce bounds in the general case. -/
/-
**Complex.HadamardThreeLines.interpStrip'** 是 Mathlib 中的一个定义，位于命名空间 `Complex.Had
amardThreeLines`。
形式化陈述：interpStrip' (f : Complex -> E) (l u : Real) (z : Complex) : Complex
参数：f : Complex -> E；l u : Real；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The correct generalization of `interpStrip` to produce bounds in the general cas
e.
-/
noncomputable def interpStrip' (f : ℂ → E) (l u : ℝ) (z : ℂ) : ℂ :=
  if sSupNormIm f l = 0 ∨ sSupNormIm f u = 0
    then 0
    else sSupNormIm f l ^ (1 - ((z - l) / (u - l))) * sSupNormIm f u ^ ((z - l) / (u - l))

/-- An auxiliary function to prove the general statement of Hadamard's three lines theorem. -/
/-
**Complex.HadamardThreeLines.scale** 是 Mathlib 中的一个定义，位于命名空间 `Complex.HadamardTh
reeLines`。
形式化陈述：scale (f : Complex -> E) (l u : Real) : Complex -> E
参数：f : Complex -> E；l u : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary function to prove the general statement of Hadamard's three lines t
heorem.
-/
def scale (f : ℂ → E) (l u : ℝ) : ℂ → E := fun z ↦ f (l + z • (u - l))

/-- The transformation on ℂ that is used for `scale` maps the closed strip ``re ⁻¹' [l, u]``
  to the closed strip ``re ⁻¹' [0, 1]``. -/
/-
**Complex.HadamardThreeLines.scale_id_mem_verticalClosedStrip_of_mem_verticalClo
sedStrip** 是 Mathlib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip {l u : Real} (
hul : l < u) {z : Complex} (hz : z in verticalClosedStrip 0 1) : l + z * (u - l)
 in verticalClosedStrip l u
参数：hul : l < u；hz : z in verticalClosedStrip 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The transformation on ℂ that is used for `scale` maps the closed strip ``re ⁻¹' 
[l, u]``
  to the closed strip ``re ⁻¹' [0, 1]``.
-/
lemma scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip {l u : ℝ} (hul : l < u) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : l + z * (u - l) ∈ verticalClosedStrip l u := by
  simp only [verticalClosedStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im,
    ofReal_im, sub_self, mul_zero, sub_zero, mem_Icc] at hz ⊢
  constructor <;> nlinarith [hz.1, hz.2, hul]

/-- The norm of the function `scale f l u` is bounded above on the closed strip `re⁻¹' [0, 1]`. -/
/-
**Complex.HadamardThreeLines.scale_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Complex.H
adamardThreeLines`。
形式化陈述：scale_bddAbove {f : Complex -> E} {l u : Real} (hul : l < u) (hB : BddAbov
e ((norm ∘ f) '' verticalClosedStrip l u)) : BddAbove ((norm ∘ scale f l u) '' v
erticalClosedStrip 0 1)
参数：hul : l < u；hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用引理 `Complex.HadamardThreeLines.scale_id_mem_verticalClosedStrip_of_mem_verti
calClosedStrip`：scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip {l u
 : Real} (hul : l < u) {z : Complex} (hz : z in verticalClosedStrip 0 1) : l…

--- 原说明 ---
The norm of the function `scale f l u` is bounded above on the closed strip `re⁻
¹' [0, 1]`.
-/
lemma scale_bddAbove {f : ℂ → E} {l u : ℝ} (hul : l < u)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)) :
    BddAbove ((norm ∘ scale f l u) '' verticalClosedStrip 0 1) := by
  refine hB.mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨l + z * (u - l), scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip hul hz, rfl⟩

/-- A bound to the norm of `f` on the line `z.re = l` induces a bound to the norm of
  `scale f l u z` on the line `z.re = 0`. -/
/-
**Complex.HadamardThreeLines.scale_bound_left** 是 Mathlib 中的一个引理，位于命名空间 `Complex
.HadamardThreeLines`。
形式化陈述：scale_bound_left {f : Complex -> E} {l u a : Real} (ha : forall z in re ⁻¹
' {l}, ‖f z‖ <= a) : forall z in re ⁻¹' {0}, ‖scale f l u z‖ <= a
参数：ha : forall z in re ⁻¹' {l}, ‖f z‖ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A bound to the norm of `f` on the line `z.re = l` induces a bound to the norm of
  `scale f l u z` on the line `z.re = 0`.
-/
lemma scale_bound_left {f : ℂ → E} {l u a : ℝ} (ha : ∀ z ∈ re ⁻¹' {l}, ‖f z‖ ≤ a) :
    ∀ z ∈ re ⁻¹' {0}, ‖scale f l u z‖ ≤ a := by
  simp only [mem_preimage, mem_singleton_iff, scale, smul_eq_mul]
  intro z hz
  exact ha (↑l + z * (↑u - ↑l)) (by simp [hz])

/-- A bound to the norm of `f` on the line `z.re = u` induces a bound to the norm of `scale f l u z`
  on the line `z.re = 1`. -/
/-
**Complex.HadamardThreeLines.scale_bound_right** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x.HadamardThreeLines`。
形式化陈述：scale_bound_right {f : Complex -> E} {l u b : Real} (hb : forall z in re ⁻
¹' {u}, ‖f z‖ <= b) : forall z in re ⁻¹' {1}, ‖scale f l u z‖ <= b
参数：hb : forall z in re ⁻¹' {u}, ‖f z‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A bound to the norm of `f` on the line `z.re = u` induces a bound to the norm of
 `scale f l u z`
  on the line `z.re = 1`.
-/
lemma scale_bound_right {f : ℂ → E} {l u b : ℝ} (hb : ∀ z ∈ re ⁻¹' {u}, ‖f z‖ ≤ b) :
    ∀ z ∈ re ⁻¹' {1}, ‖scale f l u z‖ ≤ b := by
  simp only [scale, mem_preimage, mem_singleton_iff, smul_eq_mul]
  intro z hz
  exact hb (↑l + z * (↑u - ↑l)) (by simp [hz])

/-- The supremum of the norm of `scale f l u` on the line `z.re = 0` is the same as the supremum
  of `f` on the line `z.re = l`. -/
/-
**Complex.HadamardThreeLines.sSupNormIm_scale_left** 是 Mathlib 中的一个引理，位于命名空间 `Co
mplex.HadamardThreeLines`。
形式化陈述：sSupNormIm_scale_left (f : Complex -> E) {l u : Real} (hul : l < u) : sSup
NormIm (scale f l u) 0 = sSupNormIm f l
参数：f : Complex -> E；hul : l < u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Complex.div_re`：div_re (z w : Complex) : (z / w).re = z.re * w.re / norm
Sq w + z.im * w.im / normSq w
· 使用定理 `Complex.normSq_ofReal`：normSq_ofReal (r : Real) : normSq r = r * r
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `div_mul_comm`：div_mul_comm : a / b * c = c / b * a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
The supremum of the norm of `scale f l u` on the line `z.re = 0` is the same as 
the supremum
  of `f` on the line `z.re = l`.
-/
lemma sSupNormIm_scale_left (f : ℂ → E) {l u : ℝ} (hul : l < u) :
    sSupNormIm (scale f l u) 0 = sSupNormIm f l := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {0} = f '' re ⁻¹' {l} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp [hz₁, hz₂]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re]
        simp [hz₁]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp [hz₂]
  rw [this]

/-- The supremum of the norm of `scale f l u` on the line `z.re = 1` is the same as
  the supremum of `f` on the line `z.re = u`. -/
/-
**Complex.HadamardThreeLines.sSupNormIm_scale_right** 是 Mathlib 中的一个引理，位于命名空间 `C
omplex.HadamardThreeLines`。
形式化陈述：sSupNormIm_scale_right (f : Complex -> E) {l u : Real} (hul : l < u) : sSu
pNormIm (scale f l u) 1 = sSupNormIm f u
参数：f : Complex -> E；hul : l < u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_mul_comm`：div_mul_comm : a / b * c = c / b * a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The supremum of the norm of `scale f l u` on the line `z.re = 1` is the same as
  the supremum of `f` on the line `z.re = u`.
-/
lemma sSupNormIm_scale_right (f : ℂ → E) {l u : ℝ} (hul : l < u) :
    sSupNormIm (scale f l u) 1 = sSupNormIm f u := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {1} = f '' re ⁻¹' {u} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp only [add_re, ofReal_re, mul_re, hz₁, sub_re, one_mul, sub_im, ofReal_im, sub_self,
        mul_zero, sub_zero, add_sub_cancel, hz₂, and_self]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        grind [Complex.div_re, Complex.normSq_ofReal, sub_re, ofReal_re, ofReal_im, mul_eq_zero]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp only [one_mul, add_sub_cancel, hz₂]
  rw [this]

/-- A technical lemma relating the bounds given by the three lines lemma on a general strip
to the bounds for its scaled version on the strip `re ⁻¹' [0, 1]`. -/
/-
**Complex.HadamardThreeLines.interpStrip_scale** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x.HadamardThreeLines`。
形式化陈述：interpStrip_scale (f : Complex -> E) {l u : Real} (hul : l < u) (z : Compl
ex) : interpStrip (scale f l u) ((z - ↑l) / (↑u - ↑l)) = interpStrip' f l u z
参数：f : Complex -> E；hul : l < u；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_scale_left`：sSupNormIm_scale_left 
(f : Complex -> E) {l u : Real} (hul : l < u) : sSupNormIm (scale f l u) 0 = sSu
pNormIm f l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_scale_right`：sSupNormIm_scale_righ
t (f : Complex -> E) {l u : Real} (hul : l < u) : sSupNormIm (scale f l u) 1 = s
SupNormIm f u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A technical lemma relating the bounds given by the three lines lemma on a genera
l strip
to the bounds for its scaled version on the strip `re ⁻¹' [0, 1]`.
-/
lemma interpStrip_scale (f : ℂ → E) {l u : ℝ} (hul : l < u) (z : ℂ) : interpStrip (scale f l u)
    ((z - ↑l) / (↑u - ↑l)) = interpStrip' f l u z := by
  simp only [interpStrip, interpStrip']
  simp_rw [sSupNormIm_scale_left f hul, sSupNormIm_scale_right f hul]

variable [NormedSpace ℂ E]
/-
**Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip_eps*
* 是 Mathlib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：norm_le_interpStrip_of_mem_verticalClosedStrip_eps (ε : Real) (hε : ε > 0)
 (z : Complex) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hd : Dif
fContOnCl Complex f (verticalStrip 0 1)) (hz : z in verticalClosedStrip 0 1) : ‖
f z‖ <= ‖((ε + sSupNormIm f 0) ^ (1 - z) * (ε + sSupNormIm f 1) ^ z : Complex)‖
参数：ε : Real；hε : ε > 0；z : Complex；hB : BddAbove ((norm ∘ f) '' verticalClosedSt
rip 0 1)；hd : DiffContOnCl Complex f (verticalStrip 0 1)；hz : z in verticalClose
dStrip 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_eps_pos`：sSupNormIm_eps_pos {ε : R
eal} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_inv_le_iff₀'`：mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ <= a ↔ b <= c 
* a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `mul_inv_le_iff₀`：mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ <= a ↔ b <= a * 
c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
（共 33 条，此处仅展示前 30 条）
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip_eps (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1)) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖f z‖ ≤ ‖((ε + sSupNormIm f 0) ^ (1 - z) * (ε + sSupNormIm f 1) ^ z : ℂ)‖ := by
  simp only [norm_mul, ← ofReal_add, norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _,
    sub_re, one_re]
  rw [← mul_inv_le_iff₀', ← one_mul (((ε + sSupNormIm f 1) ^ z.re)), ← mul_inv_le_iff₀,
    ← Real.rpow_neg_one, ← Real.rpow_neg_one]
  · simp only [← Real.rpow_mul (le_of_lt (sSupNormIm_eps_pos f hε _)),
    mul_neg, mul_one, neg_sub, mul_assoc]
    simpa [F, norm_invInterpStrip _ _ hε, norm_smul, mul_comm] using
      norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip f ε hε z hd hB hz
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) z.re]
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) (1 - z.re)]
/-
**Complex.HadamardThreeLines.eventuallyle** 是 Mathlib 中的一个引理，位于命名空间 `Complex.Had
amardThreeLines`。
形式化陈述：eventuallyle (z : Complex) (hB : BddAbove ((norm ∘ f) '' verticalClosedStr
ip 0 1)) (hd : DiffContOnCl Complex f (verticalStrip 0 1)) (hz : z in verticalSt
rip 0 1) : (fun _ : Real => ‖f z‖) <=ᶠ[𝓝[>] 0] (fun ε => ‖((ε + sSupNormIm f 0) 
^ (1 - z) * (ε + sSupNormIm f 1) ^ z : Complex)‖)
参数：z : Complex；hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)；hd : DiffCo
ntOnCl Complex f (verticalStrip 0 1)；hz : z in verticalStrip 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStri
p_eps`：norm_le_interpStrip_of_mem_verticalClosedStrip_eps (ε : Real) (hε : ε > 0
) (z : Complex) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0…
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
lemma eventuallyle (z : ℂ) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1)) (hz : z ∈ verticalStrip 0 1) :
    (fun _ : ℝ ↦ ‖f z‖) ≤ᶠ[𝓝[>] 0]
    (fun ε ↦ ‖((ε + sSupNormIm f 0) ^ (1 - z) * (ε + sSupNormIm f 1) ^ z : ℂ)‖) := by
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using
    norm_le_interpStrip_of_mem_verticalClosedStrip_eps f ε hε z hB hd
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))
/-
**Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalStrip_zero** 是 M
athlib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：norm_le_interpStrip_of_mem_verticalStrip_zero (z : Complex) (hd : DiffCont
OnCl Complex f (verticalStrip 0 1)) (hB : BddAbove ((norm ∘ f) '' verticalClosed
Strip 0 1)) (hz : z in verticalStrip 0 1) : ‖f z‖ <= ‖interpStrip f z‖
参数：z : Complex；hd : DiffContOnCl Complex f (verticalStrip 0 1)；hB : BddAbove ((n
orm ∘ f) '' verticalClosedStrip 0 1)；hz : z in verticalStrip 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_le_of_eventuallyLE`：∀ {α : Type u} {β : Type v} [inst : Topologi
calSpace α] [inst_1 : Preorder α] [t : OrderClosedTopology α] {f g : β → α}   {b
 : Filter β} {a₁…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.HadamardThreeLines.interpStrip_eq_of_mem_verticalStrip`：interpSt
rip_eq_of_mem_verticalStrip (z : Complex) (hz : z in verticalStrip 0 1) : interp
Strip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_nonneg`：norm_cpow_eq_rpow_re_of_nonneg {
x : Real} (hx : 0 <= x) {y : Complex} (hy : re y != 0) : ‖(x : Complex) ^ y‖ = x
 ^ re y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Complex.HadamardThreeLines.sSupNormIm_eps_pos`：sSupNormIm_eps_pos {ε : R
eal} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm f x
（共 54 条，此处仅展示前 30 条）
-/
lemma norm_le_interpStrip_of_mem_verticalStrip_zero (z : ℂ)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z ∈ verticalStrip 0 1) :
    ‖f z‖ ≤ ‖interpStrip f z‖ := by
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f z hB hd hz)
  · simp only [tendsto_const_nhds_iff]
  -- Proof that we can let epsilon tend to zero.
  · rw [interpStrip_eq_of_mem_verticalStrip _ _ hz]
    convert! ContinuousWithinAt.tendsto _ using 2
    · simp only [ofReal_zero, zero_add]
    · simp_rw [← ofReal_add]
      have : ∀ x ∈ Ioi 0, (x + sSupNormIm f 0) ^ (1 - z.re) * (x + sSupNormIm f 1) ^ z.re
          = ‖((x + sSupNormIm f 0 : ℝ) ^ (1 - z) * (x + sSupNormIm f 1 : ℝ) ^ z : ℂ)‖ := by
              intro x hx
              simp only [norm_mul]
              repeat rw [norm_cpow_eq_rpow_re_of_nonneg (le_of_lt (sSupNormIm_eps_pos f hx _)) _]
              · simp only [sub_re, one_re]
              · simpa using (ne_comm.mpr (ne_of_lt hz.1))
              · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))
      apply tendsto_nhdsWithin_congr this _
      simp only [zero_add]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _,
        norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]
      · apply Tendsto.mul
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 0)]
            exact Tendsto.add_const (sSupNormIm f 0) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [sub_nonneg, le_of_lt hz.2]
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 1)]
            exact Tendsto.add_const (sSupNormIm f 1) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [le_of_lt hz.1]
      · simpa using (ne_comm.mpr (ne_of_lt hz.1))
      · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))

/--
**Hadamard three-line theorem** on `re ⁻¹' [0, 1]`: If `f` is a bounded function, continuous on the
closed strip `re ⁻¹' [0, 1]` and differentiable on open strip `re ⁻¹' (0, 1)`, then for
`M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})` we have that for all `z` in the closed strip
`re ⁻¹' [0, 1]` the inequality `‖f(z)‖ ≤ M(0) ^ (1 - z.re) * M(1) ^ z.re` holds. -/
/-
**Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip** 是 
Mathlib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：norm_le_interpStrip_of_mem_verticalClosedStrip {l u : Real} (hul : l < u) 
{f : Complex -> E} {z : Complex} (hz : z in verticalClosedStrip l u) (hd : DiffC
ontOnCl Complex f (verticalStrip l u)) (hB : BddAbove ((norm ∘ f) '' verticalClo
sedStrip l u)) : ‖f z‖ <= ‖interpStrip' f l u z‖
参数：hul : l < u；hz : z in verticalClosedStrip l u；hd : DiffContOnCl Complex f (ve
rticalStrip l u)；hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStri
p₀₁`：norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (f : Complex -> E) {z : Co
mplex} (hz : z in verticalClosedStrip 0 1) (hd : DiffContOnCl Com…
· 使用引理 `Complex.HadamardThreeLines.mem_verticalClosedStrip_of_scale_id_mem_verti
calClosedStrip`：mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip {z :
 Complex} {l u : Real} (hul : l < u) (hz : z in verticalClosedStrip l u) : z…
· 使用引理 `Complex.HadamardThreeLines.scale_diffContOnCl`：scale_diffContOnCl {f : C
omplex -> E} {l u : Real} (hul : l < u) (hd : DiffContOnCl Complex f (verticalSt
rip l u)) : DiffContOnCl Complex (s…
· 使用引理 `Complex.HadamardThreeLines.scale_bddAbove`：scale_bddAbove {f : Complex -
> E} {l u : Real} (hul : l < u) (hB : BddAbove ((norm ∘ f) '' verticalClosedStri
p l u)) : BddAbove ((norm ∘ sca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.HadamardThreeLines.interpStrip_scale`：interpStrip_scale (f : Com
plex -> E) {l u : Real} (hul : l < u) (z : Complex) : interpStrip (scale f l u) 
((z - ↑l) / (↑u - ↑l)) = interpStr…
· 使用定理 `div_sub_div_same`：div_sub_div_same (a b c : K) : a / c - b / c = (a - b)
 / c
· 使用定理 `_private.Mathlib.Analysis.Complex.Hadamard.0.Complex.HadamardThreeLines.
fun_arg_eq`：∀ {l u : ℝ}, l < u → ∀ (z : ℂ), ↑l + (z / (↑u - ↑l) - ↑l / (↑u - ↑l)
) * (↑u - ↑l) = z

--- 原说明 ---
**Hadamard three-line theorem** on `re ⁻¹' [0, 1]`: If `f` is a bounded function
, continuous on the
closed strip `re ⁻¹' [0, 1]` and differentiable on open strip `re ⁻¹' (0, 1)`, t
hen for
`M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})` we have that for all `z` in the closed 
strip
`re ⁻¹' [0, 1]` the inequality `‖f(z)‖ ≤ M(0) ^ (1 - z.re) * M(1) ^ z.re` holds.
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (f : ℂ → E) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ ≤ ‖interpStrip f z‖ := by
  apply le_on_closure (fun w hw ↦ norm_le_interpStrip_of_mem_verticalStrip_zero f w hd hB hw)
    (Continuous.comp_continuousOn' continuous_norm hd.2)
    (Continuous.comp_continuousOn' continuous_norm (diffContOnCl_interpStrip f).2)
  rwa [verticalClosedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz

/-- **Hadamard three-line theorem** on `re ⁻¹' [0, 1]` (Variant in simpler terms): Let `f` be a
bounded function, continuous on the closed strip `re ⁻¹' [0, 1]` and differentiable on open strip
`re ⁻¹' (0, 1)`. If, for all `z.re = 0`, `‖f z‖ ≤ a` for some `a ∈ ℝ` and, similarly, for all
`z.re = 1`, `‖f z‖ ≤ b` for some `b ∈ ℝ` then for all `z` in the closed strip
`re ⁻¹' [0, 1]` the inequality `‖f(z)‖ ≤ a ^ (1 - z.re) * b ^ z.re` holds. -/
/-
**Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip** 是 Mathl
ib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Hadamard three-line theorem** on `re ⁻¹' [0, 1]` (Variant in simpler terms): L
et `f` be a
bounded function, continuous on the closed strip `re ⁻¹' [0, 1]` and differentia
ble on open strip
`re ⁻¹' (0, 1)`. If, for all `z.re = 0`, `‖f z‖ ≤ a` for some `a ∈ ℝ` and, simil
arly, for all
`z.re = 1`, `‖f z‖ ≤ b` for some `b ∈ ℝ` then for all `z` in the closed strip
`re ⁻¹' [0, 1]` the inequality `‖f(z)‖ ≤ a ^ (1 - z.re) * b ^ z.re` holds.
-/
lemma norm_le_interp_of_mem_verticalClosedStrip₀₁' (f : ℂ → E) {z : ℂ} {a b : ℝ}
    (hz : z ∈ verticalClosedStrip 0 1) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (ha : ∀ z ∈ re ⁻¹' {0}, ‖f z‖ ≤ a) (hb : ∀ z ∈ re ⁻¹' {1}, ‖f z‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - z.re) * b ^ z.re := by
  have : ‖interpStrip f z‖ ≤ sSupNormIm f 0 ^ (1 - z.re) * sSupNormIm f 1 ^ z.re := by
    by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    · rw [interpStrip_eq_of_zero f z h, norm_zero, mul_nonneg_iff]
      left
      exact ⟨Real.rpow_nonneg (sSupNormIm_nonneg f _) _,
        Real.rpow_nonneg (sSupNormIm_nonneg f _) _ ⟩
    · rcases h with ⟨h0, h1⟩
      rw [ne_comm] at h0 h1
      simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
      simp only [norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h0).mp (sSupNormIm_nonneg f _)) _]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h1).mp (sSupNormIm_nonneg f _)) _]
      simp only [sub_re, one_re, le_refl]
  apply (norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ f hz hd hB).trans (this.trans _)
  apply mul_le_mul_of_nonneg _ _ (Real.rpow_nonneg (sSupNormIm_nonneg f _) _)
  · apply (Real.rpow_nonneg _ _)
    specialize hb 1
    simp only [mem_preimage, one_re, mem_singleton_iff, forall_true_left] at hb
    exact (norm_nonneg _).trans hb
  · gcongr
    · exact sSupNormIm_nonneg f _
    · exact sub_nonneg.mpr hz.2
    rw [sSupNormIm]
    apply csSup_le _
    · simpa [comp_apply, mem_image, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂] using ha
    · use ‖(f 0)‖, 0
      simp
  · apply Real.rpow_le_rpow (sSupNormIm_nonneg f _) _ hz.1
    · rw [sSupNormIm]
      apply csSup_le _
      · simpa [comp_apply, mem_image, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] using hb
      · use ‖(f 1)‖, 1
        simp only [mem_preimage, one_re, mem_singleton_iff, comp_apply,
          and_self]

/-- The transformation on ℂ that is used for `scale` maps the strip ``re ⁻¹' (l, u)``
  to the strip ``re ⁻¹' (0, 1)``. -/
/-
**Complex.HadamardThreeLines.scale_id_mem_verticalStrip_of_mem_verticalStrip** 是
 Mathlib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：scale_id_mem_verticalStrip_of_mem_verticalStrip {l u : Real} (hul : l < u)
 {z : Complex} (hz : z in verticalStrip 0 1) : l + z * (u - l) in verticalStrip 
l u
参数：hul : l < u；hz : z in verticalStrip 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_lt_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α]
 [AddRightStrictMono α] {a b : α} (c : α), a - c < b - c ↔ a < b
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The transformation on ℂ that is used for `scale` maps the strip ``re ⁻¹' (l, u)`
`
  to the strip ``re ⁻¹' (0, 1)``.
-/
lemma scale_id_mem_verticalStrip_of_mem_verticalStrip {l u : ℝ} (hul : l < u) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : l + z * (u - l) ∈ verticalStrip l u := by
  simp only [verticalStrip, mem_preimage, mem_Ioo] at hz
  simp only [verticalStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im, ofReal_im,
    sub_self, mul_zero, sub_zero, mem_Ioo, lt_add_iff_pos_right]
  obtain ⟨hz₁, hz₂⟩ := hz
  simp only [hz₁, mul_pos_iff_of_pos_left, sub_pos, hul, true_and]
  rw [add_comm, ← sub_lt_sub_iff_right l, add_sub_assoc, sub_self, add_zero]
  nth_rewrite 2 [← one_mul (u - l)]
  gcongr

/-- If z is on the closed strip `re ⁻¹' [l, u]`, then `(z - l) / (u - l)` is on the closed strip
  `re ⁻¹' [0, 1]`. -/
/-
**Complex.HadamardThreeLines.mem_verticalClosedStrip_of_scale_id_mem_verticalClo
sedStrip** 是 Mathlib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip {z : Complex} 
{l u : Real} (hul : l < u) (hz : z in verticalClosedStrip l u) : z / (u - l) - l
 / (u - l) in verticalClosedStrip 0 1
参数：hul : l < u；hz : z in verticalClosedStrip l u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.div_re`：div_re (z w : Complex) : (z / w).re = z.re * w.re / norm
Sq w + z.im * w.im / normSq w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.normSq_ofReal`：normSq_ofReal (r : Real) : normSq r = r * r
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `div_mul_eq_div_div_swap`：div_mul_eq_div_div_swap : a / (b * c) = a / c /
 b
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
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
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
If z is on the closed strip `re ⁻¹' [l, u]`, then `(z - l) / (u - l)` is on the 
closed strip
  `re ⁻¹' [0, 1]`.
-/
lemma mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip {z : ℂ} {l u : ℝ} (hul : l < u)
    (hz : z ∈ verticalClosedStrip l u) : z / (u - l) - l / (u - l) ∈ verticalClosedStrip 0 1 := by
  simp only [verticalClosedStrip, Complex.div_re, mem_preimage, sub_re, mem_Icc,
    sub_nonneg, tsub_le_iff_right, ofReal_re, ofReal_im, sub_im, sub_self, mul_zero, zero_div,
    add_zero]
  simp only [verticalClosedStrip] at hz
  norm_cast
  simp_rw [Complex.normSq_ofReal, mul_div_assoc, div_mul_eq_div_div_swap,
    div_self (by linarith : u - l ≠ 0), ← div_eq_mul_one_div]
  constructor
  · gcongr
    exact hz.1
  · rw [← sub_le_sub_iff_right (l / (u - l)), add_sub_assoc, sub_self, add_zero, div_sub_div_same,
      div_le_one (by simp [hul]), sub_le_sub_iff_right l]
    exact hz.2

/-- The function `scale f l u` is `diffContOnCl`. -/
/-
**Complex.HadamardThreeLines.scale_diffContOnCl** 是 Mathlib 中的一个引理，位于命名空间 `Compl
ex.HadamardThreeLines`。
形式化陈述：scale_diffContOnCl {f : Complex -> E} {l u : Real} (hul : l < u) (hd : Dif
fContOnCl Complex f (verticalStrip l u)) : DiffContOnCl Complex (scale f l u) (v
erticalStrip 0 1)
参数：hul : l < u；hd : DiffContOnCl Complex f (verticalStrip l u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `DiffContOnCl.const_add`：const_add (hf : DiffContOnCl 𝕜 f s) (c : F) : Di
ffContOnCl 𝕜 (fun x => c + f x) s
· 使用定理 `DiffContOnCl.smul_const`：smul_const {𝕜' : Type*} [NontriviallyNormedFiel
d 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜
'} {s : Set E…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.MapsTo.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t 
: Set β), Set.MapsTo f s t = ∀ ⦃x : α⦄, x ∈ s → f x ∈ t
· 使用引理 `Complex.HadamardThreeLines.scale_id_mem_verticalStrip_of_mem_verticalStr
ip`：scale_id_mem_verticalStrip_of_mem_verticalStrip {l u : Real} (hul : l < u) {
z : Complex} (hz : z in verticalStrip 0 1) : l + z * (u - l) in …

--- 原说明 ---
The function `scale f l u` is `diffContOnCl`.
-/
lemma scale_diffContOnCl {f : ℂ → E} {l u : ℝ} (hul : l < u)
    (hd : DiffContOnCl ℂ f (verticalStrip l u)) :
    DiffContOnCl ℂ (scale f l u) (verticalStrip 0 1) := by
  unfold scale
  apply DiffContOnCl.comp (s := verticalStrip l u) hd
  · apply DiffContOnCl.const_add
    apply DiffContOnCl.smul_const
    exact Differentiable.diffContOnCl differentiable_id
  · rw [MapsTo]
    intro z hz
    exact scale_id_mem_verticalStrip_of_mem_verticalStrip hul hz

/-- A technical lemma needed in the proof. -/
/-
**Complex.HadamardThreeLines.fun_arg_eq** 是 Mathlib 中的一个引理，位于命名空间 `Complex.Hadam
ardThreeLines`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A technical lemma needed in the proof.
-/
private lemma fun_arg_eq {l u : ℝ} (hul : l < u) (z : ℂ) :
    (↑l + (z / (↑u - ↑l) - ↑l / (↑u - ↑l)) * (↑u - ↑l)) = z := by
  rw [sub_mul, div_mul_comm, div_self (by norm_cast; linarith),
    div_mul_comm, div_self (by norm_cast; linarith)]
  simp

/-- Another technical lemma needed in the proof. -/
/-
**Complex.HadamardThreeLines.bound_exp_eq** 是 Mathlib 中的一个引理，位于命名空间 `Complex.Had
amardThreeLines`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Another technical lemma needed in the proof.
-/
private lemma bound_exp_eq {l u : ℝ} (hul : l < u) (z : ℂ) :
    (z / (↑u - ↑l)).re - ((l : ℂ) / (↑u - ↑l)).re = (z.re - l) / (u - l) := by
  norm_cast
  rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im, mul_div_assoc,
    div_mul_eq_div_div_swap, div_self (by norm_cast; linarith),
    ← div_eq_mul_one_div]
  simp only [mul_zero, zero_div, add_zero]
  rw [← div_sub_div_same]

/--
**Hadamard three-line theorem**: If `f` is a bounded function, continuous on the
closed strip `re ⁻¹' [l, u]` and differentiable on open strip `re ⁻¹' (l, u)`, then for
`M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})` we have that for all `z` in the closed strip
`re ⁻¹' [a,b]` the inequality
`‖f(z)‖ ≤ M(0) ^ (1 - ((z.re - l) / (u - l))) * M(1) ^ ((z.re - l) / (u - l))`
holds. -/
/-
**Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip** 是 
Mathlib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：norm_le_interpStrip_of_mem_verticalClosedStrip {l u : Real} (hul : l < u) 
{f : Complex -> E} {z : Complex} (hz : z in verticalClosedStrip l u) (hd : DiffC
ontOnCl Complex f (verticalStrip l u)) (hB : BddAbove ((norm ∘ f) '' verticalClo
sedStrip l u)) : ‖f z‖ <= ‖interpStrip' f l u z‖
参数：hul : l < u；hz : z in verticalClosedStrip l u；hd : DiffContOnCl Complex f (ve
rticalStrip l u)；hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStri
p₀₁`：norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (f : Complex -> E) {z : Co
mplex} (hz : z in verticalClosedStrip 0 1) (hd : DiffContOnCl Com…
· 使用引理 `Complex.HadamardThreeLines.mem_verticalClosedStrip_of_scale_id_mem_verti
calClosedStrip`：mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip {z :
 Complex} {l u : Real} (hul : l < u) (hz : z in verticalClosedStrip l u) : z…
· 使用引理 `Complex.HadamardThreeLines.scale_diffContOnCl`：scale_diffContOnCl {f : C
omplex -> E} {l u : Real} (hul : l < u) (hd : DiffContOnCl Complex f (verticalSt
rip l u)) : DiffContOnCl Complex (s…
· 使用引理 `Complex.HadamardThreeLines.scale_bddAbove`：scale_bddAbove {f : Complex -
> E} {l u : Real} (hul : l < u) (hB : BddAbove ((norm ∘ f) '' verticalClosedStri
p l u)) : BddAbove ((norm ∘ sca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.HadamardThreeLines.interpStrip_scale`：interpStrip_scale (f : Com
plex -> E) {l u : Real} (hul : l < u) (z : Complex) : interpStrip (scale f l u) 
((z - ↑l) / (↑u - ↑l)) = interpStr…
· 使用定理 `div_sub_div_same`：div_sub_div_same (a b c : K) : a / c - b / c = (a - b)
 / c
· 使用定理 `_private.Mathlib.Analysis.Complex.Hadamard.0.Complex.HadamardThreeLines.
fun_arg_eq`：∀ {l u : ℝ}, l < u → ∀ (z : ℂ), ↑l + (z / (↑u - ↑l) - ↑l / (↑u - ↑l)
) * (↑u - ↑l) = z

--- 原说明 ---
**Hadamard three-line theorem**: If `f` is a bounded function, continuous on the
closed strip `re ⁻¹' [l, u]` and differentiable on open strip `re ⁻¹' (l, u)`, t
hen for
`M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})` we have that for all `z` in the closed 
strip
`re ⁻¹' [a,b]` the inequality
`‖f(z)‖ ≤ M(0) ^ (1 - ((z.re - l) / (u - l))) * M(1) ^ ((z.re - l) / (u - l))`
holds.
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip {l u : ℝ} (hul : l < u)
    {f : ℂ → E} {z : ℂ}
    (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)) :
    ‖f z‖ ≤ ‖interpStrip' f l u z‖ := by
  have hgoal := norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz)
    (scale_diffContOnCl hul hd) (scale_bddAbove hul hB)
  simp only [scale, smul_eq_mul] at hgoal
  rw [fun_arg_eq hul, div_sub_div_same, interpStrip_scale f hul z] at hgoal
  exact hgoal

/-- **Hadamard three-line theorem** (Variant in simpler terms): Let `f` be a
bounded function, continuous on the closed strip `re ⁻¹' [l, u]` and differentiable on open strip
`re ⁻¹' (l, u)`. If, for all `z.re = l`, `‖f z‖ ≤ a` for some `a ∈ ℝ` and, similarly, for all
`z.re = u`, `‖f z‖ ≤ b` for some `b ∈ ℝ` then for all `z` in the closed strip
`re ⁻¹' [l, u]` the inequality
`‖f(z)‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l))`
holds. -/
/-
**Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'** 是 Math
lib 中的一个引理，位于命名空间 `Complex.HadamardThreeLines`。
形式化陈述：norm_le_interp_of_mem_verticalClosedStrip' {f : Complex -> E} {z : Complex
} {a b l u : Real} (hul : l < u) (hz : z in verticalClosedStrip l u) (hd : DiffC
ontOnCl Complex f (verticalStrip l u)) (hB : BddAbove ((norm ∘ f) '' verticalClo
sedStrip l u)) (ha : forall z in re ⁻¹' {l}, ‖f z‖ <= a) (hb : forall z in re ⁻¹
' {u}, ‖f z‖ <= b) : ‖f z‖ <= a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) /
 (u - l))
参数：hul : l < u；hz : z in verticalClosedStrip l u；hd : DiffContOnCl Complex f (ve
rticalStrip l u)；hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)；ha : fora
ll z in re ⁻¹' {l}, ‖f z‖ <= a；hb : forall z in re ⁻¹' {u}, ‖f z‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`
：norm_le_interp_of_mem_verticalClosedStrip₀₁' (f : Complex -> E) {z : Complex} {
a b : Real} (hz : z in verticalClosedStrip 0 1) (hd : DiffCon…
· 使用引理 `Complex.HadamardThreeLines.mem_verticalClosedStrip_of_scale_id_mem_verti
calClosedStrip`：mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip {z :
 Complex} {l u : Real} (hul : l < u) (hz : z in verticalClosedStrip l u) : z…
· 使用引理 `Complex.HadamardThreeLines.scale_diffContOnCl`：scale_diffContOnCl {f : C
omplex -> E} {l u : Real} (hul : l < u) (hd : DiffContOnCl Complex f (verticalSt
rip l u)) : DiffContOnCl Complex (s…
· 使用引理 `Complex.HadamardThreeLines.scale_bddAbove`：scale_bddAbove {f : Complex -
> E} {l u : Real} (hul : l < u) (hB : BddAbove ((norm ∘ f) '' verticalClosedStri
p l u)) : BddAbove ((norm ∘ sca…
· 使用引理 `Complex.HadamardThreeLines.scale_bound_left`：scale_bound_left {f : Compl
ex -> E} {l u a : Real} (ha : forall z in re ⁻¹' {l}, ‖f z‖ <= a) : forall z in 
re ⁻¹' {0}, ‖scale f l u z‖ <= a
· 使用引理 `Complex.HadamardThreeLines.scale_bound_right`：scale_bound_right {f : Com
plex -> E} {l u b : Real} (hb : forall z in re ⁻¹' {u}, ‖f z‖ <= b) : forall z i
n re ⁻¹' {1}, ‖scale f l u z‖ <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.Complex.Hadamard.0.Complex.HadamardThreeLines.
bound_exp_eq`：∀ {l u : ℝ}, l < u → ∀ (z : ℂ), (z / (↑u - ↑l)).re - (↑l / (↑u - ↑
l)).re = (z.re - l) / (u - l)
· 使用定理 `_private.Mathlib.Analysis.Complex.Hadamard.0.Complex.HadamardThreeLines.
fun_arg_eq`：∀ {l u : ℝ}, l < u → ∀ (z : ℂ), ↑l + (z / (↑u - ↑l) - ↑l / (↑u - ↑l)
) * (↑u - ↑l) = z

--- 原说明 ---
**Hadamard three-line theorem** (Variant in simpler terms): Let `f` be a
bounded function, continuous on the closed strip `re ⁻¹' [l, u]` and differentia
ble on open strip
`re ⁻¹' (l, u)`. If, for all `z.re = l`, `‖f z‖ ≤ a` for some `a ∈ ℝ` and, simil
arly, for all
`z.re = u`, `‖f z‖ ≤ b` for some `b ∈ ℝ` then for all `z` in the closed strip
`re ⁻¹' [l, u]` the inequality
`‖f(z)‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l))`
holds.
-/
lemma norm_le_interp_of_mem_verticalClosedStrip' {f : ℂ → E} {z : ℂ} {a b l u : ℝ}
    (hul : l < u) (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u))
    (ha : ∀ z ∈ re ⁻¹' {l}, ‖f z‖ ≤ a) (hb : ∀ z ∈ re ⁻¹' {u}, ‖f z‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) := by
  have hgoal := norm_le_interp_of_mem_verticalClosedStrip₀₁' (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz) (scale_diffContOnCl hul hd)
    (scale_bddAbove hul hB) (scale_bound_left ha) (scale_bound_right hb)
  simp only [scale, smul_eq_mul, sub_re] at hgoal
  rw [fun_arg_eq hul, bound_exp_eq hul] at hgoal
  exact hgoal

end HadamardThreeLines
end Complex

