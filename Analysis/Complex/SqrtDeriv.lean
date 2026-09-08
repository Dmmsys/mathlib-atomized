/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of `Complex.sqrt`

This file proves that `Complex.sqrt` is differentiable on the slit plane
`Complex.slitPlane` and computes its derivative.

## Main results

* `Complex.hasDerivAt_sqrt`: the derivative of `Complex.sqrt` at `z ∈ slitPlane`
  is `z ^ (-1 / 2 : ℂ) / 2`.
* `Complex.differentiableOn_sqrt`: `Complex.sqrt` is differentiable on `slitPlane`.
* `Complex.deriv_sqrt`: the derivative equals `z ^ (-1 / 2 : ℂ) / 2`.
-/

public section

namespace Complex

/-
**Complex.hasStrictDerivAt_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_sqrt {z : Complex} (hz : z in slitPlane) : HasStrictDeriv
At sqrt (z ^ (-1 / 2 : Complex) / 2) z
参数：hz : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.congr_deriv`：HasStrictDerivAt.congr_deriv (h : HasStric
tDerivAt f f' x) (h' : f' = g') : HasStrictDerivAt f g' x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.hasStrictDerivAt_cpow_const`：Complex.hasStrictDerivAt_cpow_const
 (h : x in slitPlane) : HasStrictDerivAt (fun z : Complex => z ^ c) (c * x ^ (c 
- 1)) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.isRat_eq_true`：∀ {α : Type u} [inst : Ring α] {a b 
: α} {n : ℤ} {d : ℕ},   Mathlib.Meta.NormNum.IsRat a n d → Mathlib.Meta.NormNum.
IsRat b n d → a = b
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isRat_div`：∀ {α : Type u} [inst : DivisionRing α] {
a b : α} {cn : ℤ} {cd : ℕ},   Mathlib.Meta.NormNum.IsRat (a * b⁻¹) cn cd → Mathl
ib.Meta.NormNum.IsRa…
· 使用定理 `Mathlib.Meta.NormNum.isRat_mul`：isRat_mul {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HMul.hMul -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isRat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → Mathlib.Meta.NormNum.IsRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
lemma hasStrictDerivAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) :
    HasStrictDerivAt sqrt (z ^ (-1 / 2 : ℂ) / 2) z := by
  exact (Complex.hasStrictDerivAt_cpow_const (c := 2⁻¹) hz).congr_deriv (by
    rw [show (2 : ℂ)⁻¹ - 1 = -1 / 2 by norm_num, mul_comm, ← div_eq_mul_inv])
/-
**Complex.hasDerivAt_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_sqrt {z : Complex} (hz : z in slitPlane) : HasDerivAt sqrt (z ^
 (-1 / 2 : Complex) / 2) z
参数：hz : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.hasStrictDerivAt_sqrt`：hasStrictDerivAt_sqrt {z : Complex} (hz :
 z in slitPlane) : HasStrictDerivAt sqrt (z ^ (-1 / 2 : Complex) / 2) z
-/
lemma hasDerivAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt sqrt (z ^ (-1 / 2 : ℂ) / 2) z :=
  (hasStrictDerivAt_sqrt hz).hasDerivAt
/-
**Complex.hasDerivWithinAt_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasDerivWithinAt_sqrt {z : Complex} {s : Set Complex} (hz : z in slitPlane
) : HasDerivWithinAt sqrt (z ^ (-1 / 2 : Complex) / 2) s z
参数：hz : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.hasDerivAt_sqrt`：hasDerivAt_sqrt {z : Complex} (hz : z in slitPl
ane) : HasDerivAt sqrt (z ^ (-1 / 2 : Complex) / 2) z
-/
lemma hasDerivWithinAt_sqrt {z : ℂ} {s : Set ℂ} (hz : z ∈ slitPlane) :
    HasDerivWithinAt sqrt (z ^ (-1 / 2 : ℂ) / 2) s z :=
  (hasDerivAt_sqrt hz).hasDerivWithinAt

@[fun_prop]
/-
**Complex.differentiableAt_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_sqrt {z : Complex} (hz : z in slitPlane) : Differentiable
At Complex sqrt z
参数：hz : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.hasDerivAt_sqrt`：hasDerivAt_sqrt {z : Complex} (hz : z in slitPl
ane) : HasDerivAt sqrt (z ^ (-1 / 2 : Complex) / 2) z
-/
lemma differentiableAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ sqrt z :=
  (hasDerivAt_sqrt hz).differentiableAt

@[fun_prop]
/-
**Complex.differentiableWithinAt_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：differentiableWithinAt_sqrt {z : Complex} {s : Set Complex} (hz : z in sli
tPlane) : DifferentiableWithinAt Complex sqrt s z
参数：hz : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `Complex.differentiableAt_sqrt`：differentiableAt_sqrt {z : Complex} (hz :
 z in slitPlane) : DifferentiableAt Complex sqrt z
-/
lemma differentiableWithinAt_sqrt {z : ℂ} {s : Set ℂ} (hz : z ∈ slitPlane) :
    DifferentiableWithinAt ℂ sqrt s z :=
  (differentiableAt_sqrt hz).differentiableWithinAt

@[fun_prop]
/-
**Complex.differentiableOn_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：differentiableOn_sqrt : DifferentiableOn Complex sqrt slitPlane
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `Complex.differentiableAt_sqrt`：differentiableAt_sqrt {z : Complex} (hz :
 z in slitPlane) : DifferentiableAt Complex sqrt z
-/
lemma differentiableOn_sqrt : DifferentiableOn ℂ sqrt slitPlane :=
  fun _ hz => (differentiableAt_sqrt hz).differentiableWithinAt
/-
**Complex.deriv_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：deriv_sqrt {z : Complex} (hz : z in slitPlane) : deriv sqrt z = z ^ (-1 / 
2 : Complex) / 2
参数：hz : z in slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.hasDerivAt_sqrt`：hasDerivAt_sqrt {z : Complex} (hz : z in slitPl
ane) : HasDerivAt sqrt (z ^ (-1 / 2 : Complex) / 2) z
-/
lemma deriv_sqrt {z : ℂ} (hz : z ∈ slitPlane) : deriv sqrt z = z ^ (-1 / 2 : ℂ) / 2 :=
  (hasDerivAt_sqrt hz).deriv
/-
**Complex.derivWithin_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：derivWithin_sqrt {z : Complex} (hz : z in slitPlane) : derivWithin sqrt sl
itPlane z = z ^ (-1 / 2 : Complex) / 2
参数：hz : z in slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.hasDerivWithinAt_sqrt`：hasDerivWithinAt_sqrt {z : Complex} {s : 
Set Complex} (hz : z in slitPlane) : HasDerivWithinAt sqrt (z ^ (-1 / 2 : Comple
x) / 2) s z
· 使用定理 `IsOpen.uniqueDiffWithinAt`：IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs
 : x in s) : UniqueDiffWithinAt 𝕜 s x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Complex.isOpen_slitPlane`：IsOpen Complex.slitPlane
-/
lemma derivWithin_sqrt {z : ℂ} (hz : z ∈ slitPlane) :
    derivWithin sqrt slitPlane z = z ^ (-1 / 2 : ℂ) / 2 :=
  (hasDerivWithinAt_sqrt hz).derivWithin (isOpen_slitPlane.uniqueDiffWithinAt hz)

/-- `Complex.sqrt` is continuous at `z` provided `0 ≤ z.re` or `z.im ≠ 0`. This is weaker than
requiring `z ∈ slitPlane`, as it additionally includes the imaginary axis and `0`. -/
/-
**Complex.continuousAt_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：continuousAt_sqrt {z : Complex} (hz : 0 <= z.re ∨ z.im != 0) : ContinuousA
t sqrt z
参数：hz : 0 <= z.re ∨ z.im != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.continuousAt_cpow_const_of_re_pos`：continuousAt_cpow_const_of_re
_pos {z w : Complex} (hz : 0 <= re z ∨ im z != 0) (hw : 0 < re w) : ContinuousAt
 (fun x => x ^ w) z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Complex.div_ofNat_re`：div_ofNat_re (z : Complex) (n : Nat) [n.AtLeastTwo
] : (z / ofNat(n)).re = z.re / ofNat(n)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
`Complex.sqrt` is continuous at `z` provided `0 ≤ z.re` or `z.im ≠ 0`. This is w
eaker than
requiring `z ∈ slitPlane`, as it additionally includes the imaginary axis and `0
`.
-/
lemma continuousAt_sqrt {z : ℂ} (hz : 0 ≤ z.re ∨ z.im ≠ 0) : ContinuousAt sqrt z :=
  continuousAt_cpow_const_of_re_pos hz (by norm_num)
/-
**Complex.continuousOn_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：continuousOn_sqrt : ContinuousOn sqrt slitPlane
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用引理 `Complex.continuousAt_sqrt`：continuousAt_sqrt {z : Complex} (hz : 0 <= z.
re ∨ z.im != 0) : ContinuousAt sqrt z
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma continuousOn_sqrt : ContinuousOn sqrt slitPlane :=
  fun _ hz => (continuousAt_sqrt (hz.imp le_of_lt id)).continuousWithinAt

end Complex

