/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler, Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Positivity
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Positivity of values of L-series

The main results of this file are as follows.

* If `a : ℕ → ℂ` takes nonnegative real values and `a 1 > 0`, then `L a x > 0`
  when `x : ℝ` is in the open half-plane of absolute convergence; see
  `LSeries.positive` and `ArithmeticFunction.LSeries_positive`.

* If in addition the L-series of `a` agrees on some open right half-plane where it
  converges with an entire function `f`, then `f` is positive on the real axis;
  see `LSeries.positive_of_eq_differentiable` and
  `ArithmeticFunction.LSeries_positive_of_eq_differentiable`.
-/

public section

open scoped ComplexOrder

open Complex

namespace LSeries

/-- If all values of a `ℂ`-valued arithmetic function are nonnegative reals and `x` is a
real number in the domain of absolute convergence, then the `n`th iterated derivative
of the associated L-series is nonnegative real when `n` is even and nonpositive real
when `n` is odd. -/
/-
**LSeries.iteratedDeriv_alternating** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：iteratedDeriv_alternating {a : Nat -> Complex} (hn : 0 <= a) {x : Real} (h
 : LSeries.abscissaOfAbsConv a < x) (n : Nat) : 0 <= (-1) ^ n * iteratedDeriv n 
(LSeries a) x
参数：hn : 0 <= a；h : LSeries.abscissaOfAbsConv a < x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries_iteratedDeriv`：LSeries_iteratedDeriv {f : Nat -> Complex} (m : N
at) {s : Complex} (h : abscissaOfAbsConv f < s.re) : iteratedDeriv m (LSeries f)
 s = (-1) ^…
· 使用定理 `LSeries.eq_1`：∀ (f : ℕ → ℂ) (s : ℂ), LSeries f s = ∑' (n : ℕ), LSeries.t
erm f s n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `Complex.orderClosedTopology`：OrderClosedTopology ℂ
· 使用引理 `LSeries.term_def`：term_def (f : Nat -> Complex) (s : Complex) (n : Nat) 
: term f s n = if n = 0 then 0 else f n / n ^ s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `RCLike.toIsStrictOrderedRing`：toIsStrictOrderedRing : IsStrictOrderedRin
g K
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Complex.inv_natCast_cpow_ofReal_pos`：inv_natCast_cpow_ofReal_pos {n : Na
t} (hn : n != 0) (x : Real) : 0 < ((n : Complex) ^ (x : Complex))⁻¹
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If all values of a `ℂ`-valued arithmetic function are nonnegative reals and `x` 
is a
real number in the domain of absolute convergence, then the `n`th iterated deriv
ative
of the associated L-series is nonnegative real when `n` is even and nonpositive 
real
when `n` is odd.
-/
lemma iteratedDeriv_alternating {a : ℕ → ℂ} (hn : 0 ≤ a) {x : ℝ}
    (h : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries a) x := by
  rw [LSeries_iteratedDeriv _ h, LSeries, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
    one_mul]
  refine tsum_nonneg fun k ↦ ?_
  rw [LSeries.term_def]
  split
  · exact le_rfl
  · refine mul_nonneg ?_ <| (inv_natCast_cpow_ofReal_pos (by assumption) x).le
    induction n with
    | zero => simpa only [Function.iterate_zero, id_eq] using! hn k
    | succ n IH =>
        rw [Function.iterate_succ_apply']
        refine mul_nonneg ?_ IH
        simp only [← natCast_log, zero_le_real, Real.log_natCast_nonneg]

/-- If all values of `a : ℕ → ℂ` are nonnegative reals and `a 1` is positive,
then `L a x` is positive real for all real `x` larger than `abscissaOfAbsConv a`. -/
/-
**LSeries.positive** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：positive {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : Real} (h
x : abscissaOfAbsConv a < x) : 0 < LSeries a x
参数：ha₀ : 0 <= a；ha₁ : 0 < a 1；hx : abscissaOfAbsConv a < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LSeries.eq_1`：∀ (f : ℕ → ℂ) (s : ℂ), LSeries f s = ∑' (n : ℕ), LSeries.t
erm f s n
· 使用定理 `Summable.tsum_pos`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter 
ι} [inst : AddCommGroup α] [inst_1 : PartialOrder α]   [IsOrderedAddMonoid α] [i
nst_3 :…
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.orderClosedTopology`：OrderClosedTopology ℂ
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s
· 使用引理 `LSeries.term_nonneg`：term_nonneg {a : Nat -> Complex} {n : Nat} (h : 0 <
= a n) (x : Real) : 0 <= term a x n
· 使用引理 `LSeries.term_pos`：term_pos {a : Nat -> Complex} {n : Nat} (hn : n != 0) 
(h : 0 < a n) (x : Real) : 0 < term a x n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
If all values of `a : ℕ → ℂ` are nonnegative reals and `a 1` is positive,
then `L a x` is positive real for all real `x` larger than `abscissaOfAbsConv a`
.
-/
lemma positive {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {x : ℝ} (hx : abscissaOfAbsConv a < x) :
    0 < LSeries a x := by
  rw [LSeries]
  refine Summable.tsum_pos ?_ (fun n ↦ term_nonneg (ha₀ n) x) 1 <| term_pos one_ne_zero ha₁ x
  exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simpa only [ofReal_re] using hx

/-- If all values of `a : ℕ → ℂ` are nonnegative reals and `a 1`
is positive, and the L-series of `a` agrees with an entire function `f` on some open
right half-plane where it converges, then `f` is real and positive on `ℝ`. -/
/-
**LSeries.positive_of_differentiable_of_eqOn** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`
。
形式化陈述：positive_of_differentiable_of_eqOn {a : Nat -> Complex} (ha₀ : 0 <= a) (ha
₁ : 0 < a 1) {f : Complex -> Complex} (hf : Differentiable Complex f) {x : Real}
 (hx : abscissaOfAbsConv a <= x) (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : 
Real) : 0 < f y
参数：ha₀ : 0 <= a；ha₁ : 0 < a 1；hf : Differentiable Complex f；hx : abscissaOfAbsCo
nv a <= x；hf' : {s | x < s.re}.EqOn f (LSeries a)；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用引理 `LSeries.positive`：positive {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 
< a 1) {x : Real} (hx : abscissaOfAbsConv a < x) : 0 < LSeries a x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Differentiable.apply_le_of_iteratedDeriv_alternating`：apply_le_of_iterat
edDeriv_alternating {f : Complex -> Complex} {c : Complex} (hf : Differentiable 
Complex f) (h : forall n != 0, 0 <= (-1) ^…
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用引理 `RCLike.instOrderClosedTopology`：instOrderClosedTopology : OrderClosedTop
ology K where isClosed_le'
· 使用引理 `Set.EqOn.iteratedDeriv_of_isOpen`：Set.EqOn.iteratedDeriv_of_isOpen (hfg 
: Set.EqOn f g s) (hs : IsOpen s) (n : Nat) : Set.EqOn (iteratedDeriv n f) (iter
atedDeriv n g) s
· 使用引理 `LSeries.iteratedDeriv_alternating`：iteratedDeriv_alternating {a : Nat ->
 Complex} (hn : 0 <= a) {x : Real} (h : LSeries.abscissaOfAbsConv a < x) (n : Na
t) : 0 <= (-1) ^ n * it…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If all values of `a : ℕ → ℂ` are nonnegative reals and `a 1`
is positive, and the L-series of `a` agrees with an entire function `f` on some 
open
right half-plane where it converges, then `f` is real and positive on `ℝ`.
-/
lemma positive_of_differentiable_of_eqOn {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℝ} (hx : abscissaOfAbsConv a ≤ x)
    (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : ℝ) :
    0 < f y := by
  have hxy : x < max x y + 1 := (le_max_left x y).trans_lt (lt_add_one _)
  have hxy' : abscissaOfAbsConv a < max x y + 1 := hx.trans_lt <| mod_cast hxy
  have hys : (max x y + 1 : ℂ) ∈ {s | x < s.re} := by
    simp only [Set.mem_ofPred_eq, add_re, ofReal_re, one_re, hxy]
  have hfx : 0 < f (max x y + 1) := by
    simpa only [hf' hys, ofReal_add, ofReal_one] using positive ha₀ ha₁ hxy'
  refine (hfx.trans_le <| hf.apply_le_of_iteratedDeriv_alternating (fun n _ ↦ ?_) ?_)
  · have hs : IsOpen {s : ℂ | x < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    simpa only [hf'.iteratedDeriv_of_isOpen hs n hys, ofReal_add, ofReal_one] using
      iteratedDeriv_alternating ha₀ hxy' n
  · exact_mod_cast (le_max_right x y).trans (lt_add_one _).le

end LSeries

namespace ArithmeticFunction

/-- If all values of a `ℂ`-valued arithmetic function are nonnegative reals and `x` is a
real number in the domain of absolute convergence, then the `n`th iterated derivative
of the associated L-series is nonnegative real when `n` is even and nonpositive real
when `n` is odd. -/
/-
**ArithmeticFunction.iteratedDeriv_LSeries_alternating** 是 Mathlib 中的一个引理，位于命名空间
 `ArithmeticFunction`。
形式化陈述：iteratedDeriv_LSeries_alternating (a : ArithmeticFunction Complex) (hn : f
orall n, 0 <= a n) {x : Real} (h : LSeries.abscissaOfAbsConv a < x) (n : Nat) : 
0 <= (-1) ^ n * iteratedDeriv n (LSeries (a ·)) x
参数：a : ArithmeticFunction Complex；hn : forall n, 0 <= a n；h : LSeries.abscissaOf
AbsConv a < x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.iteratedDeriv_alternating`：iteratedDeriv_alternating {a : Nat ->
 Complex} (hn : 0 <= a) {x : Real} (h : LSeries.abscissaOfAbsConv a < x) (n : Na
t) : 0 <= (-1) ^ n * it…

--- 原说明 ---
If all values of a `ℂ`-valued arithmetic function are nonnegative reals and `x` 
is a
real number in the domain of absolute convergence, then the `n`th iterated deriv
ative
of the associated L-series is nonnegative real when `n` is even and nonpositive 
real
when `n` is odd.
-/
lemma iteratedDeriv_LSeries_alternating (a : ArithmeticFunction ℂ) (hn : ∀ n, 0 ≤ a n) {x : ℝ}
    (h : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries (a ·)) x :=
  LSeries.iteratedDeriv_alternating hn h n

/-- If all values of a `ℂ`-valued arithmetic function `a` are nonnegative reals and `a 1` is
positive, then `L a x` is positive real for all real `x` larger than `abscissaOfAbsConv a`. -/
/-
**ArithmeticFunction.LSeries_positive** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：LSeries_positive {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : 
Real} (hx : LSeries.abscissaOfAbsConv a < x) : 0 < LSeries a x
参数：ha₀ : 0 <= a；ha₁ : 0 < a 1；hx : LSeries.abscissaOfAbsConv a < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.positive`：positive {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 
< a 1) {x : Real} (hx : abscissaOfAbsConv a < x) : 0 < LSeries a x

--- 原说明 ---
If all values of a `ℂ`-valued arithmetic function `a` are nonnegative reals and 
`a 1` is
positive, then `L a x` is positive real for all real `x` larger than `abscissaOf
AbsConv a`.
-/
lemma LSeries_positive {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) :
    0 < LSeries a x :=
  LSeries.positive ha₀ ha₁ hx

/-- If all values of a `ℂ`-valued arithmetic function `a` are nonnegative reals and `a 1`
is positive, and the L-series of `a` agrees with an entire function `f` on some open
right half-plane where it converges, then `f` is real and positive on `ℝ`. -/
/-
**ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn** 是 Mathlib 中的一个
引理，位于命名空间 `ArithmeticFunction`。
形式化陈述：LSeries_positive_of_differentiable_of_eqOn {a : ArithmeticFunction Complex
} (ha₀ : 0 <= (a ·)) (ha₁ : 0 < a 1) {f : Complex -> Complex} (hf : Differentiab
le Complex f) {x : Real} (hx : LSeries.abscissaOfAbsConv a <= x) (hf' : {s | x <
 s.re}.EqOn f (LSeries a)) (y : Real) : 0 < f y
参数：ha₀ : 0 <= (a ·)；ha₁ : 0 < a 1；hf : Differentiable Complex f；hx : LSeries.abs
cissaOfAbsConv a <= x；hf' : {s | x < s.re}.EqOn f (LSeries a)；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.positive_of_differentiable_of_eqOn`：positive_of_differentiable_o
f_eqOn {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {f : Complex -> Compl
ex} (hf : Differentiable Complex…

--- 原说明 ---
If all values of a `ℂ`-valued arithmetic function `a` are nonnegative reals and 
`a 1`
is positive, and the L-series of `a` agrees with an entire function `f` on some 
open
right half-plane where it converges, then `f` is real and positive on `ℝ`.
-/
lemma LSeries_positive_of_differentiable_of_eqOn {a : ArithmeticFunction ℂ} (ha₀ : 0 ≤ (a ·))
    (ha₁ : 0 < a 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a ≤ x) (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : ℝ) :
    0 < f y :=
  LSeries.positive_of_differentiable_of_eqOn ha₀ ha₁ hf hx hf' y

end ArithmeticFunction

