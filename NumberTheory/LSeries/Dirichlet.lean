/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Positivity
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# L-series of Dirichlet characters and arithmetic functions

We collect some results on L-series of specific (arithmetic) functions, for example,
the Möbius function `μ` or the von Mangoldt function `Λ`. In particular, we show that
`L ↗Λ` is the negative of the logarithmic derivative of the Riemann zeta function
on `re s > 1`; see `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.

We also prove some general results on L-series associated to Dirichlet characters
(i.e., Dirichlet L-series). For example, we show that the abscissa of absolute convergence
equals `1` (see `DirichletCharacter.absicssaOfAbsConv_eq_one`) and that the L-series does not
vanish on the open half-plane `re s > 1` (see `DirichletCharacter.LSeries_ne_zero_of_one_lt_re`).

We deduce results on the Riemann zeta function (which is `L 1` or `L ↗ζ` on `re s > 1`)
as special cases.

## Tags

Dirichlet L-series, Möbius function, von Mangoldt function, Riemann zeta function
-/

public section

open scoped LSeries.notation

/-- `δ` is the function underlying the arithmetic function `1`. -/
/-
**ArithmeticFunction.one_eq_delta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ArithmeticFunction.one_eq_delta : ↗(1 : ArithmeticFunction Complex) = δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`δ` is the function underlying the arithmetic function `1`.
-/
lemma ArithmeticFunction.one_eq_delta : ↗(1 : ArithmeticFunction ℂ) = δ := by
  ext
  simp [one_apply, LSeries.delta]


section Moebius

/-!
### The L-series of the Möbius function

We show that `L μ s` converges absolutely if and only if `re s > 1`.
-/

namespace ArithmeticFunction

-- access notation `μ`
open scoped Moebius

open LSeries Nat Complex

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArithmeticFunction.not_LSeriesSummable_moebius_at_one** 是 Mathlib 中的一个引理，位于命名空
间 `ArithmeticFunction`。
形式化陈述：not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable ↗μ 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_summable_one_div_on_primes`：not_summable_one_div_on_primes : ¬ Summa
ble (indicator {p | p.Prime} (fun n : Nat => (1 : Real) / n))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.summable_ofReal`：∀ {α : Type u_1} {L : SummationFilter α} {f : α
 → ℝ}, Summable (fun x => ↑(f x)) L ↔ Summable f L
· 使用定理 `Summable.of_neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β}
 [inst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup 
α] {f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用定理 `Summable.indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace
 α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace
 α], Sum…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ArithmeticFunction.moebius_apply_prime`：moebius_apply_prime {p : Nat} (h
p : p.Prime) : μ p = -1
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable ↗μ 1 := by
  refine fun h ↦ not_summable_one_div_on_primes <| summable_ofReal.mp <| .of_neg ?_
  refine (h.indicator {n | n.Prime}).congr fun n ↦ ?_
  by_cases hn : n.Prime
  · simp [hn, hn.ne_zero, moebius_apply_prime hn, push_cast, neg_div]
  · simp [hn]

/-- The L-series of the Möbius function converges absolutely at `s` if and only if `re s > 1`. -/
/-
**ArithmeticFunction.LSeriesSummable_moebius_iff** 是 Mathlib 中的一个引理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：LSeriesSummable_moebius_iff {s : Complex} : LSeriesSummable ↗μ s ↔ 1 < s.r
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ArithmeticFunction.not_LSeriesSummable_moebius_at_one`：not_LSeriesSummab
le_moebius_at_one : ¬ LSeriesSummable ↗μ 1
· 使用引理 `LSeriesSummable.of_re_le_re`：LSeriesSummable.of_re_le_re {f : Nat -> Com
plex} {s s' : Complex} (h : s.re <= s'.re) (hf : LSeriesSummable f s) : LSeriesS
ummable f s'
· 使用定理 `LSeriesSummable_of_bounded_of_one_lt_re`：LSeriesSummable_of_bounded_of_o
ne_lt_re {f : Nat -> Complex} {m : Real} (h : forall n != 0, ‖f n‖ <= m) {s : Co
mplex} (hs : 1 < s.re) : LSer…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ArithmeticFunction.abs_moebius_le_one`：abs_moebius_le_one {n : Nat} : |μ
 n| <= 1

--- 原说明 ---
The L-series of the Möbius function converges absolutely at `s` if and only if `
re s > 1`.
-/
lemma LSeriesSummable_moebius_iff {s : ℂ} : LSeriesSummable ↗μ s ↔ 1 < s.re := by
  refine ⟨fun H ↦ ?_, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n _ ↦ ?_⟩
  · by_contra! h
    exact not_LSeriesSummable_moebius_at_one <| LSeriesSummable.of_re_le_re (by simpa) H
  · norm_cast
    exact abs_moebius_le_one

/-- The abscissa of absolute convergence of the L-series of the Möbius function is `1`. -/
/-
**ArithmeticFunction.abscissaOfAbsConv_moebius** 是 Mathlib 中的一个引理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：abscissaOfAbsConv_moebius : abscissaOfAbsConv ↗μ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `EReal.image_coe_Ioi`：image_coe_Ioi (x : Real) : Real.toEReal '' Ioi x = 
Ioo ↑x ⊤
· 使用定理 `csInf_Ioo`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {a b
 : α} [DenselyOrdered α], b < a → sInf (Set.Ioo b a) = b
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤

--- 原说明 ---
The abscissa of absolute convergence of the L-series of the Möbius function is `
1`.
-/
lemma abscissaOfAbsConv_moebius : abscissaOfAbsConv ↗μ = 1 := by
  simpa [abscissaOfAbsConv, LSeriesSummable_moebius_iff, Set.Ioi_def, EReal.image_coe_Ioi]
    using csInf_Ioo <| EReal.coe_lt_top 1

end ArithmeticFunction

end Moebius


/-!
### L-series of Dirichlet characters
-/

open Nat

open scoped ArithmeticFunction.zeta in
/-
**ArithmeticFunction.const_one_eq_zeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ArithmeticFunction.const_one_eq_zeta {R : Type*} [AddMonoidWithOne R] {n :
 Nat} (hn : n != 0) : (1 : Nat -> R) n = (ζ ·) n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ArithmeticFunction.const_one_eq_zeta {R : Type*} [AddMonoidWithOne R] {n : ℕ} (hn : n ≠ 0) :
    (1 : ℕ → R) n = (ζ ·) n := by
  simp [hn]
/-
**LSeries.one_convolution_eq_zeta_convolution** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.one_convolution_eq_zeta_convolution {R : Type*} [Semiring R] (f : 
Nat -> R) : (1 : Nat -> R) ⍟ f = ((ArithmeticFunction.zeta ·) : Nat -> R) ⍟ f
参数：f : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.convolution_congr`：LSeries.convolution_congr {R : Type*} [Semiri
ng R] {f f' g g' : Nat -> R} (hf : forall {n}, n != 0 -> f n = f' n) (hg : foral
l {n}, n != 0 -…
· 使用引理 `ArithmeticFunction.const_one_eq_zeta`：ArithmeticFunction.const_one_eq_ze
ta {R : Type*} [AddMonoidWithOne R] {n : Nat} (hn : n != 0) : (1 : Nat -> R) n =
 (ζ ·) n
-/
lemma LSeries.one_convolution_eq_zeta_convolution {R : Type*} [Semiring R] (f : ℕ → R) :
    (1 : ℕ → R) ⍟ f = ((ArithmeticFunction.zeta ·) : ℕ → R) ⍟ f :=
  convolution_congr ArithmeticFunction.const_one_eq_zeta fun _ ↦ rfl
/-
**LSeries.convolution_one_eq_convolution_zeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.convolution_one_eq_convolution_zeta {R : Type*} [Semiring R] (f : 
Nat -> R) : f ⍟ (1 : Nat -> R) = f ⍟ ((ArithmeticFunction.zeta ·) : Nat -> R)
参数：f : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.convolution_congr`：LSeries.convolution_congr {R : Type*} [Semiri
ng R] {f f' g g' : Nat -> R} (hf : forall {n}, n != 0 -> f n = f' n) (hg : foral
l {n}, n != 0 -…
· 使用引理 `ArithmeticFunction.const_one_eq_zeta`：ArithmeticFunction.const_one_eq_ze
ta {R : Type*} [AddMonoidWithOne R] {n : Nat} (hn : n != 0) : (1 : Nat -> R) n =
 (ζ ·) n
-/
lemma LSeries.convolution_one_eq_convolution_zeta {R : Type*} [Semiring R] (f : ℕ → R) :
    f ⍟ (1 : ℕ → R) = f ⍟ ((ArithmeticFunction.zeta ·) : ℕ → R) :=
  convolution_congr (fun _ ↦ rfl) ArithmeticFunction.const_one_eq_zeta

/-- `χ₁` is (local) notation for the (necessarily trivial) Dirichlet character modulo `1`. -/
local notation (name := Dchar_one) "χ₁" => (1 : DirichletCharacter ℂ 1)

namespace DirichletCharacter

open ArithmeticFunction in
/-- The arithmetic function associated to a Dirichlet character is multiplicative. -/
/-
**DirichletCharacter.isMultiplicative_toArithmeticFunction** 是 Mathlib 中的一个引理，位于
命名空间 `DirichletCharacter`。
形式化陈述：isMultiplicative_toArithmeticFunction {N : Nat} {R : Type*} [CommMonoidWit
hZero R] (χ : DirichletCharacter R N) : (toArithmeticFunction (χ ·)).IsMultiplic
ative
参数：χ : DirichletCharacter R N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.IsMultiplicative.iff_ne_zero`：iff_ne_zero [MonoidWith
Zero R] {f : ArithmeticFunction R} : IsMultiplicative f ↔ f 1 = 1 ∧ forall {m n 
: Nat}, m != 0 -> n != 0 -> m.Coprime…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…

--- 原说明 ---
The arithmetic function associated to a Dirichlet character is multiplicative.
-/
lemma isMultiplicative_toArithmeticFunction {N : ℕ} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) :
    (toArithmeticFunction (χ ·)).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn _ ↦ ?_⟩
  · simp [toArithmeticFunction]
  · simp [toArithmeticFunction, hm, hn]
/-
**DirichletCharacter.apply_eq_toArithmeticFunction_apply** 是 Mathlib 中的一个引理，位于命名
空间 `DirichletCharacter`。
形式化陈述：apply_eq_toArithmeticFunction_apply {N : Nat} {R : Type*} [CommMonoidWithZ
ero R] (χ : DirichletCharacter R N) {n : Nat} (hn : n != 0) : χ n = toArithmetic
Function (χ ·) n
参数：χ : DirichletCharacter R N；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_eq_toArithmeticFunction_apply {N : ℕ} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) {n : ℕ} (hn : n ≠ 0) :
    χ n = toArithmeticFunction (χ ·) n := by
  simp [toArithmeticFunction, hn]

open LSeries Nat Complex

/-- Twisting by a Dirichlet character `χ` distributes over convolution. -/
/-
**DirichletCharacter.mul_convolution_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Dirichle
tCharacter`。
形式化陈述：mul_convolution_distrib {R : Type*} [CommSemiring R] {n : Nat} (χ : Dirich
letCharacter R n) (f g : Nat -> R) : (((χ ·) : Nat -> R) * f) ⍟ (((χ ·) : Nat ->
 R) * g) = ((χ ·) : Nat -> R) * (f ⍟ g)
参数：χ : DirichletCharacter R n；f g : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.convolution_def`：convolution_def {R : Type*} [Semiring R] (f g :
 Nat -> R) : f ⍟ g = fun n => ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)

--- 原说明 ---
Twisting by a Dirichlet character `χ` distributes over convolution.
-/
lemma mul_convolution_distrib {R : Type*} [CommSemiring R] {n : ℕ} (χ : DirichletCharacter R n)
    (f g : ℕ → R) :
    (((χ ·) : ℕ → R) * f) ⍟ (((χ ·) : ℕ → R) * g) = ((χ ·) : ℕ → R) * (f ⍟ g) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [(mem_divisorsAntidiagonal.mp hp).1.symm, cast_mul, map_mul]
  exact mul_mul_mul_comm ..
/-
**DirichletCharacter.mul_delta** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：mul_delta {n : Nat} (χ : DirichletCharacter Complex n) : ↗χ * δ = δ
参数：χ : DirichletCharacter Complex n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.mul_delta`：mul_delta {f : Nat -> Complex} (h : f 1 = 1) : f * δ 
= δ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
-/
lemma mul_delta {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ * δ = δ :=
  LSeries.mul_delta <| by rw [cast_one, map_one]
/-
**DirichletCharacter.delta_mul** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：delta_mul {n : Nat} (χ : DirichletCharacter Complex n) : δ * ↗χ = δ
参数：χ : DirichletCharacter Complex n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.mul_delta`：mul_delta {n : Nat} (χ : DirichletCharacte
r Complex n) : ↗χ * δ = δ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma delta_mul {n : ℕ} (χ : DirichletCharacter ℂ n) : δ * ↗χ = δ :=
  mul_comm δ _ ▸ mul_delta ..

open ArithmeticFunction in
open scoped Moebius in -- access notation `μ`
/-- The convolution of a Dirichlet character `χ` with the twist `χ * μ` is `δ`,
the indicator function of `{1}`. -/
/-
**DirichletCharacter.convolution_mul_moebius** 是 Mathlib 中的一个引理，位于命名空间 `Dirichle
tCharacter`。
形式化陈述：convolution_mul_moebius {n : Nat} (χ : DirichletCharacter Complex n) : ↗χ 
⍟ (↗χ * ↗μ) = δ
参数：χ : DirichletCharacter Complex n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.one_convolution_eq_zeta_convolution`：LSeries.one_convolution_eq_
zeta_convolution {R : Type*} [Semiring R] (f : Nat -> R) : (1 : Nat -> R) ⍟ f = 
((ArithmeticFunction.zeta ·) : Na…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ArithmeticFunction.one_eq_delta`：ArithmeticFunction.one_eq_delta : ↗(1 :
 ArithmeticFunction Complex) = δ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ArithmeticFunction.coe_mul`：ArithmeticFunction.coe_mul {R : Type*} [Semi
ring R] (f g : ArithmeticFunction R) : f ⍟ g = ⇑(f * g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ArithmeticFunction.coe_zeta_mul_coe_moebius`：coe_zeta_mul_coe_moebius [R
ing R] : (ζ * μ : ArithmeticFunction R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `DirichletCharacter.mul_convolution_distrib`：mul_convolution_distrib {R :
 Type*} [CommSemiring R] {n : Nat} (χ : DirichletCharacter R n) (f g : Nat -> R)
 : (((χ ·) : Nat -> R) * f) ⍟ ((…
· 使用引理 `DirichletCharacter.mul_delta`：mul_delta {n : Nat} (χ : DirichletCharacte
r Complex n) : ↗χ * δ = δ

--- 原说明 ---
The convolution of a Dirichlet character `χ` with the twist `χ * μ` is `δ`,
the indicator function of `{1}`.
-/
lemma convolution_mul_moebius {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ ⍟ (↗χ * ↗μ) = δ := by
  have : (1 : ℕ → ℂ) ⍟ (μ ·) = δ := by
    rw [one_convolution_eq_zeta_convolution, ← one_eq_delta]
    simp_rw [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius]
  nth_rewrite 1 [← mul_one ↗χ]
  simpa only [mul_convolution_distrib χ 1 ↗μ, this] using mul_delta _

/-- The Dirichlet character mod `0` corresponds to `δ`. -/
/-
**DirichletCharacter.modZero_eq_delta** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharac
ter`。
形式化陈述：modZero_eq_delta {χ : DirichletCharacter Complex 0} : ↗χ = δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用引理 `ZMod.eq_one_of_isUnit_natCast`：eq_one_of_isUnit_natCast {n : Nat} (h : I
sUnit (n : ZMod 0)) : n = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
The Dirichlet character mod `0` corresponds to `δ`.
-/
lemma modZero_eq_delta {χ : DirichletCharacter ℂ 0} : ↗χ = δ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [cast_zero, χ.map_nonunit not_isUnit_zero, delta, reduceCtorEq, if_false]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp [delta]
  have : ¬ IsUnit (n : ZMod 0) := fun h ↦ hn' <| ZMod.eq_one_of_isUnit_natCast h
  simp_all [χ.map_nonunit this, delta]

/-- The Dirichlet character mod `1` corresponds to the constant function `1`. -/
/-
**DirichletCharacter.modOne_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter
`。
形式化陈述：modOne_eq_one {R : Type*} [CommMonoidWithZero R] {χ : DirichletCharacter R
 1} : ((χ ·) : Nat -> R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.level_one`：level_one (χ : DirichletCharacter R 1) : χ
 = 1
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `isUnit_of_subsingleton`：isUnit_of_subsingleton [Monoid M] [Subsingleton 
M] (a : M) : IsUnit a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1

--- 原说明 ---
The Dirichlet character mod `1` corresponds to the constant function `1`.
-/
lemma modOne_eq_one {R : Type*} [CommMonoidWithZero R] {χ : DirichletCharacter R 1} :
    ((χ ·) : ℕ → R) = 1 := by
  ext
  rw [χ.level_one, MulChar.one_apply (isUnit_of_subsingleton _), Pi.one_apply]
/-
**DirichletCharacter.LSeries_modOne_eq** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：LSeries_modOne_eq : L ↗χ₁ = L 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `DirichletCharacter.modOne_eq_one`：modOne_eq_one {R : Type*} [CommMonoidW
ithZero R] {χ : DirichletCharacter R 1} : ((χ ·) : Nat -> R) = 1
-/
lemma LSeries_modOne_eq : L ↗χ₁ = L 1 :=
  congr_arg L modOne_eq_one

set_option backward.isDefEq.respectTransparency.types false in
/-- The L-series of a Dirichlet character mod `N > 0` does not converge absolutely at `s = 1`. -/
/-
**DirichletCharacter.not_LSeriesSummable_at_one** 是 Mathlib 中的一个引理，位于命名空间 `Diric
hletCharacter`。
形式化陈述：not_LSeriesSummable_at_one {N : Nat} (hN : N != 0) (χ : DirichletCharacter
 Complex N) : ¬ LSeriesSummable ↗χ 1
参数：hN : N != 0；χ : DirichletCharacter Complex N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.not_summable_indicator_one_div_natCast`：Real.not_summable_indicator
_one_div_natCast {m : Nat} (hm : m != 0) (k : ZMod m) : ¬ Summable ({n : Nat | (
n : ZMod m) = k}.indicator fun n …
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `Set.indicator_apply_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preo
rder M] [inst_1 : Zero M] {s : Set α} {f : α → M} {a : α},   (a ∈ s → 0 ≤ f a) →
 0 ≤ s.indicator…
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `LSeries.norm_term_eq`：norm_term_eq (f : Nat -> Complex) (s : Complex) (n
 : Nat) : ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `MulChar.map_one`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} 
[inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'), χ 1 = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The L-series of a Dirichlet character mod `N > 0` does not converge absolutely a
t `s = 1`.
-/
lemma not_LSeriesSummable_at_one {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    ¬ LSeriesSummable ↗χ 1 := by
  refine fun h ↦ (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine h.norm.of_nonneg_of_le (fun m ↦ Set.indicator_apply_nonneg (fun _ ↦ by positivity))
    (fun n ↦ ?_)
  simp only [norm_term_eq, Set.indicator, Set.mem_ofPred_eq]
  split_ifs with h₁ h₂
  · simp [h₂]
  · simp [h₁, χ.map_one]
  all_goals positivity

/-- The L-series of a Dirichlet character converges absolutely at `s` if `re s > 1`. -/
/-
**DirichletCharacter.LSeriesSummable_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `Dir
ichletCharacter`。
形式化陈述：LSeriesSummable_of_one_lt_re {N : Nat} (χ : DirichletCharacter Complex N) 
{s : Complex} (hs : 1 < s.re) : LSeriesSummable ↗χ s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LSeriesSummable_of_bounded_of_one_lt_re`：LSeriesSummable_of_bounded_of_o
ne_lt_re {f : Nat -> Complex} {m : Real} (h : forall n != 0, ‖f n‖ <= m) {s : Co
mplex} (hs : 1 < s.re) : LSer…
· 使用引理 `DirichletCharacter.norm_le_one`：norm_le_one (a : ZMod n) : ‖χ a‖ <= 1

--- 原说明 ---
The L-series of a Dirichlet character converges absolutely at `s` if `re s > 1`.
-/
lemma LSeriesSummable_of_one_lt_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗χ s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ ↦ χ.norm_le_one _) hs

/-- The L-series of a Dirichlet character mod `N > 0` converges absolutely at `s` if and only if
`re s > 1`. -/
/-
**DirichletCharacter.LSeriesSummable_iff** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCha
racter`。
形式化陈述：LSeriesSummable_iff {N : Nat} (hN : N != 0) (χ : DirichletCharacter Comple
x N) {s : Complex} : LSeriesSummable ↗χ s ↔ 1 < s.re
参数：hN : N != 0；χ : DirichletCharacter Complex N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `DirichletCharacter.not_LSeriesSummable_at_one`：not_LSeriesSummable_at_on
e {N : Nat} (hN : N != 0) (χ : DirichletCharacter Complex N) : ¬ LSeriesSummable
 ↗χ 1
· 使用引理 `LSeriesSummable.of_re_le_re`：LSeriesSummable.of_re_le_re {f : Nat -> Com
plex} {s s' : Complex} (h : s.re <= s'.re) (hf : LSeriesSummable f s) : LSeriesS
ummable f s'
· 使用引理 `DirichletCharacter.LSeriesSummable_of_one_lt_re`：LSeriesSummable_of_one_
lt_re {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
 : LSeriesSummable ↗χ s

--- 原说明 ---
The L-series of a Dirichlet character mod `N > 0` converges absolutely at `s` if
 and only if
`re s > 1`.
-/
lemma LSeriesSummable_iff {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ} :
    LSeriesSummable ↗χ s ↔ 1 < s.re := by
  refine ⟨fun H ↦ ?_, LSeriesSummable_of_one_lt_re χ⟩
  by_contra! h
  exact not_LSeriesSummable_at_one hN χ <| LSeriesSummable.of_re_le_re (by simp [h]) H

/-- The abscissa of absolute convergence of the L-series of a Dirichlet character mod `N > 0`
is `1`. -/
/-
**DirichletCharacter.absicssaOfAbsConv_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Dirichl
etCharacter`。
形式化陈述：absicssaOfAbsConv_eq_one {N : Nat} (hn : N != 0) (χ : DirichletCharacter C
omplex N) : abscissaOfAbsConv ↗χ = 1
参数：hn : N != 0；χ : DirichletCharacter Complex N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `DirichletCharacter.LSeriesSummable_iff`：LSeriesSummable_iff {N : Nat} (h
N : N != 0) (χ : DirichletCharacter Complex N) {s : Complex} : LSeriesSummable ↗
χ s ↔ 1 < s.re
· 使用引理 `EReal.image_coe_Ioi`：image_coe_Ioi (x : Real) : Real.toEReal '' Ioi x = 
Ioo ↑x ⊤
· 使用定理 `csInf_Ioo`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {a b
 : α} [DenselyOrdered α], b < a → sInf (Set.Ioo b a) = b
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤

--- 原说明 ---
The abscissa of absolute convergence of the L-series of a Dirichlet character mo
d `N > 0`
is `1`.
-/
lemma absicssaOfAbsConv_eq_one {N : ℕ} (hn : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv ↗χ = 1 := by
  simpa [abscissaOfAbsConv, LSeriesSummable_iff hn χ, Set.Ioi_def, EReal.image_coe_Ioi]
    using csInf_Ioo <| EReal.coe_lt_top 1

/-- The L-series of the twist of `f` by a Dirichlet character converges at `s` if the L-series
of `f` does. -/
/-
**DirichletCharacter.LSeriesSummable_mul** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCha
racter`。
形式化陈述：LSeriesSummable_mul {N : Nat} (χ : DirichletCharacter Complex N) {f : Nat 
-> Complex} {s : Complex} (h : LSeriesSummable f s) : LSeriesSummable (↗χ * f) s
参数：χ : DirichletCharacter Complex N；h : LSeriesSummable f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `LSeries.norm_term_le`：norm_term_le {f g : Nat -> Complex} (s : Complex) 
{n : Nat} (h : ‖f n‖ <= ‖g n‖) : ‖term f s n‖ <= ‖term g s n‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `DirichletCharacter.norm_le_one`：norm_le_one (a : ZMod n) : ‖χ a‖ <= 1
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ

--- 原说明 ---
The L-series of the twist of `f` by a Dirichlet character converges at `s` if th
e L-series
of `f` does.
-/
lemma LSeriesSummable_mul {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) :
    LSeriesSummable (↗χ * f) s := by
  refine .of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ norm_term_le s ?_
  simpa using mul_le_of_le_one_left (norm_nonneg <| f n) <| χ.norm_le_one n

open scoped ArithmeticFunction.Moebius in
/-- The L-series of a Dirichlet character `χ` and of the twist of `μ` by `χ` are multiplicative
inverses. -/
/-
**DirichletCharacter.LSeries.mul_mu_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `DirichletC
haracter.LSeries`。
形式化陈述：∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ},   1 < s.re → LSeries (fun 
n => χ ↑n) s * LSeries ((fun n => χ ↑n) * fun n => ↑(ArithmeticFunction.moebius 
n)) s = 1
参数：χ : DirichletCharacter ℂ N；fun n => χ ↑n；(fun n => χ ↑n) * fun n => ↑(Arithme
ticFunction.moebius n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries_convolution'`：LSeries_convolution' {f g : Nat -> Complex} {s : C
omplex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeries (f ⍟ g) 
s = LSerie…
· 使用引理 `DirichletCharacter.LSeriesSummable_of_one_lt_re`：LSeriesSummable_of_one_
lt_re {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
 : LSeriesSummable ↗χ s
· 使用引理 `DirichletCharacter.LSeriesSummable_mul`：LSeriesSummable_mul {N : Nat} (χ
 : DirichletCharacter Complex N) {f : Nat -> Complex} {s : Complex} (h : LSeries
Summable f s) : LSeriesSumma…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ArithmeticFunction.LSeriesSummable_moebius_iff`：LSeriesSummable_moebius_
iff {s : Complex} : LSeriesSummable ↗μ s ↔ 1 < s.re
· 使用引理 `DirichletCharacter.convolution_mul_moebius`：convolution_mul_moebius {n :
 Nat} (χ : DirichletCharacter Complex n) : ↗χ ⍟ (↗χ * ↗μ) = δ
· 使用引理 `LSeries_delta`：LSeries_delta : LSeries δ = 1
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1

--- 原说明 ---
The L-series of a Dirichlet character `χ` and of the twist of `μ` by `χ` are mul
tiplicative
inverses.
-/
lemma LSeries.mul_mu_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : L ↗χ s * L (↗χ * ↗μ) s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_of_one_lt_re χ hs) <|
          LSeriesSummable_mul χ <| ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs,
    convolution_mul_moebius, LSeries_delta, Pi.one_apply]


/-!
### L-series of Dirichlet characters do not vanish on re s > 1
-/

/-- The L-series of a Dirichlet character does not vanish on the right half-plane `re s > 1`. -/
/-
**DirichletCharacter.LSeries_ne_zero_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `Dir
ichletCharacter`。
形式化陈述：LSeries_ne_zero_of_one_lt_re {N : Nat} (χ : DirichletCharacter Complex N) 
{s : Complex} (hs : 1 < s.re) : L ↗χ s != 0
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `DirichletCharacter.LSeries.mul_mu_eq_one`：∀ {N : ℕ} (χ : DirichletCharac
ter ℂ N) {s : ℂ},   1 < s.re → LSeries (fun n => χ ↑n) s * LSeries ((fun n => χ 
↑n) * fun n => ↑(ArithmeticFun…

--- 原说明 ---
The L-series of a Dirichlet character does not vanish on the right half-plane `r
e s > 1`.
-/
lemma LSeries_ne_zero_of_one_lt_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L ↗χ s ≠ 0 :=
  fun h ↦ by simpa [h] using LSeries.mul_mu_eq_one χ hs

end DirichletCharacter


section zeta

/-!
### The L-series of the constant sequence 1 / the arithmetic function ζ

Both give the same L-series (since the difference in values at zero has no effect;
see `ArithmeticFunction.LSeries_zeta_eq`), which agrees with the Riemann zeta function
on `re s > 1`. We state most results in two versions, one for `1` and one for `↗ζ`.
-/

open LSeries Nat Complex DirichletCharacter

/-- The abscissa of (absolute) convergence of the constant sequence `1` is `1`. -/
/-
**LSeries.abscissaOfAbsConv_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_one : abscissaOfAbsConv 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.absicssaOfAbsConv_eq_one`：absicssaOfAbsConv_eq_one {N
 : Nat} (hn : N != 0) (χ : DirichletCharacter Complex N) : abscissaOfAbsConv ↗χ 
= 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `DirichletCharacter.modOne_eq_one`：modOne_eq_one {R : Type*} [CommMonoidW
ithZero R] {χ : DirichletCharacter R 1} : ((χ ·) : Nat -> R) = 1

--- 原说明 ---
The abscissa of (absolute) convergence of the constant sequence `1` is `1`.
-/
lemma LSeries.abscissaOfAbsConv_one : abscissaOfAbsConv 1 = 1 :=
  modOne_eq_one (χ := χ₁) ▸ absicssaOfAbsConv_eq_one one_ne_zero χ₁

/-- The `LSeries` of the constant sequence `1` converges at `s` if and only if `re s > 1`. -/
/-
**LSeriesSummable_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LSeriesSummable_one_iff {s : Complex} : LSeriesSummable 1 s ↔ 1 < s.re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.LSeriesSummable_iff`：LSeriesSummable_iff {N : Nat} (h
N : N != 0) (χ : DirichletCharacter Complex N) {s : Complex} : LSeriesSummable ↗
χ s ↔ 1 < s.re
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `DirichletCharacter.modOne_eq_one`：modOne_eq_one {R : Type*} [CommMonoidW
ithZero R] {χ : DirichletCharacter R 1} : ((χ ·) : Nat -> R) = 1

--- 原说明 ---
The `LSeries` of the constant sequence `1` converges at `s` if and only if `re s
 > 1`.
-/
theorem LSeriesSummable_one_iff {s : ℂ} : LSeriesSummable 1 s ↔ 1 < s.re :=
  modOne_eq_one (χ := χ₁) ▸ LSeriesSummable_iff one_ne_zero χ₁


namespace ArithmeticFunction

-- access notation `ζ` and `μ`
open scoped zeta Moebius

/-- The `LSeries` of the arithmetic function `ζ` is the same as the `LSeries` associated
to the constant sequence `1`. -/
/-
**ArithmeticFunction.LSeries_zeta_eq** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFuncti
on`。
形式化陈述：LSeries_zeta_eq : L ↗ζ = L 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries_congr`：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n !
= 0 -> f n = g n) (s : Complex) : LSeries f s = LSeries g s
· 使用引理 `ArithmeticFunction.const_one_eq_zeta`：ArithmeticFunction.const_one_eq_ze
ta {R : Type*} [AddMonoidWithOne R] {n : Nat} (hn : n != 0) : (1 : Nat -> R) n =
 (ζ ·) n

--- 原说明 ---
The `LSeries` of the arithmetic function `ζ` is the same as the `LSeries` associ
ated
to the constant sequence `1`.
-/
lemma LSeries_zeta_eq : L ↗ζ = L 1 := by
  ext s
  exact (LSeries_congr const_one_eq_zeta s).symm

/-- The `LSeries` associated to the arithmetic function `ζ` converges at `s` if and only if
`re s > 1`. -/
/-
**ArithmeticFunction.LSeriesSummable_zeta_iff** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：LSeriesSummable_zeta_iff {s : Complex} : LSeriesSummable (ζ ·) s ↔ 1 < s.r
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `LSeriesSummable_congr`：LSeriesSummable_congr {f g : Nat -> Complex} (s :
 Complex) (h : forall {n}, n != 0 -> f n = g n) : LSeriesSummable f s ↔ LSeriesS
ummable g s
· 使用引理 `ArithmeticFunction.const_one_eq_zeta`：ArithmeticFunction.const_one_eq_ze
ta {R : Type*} [AddMonoidWithOne R] {n : Nat} (hn : n != 0) : (1 : Nat -> R) n =
 (ζ ·) n
· 使用定理 `LSeriesSummable_one_iff`：LSeriesSummable_one_iff {s : Complex} : LSeries
Summable 1 s ↔ 1 < s.re

--- 原说明 ---
The `LSeries` associated to the arithmetic function `ζ` converges at `s` if and 
only if
`re s > 1`.
-/
theorem LSeriesSummable_zeta_iff {s : ℂ} : LSeriesSummable (ζ ·) s ↔ 1 < s.re :=
  (LSeriesSummable_congr s const_one_eq_zeta).symm.trans <| LSeriesSummable_one_iff

/-- The abscissa of (absolute) convergence of the arithmetic function `ζ` is `1`. -/
/-
**ArithmeticFunction.abscissaOfAbsConv_zeta** 是 Mathlib 中的一个引理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：abscissaOfAbsConv_zeta : abscissaOfAbsConv ↗ζ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.abscissaOfAbsConv_congr`：LSeries.abscissaOfAbsConv_congr {f g : 
Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) : abscissaOfAbsConv f = ab
scissaOfAbsConv g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LSeries.abscissaOfAbsConv_one`：LSeries.abscissaOfAbsConv_one : abscissaO
fAbsConv 1 = 1

--- 原说明 ---
The abscissa of (absolute) convergence of the arithmetic function `ζ` is `1`.
-/
lemma abscissaOfAbsConv_zeta : abscissaOfAbsConv ↗ζ = 1 := by
  rw [abscissaOfAbsConv_congr (g := 1) fun hn ↦ by simp [hn], abscissaOfAbsConv_one]

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
/-
**ArithmeticFunction.LSeries_zeta_eq_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：LSeries_zeta_eq_riemannZeta {s : Complex} (hs : 1 < s.re) : L ↗ζ s = riema
nnZeta s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zeta_eq_tsum_one_div_nat_cpow`：zeta_eq_tsum_one_div_nat_cpow {s : Comple
x} (hs : 1 < re s) : riemannZeta s = ∑' n : Nat, 1 / (n : Complex) ^ s

--- 原说明 ---
The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on 
its
domain of convergence `1 < re s`.
-/
lemma LSeries_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s := by
  suffices ∑' n, term (fun n ↦ if n = 0 then 0 else 1) s n = ∑' n : ℕ, 1 / (n : ℂ) ^ s by
    simpa [LSeries, zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, ne_zero_of_one_lt_re hs]

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
/-
**ArithmeticFunction.LSeriesHasSum_zeta** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFun
ction`。
形式化陈述：LSeriesHasSum_zeta {s : Complex} (hs : 1 < s.re) : LSeriesHasSum ↗ζ s (rie
mannZeta s)
参数：hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.LSeriesHasSum`：LSeriesSummable.LSeriesHasSum {f : Nat ->
 Complex} {s : Complex} (h : LSeriesSummable f s) : LSeriesHasSum f s (LSeries f
 s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.LSeriesSummable_zeta_iff`：LSeriesSummable_zeta_iff {s
 : Complex} : LSeriesSummable (ζ ·) s ↔ 1 < s.re
· 使用引理 `ArithmeticFunction.LSeries_zeta_eq_riemannZeta`：LSeries_zeta_eq_riemannZ
eta {s : Complex} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s

--- 原说明 ---
The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on 
its
domain of convergence `1 < re s`.
-/
lemma LSeriesHasSum_zeta {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum ↗ζ s (riemannZeta s) :=
  LSeries_zeta_eq_riemannZeta hs ▸ (LSeriesSummable_zeta_iff.mpr hs).LSeriesHasSum

/-- The L-series of the arithmetic function `ζ` and of the Möbius function are inverses. -/
/-
**ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius** 是 Mathlib 中的一个引理，位于命名空间 
`ArithmeticFunction`。
形式化陈述：LSeries_zeta_mul_Lseries_moebius {s : Complex} (hs : 1 < s.re) : L ↗ζ s * 
L ↗μ s = 1
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries_convolution'`：LSeries_convolution' {f g : Nat -> Complex} {s : C
omplex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeries (f ⍟ g) 
s = LSerie…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.LSeriesSummable_zeta_iff`：LSeriesSummable_zeta_iff {s
 : Complex} : LSeriesSummable (ζ ·) s ↔ 1 < s.re
· 使用引理 `ArithmeticFunction.LSeriesSummable_moebius_iff`：LSeriesSummable_moebius_
iff {s : Complex} : LSeriesSummable ↗μ s ↔ 1 < s.re
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ArithmeticFunction.coe_mul`：ArithmeticFunction.coe_mul {R : Type*} [Semi
ring R] (f g : ArithmeticFunction R) : f ⍟ g = ⇑(f * g)
· 使用定理 `ArithmeticFunction.coe_zeta_mul_coe_moebius`：coe_zeta_mul_coe_moebius [R
ing R] : (ζ * μ : ArithmeticFunction R) = 1
· 使用引理 `ArithmeticFunction.one_eq_delta`：ArithmeticFunction.one_eq_delta : ↗(1 :
 ArithmeticFunction Complex) = δ
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries_delta`：LSeries_delta : LSeries δ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The L-series of the arithmetic function `ζ` and of the Möbius function are inver
ses.
-/
lemma LSeries_zeta_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_zeta_iff.mpr hs)
    (LSeriesSummable_moebius_iff.mpr hs)]
  simp [← natCoe_apply, ← intCoe_apply, coe_mul, one_eq_delta, LSeries_delta, -zeta_apply]

/-- The L-series of the arithmetic function `ζ` does not vanish on the right half-plane
`re s > 1`. -/
/-
**ArithmeticFunction.LSeries_zeta_ne_zero_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间
 `ArithmeticFunction`。
形式化陈述：LSeries_zeta_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : L ↗ζ s !
= 0
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius`：LSeries_zeta_mul_Ls
eries_moebius {s : Complex} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1

--- 原说明 ---
The L-series of the arithmetic function `ζ` does not vanish on the right half-pl
ane
`re s > 1`.
-/
lemma LSeries_zeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : L ↗ζ s ≠ 0 :=
  fun h ↦ by simpa [h, -zeta_apply] using LSeries_zeta_mul_Lseries_moebius hs

end ArithmeticFunction

open ArithmeticFunction

/-- The L-series of the constant sequence `1` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
/-
**LSeries_one_eq_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_one_eq_riemannZeta {s : Complex} (hs : 1 < s.re) : L 1 s = riemann
Zeta s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ArithmeticFunction.LSeries_zeta_eq_riemannZeta`：LSeries_zeta_eq_riemannZ
eta {s : Complex} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s
· 使用引理 `ArithmeticFunction.LSeries_zeta_eq`：LSeries_zeta_eq : L ↗ζ = L 1

--- 原说明 ---
The L-series of the constant sequence `1` equals the Riemann Zeta Function on it
s
domain of convergence `1 < re s`.
-/
lemma LSeries_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L 1 s = riemannZeta s :=
  LSeries_zeta_eq ▸ LSeries_zeta_eq_riemannZeta hs

/-- The L-series of the constant sequence `1` equals the Riemann zeta function on its
domain of convergence `1 < re s`. -/
/-
**LSeriesHasSum_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum_one {s : Complex} (hs : 1 < s.re) : LSeriesHasSum 1 s (riema
nnZeta s)
参数：hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.LSeriesHasSum`：LSeriesSummable.LSeriesHasSum {f : Nat ->
 Complex} {s : Complex} (h : LSeriesSummable f s) : LSeriesHasSum f s (LSeries f
 s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LSeriesSummable_one_iff`：LSeriesSummable_one_iff {s : Complex} : LSeries
Summable 1 s ↔ 1 < s.re
· 使用引理 `LSeries_one_eq_riemannZeta`：LSeries_one_eq_riemannZeta {s : Complex} (hs
 : 1 < s.re) : L 1 s = riemannZeta s

--- 原说明 ---
The L-series of the constant sequence `1` equals the Riemann zeta function on it
s
domain of convergence `1 < re s`.
-/
lemma LSeriesHasSum_one {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum 1 s (riemannZeta s) :=
  LSeries_one_eq_riemannZeta hs ▸ (LSeriesSummable_one_iff.mpr hs).LSeriesHasSum

open scoped Moebius in -- access notation `μ`
/-- The L-series of the constant sequence `1` and of the Möbius function are inverses. -/
/-
**LSeries_one_mul_Lseries_moebius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_one_mul_Lseries_moebius {s : Complex} (hs : 1 < s.re) : L 1 s * L 
↗μ s = 1
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius`：LSeries_zeta_mul_Ls
eries_moebius {s : Complex} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1
· 使用引理 `ArithmeticFunction.LSeries_zeta_eq`：LSeries_zeta_eq : L ↗ζ = L 1

--- 原说明 ---
The L-series of the constant sequence `1` and of the Möbius function are inverse
s.
-/
lemma LSeries_one_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L 1 s * L ↗μ s = 1 :=
  LSeries_zeta_eq ▸ LSeries_zeta_mul_Lseries_moebius hs

/-- The L-series of the constant sequence `1` does not vanish on the right half-plane
`re s > 1`. -/
/-
**LSeries_one_ne_zero_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_one_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : L 1 s != 
0
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ArithmeticFunction.LSeries_zeta_ne_zero_of_one_lt_re`：LSeries_zeta_ne_ze
ro_of_one_lt_re {s : Complex} (hs : 1 < s.re) : L ↗ζ s != 0
· 使用引理 `ArithmeticFunction.LSeries_zeta_eq`：LSeries_zeta_eq : L ↗ζ = L 1

--- 原说明 ---
The L-series of the constant sequence `1` does not vanish on the right half-plan
e
`re s > 1`.
-/
lemma LSeries_one_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : L 1 s ≠ 0 :=
  LSeries_zeta_eq ▸ LSeries_zeta_ne_zero_of_one_lt_re hs

/-- The Riemann Zeta Function does not vanish on the half-plane `re s > 1`. -/
/-
**riemannZeta_ne_zero_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : riemannZe
ta s != 0
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries_one_ne_zero_of_one_lt_re`：LSeries_one_ne_zero_of_one_lt_re {s : 
Complex} (hs : 1 < s.re) : L 1 s != 0
· 使用引理 `LSeries_one_eq_riemannZeta`：LSeries_one_eq_riemannZeta {s : Complex} (hs
 : 1 < s.re) : L 1 s = riemannZeta s

--- 原说明 ---
The Riemann Zeta Function does not vanish on the half-plane `re s > 1`.
-/
lemma riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  LSeries_one_eq_riemannZeta hs ▸ LSeries_one_ne_zero_of_one_lt_re hs

section ComplexOrderLemmas

open scoped ComplexOrder

/-- The Riemann zeta function is positive in `ComplexOrder` for real arguments greater than 1.
This means it is a positive real number:
both `(riemannZeta x).re > 0` and `(riemannZeta x).im = 0`. -/
/-
**riemannZeta_pos_of_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_pos_of_one_lt {x : Real} (hx : 1 < x) : 0 < riemannZeta x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries_one_eq_riemannZeta`：LSeries_one_eq_riemannZeta {s : Complex} (hs
 : 1 < s.re) : L 1 s = riemannZeta s
· 使用引理 `LSeries.positive`：positive {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 
< a 1) {x : Real} (hx : abscissaOfAbsConv a < x) : 0 < LSeries a x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LSeries.abscissaOfAbsConv_one`：LSeries.abscissaOfAbsConv_one : abscissaO
fAbsConv 1 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
The Riemann zeta function is positive in `ComplexOrder` for real arguments great
er than 1.
This means it is a positive real number:
both `(riemannZeta x).re > 0` and `(riemannZeta x).im = 0`.
-/
lemma riemannZeta_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < riemannZeta x := by
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  rw [← LSeries_one_eq_riemannZeta hx']
  refine LSeries.positive (fun _ ↦ by simp) (by simp) ?_
  simpa [LSeries.abscissaOfAbsConv_one] using (by exact_mod_cast hx : (1 : EReal) < x)

/-- The real part of the Riemann zeta function is positive for real arguments greater than 1. -/
/-
**riemannZeta_re_pos_of_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_re_pos_of_one_lt {x : Real} (hx : 1 < x) : 0 < (riemannZeta x)
.re
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.pos_iff`：pos_iff {z : Complex} : 0 < z ↔ 0 < z.re ∧ 0 = z.im
· 使用引理 `riemannZeta_pos_of_one_lt`：riemannZeta_pos_of_one_lt {x : Real} (hx : 1 
< x) : 0 < riemannZeta x

--- 原说明 ---
The real part of the Riemann zeta function is positive for real arguments greate
r than 1.
-/
lemma riemannZeta_re_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < (riemannZeta x).re :=
  (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).1

/-- The Riemann zeta function is real-valued for real arguments greater than 1. -/
/-
**riemannZeta_im_eq_zero_of_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_im_eq_zero_of_one_lt {x : Real} (hx : 1 < x) : (riemannZeta x)
.im = 0
参数：hx : 1 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.pos_iff`：pos_iff {z : Complex} : 0 < z ↔ 0 < z.re ∧ 0 = z.im
· 使用引理 `riemannZeta_pos_of_one_lt`：riemannZeta_pos_of_one_lt {x : Real} (hx : 1 
< x) : 0 < riemannZeta x

--- 原说明 ---
The Riemann zeta function is real-valued for real arguments greater than 1.
-/
lemma riemannZeta_im_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) : (riemannZeta x).im = 0 :=
  (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).2.symm

end ComplexOrderLemmas

end zeta


section vonMangoldt

/-!
### The L-series of the von Mangoldt function
-/

open LSeries Nat Complex ArithmeticFunction

namespace ArithmeticFunction

-- access notation `ζ`
open scoped zeta

/-- A translation of the relation `Λ * ↑ζ = log` of (real-valued) arithmetic functions
to an equality of complex sequences. -/
/-
**ArithmeticFunction.convolution_vonMangoldt_zeta** 是 Mathlib 中的一个引理，位于命名空间 `Ari
thmeticFunction`。
形式化陈述：convolution_vonMangoldt_zeta : ↗Λ ⍟ ↗ζ = ↗Complex.log
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.convolution_def`：convolution_def {R : Type*} [Semiring R] (f g :
 Nat -> R) : f ⍟ g = fun n => ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Complex.ofReal_sum`：ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real)
 : Complex) = ∑ i in s, (f i : Complex)
· 使用引理 `Complex.natCast_log`：natCast_log {n : Nat} : Real.log n = log n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ArithmeticFunction.vonMangoldt_mul_zeta`：ArithmeticFunction.vonMangoldt 
* ↑ArithmeticFunction.zeta = ArithmeticFunction.log

--- 原说明 ---
A translation of the relation `Λ * ↑ζ = log` of (real-valued) arithmetic functio
ns
to an equality of complex sequences.
-/
lemma convolution_vonMangoldt_zeta : ↗Λ ⍟ ↗ζ = ↗Complex.log := by
  ext n
  simpa [apply_ite, LSeries.convolution_def, -vonMangoldt_mul_zeta]
    using congr_arg (ofReal <| · n) vonMangoldt_mul_zeta
/-
**ArithmeticFunction.convolution_vonMangoldt_const_one** 是 Mathlib 中的一个引理，位于命名空间
 `ArithmeticFunction`。
形式化陈述：convolution_vonMangoldt_const_one : ↗Λ ⍟ 1 = ↗Complex.log
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LSeries.convolution_one_eq_convolution_zeta`：LSeries.convolution_one_eq_
convolution_zeta {R : Type*} [Semiring R] (f : Nat -> R) : f ⍟ (1 : Nat -> R) = 
f ⍟ ((ArithmeticFunction.zeta ·) …
· 使用引理 `ArithmeticFunction.convolution_vonMangoldt_zeta`：convolution_vonMangoldt
_zeta : ↗Λ ⍟ ↗ζ = ↗Complex.log
-/
lemma convolution_vonMangoldt_const_one : ↗Λ ⍟ 1 = ↗Complex.log :=
  (convolution_one_eq_convolution_zeta _).trans convolution_vonMangoldt_zeta

/-- The L-series of the von Mangoldt function `Λ` converges at `s` when `re s > 1`. -/
/-
**ArithmeticFunction.LSeriesSummable_vonMangoldt** 是 Mathlib 中的一个引理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：LSeriesSummable_vonMangoldt {s : Complex} (hs : 1 < s.re) : LSeriesSummabl
e ↗Λ s
参数：hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable_logMul_of_lt_re`：LSeriesSummable_logMul_of_lt_re {f : Na
t -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re) : LSeriesSummable (
logMul f) s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.abscissaOfAbsConv_one`：LSeries.abscissaOfAbsConv_one : abscissaO
fAbsConv 1 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LSeriesSummable.eq_1`：∀ (f : ℕ → ℂ) (s : ℂ), LSeriesSummable f s = Summa
ble (LSeries.term f s)
· 使用定理 `summable_norm_iff`：summable_norm_iff {α E : Type*} [NormedAddCommGroup E
] [NormedSpace Real E] [FiniteDimensional Real E] {f : α -> E} : (Summable fun x
 => ‖f …
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `LSeries.norm_term_le`：norm_term_le {f g : Nat -> Complex} (s : Complex) 
{n : Nat} (h : ‖f n‖ <= ‖g n‖) : ‖term f s n‖ <= ‖term g s n‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ArithmeticFunction.vonMangoldt_le_log`：∀ {n : ℕ}, ArithmeticFunction.von
Mangoldt n ≤ Real.log ↑n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The L-series of the von Mangoldt function `Λ` converges at `s` when `re s > 1`.
-/
lemma LSeriesSummable_vonMangoldt {s : ℂ} (hs : 1 < s.re) : LSeriesSummable ↗Λ s := by
  have hf := LSeriesSummable_logMul_of_lt_re
    (show abscissaOfAbsConv 1 < s.re by rw [abscissaOfAbsConv_one]; exact_mod_cast hs)
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  refine hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_term_le s ?_)
  have hΛ : ‖↗Λ n‖ ≤ ‖Complex.log n‖ := by
    simpa [abs_of_nonneg, vonMangoldt_nonneg, ← natCast_log, Real.log_natCast_nonneg]
      using vonMangoldt_le_log
  exact hΛ.trans <| by simp

end ArithmeticFunction

namespace DirichletCharacter

/-- A twisted version of the relation `Λ * ↑ζ = log` in terms of complex sequences. -/
/-
**DirichletCharacter.convolution_twist_vonMangoldt** 是 Mathlib 中的一个引理，位于命名空间 `Di
richletCharacter`。
形式化陈述：convolution_twist_vonMangoldt {N : Nat} (χ : DirichletCharacter Complex N)
 : (↗χ * ↗Λ) ⍟ ↗χ = ↗χ * ↗Complex.log
参数：χ : DirichletCharacter Complex N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ArithmeticFunction.convolution_vonMangoldt_const_one`：convolution_vonMan
goldt_const_one : ↗Λ ⍟ 1 = ↗Complex.log
· 使用引理 `DirichletCharacter.mul_convolution_distrib`：mul_convolution_distrib {R :
 Type*} [CommSemiring R] {n : Nat} (χ : DirichletCharacter R n) (f g : Nat -> R)
 : (((χ ·) : Nat -> R) * f) ⍟ ((…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
A twisted version of the relation `Λ * ↑ζ = log` in terms of complex sequences.
-/
lemma convolution_twist_vonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (↗χ * ↗Λ) ⍟ ↗χ = ↗χ * ↗Complex.log := by
  rw [← convolution_vonMangoldt_const_one, ← χ.mul_convolution_distrib, mul_one]

/-- The L-series of the twist of the von Mangoldt function `Λ` by a Dirichlet character `χ`
converges at `s` when `re s > 1`. -/
/-
**DirichletCharacter.LSeriesSummable_twist_vonMangoldt** 是 Mathlib 中的一个引理，位于命名空间
 `DirichletCharacter`。
形式化陈述：LSeriesSummable_twist_vonMangoldt {N : Nat} (χ : DirichletCharacter Comple
x N) {s : Complex} (hs : 1 < s.re) : LSeriesSummable (↗χ * ↗Λ) s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.LSeriesSummable_mul`：LSeriesSummable_mul {N : Nat} (χ
 : DirichletCharacter Complex N) {f : Nat -> Complex} {s : Complex} (h : LSeries
Summable f s) : LSeriesSumma…
· 使用引理 `ArithmeticFunction.LSeriesSummable_vonMangoldt`：LSeriesSummable_vonMango
ldt {s : Complex} (hs : 1 < s.re) : LSeriesSummable ↗Λ s

--- 原说明 ---
The L-series of the twist of the von Mangoldt function `Λ` by a Dirichlet charac
ter `χ`
converges at `s` when `re s > 1`.
-/
lemma LSeriesSummable_twist_vonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (↗χ * ↗Λ) s :=
  LSeriesSummable_mul χ <| LSeriesSummable_vonMangoldt hs

/-- The L-series of the twist of the von Mangoldt function `Λ` by a Dirichlet character `χ` at `s`
equals the negative logarithmic derivative of the L-series of `χ` when `re s > 1`. -/
/-
**DirichletCharacter.LSeries_twist_vonMangoldt_eq** 是 Mathlib 中的一个引理，位于命名空间 `Dir
ichletCharacter`。
形式化陈述：LSeries_twist_vonMangoldt_eq {N : Nat} (χ : DirichletCharacter Complex N) 
{s : Complex} (hs : 1 < s.re) : L (↗χ * ↗Λ) s = -deriv (L ↗χ) s / L ↗χ s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `DirichletCharacter.modZero_eq_delta`：modZero_eq_delta {χ : DirichletChar
acter Complex 0} : ↗χ = δ
· 使用引理 `LSeries.delta_mul_eq_smul_delta`：delta_mul_eq_smul_delta {f : Nat -> Com
plex} : δ * f = f 1 • δ
· 使用定理 `ArithmeticFunction.vonMangoldt_apply_one`：ArithmeticFunction.vonMangoldt
 1 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries_zero`：LSeries_zero : LSeries 0 = 0
· 使用引理 `LSeries_delta`：LSeries_delta : LSeries δ = 1
· 使用定理 `deriv_one`：deriv_one [One F] : deriv (1 : 𝕜 -> F) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.LSeriesSummable_iff`：LSeriesSummable_iff {N : Nat} (h
N : N != 0) (χ : DirichletCharacter Complex N) {s : Complex} : LSeriesSummable ↗
χ s ↔ 1 < s.re
· 使用引理 `DirichletCharacter.absicssaOfAbsConv_eq_one`：absicssaOfAbsConv_eq_one {N
 : Nat} (hn : N != 0) (χ : DirichletCharacter Complex N) : abscissaOfAbsConv ↗χ 
= 1
· 使用定理 `EReal.coe_one`：coe_one : ((1 : Real) : EReal) = 1
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用引理 `DirichletCharacter.LSeriesSummable_twist_vonMangoldt`：LSeriesSummable_tw
ist_vonMangoldt {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs :
 1 < s.re) : LSeriesSummable (↗χ * ↗Λ) s
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用引理 `DirichletCharacter.LSeries_ne_zero_of_one_lt_re`：LSeries_ne_zero_of_one_
lt_re {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
 : L ↗χ s != 0
· 使用引理 `LSeries_convolution'`：LSeries_convolution' {f g : Nat -> Complex} {s : C
omplex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeries (f ⍟ g) 
s = LSerie…
· 使用引理 `DirichletCharacter.convolution_twist_vonMangoldt`：convolution_twist_vonM
angoldt {N : Nat} (χ : DirichletCharacter Complex N) : (↗χ * ↗Λ) ⍟ ↗χ = ↗χ * ↗Co
mplex.log
· 使用引理 `LSeries_deriv`：LSeries_deriv {f : Nat -> Complex} {s : Complex} (h : abs
cissaOfAbsConv f < s.re) : deriv (LSeries f) s = -LSeries (logMul f) s
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The L-series of the twist of the von Mangoldt function `Λ` by a Dirichlet charac
ter `χ` at `s`
equals the negative logarithmic derivative of the L-series of `χ` when `re s > 1
`.
-/
lemma LSeries_twist_vonMangoldt_eq {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗Λ) s = -deriv (L ↗χ) s / L ↗χ s := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [modZero_eq_delta, delta_mul_eq_smul_delta, LSeries_delta]
  -- now `N ≠ 0`
  have hχ : LSeriesSummable ↗χ s := (LSeriesSummable_iff hN χ).mpr hs
  have hs' : abscissaOfAbsConv ↗χ < s.re := by
    rwa [absicssaOfAbsConv_eq_one hN, ← EReal.coe_one, EReal.coe_lt_coe_iff]
  have hΛ : LSeriesSummable (↗χ * ↗Λ) s := LSeriesSummable_twist_vonMangoldt χ hs
  rw [eq_div_iff <| LSeries_ne_zero_of_one_lt_re χ hs, ← LSeries_convolution' hΛ hχ,
    convolution_twist_vonMangoldt, LSeries_deriv hs', neg_neg]
  exact LSeries_congr (fun _ ↦ by simp [mul_comm, logMul]) s

end DirichletCharacter

namespace ArithmeticFunction

open DirichletCharacter in
/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the L-series of the constant sequence `1` on its domain of convergence `re s > 1`. -/
/-
**ArithmeticFunction.LSeries_vonMangoldt_eq** 是 Mathlib 中的一个引理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：LSeries_vonMangoldt_eq {s : Complex} (hs : 1 < s.re) : L ↗Λ s = - deriv (L
 1) s / L 1 s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LSeries_congr`：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n !
= 0 -> f n = g n) (s : Complex) : LSeries f s = LSeries g s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `DirichletCharacter.LSeries_twist_vonMangoldt_eq`：LSeries_twist_vonMangol
dt_eq {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
 : L (↗χ * ↗Λ) s = -deriv (L ↗χ) s / …
· 使用引理 `DirichletCharacter.LSeries_modOne_eq`：LSeries_modOne_eq : L ↗χ₁ = L 1

--- 原说明 ---
The L-series of the von Mangoldt function `Λ` equals the negative logarithmic de
rivative
of the L-series of the constant sequence `1` on its domain of convergence `re s 
> 1`.
-/
lemma LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) : L ↗Λ s = - deriv (L 1) s / L 1 s := by
  refine (LSeries_congr (fun {n} _ ↦ ?_) s).trans <|
    LSeries_modOne_eq ▸ LSeries_twist_vonMangoldt_eq χ₁ hs
  simp [Subsingleton.eq_one (α := ZMod 1)]

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the Riemann zeta function on its domain of convergence `re s > 1`. -/
/-
**ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div** 是 Mathlib 中的
一个引理，位于命名空间 `ArithmeticFunction`。
形式化陈述：LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : Complex} (hs : 1 < s.re)
 : L ↗Λ s = - deriv riemannZeta s / riemannZeta s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用引理 `LSeries_one_eq_riemannZeta`：LSeries_one_eq_riemannZeta {s : Complex} (hs
 : 1 < s.re) : L 1 s = riemannZeta s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ArithmeticFunction.LSeries_vonMangoldt_eq`：LSeries_vonMangoldt_eq {s : C
omplex} (hs : 1 < s.re) : L ↗Λ s = - deriv (L 1) s / L 1 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The L-series of the von Mangoldt function `Λ` equals the negative logarithmic de
rivative
of the Riemann zeta function on its domain of convergence `re s > 1`.
-/
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = - deriv riemannZeta s / riemannZeta s := by
  suffices deriv (L 1) s = deriv riemannZeta s by
    rw [LSeries_vonMangoldt_eq hs, ← LSeries_one_eq_riemannZeta hs, this]
  refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
    fun _ ↦ LSeries_one_eq_riemannZeta⟩

end ArithmeticFunction

end vonMangoldt

