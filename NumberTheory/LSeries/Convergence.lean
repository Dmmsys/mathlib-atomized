/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Convergence of L-series

We define `LSeries.abscissaOfAbsConv f` (as an `EReal`) to be the infimum
of all real numbers `x` such that the L-series of `f` converges for complex arguments with
real part `x` and provide some results about it.

## Tags

L-series, abscissa of convergence
-/

@[expose] public section

open Complex

/-- The abscissa `x : EReal` of absolute convergence of the L-series associated to `f`:
the series converges absolutely at `s` when `re s > x` and does not converge absolutely
when `re s < x`. -/
/-
**LSeries.abscissaOfAbsConv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv (f : Nat -> Complex) : EReal
参数：f : Nat -> Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The abscissa `x : EReal` of absolute convergence of the L-series associated to `
f`:
the series converges absolutely at `s` when `re s > x` and does not converge abs
olutely
when `re s < x`.
-/
noncomputable def LSeries.abscissaOfAbsConv (f : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | LSeriesSummable f x}
/-
**LSeries.abscissaOfAbsConv_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_congr {f g : Nat -> Complex} (h : forall {n}, n 
!= 0 -> f n = g n) : abscissaOfAbsConv f = abscissaOfAbsConv g
参数：h : forall {n}, n != 0 -> f n = g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `LSeriesSummable_congr`：LSeriesSummable_congr {f g : Nat -> Complex} (s :
 Complex) (h : forall {n}, n != 0 -> f n = g n) : LSeriesSummable f s ↔ LSeriesS
ummable g s
-/
lemma LSeries.abscissaOfAbsConv_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
  congr_arg sInf <| congr_arg _ <| Set.ext fun x ↦ LSeriesSummable_congr x h

open Filter in
/-- If `f` and `g` agree on large `n : ℕ`, then their `LSeries` have the same
abscissa of absolute convergence. -/
/-
**LSeries.abscissaOfAbsConv_congr'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_congr' {f g : Nat -> Complex} (h : f =ᶠ[atTop] g
) : abscissaOfAbsConv f = abscissaOfAbsConv g
参数：h : f =ᶠ[atTop] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `LSeriesSummable_congr'`：LSeriesSummable_congr' {f g : Nat -> Complex} (s
 : Complex) (h : f =ᶠ[atTop] g) : LSeriesSummable f s ↔ LSeriesSummable g s

--- 原说明 ---
If `f` and `g` agree on large `n : ℕ`, then their `LSeries` have the same
abscissa of absolute convergence.
-/
lemma LSeries.abscissaOfAbsConv_congr' {f g : ℕ → ℂ} (h : f =ᶠ[atTop] g) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
  congr_arg sInf <| congr_arg _ <| Set.ext fun x ↦ LSeriesSummable_congr' x h

open LSeries
/-
**LSeriesSummable_of_abscissaOfAbsConv_lt_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable_of_abscissaOfAbsConv_lt_re {f : Nat -> Complex} {s : Compl
ex} (hs : abscissaOfAbsConv f < s.re) : LSeriesSummable f s
参数：hs : abscissaOfAbsConv f < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LSeriesSummable.of_re_le_re`：LSeriesSummable.of_re_le_re {f : Nat -> Com
plex} {s s' : Complex} (h : s.re <= s'.re) (hf : LSeriesSummable f s) : LSeriesS
ummable f s'
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
-/
lemma LSeriesSummable_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) : LSeriesSummable f s := by
  obtain ⟨y, hy, hys⟩ : ∃ a : ℝ, LSeriesSummable f a ∧ a < s.re := by
    simpa [abscissaOfAbsConv, sInf_lt_iff] using hs
  exact hy.of_re_le_re <| ofReal_re y ▸ hys.le
/-
**LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re {f : Nat -> Complex} {s :
 Complex} (hs : abscissaOfAbsConv f < s.re) : exists x : Real, x < s.re ∧ LSerie
sSummable f x
参数：hs : abscissaOfAbsConv f < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.exists_between_coe_real`：exists_between_coe_real {x z : EReal} (h 
: x < z) : exists y : Real, x < y ∧ y < z
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s
-/
lemma LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) :
    ∃ x : ℝ, x < s.re ∧ LSeriesSummable f x := by
  obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hs
  exact ⟨x, by simpa using hx₂, LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁⟩
/-
**LSeriesSummable.abscissaOfAbsConv_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.abscissaOfAbsConv_le {f : Nat -> Complex} {s : Complex} (h
 : LSeriesSummable f s) : abscissaOfAbsConv f <= s.re
参数：h : LSeriesSummable f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LSeriesSummable.of_re_le_re`：LSeriesSummable.of_re_le_re {f : Nat -> Com
plex} {s s' : Complex} (h : s.re <= s'.re) (hf : LSeriesSummable f s) : LSeriesS
ummable f s'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma LSeriesSummable.abscissaOfAbsConv_le {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    abscissaOfAbsConv f ≤ s.re :=
  sInf_le <| by simpa using h.of_re_le_re (by simp)
/-
**LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : Nat -> Comp
lex} {x : Real} (h : forall y : Real, x < y -> LSeriesSummable f y) : abscissaOf
AbsConv f <= x
参数：h : forall y : Real, x < y -> LSeriesSummable f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sInf_le_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : ℕ → ℂ} {x : ℝ}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  refine sInf_le_iff.mpr fun y hy ↦ le_of_forall_gt_imp_ge_of_dense fun a ↦ ?_
  replace hy : ∀ (a : ℝ), LSeriesSummable f a → y ≤ a := by simpa [mem_lowerBounds] using hy
  cases a with
  | coe a₀ => exact_mod_cast fun ha ↦ hy a₀ (h a₀ ha)
  | bot => simp
  | top => simp
/-
**LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : Nat -> Com
plex} {x : EReal} (h : forall y : Real, x < y -> LSeriesSummable f y) : abscissa
OfAbsConv f <= x
参数：h : forall y : Real, x < y -> LSeriesSummable f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sInf_eq_bot`：∀ {α : Type u_1} [inst : CompleteLinearOrder α] {s : Set α}
, sInf s = ⊥ ↔ ∀ (b : α), ⊥ < b → ∃ a ∈ s, a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
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
· 使用定理 `EReal.zero_lt_top`：zero_lt_top : (0 : EReal) < ⊤
· 使用引理 `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable`：LSeries.absci
ssaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : Nat -> Complex} {x : Real} (h 
: forall y : Real, x < y -> LSeriesSummable f y…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : ℕ → ℂ} {x : EReal}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  cases x with
  | coe => exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable <| mod_cast h
  | top => exact le_top
  | bot =>
    refine le_of_eq <| sInf_eq_bot.mpr fun y hy ↦ ?_
    cases y with
    | bot => simp at hy
    | coe y => exact ⟨_, ⟨_, h _ <| EReal.bot_lt_coe _, rfl⟩, mod_cast sub_one_lt y⟩
    | top => exact ⟨_, ⟨_, h _ <| EReal.bot_lt_coe 0, rfl⟩, EReal.zero_lt_top⟩

/-- If `‖f n‖` is bounded by a constant times `n^x`, then the abscissa of absolute convergence
of `f` is bounded by `x + 1`. -/
/-
**LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow {f : Nat -> Complex} {x 
: Real} (h : exists C, forall n != 0, ‖f n‖ <= C * n ^ x) : abscissaOfAbsConv f 
<= x + 1
参数：h : exists C, forall n != 0, ‖f n‖ <= C * n ^ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `EReal.exists_between_coe_real`：exists_between_coe_real {x z : EReal} (h 
: x < z) : exists y : Real, x < y ∧ y < z
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `LSeriesSummable.abscissaOfAbsConv_le`：LSeriesSummable.abscissaOfAbsConv_
le {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) : abscissaOfAbsC
onv f <= s.re
· 使用引理 `LSeriesSummable_of_le_const_mul_rpow`：LSeriesSummable_of_le_const_mul_rp
ow {f : Nat -> Complex} {x : Real} {s : Complex} (hs : x < s.re) (h : exists C, 
forall n != 0, ‖f n‖ <= C …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
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

--- 原说明 ---
If `‖f n‖` is bounded by a constant times `n^x`, then the abscissa of absolute c
onvergence
of `f` is bounded by `x + 1`.
-/
lemma LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow {f : ℕ → ℂ} {x : ℝ}
    (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ x) : abscissaOfAbsConv f ≤ x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_le_const_mul_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
    |>.abscissaOfAbsConv_le.trans_lt hy₂).false

open Filter in
/-- If `‖f n‖` is `O(n^x)`, then the abscissa of absolute convergence
of `f` is bounded by `x + 1`. -/
/-
**LSeries.abscissaOfAbsConv_le_of_isBigO_rpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_le_of_isBigO_rpow {f : Nat -> Complex} {x : Real
} (h : f =O[atTop] fun n => (n : Real) ^ x) : abscissaOfAbsConv f <= x + 1
参数：h : f =O[atTop] fun n => (n : Real) ^ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `EReal.exists_between_coe_real`：exists_between_coe_real {x z : EReal} (h 
: x < z) : exists y : Real, x < y ∧ y < z
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `LSeriesSummable.abscissaOfAbsConv_le`：LSeriesSummable.abscissaOfAbsConv_
le {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) : abscissaOfAbsC
onv f <= s.re
· 使用引理 `LSeriesSummable_of_isBigO_rpow`：LSeriesSummable_of_isBigO_rpow {f : Nat 
-> Complex} {x : Real} {s : Complex} (hs : x < s.re) (h : f =O[atTop] fun n => (
n : Real) ^ (x - 1))…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
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

--- 原说明 ---
If `‖f n‖` is `O(n^x)`, then the abscissa of absolute convergence
of `f` is bounded by `x + 1`.
-/
lemma LSeries.abscissaOfAbsConv_le_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ}
    (h : f =O[atTop] fun n ↦ (n : ℝ) ^ x) :
    abscissaOfAbsConv f ≤ x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_isBigO_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
    |>.abscissaOfAbsConv_le.trans_lt hy₂).false

/-- If `f` is bounded, then the abscissa of absolute convergence of `f` is bounded above by `1`. -/
/-
**LSeries.abscissaOfAbsConv_le_of_le_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_le_of_le_const {f : Nat -> Complex} (h : exists 
C, forall n != 0, ‖f n‖ <= C) : abscissaOfAbsConv f <= 1
参数：h : exists C, forall n != 0, ‖f n‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow`：LSeries.abscissaOfAbs
Conv_le_of_le_const_mul_rpow {f : Nat -> Complex} {x : Real} (h : exists C, fora
ll n != 0, ‖f n‖ <= C * n ^ x) : abscis…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If `f` is bounded, then the abscissa of absolute convergence of `f` is bounded a
bove by `1`.
-/
lemma LSeries.abscissaOfAbsConv_le_of_le_const {f : ℕ → ℂ} (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C) :
    abscissaOfAbsConv f ≤ 1 := by
  simpa using abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) (by simpa using h)

open Filter in
/-- If `f` is `O(1)`, then the abscissa of absolute convergence of `f` is bounded above by `1`. -/
/-
**LSeries.abscissaOfAbsConv_le_one_of_isBigO_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_le_one_of_isBigO_one {f : Nat -> Complex} (h : f
 =O[atTop] fun _ => (1 : Real)) : abscissaOfAbsConv f <= 1
参数：h : f =O[atTop] fun _ => (1 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `LSeries.abscissaOfAbsConv_le_of_isBigO_rpow`：LSeries.abscissaOfAbsConv_l
e_of_isBigO_rpow {f : Nat -> Complex} {x : Real} (h : f =O[atTop] fun n => (n : 
Real) ^ x) : abscissaOfAbsConv f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α

--- 原说明 ---
If `f` is `O(1)`, then the abscissa of absolute convergence of `f` is bounded ab
ove by `1`.
-/
lemma LSeries.abscissaOfAbsConv_le_one_of_isBigO_one {f : ℕ → ℂ} (h : f =O[atTop] fun _ ↦ (1 : ℝ)) :
    abscissaOfAbsConv f ≤ 1 := by
  simpa using abscissaOfAbsConv_le_of_isBigO_rpow (x := 0) (by simpa using h)

/-- If `f` is real-valued and `x` is strictly greater than the abscissa of absolute convergence
of `f`, then the real series `∑' n, f n / n ^ x` converges. -/
/-
**LSeries.summable_real_of_abscissaOfAbsConv_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.summable_real_of_abscissaOfAbsConv_lt {f : Nat -> Real} {x : Real}
 (h : abscissaOfAbsConv (f ·) < x) : Summable fun n : Nat => f n / (n : Real) ^ 
x
参数：h : abscissaOfAbsConv (f ·) < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `Summable.congr_cofinite`：∀ {α : Type u_1} {β : Type u_2} [inst : AddComm
Group α] [inst_1 : TopologicalSpace α] [IsTopologicalAddGroup α]   {f g : β → α}
, Summable f …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
If `f` is real-valued and `x` is strictly greater than the abscissa of absolute 
convergence
of `f`, then the real series `∑' n, f n / n ^ x` converges.
-/
lemma LSeries.summable_real_of_abscissaOfAbsConv_lt {f : ℕ → ℝ} {x : ℝ}
    (h : abscissaOfAbsConv (f ·) < x) :
    Summable fun n : ℕ ↦ f n / (n : ℝ) ^ x := by
  have aux : term (f ·) x = fun n ↦ ↑(if n = 0 then 0 else f n / (n : ℝ) ^ x) := by
    ext n
    simp [term_def, apply_ite ((↑) : ℝ → ℂ), ofReal_cpow n.cast_nonneg]
  have := LSeriesSummable_of_abscissaOfAbsConv_lt_re (ofReal_re x ▸ h)
  simp only [LSeriesSummable, aux, summable_ofReal] at this
  refine this.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
    using if_neg (by simpa using hn)

/-- If `F` is a binary operation on `ℕ → ℂ` with the property that the `LSeries` of `F f g`
converges whenever the `LSeries` of `f` and `g` do, then the abscissa of absolute convergence
of `F f g` is at most the maximum of the abscissa of absolute convergence of `f`
and that of `g`. -/
/-
**LSeries.abscissaOfAbsConv_binop_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_binop_le {F : (Nat -> Complex) -> (Nat -> Comple
x) -> (Nat -> Complex)} (hF : forall {f g s}, LSeriesSummable f s -> LSeriesSumm
able g s -> LSeriesSummable (F f g) s) (f g : Nat -> Complex) : abscissaOfAbsCon
v (F f g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g)
参数：Nat -> Complex；Nat -> Complex；Nat -> Complex；hF : forall {f g s}, LSeriesSumm
able f s -> LSeriesSummable g s -> LSeriesSummable (F f g) s；f g : Nat -> Comple
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'`：LSeries.absc
issaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : Nat -> Complex} {x : EReal} 
(h : forall y : Real, x < y -> LSeriesSummable f…
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
If `F` is a binary operation on `ℕ → ℂ` with the property that the `LSeries` of 
`F f g`
converges whenever the `LSeries` of `f` and `g` do, then the abscissa of absolut
e convergence
of `F f g` is at most the maximum of the abscissa of absolute convergence of `f`
and that of `g`.
-/
lemma LSeries.abscissaOfAbsConv_binop_le {F : (ℕ → ℂ) → (ℕ → ℂ) → (ℕ → ℂ)}
    (hF : ∀ {f g s}, LSeriesSummable f s → LSeriesSummable g s → LSeriesSummable (F f g) s)
    (f g : ℕ → ℂ) :
    abscissaOfAbsConv (F f g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun x hx ↦ hF ?_ ?_
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ (le_max_left ..).trans_lt hx
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ (le_max_right ..).trans_lt hx
