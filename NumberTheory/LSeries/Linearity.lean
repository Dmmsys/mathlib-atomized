/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Linearity of the L-series of `f` as a function of `f`

We show that the `LSeries` of `f : ℕ → ℂ` is a linear function of `f` (assuming convergence
of both L-series when adding two functions).
-/

public section

/-!
### Addition
-/

open LSeries

/-
**LSeries.term_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_add (f g : Nat -> Complex) (s : Complex) : term (f + g) s = t
erm f s + term g s
参数：f g : Nat -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
-/
lemma LSeries.term_add (f g : ℕ → ℂ) (s : ℂ) : term (f + g) s = term f s + term g s := by
  ext ⟨- | n⟩ <;>
  simp [add_div]
/-
**LSeries.term_add_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_add_apply (f g : Nat -> Complex) (s : Complex) (n : Nat) : te
rm (f + g) s n = term f s n + term g s n
参数：f g : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.term_add`：LSeries.term_add (f g : Nat -> Complex) (s : Complex) 
: term (f + g) s = term f s + term g s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LSeries.term_add_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f + g) s n = term f s n + term g s n := by
  simp [term_add]
/-
**LSeriesHasSum.add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.add {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHa
sSum f s a) (hg : LSeriesHasSum g s b) : LSeriesHasSum (f + g) s (a + b)
参数：hf : LSeriesHasSum f s a；hg : LSeriesHasSum g s b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_add`：LSeries.term_add (f g : Nat -> Complex) (s : Complex) 
: term (f + g) s = term f s + term g s
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
-/
lemma LSeriesHasSum.add {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f + g) s (a + b) := by
  simpa [LSeriesHasSum, term_add] using! HasSum.add hf hg
/-
**LSeriesSummable.add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.add {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSumm
able f s) (hg : LSeriesSummable g s) : LSeriesSummable (f + g) s
参数：hf : LSeriesSummable f s；hg : LSeriesSummable g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Summable.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [Continuous
Ad…
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
-/
lemma LSeriesSummable.add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f + g) s := by
  simpa [LSeriesSummable, ← term_add_apply] using Summable.add hf hg

@[simp]
/-
**LSeries_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_add {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s
) (hg : LSeriesSummable g s) : LSeries (f + g) s = LSeries f s + LSeries g s
参数：hf : LSeriesSummable f s；hg : LSeriesSummable g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.term_add`：LSeries.term_add (f g : Nat -> Complex) (s : Complex) 
: term (f + g) s = term f s + term g s
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `Complex.instT2Space`：T2Space ℂ
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
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma LSeries_add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f + g) s = LSeries f s + LSeries g s := by
  simpa [LSeries, term_add] using hf.tsum_add hg

/-!
### Negation
-/

/-
**LSeries.term_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_neg (f : Nat -> Complex) (s : Complex) : term (-f) s = -term 
f s
参数：f : Nat -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)

--- 原说明 ---
### Negation
-/
lemma LSeries.term_neg (f : ℕ → ℂ) (s : ℂ) : term (-f) s = -term f s := by
  ext ⟨- | n⟩ <;>
  simp [neg_div]
/-
**LSeries.term_neg_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_neg_apply (f : Nat -> Complex) (s : Complex) (n : Nat) : term
 (-f) s n = -term f s n
参数：f : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.term_neg`：LSeries.term_neg (f : Nat -> Complex) (s : Complex) : 
term (-f) s = -term f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LSeries.term_neg_apply (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : term (-f) s n = -term f s n := by
  simp [term_neg]
/-
**LSeriesHasSum.neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.neg {f : Nat -> Complex} {s a : Complex} (hf : LSeriesHasSum
 f s a) : LSeriesHasSum (-f) s (-a)
参数：hf : LSeriesHasSum f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_neg`：LSeries.term_neg (f : Nat -> Complex) (s : Complex) : 
term (-f) s = -term f s
· 使用定理 `HasSum.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [ins
t : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f
…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma LSeriesHasSum.neg {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa [LSeriesHasSum, term_neg] using! HasSum.neg hf
/-
**LSeriesSummable.neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.neg {f : Nat -> Complex} {s : Complex} (hf : LSeriesSummab
le f s) : LSeriesSummable (-f) s
参数：hf : LSeriesSummable f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_neg`：LSeries.term_neg (f : Nat -> Complex) (s : Complex) : 
term (-f) s = -term f s
· 使用定理 `Summable.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [i
nst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] 
{f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma LSeriesSummable.neg {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (-f) s := by
  simpa [LSeriesSummable, term_neg] using! Summable.neg hf

@[simp]
/-
**LSeriesSummable.neg_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.neg_iff {f : Nat -> Complex} {s : Complex} : LSeriesSummab
le (-f) s ↔ LSeriesSummable f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.neg`：LSeriesSummable.neg {f : Nat -> Complex} {s : Compl
ex} (hf : LSeriesSummable f s) : LSeriesSummable (-f) s
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma LSeriesSummable.neg_iff {f : ℕ → ℂ} {s : ℂ} :
    LSeriesSummable (-f) s ↔ LSeriesSummable f s :=
  ⟨fun H ↦ neg_neg f ▸ H.neg, .neg⟩

@[simp]
/-
**LSeries_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_neg (f : Nat -> Complex) (s : Complex) : LSeries (-f) s = -LSeries
 f s
参数：f : Nat -> Complex；s : Complex。
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
· 使用引理 `LSeries.term_neg_apply`：LSeries.term_neg_apply (f : Nat -> Complex) (s :
 Complex) (n : Nat) : term (-f) s n = -term f s n
· 使用定理 `tsum_neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [inst 
: AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LSeries_neg (f : ℕ → ℂ) (s : ℂ) : LSeries (-f) s = -LSeries f s := by
  simp [LSeries, term_neg_apply, tsum_neg]

/-!
### Subtraction
-/

/-
**LSeries.term_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_sub (f g : Nat -> Complex) (s : Complex) : term (f - g) s = t
erm f s - term g s
参数：f g : Nat -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `LSeries.term_add`：LSeries.term_add (f g : Nat -> Complex) (s : Complex) 
: term (f + g) s = term f s + term g s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LSeries.term_neg`：LSeries.term_neg (f : Nat -> Complex) (s : Complex) : 
term (-f) s = -term f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Subtraction
-/
lemma LSeries.term_sub (f g : ℕ → ℂ) (s : ℂ) : term (f - g) s = term f s - term g s := by
  simp_rw [sub_eq_add_neg, term_add, term_neg]
/-
**LSeries.term_sub_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_sub_apply (f g : Nat -> Complex) (s : Complex) (n : Nat) : te
rm (f - g) s n = term f s n - term g s n
参数：f g : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_sub`：LSeries.term_sub (f g : Nat -> Complex) (s : Complex) 
: term (f - g) s = term f s - term g s
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
-/
lemma LSeries.term_sub_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f - g) s n = term f s n - term g s n := by
  rw [term_sub, Pi.sub_apply]
/-
**LSeriesHasSum.sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.sub {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHa
sSum f s a) (hg : LSeriesHasSum g s b) : LSeriesHasSum (f - g) s (a - b)
参数：hf : LSeriesHasSum f s a；hg : LSeriesHasSum g s b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_sub`：LSeries.term_sub (f g : Nat -> Complex) (s : Complex) 
: term (f - g) s = term f s - term g s
· 使用定理 `HasSum.sub`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [ins
t : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f
…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma LSeriesHasSum.sub {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f - g) s (a - b) := by
  simpa [LSeriesHasSum, term_sub] using! HasSum.sub hf hg
/-
**LSeriesSummable.sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.sub {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSumm
able f s) (hg : LSeriesSummable g s) : LSeriesSummable (f - g) s
参数：hf : LSeriesSummable f s；hg : LSeriesSummable g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Summable.sub`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [i
nst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] 
{f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma LSeriesSummable.sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f - g) s := by
  simpa [LSeriesSummable, ← term_sub_apply] using Summable.sub hf hg

@[simp]
/-
**LSeries_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_sub {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s
) (hg : LSeriesSummable g s) : LSeries (f - g) s = LSeries f s - LSeries g s
参数：hf : LSeriesSummable f s；hg : LSeriesSummable g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.term_sub`：LSeries.term_sub (f g : Nat -> Complex) (s : Complex) 
: term (f - g) s = term f s - term g s
· 使用定理 `Summable.tsum_sub`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter 
β} [inst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGrou
p α] {f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma LSeries_sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f - g) s = LSeries f s - LSeries g s := by
  simpa [LSeries, term_sub] using hf.tsum_sub hg

/-!
### Scalar multiplication
-/

/-
**LSeries.term_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_smul (f : Nat -> Complex) (c s : Complex) : term (c • f) s = 
c • term f s
参数：f : Nat -> Complex；c s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)

--- 原说明 ---
### Scalar multiplication
-/
lemma LSeries.term_smul (f : ℕ → ℂ) (c s : ℂ) : term (c • f) s = c • term f s := by
  ext ⟨- | n⟩ <;>
  simp [mul_div_assoc]
/-
**LSeries.term_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_smul_apply (f : Nat -> Complex) (c s : Complex) (n : Nat) : t
erm (c • f) s n = c * term f s n
参数：f : Nat -> Complex；c s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.term_smul`：LSeries.term_smul (f : Nat -> Complex) (c s : Complex
) : term (c • f) s = c • term f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LSeries.term_smul_apply (f : ℕ → ℂ) (c s : ℂ) (n : ℕ) :
    term (c • f) s n = c * term f s n := by
  simp [term_smul]
/-
**LSeriesHasSum.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.smul {f : Nat -> Complex} (c : Complex) {s a : Complex} (hf 
: LSeriesHasSum f s a) : LSeriesHasSum (c • f) s (c * a)
参数：c : Complex；hf : LSeriesHasSum f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_smul`：LSeries.term_smul (f : Nat -> Complex) (c s : Complex
) : term (c • f) s = c • term f s
· 使用定理 `HasSum.const_smul`：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L)
 : HasSum (fun i => b • f i) (b • a) L
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
-/
lemma LSeriesHasSum.smul {f : ℕ → ℂ} (c : ℂ) {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (c • f) s (c * a) := by
  simpa [LSeriesHasSum, term_smul] using! hf.const_smul c
/-
**LSeriesSummable.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.smul {f : Nat -> Complex} (c : Complex) {s : Complex} (hf 
: LSeriesSummable f s) : LSeriesSummable (c • f) s
参数：c : Complex；hf : LSeriesSummable f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_smul`：LSeries.term_smul (f : Nat -> Complex) (c s : Complex
) : term (c • f) s = c • term f s
· 使用定理 `Summable.const_smul`：Summable.const_smul (b : γ) (hf : Summable f L) : S
ummable (fun i => b • f i) L
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
-/
lemma LSeriesSummable.smul {f : ℕ → ℂ} (c : ℂ) {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (c • f) s := by
  simpa [LSeriesSummable, term_smul] using! hf.const_smul c
/-
**LSeriesSummable.of_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.of_smul {f : Nat -> Complex} {c s : Complex} (hc : c != 0)
 (hf : LSeriesSummable (c • f) s) : LSeriesSummable f s
参数：hc : c != 0；hf : LSeriesSummable (c • f) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `LSeriesSummable.smul`：LSeriesSummable.smul {f : Nat -> Complex} (c : Com
plex) {s : Complex} (hf : LSeriesSummable f s) : LSeriesSummable (c • f) s
-/
lemma LSeriesSummable.of_smul {f : ℕ → ℂ} {c s : ℂ} (hc : c ≠ 0) (hf : LSeriesSummable (c • f) s) :
    LSeriesSummable f s := by
  simpa [hc] using hf.smul (c⁻¹)
/-
**LSeriesSummable.smul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.smul_iff {f : Nat -> Complex} {c s : Complex} (hc : c != 0
) : LSeriesSummable (c • f) s ↔ LSeriesSummable f s
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.of_smul`：LSeriesSummable.of_smul {f : Nat -> Complex} {c
 s : Complex} (hc : c != 0) (hf : LSeriesSummable (c • f) s) : LSeriesSummable f
 s
· 使用引理 `LSeriesSummable.smul`：LSeriesSummable.smul {f : Nat -> Complex} (c : Com
plex) {s : Complex} (hf : LSeriesSummable f s) : LSeriesSummable (c • f) s
-/
lemma LSeriesSummable.smul_iff {f : ℕ → ℂ} {c s : ℂ} (hc : c ≠ 0) :
    LSeriesSummable (c • f) s ↔ LSeriesSummable f s :=
  ⟨of_smul hc, smul c⟩

@[simp]
/-
**LSeries_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_smul (f : Nat -> Complex) (c s : Complex) : LSeries (c • f) s = c 
* LSeries f s
参数：f : Nat -> Complex；c s : Complex。
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
· 使用引理 `LSeries.term_smul_apply`：LSeries.term_smul_apply (f : Nat -> Complex) (c
 s : Complex) (n : Nat) : term (c • f) s n = c * term f s n
· 使用定理 `tsum_mul_left`：tsum_mul_left [T2Space α] : ∑'[L] x, a * f x = a * ∑'[L] 
x, f x
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LSeries_smul (f : ℕ → ℂ) (c s : ℂ) : LSeries (c • f) s = c * LSeries f s := by
  simp [LSeries, term_smul_apply, tsum_mul_left]

/-!
### Sums
-/

section sum

variable {ι : Type*} (f : ι → ℕ → ℂ) (S : Finset ι) (s : ℂ)

@[simp]
/-
**LSeries.term_sum_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_sum_apply (n : Nat) : term (∑ i in S, f i) s n = ∑ i in S, te
rm (f i) s n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma LSeries.term_sum_apply (n : ℕ) :
    term (∑ i ∈ S, f i) s n = ∑ i ∈ S, term (f i) s n := by
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, Finset.sum_div]
/-
**LSeries.term_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.term_sum : term (∑ i in S, f i) s = ∑ i in S, term (f i) s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_sum_apply`：LSeries.term_sum_apply (n : Nat) : term (∑ i in 
S, f i) s n = ∑ i in S, term (f i) s n
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LSeries.term_sum : term (∑ i ∈ S, f i) s = ∑ i ∈ S, term (f i) s :=
  funext fun _ ↦ by simp

variable {f S s}
/-
**LSeriesHasSum.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.sum {a : ι -> Complex} (hf : forall i in S, LSeriesHasSum (f
 i) s (a i)) : LSeriesHasSum (∑ i in S, f i) s (∑ i in S, a i)
参数：hf : forall i in S, LSeriesHasSum (f i) s (a i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LSeries.term_sum`：LSeries.term_sum : term (∑ i in S, f i) s = ∑ i in S, 
term (f i) s
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
· 使用定理 `hasSum_sum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β} [ContinuousA
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
-/
lemma LSeriesHasSum.sum {a : ι → ℂ} (hf : ∀ i ∈ S, LSeriesHasSum (f i) s (a i)) :
    LSeriesHasSum (∑ i ∈ S, f i) s (∑ i ∈ S, a i) := by
  simpa [LSeriesHasSum, term_sum, Finset.sum_fn S fun i ↦ term (f i) s] using hasSum_sum hf
/-
**LSeriesSummable.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.sum (hf : forall i in S, LSeriesSummable (f i) s) : LSerie
sSummable (∑ i in S, f i) s
参数：hf : forall i in S, LSeriesSummable (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `summable_sum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Add
CommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β} [Continuou
sA…
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
-/
lemma LSeriesSummable.sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeriesSummable (∑ i ∈ S, f i) s := by
  simpa [LSeriesSummable, ← term_sum_apply] using summable_sum hf

@[simp]
/-
**LSeries_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_sum (hf : forall i in S, LSeriesSummable (f i) s) : LSeries (∑ i i
n S, f i) s = ∑ i in S, LSeries (f i) s
参数：hf : forall i in S, LSeriesSummable (f i) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LSeries.term_sum_apply`：LSeries.term_sum_apply (n : Nat) : term (∑ i in 
S, f i) s n = ∑ i in S, term (f i) s n
· 使用定理 `Summable.tsum_finsetSum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β}
 [T2Space α] …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
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
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma LSeries_sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeries (∑ i ∈ S, f i) s = ∑ i ∈ S, LSeries (f i) s := by
  simpa [LSeries, term_sum] using Summable.tsum_finsetSum hf

end sum

