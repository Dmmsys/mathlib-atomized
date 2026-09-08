/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The Height of an Ideal

In this file, we define the height of a prime ideal and the height of an ideal.

## Main definitions

* `Ideal.height` : The height of an ideal. We defined it as the infimum of the `primeHeight` of the
  minimal prime ideals of I.

-/

public section

variable {R : Type*} [CommRing R] (I : Ideal R)

open Ideal

/-- The height of a prime ideal is defined as the supremum of the lengths of strictly decreasing
chains of prime ideals below it. -/
/-
**Ideal.primeHeight** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The height of a prime ideal is defined as the supremum of the lengths of strictl
y decreasing
chains of prime ideals below it.
-/
private noncomputable def Ideal.primeHeight [hI : I.IsPrime] : ℕ∞ :=
  Order.height (⟨I, hI⟩ : PrimeSpectrum R)

/-- The height of an ideal is defined as the infimum of the heights of its minimal prime ideals. -/
/-
**Ideal.height** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.height : Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The height of an ideal is defined as the infimum of the heights of its minimal p
rime ideals.
-/
noncomputable def Ideal.height : ℕ∞ :=
  ⨅ J ∈ I.minimalPrimes, @Ideal.primeHeight _ _ J ‹J ∈ I.minimalPrimes›.isPrime

set_option backward.isDefEq.respectTransparency.types false in
/-- For a prime ideal, its height equals its prime height. -/
/-
**Ideal.height_eq_primeHeight** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a prime ideal, its height equals its prime height.
-/
private lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
  simp [height, primeHeight, Ideal.minimalPrimes_eq_subsingleton_self]
/-
**PrimeSpectrum.height_eq_orderHeight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.height_eq_orderHeight (p : PrimeSpectrum R) : p.asIdeal.heig
ht = Order.height p
参数：p : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
lemma PrimeSpectrum.height_eq_orderHeight (p : PrimeSpectrum R) :
    p.asIdeal.height = Order.height p :=
  p.asIdeal.height_eq_primeHeight
/-
**Ideal.height_eq_inf_minimalPrimes** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_eq_inf_minimalPrimes : I.height = ⨅ J in I.minimalPrimes, J.h
eight
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
-/
lemma Ideal.height_eq_inf_minimalPrimes : I.height = ⨅ J ∈ I.minimalPrimes, J.height := by
  apply iInf_congr (fun p ↦ iInf_congr fun hp ↦ ?_)
  have := hp.isPrime
  exact (Ideal.height_eq_primeHeight _).symm
/-
**Ideal.exists_isPrime_height_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_isPrime_height_eq {I : Ideal R} {n : Nat} (hI : I.height = n)
 : exists (p : Ideal R) (_ : p.IsPrime) (_ : I <= p), p.height = n
参数：hI : I.height = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
-/
lemma Ideal.exists_isPrime_height_eq {I : Ideal R} {n : ℕ} (hI : I.height = n) :
    ∃ (p : Ideal R) (_ : p.IsPrime) (_  : I ≤ p), p.height = n := by
  simp only [Ideal.height, ENat.iInf_eq_natCast_iff] at hI
  rcases hI with ⟨⟨p, ⟨⟨⟨hpp, hIp⟩, _⟩, h⟩, -⟩, -⟩
  exact ⟨p, hpp, hIp, h ▸ p.height_eq_primeHeight⟩

/-- An ideal has finite height if it is either the unit ideal or its height is finite.
We include the unit ideal in order to have the instance `IsNoetherianRing R → FiniteHeight I`. -/
@[mk_iff]
/-
**Ideal.FiniteHeight** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → Ideal R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal has finite height if it is either the unit ideal or its height is finit
e.
We include the unit ideal in order to have the instance `IsNoetherianRing R → Fi
niteHeight I`.
-/
class Ideal.FiniteHeight : Prop where
  eq_top_or_height_ne_top : I = ⊤ ∨ I.height ≠ ⊤
/-
**Ideal.finiteHeight_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.finiteHeight_iff_lt {I : Ideal R} : Ideal.FiniteHeight I ↔ I = ⊤ ∨ I
.height < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.finiteHeight_iff`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal 
R), I.FiniteHeight ↔ I = ⊤ ∨ I.height ≠ ⊤
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ideal.finiteHeight_iff_lt {I : Ideal R} :
    Ideal.FiniteHeight I ↔ I = ⊤ ∨ I.height < ⊤ := by
  rw [Ideal.finiteHeight_iff, lt_top_iff_ne_top]
/-
**Ideal.height_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_ne_top {I : Ideal R} (hI : I != ⊤) [I.FiniteHeight] : I.heigh
t != ⊤
参数：hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.FiniteHeight.eq_top_or_height_ne_top`：∀ {R : Type u_1} {inst : Com
mRing R} {I : Ideal R} [self : I.FiniteHeight], I = ⊤ ∨ I.height ≠ ⊤
-/
lemma Ideal.height_ne_top {I : Ideal R} (hI : I ≠ ⊤) [I.FiniteHeight] :
    I.height ≠ ⊤ :=
  (‹I.FiniteHeight›.eq_top_or_height_ne_top).resolve_left hI
/-
**Ideal.height_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_lt_top {I : Ideal R} (hI : I != ⊤) [I.FiniteHeight] : I.heigh
t < ⊤
参数：hI : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用引理 `Ideal.height_ne_top`：Ideal.height_ne_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height != ⊤
-/
lemma Ideal.height_lt_top {I : Ideal R} (hI : I ≠ ⊤) [I.FiniteHeight] :
    I.height < ⊤ :=
  (Ideal.height_ne_top hI).lt_top
/-
**Ideal.height_ne_top_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_ne_top_of_isPrime {I : Ideal R} [I.FiniteHeight] [I.IsPrime] 
: I.height != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.height_ne_top`：Ideal.height_ne_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height != ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
lemma Ideal.height_ne_top_of_isPrime {I : Ideal R} [I.FiniteHeight] [I.IsPrime] :
    I.height ≠ ⊤ :=
  Ideal.height_ne_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_ne_top_of_isPrime` instead." (since := "2026-04-04")]
/-
**Ideal.primeHeight_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.primeHeight_ne_top (I : Ideal R) [I.FiniteHeight] [I.IsPrime] :
    I.primeHeight ≠ ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top ‹I.IsPrime›.ne_top
/-
**Ideal.height_lt_top_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_lt_top_of_isPrime {I : Ideal R} [I.FiniteHeight] [I.IsPrime] 
: I.height < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.height_lt_top`：Ideal.height_lt_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height < ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
lemma Ideal.height_lt_top_of_isPrime {I : Ideal R} [I.FiniteHeight] [I.IsPrime] :
    I.height < ⊤ :=
  Ideal.height_lt_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_lt_top_of_isPrime` instead." (since := "2026-04-04")]
/-
**Ideal.primeHeight_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.primeHeight_lt_top (I : Ideal R) [I.FiniteHeight] [I.IsPrime] :
    I.primeHeight < ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top ‹I.IsPrime›.ne_top
/-
**Ideal.exists_ltSeries_length_eq_height** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_ltSeries_length_eq_height (p : Ideal R) [p.IsPrime] [p.Finite
Height] : exists (l : LTSeries (PrimeSpectrum R)), RelSeries.last l = ⟨p, inferI
nstance⟩ ∧ l.length = p.height
参数：p : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.ne_top_iff_exists`：ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m 
= n
· 使用引理 `Ideal.height_ne_top`：Ideal.height_ne_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height != ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.primeHeight.eq_1`：∀ {R 
: Type u_1} [inst : CommRing R] (I : Ideal R) [hI : I.IsPrime],   Ideal.primeHei
ght✝ I = Order.height { asIdeal := I, isPrime := hI }
· 使用引理 `Order.exists_series_of_height_eq_coe`：exists_series_of_height_eq_coe (a 
: α) {n : Nat} (h : height a = n) : exists p : LTSeries α, p.last = a ∧ p.length
 = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Ideal.exists_ltSeries_length_eq_height (p : Ideal R) [p.IsPrime] [p.FiniteHeight] :
    ∃ (l : LTSeries (PrimeSpectrum R)),
      RelSeries.last l = ⟨p, inferInstance⟩ ∧ l.length = p.height := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (p.height_ne_top (IsPrime.ne_top ‹_›))
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight] at hn ⊢
  obtain ⟨l, last, len⟩ := Order.exists_series_of_height_eq_coe (⟨p, ‹_›⟩ : PrimeSpectrum R) hn.symm
  exact ⟨l, last, len ▸ hn⟩
/-
**Ideal.height_mono_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.height_mono_of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I ≤ J) :
    I.height ≤ J.height := by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  gcongr
  exact h

@[deprecated "Use `Ideal.height_mono_of_isPrime` instead." (since := "2026-04-04")]
/-
**Ideal.primeHeight_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.primeHeight_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I ≤ J) :
    I.primeHeight ≤ J.primeHeight := by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_mono_of_isPrime h
/-
**Ideal.height_add_one_le_of_lt_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_add_one_le_of_lt_of_isPrime {I J : Ideal R} [I.IsPrime] [J.Is
Prime] (h : I < J) : I.height + 1 <= J.height
参数：h : I < J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用引理 `Order.height_add_one_le`：height_add_one_le {a b : α} (hab : a < b) : hei
ght a + 1 <= height b
-/
lemma Ideal.height_add_one_le_of_lt_of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) :
    I.height + 1 ≤ J.height := by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  exact Order.height_add_one_le h

@[deprecated "Use `Ideal.height_add_one_le_of_lt_of_isPrime` instead." (since := "2026-04-04")]
/-
**Ideal.primeHeight_add_one_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.primeHeight_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] [J.IsPrime]
    (h : I < J) : I.primeHeight + 1 ≤ J.primeHeight := by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_add_one_le_of_lt_of_isPrime h

@[simp]
/-
**Ideal.height_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.height_top : (⊤ : Ideal R).height = ⊤
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ideal.minimalPrimes_top`：Ideal.minimalPrimes_top : (⊤ : Ideal R).minimal
Primes = ∅
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ideal.height_top : (⊤ : Ideal R).height = ⊤ := by
  simp [height, minimalPrimes_top]

@[gcongr]
/-
**Ideal.height_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.height <= J.height
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.height_eq_inf_minimalPrimes`：Ideal.height_eq_inf_minimalPrimes : I
.height = ⨅ J in I.minimalPrimes, J.height
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_mono_of_isPrime`
：∀ {R : Type u_1} [inst : CommRing R] {I J : Ideal R} [I.IsPrime] [J.IsPrime], I
 ≤ J → I.height ≤ J.height
-/
theorem Ideal.height_mono {I J : Ideal R} (h : I ≤ J) : I.height ≤ J.height := by
  simp only [I.height_eq_inf_minimalPrimes, J.height_eq_inf_minimalPrimes]
  refine le_iInf₂ (fun p hp ↦ ?_)
  have := hp.isPrime
  obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp.le)
  have := hq.isPrime
  exact (iInf₂_le q hq).trans (Ideal.height_mono_of_isPrime e)

@[gcongr]
/-
**Ideal.height_strict_mono_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_strict_mono_of_isPrime {I J : Ideal R} [I.IsPrime] (h : I < J
) [I.FiniteHeight] : I.height < J.height
参数：h : I < J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.height_top`：Ideal.height_top : (⊤ : Ideal R).height = ⊤
· 使用引理 `Ideal.height_lt_top`：Ideal.height_lt_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height < ⊤
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用引理 `Ideal.height_ne_top`：Ideal.height_ne_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height != ⊤
· 使用引理 `Ideal.height_eq_inf_minimalPrimes`：Ideal.height_eq_inf_minimalPrimes : I
.height = ⨅ J in I.minimalPrimes, J.height
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用引理 `Ideal.height_add_one_le_of_lt_of_isPrime`：Ideal.height_add_one_le_of_lt_
of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) : I.height + 1 <=
 J.height
-/
lemma Ideal.height_strict_mono_of_isPrime {I J : Ideal R} [I.IsPrime]
    (h : I < J) [I.FiniteHeight] : I.height < J.height := by
  by_cases hJ : J = ⊤
  · grw [hJ, height_top]
    exact I.height_lt_top IsPrime.ne_top'
  · rw [← ENat.add_one_le_iff (I.height_ne_top IsPrime.ne_top'), J.height_eq_inf_minimalPrimes]
    refine le_iInf₂ (fun K hK ↦ ?_)
    have := hK.isPrime
    have : I < K := lt_of_lt_of_le h hK.le
    exact Ideal.height_add_one_le_of_lt_of_isPrime this
/-
**Ideal.height_strict_mono_of_isPrime_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_strict_mono_of_isPrime_of_isPrime {I J : Ideal R} [I.IsPrime]
 [J.IsPrime] (h : I < J) [J.FiniteHeight] : I.height < J.height
参数：h : I < J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.finiteHeight_iff`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal 
R), I.FiniteHeight ↔ I = ⊤ ∨ I.height ≠ ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Ideal.height_lt_top`：Ideal.height_lt_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height < ⊤
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用引理 `Ideal.height_strict_mono_of_isPrime`：Ideal.height_strict_mono_of_isPrime
 {I J : Ideal R} [I.IsPrime] (h : I < J) [I.FiniteHeight] : I.height < J.height
-/
lemma Ideal.height_strict_mono_of_isPrime_of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime]
    (h : I < J) [J.FiniteHeight] : I.height < J.height := by
  have : I.FiniteHeight := I.finiteHeight_iff.mpr
    (Or.inr (lt_of_le_of_lt (Ideal.height_mono h.le) (J.height_lt_top IsPrime.ne_top')).ne)
  exact Ideal.height_strict_mono_of_isPrime h

@[deprecated (since := "2026-04-02")]
alias Ideal.height_strict_mono_of_isPrime_of_is_prime :=
  Ideal.height_strict_mono_of_isPrime_of_isPrime

@[deprecated "Use `Ideal.height_strict_mono_of_isPrime_of_isPrime` instead."
  (since := "2026-04-02")]
/-
**Ideal.primeHeight_strict_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.primeHeight_strict_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J)
    [J.FiniteHeight] : I.primeHeight < J.primeHeight := by
  simpa [← Ideal.height_eq_primeHeight] using Ideal.height_strict_mono_of_isPrime_of_isPrime h
/-
**Ideal.height_le_ringKrullDim_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_le_ringKrullDim_of_isPrime {I : Ideal R} [I.IsPrime] : I.heig
ht <= ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.primeHeight.eq_1`：∀ {R 
: Type u_1} [inst : CommRing R] (I : Ideal R) [hI : I.IsPrime],   Ideal.primeHei
ght✝ I = Order.height { asIdeal := I, isPrime := hI }
· 使用引理 `Order.height_le_krullDim`：height_le_krullDim (a : α) : height a <= krull
Dim α
-/
lemma Ideal.height_le_ringKrullDim_of_isPrime {I : Ideal R} [I.IsPrime] :
    I.height ≤ ringKrullDim R := by
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  exact Order.height_le_krullDim _

/-- A prime ideal of finite height is equal to any ideal that contains it with no greater height. -/
/-
**Ideal.eq_of_le_of_height_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.eq_of_le_of_height_le [I.IsPrime] [I.FiniteHeight] {J : Ideal R} (h 
: I <= J) (h_height : J.height <= I.height) : I = J
参数：h : I <= J；h_height : J.height <= I.height。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `Ideal.height_strict_mono_of_isPrime`：Ideal.height_strict_mono_of_isPrime
 {I J : Ideal R} [I.IsPrime] (h : I < J) [I.FiniteHeight] : I.height < J.height

--- 原说明 ---
A prime ideal of finite height is equal to any ideal that contains it with no gr
eater height.
-/
lemma Ideal.eq_of_le_of_height_le [I.IsPrime] [I.FiniteHeight]
    {J : Ideal R} (h : I ≤ J) (h_height : J.height ≤ I.height) : I = J :=
  eq_of_le_of_not_lt h fun hlt => not_le.mpr (Ideal.height_strict_mono_of_isPrime hlt) h_height

@[deprecated "Use `Ideal.height_le_ringKrullDim_of_isPrime` instead." (since := "2026-04-04")]
/-
**Ideal.primeHeight_le_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.primeHeight_le_ringKrullDim {I : Ideal R} [I.IsPrime] :
    I.primeHeight ≤ ringKrullDim R := Order.height_le_krullDim _
/-
**Ideal.height_le_ringKrullDim_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_le_ringKrullDim_of_ne_top {I : Ideal R} (h : I != ⊤) : I.heig
ht <= ringKrullDim R
参数：h : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.nonempty_minimalPrimes`：Ideal.nonempty_minimalPrimes (h : I != ⊤) 
: Nonempty I.minimalPrimes
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.height_eq_inf_minimalPrimes`：Ideal.height_eq_inf_minimalPrimes : I
.height = ⨅ J in I.minimalPrimes, J.height
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用引理 `Ideal.height_le_ringKrullDim_of_isPrime`：Ideal.height_le_ringKrullDim_of
_isPrime {I : Ideal R} [I.IsPrime] : I.height <= ringKrullDim R
-/
lemma Ideal.height_le_ringKrullDim_of_ne_top {I : Ideal R} (h : I ≠ ⊤) :
    I.height ≤ ringKrullDim R := by
  obtain ⟨P, hP⟩ : Nonempty (I.minimalPrimes) := Ideal.nonempty_minimalPrimes h
  rw [I.height_eq_inf_minimalPrimes]
  have := hP.isPrime
  refine (WithBot.coe_le_coe.mpr (iInf₂_le _ hP)).trans P.height_le_ringKrullDim_of_isPrime

/-- If `R` has finite Krull dimension, there exists a maximal ideal `m` with `ht m = dim R`. -/
/-
**Ideal.exists_isMaximal_height** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_isMaximal_height [FiniteRingKrullDim R] : exists (p : Ideal R
), p.IsMaximal ∧ p.height = ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Ideal.height_le_ringKrullDim_of_ne_top`：Ideal.height_le_ringKrullDim_of_
ne_top {I : Ideal R} (h : I != ⊤) : I.height <= ringKrullDim R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LTSeries.height_last_longestOf`：∀ {α : Type u_1} [inst : Preorder α] [in
st_1 : FiniteDimensionalOrder α],   ↑(Order.height (RelSeries.last (LTSeries.lon
gestOf α))) = Order.…
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height

--- 原说明 ---
If `R` has finite Krull dimension, there exists a maximal ideal `m` with `ht m =
 dim R`.
-/
lemma Ideal.exists_isMaximal_height [FiniteRingKrullDim R] :
    ∃ (p : Ideal R), p.IsMaximal ∧ p.height = ringKrullDim R := by
  let l := LTSeries.longestOf (PrimeSpectrum R)
  obtain ⟨m, hm, hle⟩ := l.last.asIdeal.exists_le_maximal IsPrime.ne_top'
  refine ⟨m, hm, le_antisymm (height_le_ringKrullDim_of_ne_top IsPrime.ne_top') ?_⟩
  trans (l.last.asIdeal.height : WithBot ℕ∞)
  · rw [Ideal.height_eq_primeHeight]
    exact LTSeries.height_last_longestOf.symm.le
  · norm_cast
    exact height_mono hle
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) Ideal.finiteHeight_of_finiteRingKrullDim {I : Ideal R}
    [FiniteRingKrullDim R] : I.FiniteHeight := by
  rw [finiteHeight_iff, or_iff_not_imp_left, ← lt_top_iff_ne_top, ← WithBot.coe_lt_coe]
  exact fun h ↦ lt_of_le_of_lt (Ideal.height_le_ringKrullDim_of_ne_top h) ringKrullDim_lt_top

/-- If J has finite height and I ≤ J, then I has finite height -/
/-
**Ideal.finiteHeight_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.finiteHeight_of_le {I J : Ideal R} (e : I <= J) (hJ : J != ⊤) [Finit
eHeight J] : FiniteHeight I where eq_top_or_height_ne_top
参数：e : I <= J；hJ : J != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height
· 使用引理 `Ideal.height_lt_top`：Ideal.height_lt_top {I : Ideal R} (hI : I != ⊤) [I.
FiniteHeight] : I.height < ⊤

--- 原说明 ---
If J has finite height and I ≤ J, then I has finite height
-/
lemma Ideal.finiteHeight_of_le {I J : Ideal R} (e : I ≤ J) (hJ : J ≠ ⊤) [FiniteHeight J] :
    FiniteHeight I where
  eq_top_or_height_ne_top := Or.inr <|
    lt_top_iff_ne_top.mp ((height_mono e).trans_lt (height_lt_top hJ))

/-- If J is a prime ideal containing I, and its height is less than or equal to the height of I,
then J is a minimal prime over I -/
/-
**Ideal.mem_minimalPrimes_of_height_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.mem_minimalPrimes_of_height_le {I J : Ideal R} (e : I <= J) [J.IsPri
me] [FiniteHeight J] (e' : J.height <= I.height) : J in I.minimalPrimes
参数：e : I <= J；e' : J.height <= I.height。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用引理 `Ideal.finiteHeight_of_le`：Ideal.finiteHeight_of_le {I J : Ideal R} (e : 
I <= J) (hJ : J != ⊤) [FiniteHeight J] : FiniteHeight I where eq_top_or_height_n
e_top
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Ideal.height_strict_mono_of_isPrime`：Ideal.height_strict_mono_of_isPrime
 {I J : Ideal R} [I.IsPrime] (h : I < J) [I.FiniteHeight] : I.height < J.height
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p

--- 原说明 ---
If J is a prime ideal containing I, and its height is less than or equal to the 
height of I,
then J is a minimal prime over I
-/
lemma Ideal.mem_minimalPrimes_of_height_le {I J : Ideal R} (e : I ≤ J) [J.IsPrime]
    [FiniteHeight J] (e' : J.height ≤ I.height) : J ∈ I.minimalPrimes := by
  obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
  convert! h₁
  refine (eq_of_le_of_not_lt h₂ fun h₃ ↦ ?_).symm
  have := h₁.isPrime
  have := finiteHeight_of_le h₂ IsPrime.ne_top'
  exact lt_irrefl _ ((height_strict_mono_of_isPrime h₃).trans_le
    (e'.trans <| height_mono h₁.le))

@[deprecated (since := "2026-07-28")]
alias Ideal.mem_minimalPrimes_of_height_eq := Ideal.mem_minimalPrimes_of_height_le

/-- A prime ideal has height zero if and only if it is minimal -/
/-
**Ideal.height_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_eq_zero_iff {I : Ideal R} [I.IsPrime] : height I = 0 ↔ I in m
inimalPrimes R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.primeHeight.eq_1`：∀ {R 
: Type u_1} [inst : CommRing R] (I : Ideal R) [hI : I.IsPrime],   Ideal.primeHei
ght✝ I = Order.height { asIdeal := I, isPrime := hI }
· 使用定理 `Order.height_eq_zero`：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Orde
r.height x = 0 ↔ IsMin x
· 使用引理 `minimalPrimes_eq_minimals`：minimalPrimes_eq_minimals : minimalPrimes R =
 {x | Minimal Ideal.IsPrime x}
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
A prime ideal has height zero if and only if it is minimal
-/
lemma Ideal.height_eq_zero_iff {I : Ideal R} [I.IsPrime] : height I = 0 ↔ I ∈ minimalPrimes R := by
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_eq_zero,
    minimalPrimes_eq_minimals]
  refine ⟨fun h ↦ ⟨‹_›, ?_⟩, fun ⟨hI, hI'⟩ b hb ↦ hI' b.isPrime hb⟩
  by_contra! ⟨P, ⟨hP₁, ⟨hP₂, hP₃⟩⟩⟩
  exact hP₃ (h (b := ⟨P, hP₁⟩) hP₂)

@[deprecated "Use `Ideal.height_eq_zero_iff` instead." (since := "2026-04-02")]
/-
**Ideal.primeHeight_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.primeHeight_eq_zero_iff {I : Ideal R} [I.IsPrime] :
    primeHeight I = 0 ↔ I ∈ minimalPrimes R := by
  rw [← Ideal.height_eq_primeHeight, Ideal.height_eq_zero_iff]

/-- If `x` is a non-zero-divisor, then `span {x}` has height at least 1. -/
/-
**Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors {x : R} (hx : x 
in nonZeroDivisors R) : 1 <= (span {x}).height
参数：hx : x in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.height_eq_inf_minimalPrimes`：Ideal.height_eq_inf_minimalPrimes : I
.height = ⨅ J in I.minimalPrimes, J.height
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Ideal.height_eq_zero_iff`：Ideal.height_eq_zero_iff {I : Ideal R} [I.IsPr
ime] : height I = 0 ↔ I in minimalPrimes R
· 使用引理 `notMem_nonZeroDivisors_of_mem_mem_minimalPrimes`：notMem_nonZeroDivisors_
of_mem_mem_minimalPrimes {x : R} {q : Ideal R} (hx : x in q) (hq : q in minimalP
rimes R) : x ∉ nonZeroDivisors R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a

--- 原说明 ---
If `x` is a non-zero-divisor, then `span {x}` has height at least 1.
-/
lemma Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    {x : R} (hx : x ∈ nonZeroDivisors R) : 1 ≤ (span {x}).height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun q hq => ?_
  have : q.IsPrime := hq.isPrime
  rw [Order.one_le_iff_ne_zero, Ne, height_eq_zero_iff]
  intro hmin
  exact absurd hx <| notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (hq.1.2 <| Ideal.mem_span_singleton.mpr <| dvd_refl x) hmin

@[simp]
/-
**Ideal.height_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_bot [Nontrivial R] : (⊥ : Ideal R).height = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.nonempty_minimalPrimes`：Ideal.nonempty_minimalPrimes (h : I != ⊤) 
: Nonempty I.minimalPrimes
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.height_eq_inf_minimalPrimes`：Ideal.height_eq_inf_minimalPrimes : I
.height = ⨅ J in I.minimalPrimes, J.height
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Ideal.height_eq_zero_iff`：Ideal.height_eq_zero_iff {I : Ideal R} [I.IsPr
ime] : height I = 0 ↔ I in minimalPrimes R
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
-/
lemma Ideal.height_bot [Nontrivial R] : (⊥ : Ideal R).height = 0 := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) top_ne_bot.symm
  rw [Ideal.height_eq_inf_minimalPrimes]
  simp only [ENat.iInf_eq_zero]
  refine ⟨p, hp, haveI := hp.isPrime; height_eq_zero_iff.mpr hp⟩

@[simp]
/-
**Ideal.height_eq_zero_iff_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_eq_zero_iff_eq_bot [IsDomain R] {I : Ideal R} : I.height = 0 
↔ I = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.exists_isPrime_height_eq`：Ideal.exists_isPrime_height_eq {I : Idea
l R} {n : Nat} (hI : I.height = n) : exists (p : Ideal R) (_ : p.IsPrime) (_ : I
 <= p), p.height = n
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `IsDomain.minimalPrimes_eq_singleton_bot`：IsDomain.minimalPrimes_eq_singl
eton_bot [IsDomain R] : minimalPrimes R = {⊥}
· 使用引理 `Ideal.height_eq_zero_iff`：Ideal.height_eq_zero_iff {I : Ideal R} [I.IsPr
ime] : height I = 0 ↔ I in minimalPrimes R
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Ideal.height_bot`：Ideal.height_bot [Nontrivial R] : (⊥ : Ideal R).height
 = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ideal.height_eq_zero_iff_eq_bot [IsDomain R] {I : Ideal R} : I.height = 0 ↔ I = ⊥ := by
  refine ⟨fun hI ↦ ?_, fun hI0 ↦ by simp [hI0]⟩
  rcases exists_isPrime_height_eq hI with ⟨p, _, hIp, hp0⟩
  rw [CharP.cast_eq_zero, height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
    Set.mem_singleton_iff] at hp0
  exact bot_unique (hIp.trans_eq hp0)
/-
**Ideal.ne_bot_of_height_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.ne_bot_of_height_eq_one [IsDomain R] {I : Ideal R} (h : I.height = 1
) : I != ⊥
参数：h : I.height = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Ideal.height_eq_zero_iff_eq_bot`：Ideal.height_eq_zero_iff_eq_bot [IsDoma
in R] {I : Ideal R} : I.height = 0 ↔ I = ⊥
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
-/
theorem Ideal.ne_bot_of_height_eq_one [IsDomain R] {I : Ideal R} (h : I.height = 1) : I ≠ ⊥ :=
  I.height_eq_zero_iff_eq_bot.not.mp (ne_zero_of_eq_one h)

/-- In a trivial commutative ring, the height of any ideal is `∞`. -/
@[simp, nontriviality]
/-
**Ideal.height_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_of_subsingleton [Subsingleton R] : I.height = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Ideal.height_top`：Ideal.height_top : (⊤ : Ideal R).height = ⊤

--- 原说明 ---
In a trivial commutative ring, the height of any ideal is `∞`.
-/
lemma Ideal.height_of_subsingleton [Subsingleton R] : I.height = ⊤ := by
  rw [Subsingleton.elim I ⊤, Ideal.height_top]
/-
**Ideal.isMaximal_of_height_eq_ringKrullDim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.isMaximal_of_height_eq_ringKrullDim {I : Ideal R} [I.IsPrime] [Finit
eRingKrullDim R] (e : I.height = ringKrullDim R) : I.IsMaximal
参数：e : I.height = ringKrullDim R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用引理 `Ideal.height_strict_mono_of_isPrime`：Ideal.height_strict_mono_of_isPrime
 {I J : Ideal R} [I.IsPrime] (h : I < J) [I.FiniteHeight] : I.height < J.height
· 使用定理 `Ideal.finiteHeight_of_finiteRingKrullDim`：∀ {R : Type u_1} [inst : CommR
ing R] {I : Ideal R} [FiniteRingKrullDim R], I.FiniteHeight
· 使用引理 `Ideal.height_le_ringKrullDim_of_ne_top`：Ideal.height_le_ringKrullDim_of_
ne_top {I : Ideal R} (h : I != ⊤) : I.height <= ringKrullDim R
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem Ideal.isMaximal_of_height_eq_ringKrullDim {I : Ideal R} [I.IsPrime]
    [FiniteRingKrullDim R] (e : I.height = ringKrullDim R) : I.IsMaximal := by
  have h : I ≠ ⊤ := Ideal.IsPrime.ne_top'
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
  rcases lt_or_eq_of_le hM' with (hM' | hM')
  · have h1 := Ideal.height_strict_mono_of_isPrime hM'
    have h2 := e ▸ M.height_le_ringKrullDim_of_ne_top hM.ne_top
    simp [← not_lt, h1] at h2
  · exact hM' ▸ hM

@[deprecated "Use `Ideal.isMaximal_of_height_eq_ringKrullDim` instead." (since := "2026-04-02")]
/-
**Ideal.isMaximal_of_primeHeight_eq_ringKrullDim** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Ideal.isMaximal_of_primeHeight_eq_ringKrullDim {I : Ideal R} [I.IsPrime]
    [FiniteRingKrullDim R] (e : I.primeHeight = ringKrullDim R) : I.IsMaximal :=
  Ideal.isMaximal_of_height_eq_ringKrullDim (by simpa [Ideal.height_eq_primeHeight])

/-- The height of the maximal ideal equals the Krull dimension in a local ring. -/
@[simp]
/-
**IsLocalRing.maximalIdeal_height_eq_ringKrullDim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalRing.maximalIdeal_height_eq_ringKrullDim [IsLocalRing R] : (IsLocal
Ring.maximalIdeal R).height = ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.primeHeight.eq_1`：∀ {R 
: Type u_1} [inst : CommRing R] (I : Ideal R) [hI : I.IsPrime],   Ideal.primeHei
ght✝ I = Order.height { asIdeal := I, isPrime := hI }
· 使用引理 `Order.height_top_eq_krullDim`：height_top_eq_krullDim [OrderTop α] : heig
ht (⊤ : α) = krullDim α

--- 原说明 ---
The height of the maximal ideal equals the Krull dimension in a local ring.
-/
theorem IsLocalRing.maximalIdeal_height_eq_ringKrullDim [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).height = ringKrullDim R := by
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  exact Order.height_top_eq_krullDim

@[deprecated "Use `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` instead."
  (since := "2026-04-04")]
/-
**IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim** 是 Mathlib 中的一个定理，位于命名空间
 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).primeHeight = ringKrullDim R := by
  simp [← Ideal.height_eq_primeHeight]

/-- For a local ring with finite Krull dimension, a prime ideal has height equal to the Krull
dimension if and only if it is the maximal ideal. -/
/-
**Ideal.height_eq_ringKrullDim_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.height_eq_ringKrullDim_iff [FiniteRingKrullDim R] [IsLocalRing R] {I
 : Ideal R} [I.IsPrime] : I.height = ringKrullDim R ↔ I = IsLocalRing.maximalIde
al R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Ideal.isMaximal_of_height_eq_ringKrullDim`：Ideal.isMaximal_of_height_eq_
ringKrullDim {I : Ideal R} [I.IsPrime] [FiniteRingKrullDim R] (e : I.height = ri
ngKrullDim R) : I.IsMaximal
· 使用定理 `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`：IsLocalRing.maximalIdea
l_height_eq_ringKrullDim [IsLocalRing R] : (IsLocalRing.maximalIdeal R).height =
 ringKrullDim R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For a local ring with finite Krull dimension, a prime ideal has height equal to 
the Krull
dimension if and only if it is the maximal ideal.
-/
theorem Ideal.height_eq_ringKrullDim_iff [FiniteRingKrullDim R] [IsLocalRing R] {I : Ideal R}
    [I.IsPrime] : I.height = ringKrullDim R ↔ I = IsLocalRing.maximalIdeal R := by
  constructor
  · intro h
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_height_eq_ringKrullDim h)
  · rintro rfl
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

@[deprecated "Use `Ideal.height_eq_ringKrullDim_iff` instead." (since := "2026-04-02")]
/-
**Ideal.primeHeight_eq_ringKrullDim_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Ideal.primeHeight_eq_ringKrullDim_iff [FiniteRingKrullDim R] [IsLocalRing R]
    {I : Ideal R} [I.IsPrime] :
    Ideal.primeHeight I = ringKrullDim R ↔ I = IsLocalRing.maximalIdeal R := by
  rw [← Ideal.height_eq_primeHeight, Ideal.height_eq_ringKrullDim_iff]
/-
**Ideal.height_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_le_iff {p : Ideal R} {n : Nat} [p.IsPrime] : p.height <= n ↔ 
forall q : Ideal R, q.IsPrime -> q < p -> q.height < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.primeHeight.eq_1`：∀ {R 
: Type u_1} [inst : CommRing R] (I : Ideal R) [hI : I.IsPrime],   Ideal.primeHei
ght✝ I = Order.height { asIdeal := I, isPrime := hI }
· 使用引理 `Order.height_le_coe_iff`：height_le_coe_iff {x : α} {n : Nat} : height x 
<= n ↔ forall y < x, height y < n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ideal.height_le_iff {p : Ideal R} {n : ℕ} [p.IsPrime] :
    p.height ≤ n ↔ ∀ q : Ideal R, q.IsPrime → q < p → q.height < n := by
  rw [height_eq_primeHeight, primeHeight, Order.height_le_coe_iff,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall]
  congr!
  rw [height_eq_primeHeight, primeHeight]
  rfl
/-
**Ideal.height_le_iff_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.height_le_iff_covBy {p : Ideal R} {n : Nat} [p.IsPrime] [IsNoetheria
nRing R] : p.height <= n ↔ forall q : Ideal R, q.IsPrime -> q < p -> (forall q' 
: Ideal R, q'.IsPrime -> q < q' -> ¬ q' < p) -> q.height < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.height_le_iff`：Ideal.height_le_iff {p : Ideal R} {n : Nat} [p.IsPr
ime] : p.height <= n ↔ forall q : Ideal R, q.IsPrime -> q < p -> q.height < n
· 使用定理 `exists_le_covBy_of_lt`：exists_le_covBy_of_lt [IsStronglyCoatomic α] (h :
 a < b) : exists x, a <= x ∧ x ⋖ b
· 使用定理 `instIsStronglyCoatomicOfWellFoundedGT`：∀ {α : Type u_2} [inst : PartialO
rder α] [WellFoundedGT α], IsStronglyCoatomic α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Ideal.height_le_iff_covBy {p : Ideal R} {n : ℕ} [p.IsPrime] [IsNoetherianRing R] :
    p.height ≤ n ↔ ∀ q : Ideal R, q.IsPrime → q < p →
      (∀ q' : Ideal R, q'.IsPrime → q < q' → ¬ q' < p) → q.height < n := by
  rw [Ideal.height_le_iff]
  constructor
  · intro H q hq e _
    exact H q hq e
  · intro H q hq e
    obtain ⟨⟨x, hx⟩, hqx, hxp⟩ :=
      @exists_le_covBy_of_lt { I : Ideal R // I.IsPrime } ⟨q, hq⟩ ⟨p, ‹_›⟩ _ _ e
    exact (Ideal.height_mono hqx).trans_lt
      (H _ hx hxp.1 (fun I hI e ↦ hxp.2 (show Subtype.mk x hx < ⟨I, hI⟩ from e)))

/-- Use `RingEquiv.height_comap` instead, which does not assume `IsPrime`. -/
/-
**RingEquiv.height_comap_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `RingEquiv.height_comap` instead, which does not assume `IsPrime`.
-/
private lemma RingEquiv.height_comap_of_isPrime {S : Type*} [CommRing S] (e : R ≃+* S)
    (p : Ideal S) [p.IsPrime] : (p.comap e).height = p.height := by
  rw [height_eq_primeHeight, height_eq_primeHeight, primeHeight, primeHeight,
    ← Order.height_orderIso (PrimeSpectrum.comapEquiv e.symm) ⟨p, ‹_›⟩]
  have := p.map_comap_of_equiv e.symm
  congr

@[simp]
/-
**RingEquiv.height_comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingEquiv.height_comap {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal S
) : (I.comap e).height = I.height
参数：e : R ≃+* S；I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Equiv.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: InfSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨅ x,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `Ideal.comap_minimalPrimes_eq_of_surjective`：Ideal.comap_minimalPrimes_eq
_of_surjective {f : R ->+* S} (hf : Function.Surjective f) (I : Ideal S) : (I.co
map f).minimalPrimes = Ideal.com…
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingEquiv.idealComapOrderIso_apply`：∀ {R : Type u_1} {S : Type u_2} [ins
t : Semiring R] [inst_1 : Semiring S] (e : R ≃+* S) (I : Ideal S),   e.idealComa
pOrderIso I = Ideal.coma…
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.primeHeight.congr_simp`
：∀ {R : Type u_1} [inst : CommRing R] (I I_1 : Ideal R) (e_I : I = I_1) [hI : I.
IsPrime],   Ideal.primeHeight✝ I = Ideal.primeHeight✝ I_1
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.RingEquiv.height_comap_of_isP
rime`：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
(e : R ≃+* S) (p : Ideal S) [p.IsPrime],   (Ideal.comap e p).heigh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RingEquiv.height_comap {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal S) :
    (I.comap e).height = I.height := by
  refine (Equiv.iInf_congr e.idealComapOrderIso fun J ↦ (Equiv.iInf_congr ?_ fun h ↦ ?_).symm).symm
  · refine .ofIff ?_
    rw [← Ideal.comap_coe,
      Ideal.comap_minimalPrimes_eq_of_surjective (f := (↑e : R →+* S)) e.surjective]
    exact e.idealComapOrderIso.injective.mem_set_image.symm
  · have : J.IsPrime := h.isPrime
    simp only [EquivLike.coe_coe, RingEquiv.idealComapOrderIso_apply,
      ← Ideal.height_eq_primeHeight, RingEquiv.height_comap_of_isPrime]

@[simp]
/-
**RingEquiv.height_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingEquiv.height_map {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal R) 
: (I.map e).height = I.height
参数：e : R ≃+* S；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用引理 `RingEquiv.height_comap`：RingEquiv.height_comap {S : Type*} [CommRing S] 
(e : R ≃+* S) (I : Ideal S) : (I.comap e).height = I.height
-/
lemma RingEquiv.height_map {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal R) :
    (I.map e).height = I.height := by
  rw [← Ideal.comap_symm e, height_comap]

/-- `dim R ≤ n` if and only if the height of all prime ideals is less than `n`. -/
/-
**ringKrullDim_le_iff_height_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_le_iff_height_le {R : Type*} [CommRing R] (n : WithBot Nat∞) 
: ringKrullDim R <= n ↔ forall ⦃p : Ideal R⦄, p.IsPrime -> p.height <= n
参数：n : WithBot Nat∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ringKrullDim.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R], ringKrullDi
m R = Order.krullDim (PrimeSpectrum R)
· 使用引理 `Order.krullDim_eq_iSup_height`：krullDim_eq_iSup_height : krullDim α = ⨆ 
(a : α), ↑(height a)
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
`dim R ≤ n` if and only if the height of all prime ideals is less than `n`.
-/
lemma ringKrullDim_le_iff_height_le {R : Type*} [CommRing R] (n : WithBot ℕ∞) :
    ringKrullDim R ≤ n ↔ ∀ ⦃p : Ideal R⦄, p.IsPrime → p.height ≤ n := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_height, iSup_le_iff]
  refine ⟨fun h p hp ↦ ?_, fun h p ↦ ?_⟩
  · rw [Ideal.height_eq_primeHeight]
    exact h ⟨p, hp⟩
  · specialize h p.2
    rwa [Ideal.height_eq_primeHeight] at h

/-- `dim R ≤ n` if and only if the height of all maximal ideals is less than `n`. -/
/-
**ringKrullDim_le_iff_isMaximal_height_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_le_iff_isMaximal_height_le {R : Type*} [CommRing R] (n : With
Bot Nat∞) : ringKrullDim R <= n ↔ forall ⦃m : Ideal R⦄, m.IsMaximal -> m.height 
<= n
参数：n : WithBot Nat∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringKrullDim_le_iff_height_le`：ringKrullDim_le_iff_height_le {R : Type*}
 [CommRing R] (n : WithBot Nat∞) : ringKrullDim R <= n ↔ forall ⦃p : Ideal R⦄, p
.IsPrime -> p.heigh…
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height

--- 原说明 ---
`dim R ≤ n` if and only if the height of all maximal ideals is less than `n`.
-/
lemma ringKrullDim_le_iff_isMaximal_height_le {R : Type*} [CommRing R] (n : WithBot ℕ∞) :
    ringKrullDim R ≤ n ↔ ∀ ⦃m : Ideal R⦄, m.IsMaximal → m.height ≤ n := by
  rw [ringKrullDim_le_iff_height_le]
  refine ⟨fun h m hm ↦ h hm.isPrime, fun h p hp ↦ ?_⟩
  obtain ⟨m, hm, hle⟩ := p.exists_le_maximal hp.ne_top
  refine le_trans ?_ (h hm)
  norm_cast
  exact Ideal.height_mono hle
/-
**IsLocalization.height_under_eq_of_isPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem IsLocalization.height_under_eq_of_isPrime (S : Submonoid R) {A : Type*} [CommRing A]
    [Algebra R A] [IsLocalization S A] (J : Ideal A) [J.IsPrime] :
    (J.comap (algebraMap R A)).height = J.height := by
  rw [eq_comm, Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight, Ideal.primeHeight,
    Ideal.primeHeight, ← WithBot.coe_inj, Order.height_eq_krullDim_Iic,
    Order.height_eq_krullDim_Iic]
  let e := IsLocalization.orderIsoOfPrime S A
  have H (p : Ideal R) (hp : p ≤ J.comap (algebraMap R A)) : Disjoint (S : Set R) p :=
    Set.disjoint_of_subset_right hp (e ⟨_, ‹J.IsPrime›⟩).2.2
  exact Order.krullDim_eq_of_orderIso
    { toFun I := ⟨⟨I.1.1.comap (algebraMap R A), (e ⟨_, I.1.2⟩).2.1⟩, Ideal.comap_mono I.2⟩
      invFun I := ⟨⟨_, (e.symm ⟨_, I.1.2, H _ I.2⟩).2⟩, Ideal.map_le_iff_le_comap.mpr I.2⟩
      left_inv I := Subtype.ext <| PrimeSpectrum.ext_iff.mpr <|
        congrArg (fun I ↦ I.1) (e.left_inv ⟨_, I.1.2⟩)
      right_inv I := Subtype.ext <| PrimeSpectrum.ext_iff.mpr <|
        congrArg (fun I ↦ I.1) (e.right_inv ⟨_, I.1.2, H _ I.2⟩)
      map_rel_iff' {I₁ I₂} := @RelIso.map_rel_iff _ _ _ _ e ⟨_, I₁.1.2⟩ ⟨_, I₂.1.2⟩ }

@[deprecated "Use `Ideal.height_ne_top_of_isPrime` instead." (since := "2026-04-04")]
/-
**IsLocalization.primeHeight_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem IsLocalization.primeHeight_comap (S : Submonoid R) {A : Type*} [CommRing A]
    [Algebra R A] [IsLocalization S A] (J : Ideal A) [J.IsPrime] :
    (J.comap (algebraMap R A)).primeHeight = J.primeHeight := by
  simpa [Ideal.height_eq_primeHeight] using IsLocalization.height_under_eq_of_isPrime S J
/-
**IsLocalization.height_under** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.height_under (S : Submonoid R) {A : Type*} [CommRing A] [Al
gebra R A] [IsLocalization S A] (J : Ideal A) : (J.under R).height = J.height
参数：S : Submonoid R；J : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.height_eq_inf_minimalPrimes`：Ideal.height_eq_inf_minimalPrimes : I
.height = ⨅ J in I.minimalPrimes, J.height
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsLocalization.minimalPrimes_comap`：IsLocalization.minimalPrimes_comap [
IsLocalization S A] (J : Ideal A) : (J.comap (algebraMap R A)).minimalPrimes = I
deal.comap (algebraMap R…
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.IsLocalization.height_under_e
q_of_isPrime`：∀ {R : Type u_1} [inst : CommRing R] (S : Submonoid R) {A : Type u
_2} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [IsLocalization S A] (J…
-/
theorem IsLocalization.height_under (S : Submonoid R) {A : Type*} [CommRing A] [Algebra R A]
    [IsLocalization S A] (J : Ideal A) : (J.under R).height = J.height := by
  rw [(J.comap _).height_eq_inf_minimalPrimes, J.height_eq_inf_minimalPrimes]
  simp only [IsLocalization.minimalPrimes_comap S A, iInf_image]
  apply iInf_congr (fun p ↦ iInf_congr fun hp ↦ ?_)
  have := hp.isPrime
  exact IsLocalization.height_under_eq_of_isPrime S _

@[deprecated (since := "2026-04-09")] alias IsLocalization.height_comap :=
  IsLocalization.height_under
/-
**IsLocalization.AtPrime.ringKrullDim_eq_height** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.AtPrime.ringKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A
 : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A I] : ringKrullDim
 A = I.height
参数：I : Ideal R；A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`：IsLocalRing.maximalIdea
l_height_eq_ringKrullDim [IsLocalRing R] : (IsLocalRing.maximalIdeal R).height =
 ringKrullDim R
· 使用定理 `IsLocalization.height_under`：IsLocalization.height_under (S : Submonoid 
R) {A : Type*} [CommRing A] [Algebra R A] [IsLocalization S A] (J : Ideal A) : (
J.under R).height…
· 使用定理 `IsLocalization.AtPrime.under_maximalIdeal`：under_maximalIdeal (h : IsLoc
alRing S
-/
theorem IsLocalization.AtPrime.ringKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization.AtPrime A I] :
    ringKrullDim A = I.height := by
  have := IsLocalization.AtPrime.isLocalRing A I
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      ← IsLocalization.height_under I.primeCompl,
      ← IsLocalization.AtPrime.under_maximalIdeal A I]
/-
**IsLocalization.height_map_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.height_map_of_disjoint {S : Type*} [CommRing S] [Algebra R 
S] (M : Submonoid R) [IsLocalization M S] (p : Ideal R) [p.IsPrime] (h : Disjoin
t (M : Set R) (p : Set R)) : (p.map <| algebraMap R S).height = p.height
参数：M : Submonoid R；p : Ideal R；h : Disjoint (M : Set R) (p : Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`：isL
ocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
 [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ringKrullDim_eq_of_ringEquiv`：ringKrullDim_eq_of_ringEquiv (e : R ≃+* S)
 : ringKrullDim R = ringKrullDim S
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用定理 `IsLocalization.AtPrime.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring
 R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   (P P_1 : I
deal R) (e_P : P = P_1)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.AtPrime.ringKrullDim_eq_height`：IsLocalization.AtPrime.ri
ngKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A : Type*) [CommRing A] [Algebra
 R A] [IsLocalization.AtPrime A I] …
-/
lemma IsLocalization.height_map_of_disjoint {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (p : Ideal R) [p.IsPrime] (h : Disjoint (M : Set R) (p : Set R)) :
    (p.map <| algebraMap R S).height = p.height := by
  let P := p.map (algebraMap R S)
  have : P.IsPrime := isPrime_of_isPrime_disjoint M S p ‹_› h
  have := isLocalization_isLocalization_atPrime_isLocalization (M := M) (Localization.AtPrime P) P
  simp_rw [P, under_map_of_isPrime_disjoint M S _ h] at this
  have := ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime P) (Localization.AtPrime p)).toRingEquiv
  rw [AtPrime.ringKrullDim_eq_height P, AtPrime.ringKrullDim_eq_height p] at this
  exact WithBot.coe_eq_coe.mp this

@[deprecated "Use `mem_minimalPrimes_of_height_le` instead." (since := "2026-04-02")]
/-
**mem_minimalPrimes_of_primeHeight_eq_height** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_minimalPrimes_of_primeHeight_eq_height {I J : Ideal R} [J.IsPrime] (e : I ≤ J)
    (e' : J.primeHeight = I.height) [J.FiniteHeight] : J ∈ I.minimalPrimes := by
  rw [← J.height_eq_primeHeight] at e'
  exact mem_minimalPrimes_of_height_le e (e' ▸ le_refl _)
/-
**exists_spanRank_le_and_le_height_of_le_height** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_spanRank_le_and_le_height_of_le_height [IsNoetherianRing R] (I : Id
eal R) (r : Nat) (hr : r <= I.height) : exists J <= I, J.spanRank <= r ∧ r <= J.
height
参数：I : Ideal R；r : Nat；hr : r <= I.height。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Ideal.finite_minimalPrimes_of_isNoetherianRing`：Ideal.finite_minimalPrim
es_of_isNoetherianRing (I : Ideal R) : I.minimalPrimes.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.subset_union_prime`：subset_union_prime {R : Type u} [CommRing R] {
s : Finset ι} {f : ι -> Ideal R} (a b : ι) (hp : forall i in s, i != a -> i != b
 -> IsPrime (f…
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
（共 57 条，此处仅展示前 30 条）
-/
lemma exists_spanRank_le_and_le_height_of_le_height [IsNoetherianRing R] (I : Ideal R) (r : ℕ)
    (hr : r ≤ I.height) : ∃ J ≤ I, J.spanRank ≤ r ∧ r ≤ J.height := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨J, h₁, h₂, h₃⟩ := ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let S := { K | K ∈ J.minimalPrimes ∧ Ideal.height K = r }
    have hS : Set.Finite S := Set.Finite.subset J.finite_minimalPrimes_of_isNoetherianRing
      (fun _ h => h.1)
    have : ¬(I : Set R) ⊆ ⋃ K ∈ hS.toFinset, (K : Set R) := by
      refine (Ideal.subset_union_prime ⊥ ⊥ ?_).not.mpr ?_
      · rintro K hK - -
        rw [Set.Finite.mem_toFinset] at hK
        exact hK.1.isPrime
      · push Not
        intro K hK e
        have := hr.trans (Ideal.height_mono e)
        rw [Set.Finite.mem_toFinset] at hK
        rw [hK.2, ← not_lt] at this
        norm_cast at this
        exact this r.lt_succ_self
    simp_rw [Set.not_subset, Set.mem_iUnion, not_exists, Set.Finite.mem_toFinset] at this
    obtain ⟨x, hx₁, hx₂⟩ := this
    refine ⟨J ⊔ Ideal.span {x}, sup_le h₁ ?_, ?_, ?_⟩
    · rwa [Ideal.span_le, Set.singleton_subset_iff]
    · apply Submodule.spanRank_sup_le_sum_spanRank.trans
      push_cast
      exact add_le_add h₂ ((Submodule.spanRank_span_le_card _).trans (by simp))
    · refine le_iInf₂ (fun p hp ↦ ?_)
      have := hp.isPrime
      rw [← p.height_eq_primeHeight]
      by_cases h : p.height = ⊤
      · exact le_of_le_of_eq le_top h.symm
      have : p.FiniteHeight := ⟨Or.inr h⟩
      have := Ideal.height_mono (le_sup_left.trans hp.le)
      suffices h : (r : ℕ∞) ≠ p.height by
        exact Order.add_one_le_of_lt (lt_of_le_of_ne (h₃.trans this) h)
      intro e
      apply hx₂ p
      · refine ⟨mem_minimalPrimes_of_height_le (le_sup_left.trans hp.le) (e.symm.trans_le h₃),
          e.symm⟩
      · apply hp.le <| Ideal.mem_sup_right <| mem_span_singleton_self x

/-- In a nontrivial commutative ring `R`, the supremum of heights of all ideals is equal to the
Krull dimension of `R`. -/
/-
**Ideal.sup_height_eq_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.sup_height_eq_ringKrullDim [Nontrivial R] : ↑(⨆ (I : Ideal R) (_ : I
 != ⊤), I.height) = ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_iSup`：WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} 
(hf : BddAbove (range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Ideal.height_top`：Ideal.height_top : (⊤ : Ideal R).height = ⊤
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Height.0.Ideal.height_eq_primeHeight`：
∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [inst_1 : I.IsPrime], I.heigh
t = Ideal.primeHeight✝ I
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤

--- 原说明 ---
In a nontrivial commutative ring `R`, the supremum of heights of all ideals is e
qual to the
Krull dimension of `R`.
-/
lemma Ideal.sup_height_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I ≠ ⊤), I.height) = ringKrullDim R := by
  apply le_antisymm
  · rw [WithBot.coe_iSup ⟨⊤, fun _ _ => le_top⟩]
    refine iSup_le fun I => ?_
    by_cases h : I = ⊤
    · simp [h, ringKrullDim_nonneg_of_nontrivial]
    · simp [h, height_le_ringKrullDim_of_ne_top]
  · refine iSup_le fun p => WithBot.coe_le_coe.mpr (le_trans (b := p.last.asIdeal.height) ?_ ?_)
    · rw [height_eq_primeHeight]
      apply le_trans (b := ⨆ (_ : p.last ≤ p.last), ↑p.length)
      · exact le_iSup (fun _ => (↑p.length : ℕ∞)) le_rfl
      · exact le_iSup (fun p' => (⨆ _, p'.length : ℕ∞)) p
    · apply le_trans (b := ⨆ (_ : (p.last).asIdeal ≠ ⊤), p.last.asIdeal.height)
      · exact le_iSup_of_le p.last.isPrime.ne_top' le_rfl
      · exact le_iSup (fun I => ⨆ _, I.height) p.last.asIdeal

/-- In a nontrivial commutative ring `R`, the supremum of heights of all prime ideals is
equal to the Krull dimension of `R`. -/
/-
**Ideal.sup_isPrime_height_eq_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.sup_isPrime_height_eq_ringKrullDim [Nontrivial R] : ↑(⨆ (I : Ideal R
) (_ : I.IsPrime), I.height) = ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.sup_height_eq_ringKrullDim`：Ideal.sup_height_eq_ringKrullDim [Nont
rivial R] : ↑(⨆ (I : Ideal R) (_ : I != ⊤), I.height) = ringKrullDim R
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Ideal.height_top`：Ideal.height_top : (⊤ : Ideal R).height = ⊤
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `Ideal.height_bot`：Ideal.height_bot [Nontrivial R] : (⊥ : Ideal R).height
 = 0
· 使用定理 `ENat.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Ideal.nonempty_minimalPrimes`：Ideal.nonempty_minimalPrimes (h : I != ⊤) 
: Nonempty I.minimalPrimes
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
In a nontrivial commutative ring `R`, the supremum of heights of all prime ideal
s is
equal to the Krull dimension of `R`.
-/
lemma Ideal.sup_isPrime_height_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsPrime), I.height) = ringKrullDim R := by
  rw [← sup_height_eq_ringKrullDim, WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.ne_top, le_refl _⟩
  · refine iSup_mono' fun I => ?_
    by_cases I_top : I = ⊤
    · exact ⟨⊥, by simp [I_top]⟩
    · obtain ⟨P, hP⟩ := Set.nonempty_coe_sort.mp (nonempty_minimalPrimes I_top)
      refine ⟨P, iSup_pos (α := ℕ∞) I_top ▸ le_iSup_of_le (hP.left.left) ?_⟩
      have := hP.isPrime
      exact iInf_le_of_le P (iInf_le_of_le hP (ge_of_eq (Ideal.height_eq_primeHeight P)))

@[deprecated "Use `Ideal.sup_height_isPrime_eq_ringKrullDim` instead." (since := "2026-04-02")]
/-
**Ideal.sup_primeHeight_eq_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.sup_primeHeight_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsPrime), I.primeHeight) = ringKrullDim R := by
  simp [← Ideal.height_eq_primeHeight, Ideal.sup_isPrime_height_eq_ringKrullDim]

/-- In a nontrivial commutative ring `R`, the supremum of heights of all maximal ideals is
equal to the Krull dimension of `R`. -/
/-
**Ideal.sup_isMaximal_height_eq_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.sup_isMaximal_height_eq_ringKrullDim [Nontrivial R] : ↑(⨆ (I : Ideal
 R) (_ : I.IsMaximal), I.height) = ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.sup_height_eq_ringKrullDim`：Ideal.sup_height_eq_ringKrullDim [Nont
rivial R] : ↑(⨆ (I : Ideal R) (_ : I != ⊤), I.height) = ringKrullDim R
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.height_mono`：Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.he
ight <= J.height

--- 原说明 ---
In a nontrivial commutative ring `R`, the supremum of heights of all maximal ide
als is
equal to the Krull dimension of `R`.
-/
lemma Ideal.sup_isMaximal_height_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsMaximal), I.height) = ringKrullDim R := by
  rw [← Ideal.sup_height_eq_ringKrullDim, WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.isPrime.ne_top , le_rfl⟩
  · refine iSup_mono' fun I => ?_
    obtain rfl | I_top := eq_or_ne I ⊤
    · exact ⟨⊥, by grind [iSup_le_iff, Ideal.IsPrime.ne_top]⟩
    · obtain ⟨M, hM, hIM⟩ := exists_le_maximal I I_top
      exact ⟨M, iSup_mono' (fun hI ↦ ⟨hM, height_mono hIM⟩)⟩

@[deprecated "Use `Ideal.sup_height_of_maximal_eq_ringKrullDim` instead." (since := "2026-04-02")]
/-
**Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsMaximal), I.primeHeight) = ringKrullDim R := by
  simp_rw [← Ideal.height_eq_primeHeight, Ideal.sup_isMaximal_height_eq_ringKrullDim]

section isLocalization

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]

/-
**Ring.krullDimLE_of_isLocalization_maximal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.krullDimLE_of_isLocalization_maximal {n : Nat} (h : forall (P : Ideal
 R) [P.IsMaximal], Ring.KrullDimLE n (Rₚ P)) : Ring.KrullDimLE n R
参数：h : forall (P : Ideal R) [P.IsMaximal], Ring.KrullDimLE n (Rₚ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringKrullDim_eq_bot_of_subsingleton`：ringKrullDim_eq_bot_of_subsingleton
 [Subsingleton R] : ringKrullDim R = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.sup_isMaximal_height_eq_ringKrullDim`：Ideal.sup_isMaximal_height_e
q_ringKrullDim [Nontrivial R] : ↑(⨆ (I : Ideal R) (_ : I.IsMaximal), I.height) =
 ringKrullDim R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `IsLocalization.AtPrime.ringKrullDim_eq_height`：IsLocalization.AtPrime.ri
ngKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A : Type*) [CommRing A] [Algebra
 R A] [IsLocalization.AtPrime A I] …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Ring.krullDimLE_of_isLocalization_maximal {n : ℕ}
    (h : ∀ (P : Ideal R) [P.IsMaximal], Ring.KrullDimLE n (Rₚ P)) :
    Ring.KrullDimLE n R := by
  simp_rw [Ring.krullDimLE_iff] at h ⊢
  nontriviality R
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim]
  refine (WithBot.coe_le_coe).mpr (iSup₂_le_iff.mpr fun P hP ↦ ?_)
  rw [← WithBot.coe_le_coe, ← IsLocalization.AtPrime.ringKrullDim_eq_height P (Rₚ P)]
  exact h P

end isLocalization

/-
**Ideal.eq_span_singleton_of_height_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.eq_span_singleton_of_height_eq_one [IsDomain R] {p : Ideal R} [p.IsP
rime] (h1 : p.height = 1) {x : R} (hx : x in p) (hxp : Prime x) : p = span {x}
参数：h1 : p.height = 1；hx : x in p；hxp : Prime x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ideal.finiteHeight_iff`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal 
R), I.FiniteHeight ↔ I = ⊤ ∨ I.height ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用引理 `Ideal.height_eq_zero_iff_eq_bot`：Ideal.height_eq_zero_iff_eq_bot [IsDoma
in R] {I : Ideal R} : I.height = 0 ↔ I = ⊥
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用引理 `Ideal.height_strict_mono_of_isPrime_of_isPrime`：Ideal.height_strict_mono
_of_isPrime_of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) [J.Fi
niteHeight] : I.height < J.height
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma Ideal.eq_span_singleton_of_height_eq_one [IsDomain R] {p : Ideal R} [p.IsPrime]
    (h1 : p.height = 1) {x : R} (hx : x ∈ p) (hxp : Prime x) : p = span {x} := by
  have : (span {x}).IsPrime := by simp [span_singleton_prime hxp.ne_zero, hxp]
  have : p.FiniteHeight := by simp [p.finiteHeight_iff, h1]
  by_contra! hne
  apply hxp.ne_zero
  rw [← span_singleton_eq_bot, ← height_eq_zero_iff_eq_bot, ← Order.lt_one_iff, ← h1]
  refine height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne ?_ hne.symm)
  simp only [p.span_singleton_le_iff_mem, hx]
