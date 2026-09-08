/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Data.ENat.Basic

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailingDegree p`: the multiplicity of `X` in the polynomial `p`
* `natTrailingDegree`: a variant of `trailingDegree` that takes values in the natural numbers
* `trailingCoeff`: the coefficient at index `natTrailingDegree p`

Converts most results about `degree`, `natDegree` and `leadingCoeff` to results about the bottom
end of a polynomial
-/

@[expose] public section


noncomputable section

open Function Polynomial Finsupp Finset

open scoped Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-- `trailingDegree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailingDegree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailingDegree 0 = ⊤`. -/
/-
**Polynomial.trailingDegree** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree (p : R[X]) : Nat∞
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`trailingDegree p` is the multiplicity of `x` in the polynomial `p`, i.e. the sm
allest
`X`-exponent in `p`.
`trailingDegree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` th
at appears
in `p`, otherwise
`trailingDegree 0 = ⊤`.
-/
def trailingDegree (p : R[X]) : ℕ∞ :=
  p.support.min
/-
**Polynomial.trailingDegree_lt_wf** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < tr
ailingDegree q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `instWellFoundedLTENat`：WellFoundedLT ℕ∞
-/
theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wf trailingDegree wellFounded_lt

/-- `natTrailingDegree p` forces `trailingDegree p` to `ℕ`, by defining
`natTrailingDegree ⊤ = 0`. -/
/-
**Polynomial.natTrailingDegree** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree (p : R[X]) : Nat
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`natTrailingDegree p` forces `trailingDegree p` to `ℕ`, by defining
`natTrailingDegree ⊤ = 0`.
-/
def natTrailingDegree (p : R[X]) : ℕ :=
  ENat.toNat (trailingDegree p)

/-- `trailingCoeff p` gives the coefficient of the smallest power of `X` in `p`. -/
/-
**Polynomial.trailingCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：trailingCoeff (p : R[X]) : R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`trailingCoeff p` gives the coefficient of the smallest power of `X` in `p`.
-/
def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)

/-- a polynomial is `monic_at` if its trailing coefficient is 1 -/
/-
**Polynomial.TrailingMonic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：TrailingMonic (p : R[X])
参数：p : R[X]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a polynomial is `monic_at` if its trailing coefficient is 1
-/
def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)
/-
**Polynomial.TrailingMonic.def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.TrailingMon
ic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.TrailingMonic ↔ p
.trailingCoeff = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem TrailingMonic.def : TrailingMonic p ↔ trailingCoeff p = 1 :=
  Iff.rfl
/-
**Polynomial.TrailingMonic.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Trail
ingMonic`。
形式化陈述：{R : Type u} → [inst : Semiring R] → {p : Polynomial R} → [DecidableEq R] 
→ Decidable p.TrailingMonic
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance TrailingMonic.decidable [DecidableEq R] : Decidable (TrailingMonic p) :=
  inferInstanceAs <| Decidable (trailingCoeff p = (1 : R))

@[simp]
/-
**Polynomial.TrailingMonic.trailingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.T
railingMonic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.TrailingMonic → p
.trailingCoeff = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TrailingMonic.trailingCoeff {p : R[X]} (hp : p.TrailingMonic) : trailingCoeff p = 1 :=
  hp

@[simp]
/-
**Polynomial.trailingDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_zero : trailingDegree (0 : R[X]) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trailingDegree_zero : trailingDegree (0 : R[X]) = ⊤ :=
  rfl

@[simp]
/-
**Polynomial.trailingCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingCoeff_zero : trailingCoeff (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trailingCoeff_zero : trailingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
/-
**Polynomial.natTrailingDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_zero : natTrailingDegree (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natTrailingDegree_zero : natTrailingDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
/-
**Polynomial.trailingDegree_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_eq_top : trailingDegree p = ⊤ ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.support_eq_empty`：support_eq_empty : p.support = ∅ ↔ p = 0
· 使用定理 `Finset.min_eq_top`：min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trailingDegree_eq_top : trailingDegree p = ⊤ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩
/-
**Polynomial.trailingDegree_eq_natTrailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：trailingDegree_eq_natTrailingDegree (hp : p != 0) : trailingDegree p = (na
tTrailingDegree p : Nat∞)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.trailingDegree_eq_top`：trailingDegree_eq_top : trailingDegree
 p = ⊤ ↔ p = 0
-/
theorem trailingDegree_eq_natTrailingDegree (hp : p ≠ 0) :
    trailingDegree p = (natTrailingDegree p : ℕ∞) :=
  .symm <| ENat.natCast_toNat <| mt trailingDegree_eq_top.1 hp
/-
**Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : Nat} (hp : p !=
 0) : p.trailingDegree = n ↔ p.natTrailingDegree = n
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [trailingDegree_eq_natTrailingDegree hp, Nat.cast_inj]
/-
**Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq_of_pos** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : Nat} (hn
 : n != 0) : p.trailingDegree = n ↔ p.natTrailingDegree = n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p
 : Polynomial R), p.natTrailingDegree = p.trailingDegree.toNat
· 使用定理 `ENat.toNat_eq_iff`：toNat_eq_iff {m : Nat∞} {n : Nat} (hn : n != 0) : toN
at m = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : n ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [natTrailingDegree, ENat.toNat_eq_iff hn]
/-
**Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : Nat} (h : t
railingDegree p = n) : natTrailingDegree p = n
参数：h : trailingDegree p = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : ℕ}
    (h : trailingDegree p = n) : natTrailingDegree p = n := by
  simp [natTrailingDegree, h]

@[simp]
/-
**Polynomial.natTrailingDegree_le_trailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) <= trailingDe
gree p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.natCast_toNat_le_self`：natCast_toNat_le_self (n : Nat∞) : ↑(toNat n
) <= n
-/
theorem natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) ≤ trailingDegree p :=
  ENat.natCast_toNat_le_self _
/-
**Polynomial.natTrailingDegree_eq_of_trailingDegree_eq** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]} (h : tra
ilingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q
参数：h : trailingDegree p = trailingDegree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold natTrailingDegree
  rw [h]
/-
**Polynomial.trailingDegree_le_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：trailingDegree_le_of_ne_zero (h : coeff p n != 0) : trailingDegree p <= n
参数：h : coeff p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.min_le`：min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
-/
theorem trailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : trailingDegree p ≤ n :=
  min_le (mem_support_iff.2 h)
/-
**Polynomial.natTrailingDegree_le_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：natTrailingDegree_le_of_ne_zero (h : coeff p n != 0) : natTrailingDegree p
 <= n
参数：h : coeff p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_of_le_natCast`：toNat_le_of_le_natCast {m : Nat∞} {n : Nat}
 (h : m <= n) : toNat m <= n
· 使用定理 `Polynomial.trailingDegree_le_of_ne_zero`：trailingDegree_le_of_ne_zero (h
 : coeff p n != 0) : trailingDegree p <= n
-/
theorem natTrailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : natTrailingDegree p ≤ n :=
  ENat.toNat_le_of_le_natCast <| trailingDegree_le_of_ne_zero h
/-
**Polynomial.coeff_natTrailingDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.coeff p.natTraili
ngDegree = 0 ↔ p = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.min_mem_image_coe`：min_mem_image_coe {s : Finset α} (hs : s.Nonem
pty) : s.min in (s.image (↑) : Finset (WithTop α))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.support_nonempty`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.support.Nonempty ↔ p ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq`：trailingDegree_eq
_iff_natTrailingDegree_eq {p : R[X]} {n : Nat} (hp : p != 0) : p.trailingDegree 
= n ↔ p.natTrailingDegree = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coeff_natTrailingDegree_eq_zero : coeff p p.natTrailingDegree = 0 ↔ p = 0 := by
  constructor
  · rintro h
    by_contra hp
    obtain ⟨n, hpn, hn⟩ := by simpa using min_mem_image_coe <| support_nonempty.2 hp
    obtain rfl := (trailingDegree_eq_iff_natTrailingDegree_eq hp).1 hn.symm
    exact hpn h
  · rintro rfl
    simp
/-
**Polynomial.coeff_natTrailingDegree_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：coeff_natTrailingDegree_ne_zero : coeff p p.natTrailingDegree != 0 ↔ p != 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.coeff_natTrailingDegree_eq_zero`：∀ {R : Type u} [inst : Semir
ing R] {p : Polynomial R}, p.coeff p.natTrailingDegree = 0 ↔ p = 0
-/
lemma coeff_natTrailingDegree_ne_zero : coeff p p.natTrailingDegree ≠ 0 ↔ p ≠ 0 :=
  coeff_natTrailingDegree_eq_zero.not

@[simp]
/-
**Polynomial.trailingDegree_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_eq_zero : trailingDegree p = 0 ↔ coeff p 0 != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.min_eq_bot`：∀ {α : Type u_2} [inst : LinearOrder α] [inst_1 : Ord
erBot α] {s : Finset α}, s.min = ⊥ ↔ ⊥ ∈ s
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
-/
lemma trailingDegree_eq_zero : trailingDegree p = 0 ↔ coeff p 0 ≠ 0 :=
  Finset.min_eq_bot.trans mem_support_iff
/-
**Polynomial.natTrailingDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.natTrailingDegree
 = 0 ↔ p = 0 ∨ p.coeff 0 ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma natTrailingDegree_eq_zero : natTrailingDegree p = 0 ↔ p = 0 ∨ coeff p 0 ≠ 0 := by
  simp [natTrailingDegree, or_comm]
/-
**Polynomial.natTrailingDegree_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_ne_zero : natTrailingDegree p != 0 ↔ p != 0 ∧ coeff p 0 
= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.natTrailingDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R}, p.natTrailingDegree = 0 ↔ p = 0 ∨ p.coeff 0 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma natTrailingDegree_ne_zero : natTrailingDegree p ≠ 0 ↔ p ≠ 0 ∧ coeff p 0 = 0 :=
  natTrailingDegree_eq_zero.not.trans <| by rw [not_or, not_ne_iff]
/-
**Polynomial.trailingDegree_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_ne_zero : trailingDegree p != 0 ↔ coeff p 0 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `Polynomial.trailingDegree_eq_zero`：trailingDegree_eq_zero : trailingDegr
ee p = 0 ↔ coeff p 0 != 0
-/
lemma trailingDegree_ne_zero : trailingDegree p ≠ 0 ↔ coeff p 0 = 0 :=
  trailingDegree_eq_zero.not_left
/-
**Polynomial.trailingDegree_le_trailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R},   q.coeff p.natTr
ailingDegree ≠ 0 → q.trailingDegree ≤ p.trailingDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.trailingDegree_le_of_ne_zero`：trailingDegree_le_of_ne_zero (h
 : coeff p n != 0) : trailingDegree p <= n
· 使用定理 `Polynomial.natTrailingDegree_le_trailingDegree`：natTrailingDegree_le_tra
ilingDegree : ↑(natTrailingDegree p) <= trailingDegree p
-/
@[simp] theorem trailingDegree_le_trailingDegree (h : coeff q (natTrailingDegree p) ≠ 0) :
    trailingDegree q ≤ trailingDegree p :=
  (trailingDegree_le_of_ne_zero h).trans natTrailingDegree_le_trailingDegree
/-
**Polynomial.trailingCoeff_eq_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingCoeff_eq_coeff_zero (h : coeff p 0 != 0) : trailingCoeff p = coeff
 p 0
参数：h : coeff p 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : P
olynomial R), p.trailingCoeff = p.coeff p.natTrailingDegree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natTrailingDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R}, p.natTrailingDegree = 0 ↔ p = 0 ∨ p.coeff 0 ≠ 0
-/
theorem trailingCoeff_eq_coeff_zero (h : coeff p 0 ≠ 0) : trailingCoeff p = coeff p 0 := by
  rw [trailingCoeff, (natTrailingDegree_eq_zero.mpr <| .inr h)]
/-
**Polynomial.trailingDegree_ne_of_natTrailingDegree_ne** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：trailingDegree_ne_of_natTrailingDegree_ne {n : Nat} : p.natTrailingDegree 
!= n -> trailingDegree p != n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p
 : Polynomial R), p.natTrailingDegree = p.trailingDegree.toNat
· 使用定理 `ENat.toNat_natCast`：toNat_natCast (n : Nat) : toNat n = n
-/
theorem trailingDegree_ne_of_natTrailingDegree_ne {n : ℕ} :
    p.natTrailingDegree ≠ n → trailingDegree p ≠ n :=
  mt fun h => by rw [natTrailingDegree, h, ENat.toNat_natCast]
/-
**Polynomial.natTrailingDegree_le_of_trailingDegree_le** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：natTrailingDegree_le_of_trailingDegree_le {n : Nat} {hp : p != 0} (H : (n 
: Nat∞) <= trailingDegree p) : n <= natTrailingDegree p
参数：H : (n : Nat∞) <= trailingDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
-/
theorem natTrailingDegree_le_of_trailingDegree_le {n : ℕ} {hp : p ≠ 0}
    (H : (n : ℕ∞) ≤ trailingDegree p) : n ≤ natTrailingDegree p := by
  rwa [trailingDegree_eq_natTrailingDegree hp, Nat.cast_le] at H
/-
**Polynomial.natTrailingDegree_le_natTrailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：natTrailingDegree_le_natTrailingDegree (hq : q != 0) (hpq : p.trailingDegr
ee <= q.trailingDegree) : p.natTrailingDegree <= q.natTrailingDegree
参数：hq : q != 0；hpq : p.trailingDegree <= q.trailingDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_toNat`：toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n !=
 ⊤) : toNat m <= toNat n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem natTrailingDegree_le_natTrailingDegree (hq : q ≠ 0)
    (hpq : p.trailingDegree ≤ q.trailingDegree) : p.natTrailingDegree ≤ q.natTrailingDegree :=
  ENat.toNat_le_toNat hpq <| by simpa

@[simp]
/-
**Polynomial.trailingDegree_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_monomial (ha : a != 0) : trailingDegree (monomial n a) = n
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : 
Polynomial R), p.trailingDegree = p.support.min
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `Finset.min_singleton`：min_singleton {a : α} : Finset.min {a} = (a : With
Top α)
-/
theorem trailingDegree_monomial (ha : a ≠ 0) : trailingDegree (monomial n a) = n := by
  rw [trailingDegree, support_monomial n ha, min_singleton]
  rfl
/-
**Polynomial.natTrailingDegree_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_monomial (ha : a != 0) : natTrailingDegree (monomial n a
) = n
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p
 : Polynomial R), p.natTrailingDegree = p.trailingDegree.toNat
· 使用定理 `Polynomial.trailingDegree_monomial`：trailingDegree_monomial (ha : a != 0
) : trailingDegree (monomial n a) = n
-/
theorem natTrailingDegree_monomial (ha : a ≠ 0) : natTrailingDegree (monomial n a) = n := by
  rw [natTrailingDegree, trailingDegree_monomial ha]
  rfl
/-
**Polynomial.natTrailingDegree_monomial_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) <= n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natTrailingDegree_monomial`：natTrailingDegree_monomial (ha : 
a != 0) : natTrailingDegree (monomial n a) = n
-/
theorem natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) ≤ n :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le
/-
**Polynomial.le_trailingDegree_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_trailingDegree_monomial : ↑n <= trailingDegree (monomial n a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Polynomial.trailingDegree_monomial`：trailingDegree_monomial (ha : a != 0
) : trailingDegree (monomial n a) = n
-/
theorem le_trailingDegree_monomial : ↑n ≤ trailingDegree (monomial n a) :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge

@[simp]
/-
**Polynomial.trailingDegree_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_C (ha : a != 0) : trailingDegree (C a) = (0 : Nat∞)
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.trailingDegree_monomial`：trailingDegree_monomial (ha : a != 0
) : trailingDegree (monomial n a) = n
-/
theorem trailingDegree_C (ha : a ≠ 0) : trailingDegree (C a) = (0 : ℕ∞) :=
  trailingDegree_monomial ha
/-
**Polynomial.le_trailingDegree_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_trailingDegree_C : (0 : Nat∞) <= trailingDegree (C a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.le_trailingDegree_monomial`：le_trailingDegree_monomial : ↑n <
= trailingDegree (monomial n a)
-/
theorem le_trailingDegree_C : (0 : ℕ∞) ≤ trailingDegree (C a) :=
  le_trailingDegree_monomial
/-
**Polynomial.trailingDegree_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_one_le : (0 : Nat∞) <= trailingDegree (1 : R[X])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.le_trailingDegree_C`：le_trailingDegree_C : (0 : Nat∞) <= trai
lingDegree (C a)
-/
theorem trailingDegree_one_le : (0 : ℕ∞) ≤ trailingDegree (1 : R[X]) := by
  rw [← C_1]
  exact le_trailingDegree_C

@[simp]
/-
**Polynomial.natTrailingDegree_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_C (a : R) : natTrailingDegree (C a) = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.natTrailingDegree_monomial_le`：natTrailingDegree_monomial_le 
: natTrailingDegree (monomial n a) <= n
-/
theorem natTrailingDegree_C (a : R) : natTrailingDegree (C a) = 0 :=
  nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le

@[simp]
/-
**Polynomial.natTrailingDegree_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_one : natTrailingDegree (1 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_C`：natTrailingDegree_C (a : R) : natTrailin
gDegree (C a) = 0
-/
theorem natTrailingDegree_one : natTrailingDegree (1 : R[X]) = 0 :=
  natTrailingDegree_C 1

@[simp]
/-
**Polynomial.natTrailingDegree_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_natCast (n : Nat) : natTrailingDegree (n : R[X]) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree_C`：natTrailingDegree_C (a : R) : natTrailin
gDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natTrailingDegree_natCast (n : ℕ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, natTrailingDegree_C]

@[simp]
/-
**Polynomial.trailingDegree_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_C_mul_X_pow (n : Nat) (ha : a != 0) : trailingDegree (C a *
 X ^ n) = n
参数：n : Nat；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.trailingDegree_monomial`：trailingDegree_monomial (ha : a != 0
) : trailingDegree (monomial n a) = n
-/
theorem trailingDegree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : trailingDegree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, trailingDegree_monomial ha]
/-
**Polynomial.le_trailingDegree_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：le_trailingDegree_C_mul_X_pow (n : Nat) (a : R) : (n : Nat∞) <= trailingDe
gree (C a * X ^ n)
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.le_trailingDegree_monomial`：le_trailingDegree_monomial : ↑n <
= trailingDegree (monomial n a)
-/
theorem le_trailingDegree_C_mul_X_pow (n : ℕ) (a : R) :
    (n : ℕ∞) ≤ trailingDegree (C a * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailingDegree_monomial
/-
**Polynomial.coeff_eq_zero_of_lt_trailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：coeff_eq_zero_of_lt_trailingDegree (h : (n : Nat∞) < trailingDegree p) : c
oeff p n = 0
参数：h : (n : Nat∞) < trailingDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.trailingDegree_le_of_ne_zero`：trailingDegree_le_of_ne_zero (h
 : coeff p n != 0) : trailingDegree p <= n
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem coeff_eq_zero_of_lt_trailingDegree (h : (n : ℕ∞) < trailingDegree p) : coeff p n = 0 :=
  Classical.not_not.1 (mt trailingDegree_le_of_ne_zero (not_le_of_gt h))
/-
**Polynomial.coeff_eq_zero_of_lt_natTrailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : Nat} (h : n < p.natT
railingDegree) : p.coeff n = 0
参数：h : n < p.natTrailingDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_lt_trailingDegree`：coeff_eq_zero_of_lt_trail
ingDegree (h : (n : Nat∞) < trailingDegree p) : coeff p n = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingDegree_zero`：trailingDegree_zero : trailingDegree (0 
: R[X]) = ⊤
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
-/
theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_lt_trailingDegree
  by_cases hp : p = 0
  · rw [hp, trailingDegree_zero]
    exact WithTop.coe_lt_top n
  · rw [trailingDegree_eq_natTrailingDegree hp]
    exact WithTop.coe_lt_coe.2 h

@[simp]
/-
**Polynomial.coeff_natTrailingDegree_pred_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : Nat∞) < natTrai
lingDegree p} : p.coeff (p.natTrailingDegree - 1) = 0
参数：0 : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`：coeff_eq_zero_of_lt_na
tTrailingDegree {p : R[X]} {n : Nat} (h : n < p.natTrailingDegree) : p.coeff n =
 0
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_pos`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α] {a : α},
 0 < ↑a ↔ 0 < a
-/
theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : ℕ∞) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
  coeff_eq_zero_of_lt_natTrailingDegree <|
    Nat.sub_lt (WithTop.coe_pos.mp hp) Nat.one_pos
/-
**Polynomial.le_trailingDegree_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_trailingDegree_X_pow (n : Nat) : (n : Nat∞) <= trailingDegree (X ^ n : 
R[X])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.le_trailingDegree_C_mul_X_pow`：le_trailingDegree_C_mul_X_pow 
(n : Nat) (a : R) : (n : Nat∞) <= trailingDegree (C a * X ^ n)
-/
theorem le_trailingDegree_X_pow (n : ℕ) : (n : ℕ∞) ≤ trailingDegree (X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using le_trailingDegree_C_mul_X_pow n (1 : R)
/-
**Polynomial.le_trailingDegree_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_trailingDegree_X : (1 : Nat∞) <= trailingDegree (X : R[X])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.le_trailingDegree_monomial`：le_trailingDegree_monomial : ↑n <
= trailingDegree (monomial n a)
-/
theorem le_trailingDegree_X : (1 : ℕ∞) ≤ trailingDegree (X : R[X]) :=
  le_trailingDegree_monomial
/-
**Polynomial.natTrailingDegree_X_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_X_le : (X : R[X]).natTrailingDegree <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_monomial_le`：natTrailingDegree_monomial_le 
: natTrailingDegree (monomial n a) <= n
-/
theorem natTrailingDegree_X_le : (X : R[X]).natTrailingDegree ≤ 1 :=
  natTrailingDegree_monomial_le

@[simp]
/-
**Polynomial.trailingCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingCoeff_eq_zero : trailingCoeff p = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Finset.mem_of_min`：mem_of_min {s : Finset α} : forall {a : α}, s.min = a
 -> a in s
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem trailingCoeff_eq_zero : trailingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    _root_.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩
/-
**Polynomial.trailingCoeff_nonzero_iff_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：trailingCoeff_nonzero_iff_nonzero : trailingCoeff p != 0 ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.trailingCoeff_eq_zero`：trailingCoeff_eq_zero : trailingCoeff 
p = 0 ↔ p = 0
-/
theorem trailingCoeff_nonzero_iff_nonzero : trailingCoeff p ≠ 0 ↔ p ≠ 0 :=
  not_congr trailingCoeff_eq_zero
/-
**Polynomial.natTrailingDegree_mem_support_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：natTrailingDegree_mem_support_of_nonzero : p != 0 -> natTrailingDegree p i
n p.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Polynomial.trailingCoeff_nonzero_iff_nonzero`：trailingCoeff_nonzero_iff_
nonzero : trailingCoeff p != 0 ↔ p != 0
-/
theorem natTrailingDegree_mem_support_of_nonzero : p ≠ 0 → natTrailingDegree p ∈ p.support :=
  mem_support_iff.mpr ∘ trailingCoeff_nonzero_iff_nonzero.mpr
/-
**Polynomial.natTrailingDegree_le_of_mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：natTrailingDegree_le_of_mem_supp (a : Nat) : a in p.support -> natTrailing
Degree p <= a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
-/
theorem natTrailingDegree_le_of_mem_supp (a : ℕ) : a ∈ p.support → natTrailingDegree p ≤ a :=
  natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp
/-
**Polynomial.natTrailingDegree_eq_support_min'** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：natTrailingDegree_eq_support_min' (h : p != 0) : natTrailingDegree p = p.s
upport.min' (nonempty_support_iff.mpr h)
参数：h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.nonempty_support_iff`：nonempty_support_iff : p.support.Nonemp
ty ↔ p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p
 : Polynomial R), p.natTrailingDegree = p.trailingDegree.toNat
· 使用定理 `Polynomial.trailingDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : 
Polynomial R), p.trailingDegree = p.support.min
· 使用定理 `Polynomial.support_nonempty`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.support.Nonempty ↔ p ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_min'`：coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs
) = s.min
-/
theorem natTrailingDegree_eq_support_min' (h : p ≠ 0) :
    natTrailingDegree p = p.support.min' (nonempty_support_iff.mpr h) := by
  rw [natTrailingDegree, trailingDegree, ← Finset.coe_min' (support_nonempty.mpr h)]
  norm_cast
/-
**Polynomial.le_natTrailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_natTrailingDegree (hp : p != 0) (hn : forall m < n, p.coeff m = 0) : n 
<= p.natTrailingDegree
参数：hp : p != 0；hn : forall m < n, p.coeff m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.nonempty_support_iff`：nonempty_support_iff : p.support.Nonemp
ty ↔ p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree_eq_support_min'`：natTrailingDegree_eq_suppo
rt_min' (h : p != 0) : natTrailingDegree p = p.support.min' (nonempty_support_if
f.mpr h)
· 使用定理 `Finset.le_min'`：le_min' (x) (H2 : forall y in s, x <= y) : x <= s.min' H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
-/
theorem le_natTrailingDegree (hp : p ≠ 0) (hn : ∀ m < n, p.coeff m = 0) :
    n ≤ p.natTrailingDegree := by
  rw [natTrailingDegree_eq_support_min' hp]
  exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm <| hn _ hmn
/-
**Polynomial.natTrailingDegree_le_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree <= p.natDe
gree
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Polynomial.natTrailingDegree_zero`：natTrailingDegree_zero : natTrailingD
egree (0 : R[X]) = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.trailingCoeff_eq_zero`：trailingCoeff_eq_zero : trailingCoeff 
p = 0 ↔ p = 0
-/
theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero, natTrailingDegree_zero]
  · exact le_natDegree_of_ne_zero (mt trailingCoeff_eq_zero.mp hp)
/-
**Polynomial.natTrailingDegree_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_mul_X_pow {p : R[X]} (hp : p != 0) (n : Nat) : (p * X ^ 
n).natTrailingDegree = p.natTrailingDegree + n
参数：hp : p != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.trailingCoeff_eq_zero`：trailingCoeff_eq_zero : trailingCoeff 
p = 0 ↔ p = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : P
olynomial R), p.trailingCoeff = p.coeff p.natTrailingDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_mul_X_pow`：coeff_mul_X_pow (p : R[X]) (n d : Nat) : coe
ff (p * Polynomial.X ^ n) (d + n) = coeff p d
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.nonempty_support_iff`：nonempty_support_iff : p.support.Nonemp
ty ↔ p != 0
· 使用定理 `Polynomial.mul_X_pow_eq_zero`：mul_X_pow_eq_zero {p : R[X]} {n : Nat} (H 
: p * X ^ n = 0) : p = 0
· 使用定理 `Polynomial.natTrailingDegree_eq_support_min'`：natTrailingDegree_eq_suppo
rt_min' (h : p != 0) : natTrailingDegree p = p.support.min' (nonempty_support_if
f.mpr h)
· 使用定理 `Finset.le_min'_iff`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset 
α) (H : s.Nonempty) {x : α}, x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Polynomial.coeff_mul_X_pow'`：coeff_mul_X_pow' (p : R[X]) (n d : Nat) : (
p * X ^ n).coeff d = ite (n <= d) (p.coeff (d - n)) 0
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_tsub_iff_right`：le_tsub_iff_right (h : a <= c) : b <= c - a ↔ b + a <
= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem natTrailingDegree_mul_X_pow {p : R[X]} (hp : p ≠ 0) (n : ℕ) :
    (p * X ^ n).natTrailingDegree = p.natTrailingDegree + n := by
  apply le_antisymm
  · refine natTrailingDegree_le_of_ne_zero fun h => mt trailingCoeff_eq_zero.mp hp ?_
    rwa [trailingCoeff, ← coeff_mul_X_pow]
  · rw [natTrailingDegree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    exact (le_tsub_iff_right key).mp (natTrailingDegree_le_of_ne_zero hy)
/-
**Polynomial.le_trailingDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_trailingDegree_mul : p.trailingDegree + q.trailingDegree <= (p * q).tra
ilingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_min`：∀ {α : Type u_2} [inst : LinearOrder α] {m : WithTop α} {
s : Finset α}, (∀ a ∈ s, m ≤ ↑a) → m ≤ s.min
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.min_le`：min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
-/
theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree := by
  refine Finset.le_min fun n hn => ?_
  rw [mem_support_iff, coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans_eq ?_
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← mem_antidiagonal]
/-
**Polynomial.le_natTrailingDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_natTrailingDegree_mul (h : p * q != 0) : p.natTrailingDegree + q.natTra
ilingDegree <= (p * q).natTrailingDegree
参数：h : p * q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
· 使用定理 `Polynomial.le_trailingDegree_mul`：le_trailingDegree_mul : p.trailingDegr
ee + q.trailingDegree <= (p * q).trailingDegree
-/
theorem le_natTrailingDegree_mul (h : p * q ≠ 0) :
    p.natTrailingDegree + q.natTrailingDegree ≤ (p * q).natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, mul_zero])
  rw [← ENat.natCast_le_natCast, ENat.natCast_add, ← trailingDegree_eq_natTrailingDegree hp,
    ← trailingDegree_eq_natTrailingDegree hq, ← trailingDegree_eq_natTrailingDegree h]
  exact le_trailingDegree_mul
/-
**Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial`。
形式化陈述：coeff_mul_natTrailingDegree_add_natTrailingDegree : (p * q).coeff (p.natTr
ailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`：coeff_eq_zero_of_lt_na
tTrailingDegree {p : R[X]} {n : Nat} (h : n < p.natTrailingDegree) : p.coeff n =
 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_add_iff_eq_and_eq`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Part
ialOrder α] [AddLeftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a ≤ c 
→ b ≤ d → (a +…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
-/
theorem coeff_mul_natTrailingDegree_add_natTrailingDegree : (p * q).coeff
    (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff := by
  rw [coeff_mul]
  refine
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) ?_ fun h =>
      (h (mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [mem_antidiagonal] at h₁
  by_cases! hi : i < p.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  by_cases! hj : j < q.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  refine (h₂ (Prod.ext_iff.mpr ?_).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm
/-
**Polynomial.trailingDegree_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff != 0) : (p * q)
.trailingDegree = p.trailingDegree + q.trailingDegree
参数：h : p.trailingCoeff * q.trailingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingCoeff_zero`：trailingCoeff_zero : trailingCoeff (0 : R
[X]) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `Polynomial.trailingDegree_le_of_ne_zero`：trailingDegree_le_of_ne_zero (h
 : coeff p n != 0) : trailingDegree p <= n
· 使用定理 `Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree`：coeff_mul_
natTrailingDegree_add_natTrailingDegree : (p * q).coeff (p.natTrailingDegree + q
.natTrailingDegree) = p.trailingCoeff * q.trailing…
· 使用定理 `Polynomial.le_trailingDegree_mul`：le_trailingDegree_mul : p.trailingDegr
ee + q.trailingDegree <= (p * q).trailingDegree
-/
theorem trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  refine le_antisymm ?_ le_trailingDegree_mul
  rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq, ←
    ENat.natCast_add]
  apply trailingDegree_le_of_ne_zero
  rwa [coeff_mul_natTrailingDegree_add_natTrailingDegree]
/-
**Polynomial.natTrailingDegree_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff != 0) : (p *
 q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree
参数：h : p.trailingCoeff * q.trailingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingCoeff_zero`：trailingCoeff_zero : trailingCoeff (0 : R
[X]) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some`：natTrailingDe
gree_eq_of_trailingDegree_eq_some {p : R[X]} {n : Nat} (h : trailingDegree p = n
) : natTrailingDegree p = n
· 使用定理 `Polynomial.trailingDegree_mul'`：trailingDegree_mul' (h : p.trailingCoeff
 * q.trailingCoeff != 0) : (p * q).trailingDegree = p.trailingDegree + q.trailin
gDegree
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
-/
theorem natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  apply natTrailingDegree_eq_of_trailingDegree_eq_some
  rw [trailingDegree_mul' h, ENat.natCast_add, ← trailingDegree_eq_natTrailingDegree hp,
    ← trailingDegree_eq_natTrailingDegree hq]
/-
**Polynomial.natTrailingDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_mul [NoZeroDivisors R] (hp : p != 0) (hq : q != 0) : (p 
* q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree
参数：hp : p != 0；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_mul'`：natTrailingDegree_mul' (h : p.trailin
gCoeff * q.trailingCoeff != 0) : (p * q).natTrailingDegree = p.natTrailingDegree
 + q.natTrailingDegree
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.trailingCoeff_eq_zero`：trailingCoeff_eq_zero : trailingCoeff 
p = 0 ↔ p = 0
-/
theorem natTrailingDegree_mul [NoZeroDivisors R] (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree :=
  natTrailingDegree_mul'
    (mul_ne_zero (mt trailingCoeff_eq_zero.mp hp) (mt trailingCoeff_eq_zero.mp hq))

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
/-
**Polynomial.trailingDegree_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_one : trailingDegree (1 : R[X]) = (0 : Nat∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.trailingDegree_C`：trailingDegree_C (ha : a != 0) : trailingDe
gree (C a) = (0 : Nat∞)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem trailingDegree_one : trailingDegree (1 : R[X]) = (0 : ℕ∞) :=
  trailingDegree_C one_ne_zero

@[simp]
/-
**Polynomial.trailingDegree_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_X : trailingDegree (X : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.trailingDegree_monomial`：trailingDegree_monomial (ha : a != 0
) : trailingDegree (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem trailingDegree_X : trailingDegree (X : R[X]) = 1 :=
  trailingDegree_monomial one_ne_zero

@[simp]
/-
**Polynomial.natTrailingDegree_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_X : (X : R[X]).natTrailingDegree = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_monomial`：natTrailingDegree_monomial (ha : 
a != 0) : natTrailingDegree (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem natTrailingDegree_X : (X : R[X]).natTrailingDegree = 1 :=
  natTrailingDegree_monomial one_ne_zero

@[simp]
/-
**Polynomial.trailingDegree_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_X_pow (n : Nat) : (X ^ n : R[X]).trailingDegree = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.trailingDegree_monomial`：trailingDegree_monomial (ha : a != 0
) : trailingDegree (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma trailingDegree_X_pow (n : ℕ) :
    (X ^ n : R[X]).trailingDegree = n := by
  rw [X_pow_eq_monomial, trailingDegree_monomial one_ne_zero]

@[simp]
/-
**Polynomial.natTrailingDegree_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_X_pow (n : Nat) : (X ^ n : R[X]).natTrailingDegree = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.natTrailingDegree_monomial`：natTrailingDegree_monomial (ha : 
a != 0) : natTrailingDegree (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma natTrailingDegree_X_pow (n : ℕ) :
    (X ^ n : R[X]).natTrailingDegree = n := by
  rw [X_pow_eq_monomial, natTrailingDegree_monomial one_ne_zero]

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
/-
**Polynomial.trailingDegree_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_neg`：support_neg {p : R[X]} : (-p).support = p.suppor
t
-/
theorem trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailingDegree
  rw [support_neg]

@[simp]
/-
**Polynomial.natTrailingDegree_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDeg
ree p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingDegree_neg`：trailingDegree_neg (p : R[X]) : trailingD
egree (-p) = trailingDegree p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [natTrailingDegree]

@[simp]
/-
**Polynomial.natTrailingDegree_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_intCast (n : Int) : natTrailingDegree (n : R[X]) = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree_C`：natTrailingDegree_C (a : R) : natTrailin
gDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natTrailingDegree_intCast (n : ℤ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_intCast, natTrailingDegree_C]

end Ring

section Semiring

variable [Semiring R]

/-- The second-lowest coefficient, or 0 for constants -/
/-
**Polynomial.nextCoeffUp** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：nextCoeffUp (p : R[X]) : R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second-lowest coefficient, or 0 for constants
-/
def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)
/-
**Polynomial.nextCoeffUp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R], Polynomial.nextCoeffUp 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nextCoeffUp_zero : nextCoeffUp (0 : R[X]) = 0 := by simp [nextCoeffUp]

@[simp]
/-
**Polynomial.nextCoeffUp_C_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeffUp_C_eq_zero (c : R) : nextCoeffUp (C c) = 0
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nextCoeffUp.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Pol
ynomial R),   p.nextCoeffUp = if p.natTrailingDegree = 0 then 0 else p.coeff (p.
natTrailingDegree…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Polynomial.natTrailingDegree_C`：natTrailingDegree_C (a : R) : natTrailin
gDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nextCoeffUp_C_eq_zero (c : R) : nextCoeffUp (C c) = 0 := by
  rw [nextCoeffUp]
  simp
/-
**Polynomial.nextCoeffUp_of_constantCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：nextCoeffUp_of_constantCoeff_eq_zero (p : R[X]) (hp : coeff p 0 = 0) : nex
tCoeffUp p = p.coeff (p.natTrailingDegree + 1)
参数：p : R[X]；hp : coeff p 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nextCoeffUp_zero`：∀ {R : Type u} [inst : Semiring R], Polynom
ial.nextCoeffUp 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.nextCoeffUp.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Pol
ynomial R),   p.nextCoeffUp = if p.natTrailingDegree = 0 then 0 else p.coeff (p.
natTrailingDegree…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.natTrailingDegree_ne_zero`：natTrailingDegree_ne_zero : natTra
ilingDegree p != 0 ↔ p != 0 ∧ coeff p 0 = 0
-/
theorem nextCoeffUp_of_constantCoeff_eq_zero (p : R[X]) (hp : coeff p 0 = 0) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  · rw [nextCoeffUp, if_neg (natTrailingDegree_ne_zero.2 ⟨hp₀, hp⟩)]

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]}

/-
**Polynomial.coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt** 是 Mathlib 中的
一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt (h : trailingDegree p
 < trailingDegree q) : coeff q (natTrailingDegree p) = 0
参数：h : trailingDegree p < trailingDegree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_lt_trailingDegree`：coeff_eq_zero_of_lt_trail
ingDegree (h : (n : Nat∞) < trailingDegree p) : coeff p n = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.natTrailingDegree_le_trailingDegree`：natTrailingDegree_le_tra
ilingDegree : ↑(natTrailingDegree p) <= trailingDegree p
-/
theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : trailingDegree p < trailingDegree q) : coeff q (natTrailingDegree p) = 0 :=
  coeff_eq_zero_of_lt_trailingDegree <| natTrailingDegree_le_trailingDegree.trans_lt h
/-
**Polynomial.ne_zero_of_trailingDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：ne_zero_of_trailingDegree_lt {n : Nat∞} (h : trailingDegree p < n) : p != 
0
参数：h : trailingDegree p < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ne_zero_of_trailingDegree_lt {n : ℕ∞} (h : trailingDegree p < n) : p ≠ 0 := fun h₀ =>
  h.not_ge (by simp [h₀])
/-
**Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero** 是 Mathlib 中的一个
引理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (h : constantCoeff p !=
 0) : p.natTrailingDegree = 0
参数：h : constantCoeff p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_nonpos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [ins
t_1 : Zero α] [IsBotZeroClass α], a ≤ 0 → a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
-/
lemma natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (h : constantCoeff p ≠ 0) :
    p.natTrailingDegree = 0 :=
  eq_zero_of_nonpos (natTrailingDegree_le_of_ne_zero h)

namespace Monic

/-
**Polynomial.Monic.eq_X_pow_iff_natDegree_le_natTrailingDegree** 是 Mathlib 中的一个引
理，位于命名空间 `Polynomial.Monic`。
形式化陈述：eq_X_pow_iff_natDegree_le_natTrailingDegree (h₁ : p.Monic) : p = X ^ p.nat
Degree ↔ p.natDegree <= p.natTrailingDegree
参数：h₁ : p.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Polynomial.natTrailingDegree_X_pow`：natTrailingDegree_X_pow (n : Nat) : 
(X ^ n : R[X]).natTrailingDegree = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`：coeff_eq_zero_of_lt_na
tTrailingDegree {p : R[X]} {n : Nat} (h : n < p.natTrailingDegree) : p.coeff n =
 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
-/
lemma eq_X_pow_iff_natDegree_le_natTrailingDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natDegree ≤ p.natTrailingDegree := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · nontriviality R
    rw [h, natTrailingDegree_X_pow, ← h]
  · ext n
    rw [coeff_X_pow]
    obtain hn | rfl | hn := lt_trichotomy n p.natDegree
    · rw [if_neg hn.ne, coeff_eq_zero_of_lt_natTrailingDegree (hn.trans_le h)]
    · simpa only [if_pos rfl] using! h₁.leadingCoeff
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt hn]
/-
**Polynomial.Monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree** 是 Mathlib 中的一个引
理，位于命名空间 `Polynomial.Monic`。
形式化陈述：eq_X_pow_iff_natTrailingDegree_eq_natDegree (h₁ : p.Monic) : p = X ^ p.nat
Degree ↔ p.natTrailingDegree = p.natDegree
参数：h₁ : p.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Polynomial.Monic.eq_X_pow_iff_natDegree_le_natTrailingDegree`：eq_X_pow_i
ff_natDegree_le_natTrailingDegree (h₁ : p.Monic) : p = X ^ p.natDegree ↔ p.natDe
gree <= p.natTrailingDegree
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `Polynomial.natTrailingDegree_le_natDegree`：natTrailingDegree_le_natDegre
e (p : R[X]) : p.natTrailingDegree <= p.natDegree
-/
lemma eq_X_pow_iff_natTrailingDegree_eq_natDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natTrailingDegree = p.natDegree :=
  h₁.eq_X_pow_iff_natDegree_le_natTrailingDegree.trans (natTrailingDegree_le_natDegree p).ge_iff_eq

end Monic

end Semiring

end Polynomial

