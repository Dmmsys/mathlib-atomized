/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Multiplicity

/-!
# Division of univariate polynomials

The main defs are `divByMonic` and `modByMonic`.
The compatibility between these is given by `modByMonic_add_div`.
We also define `rootMultiplicity`.
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R]

/-
**Polynomial.X_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_X_mul_zero`：coeff_X_mul_zero (p : R[X]) : coeff (X * p)
 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.X_mul_divX_add`：X_mul_divX_add (p : R[X]) : X * divX p + C (p
.coeff 0) = p
-/
theorem X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0 :=
  ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩
/-
**Polynomial.X_pow_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_dvd_iff {f : R[X]} {n : Nat} : X ^ n ∣ f ↔ forall d < n, f.coeff d =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_X_pow_mul'`：coeff_X_pow_mul' (p : R[X]) (n d : Nat) : (
X ^ n * p).coeff d = ite (n <= d) (p.coeff (d - n)) 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Polynomial.coeff_X_pow_mul`：coeff_X_pow_mul (p : R[X]) (n d : Nat) : coe
ff (Polynomial.X ^ n * p) (d + n) = coeff p d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.X_dvd_iff`：X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem X_pow_dvd_iff {f : R[X]} {n : ℕ} : X ^ n ∣ f ↔ ∀ d < n, f.coeff d = 0 :=
  ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_gt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with
    | zero => simp [pow_zero]
    | succ n hn =>
      obtain ⟨g, hgf⟩ := hn fun d : ℕ => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      have := coeff_X_pow_mul g n 0
      rw [zero_add, ← hgf, hd n (Nat.lt_succ_self n)] at this
      obtain ⟨k, hgk⟩ := Polynomial.X_dvd_iff.mpr this.symm
      use k
      rwa [pow_succ, mul_assoc, ← hgk]⟩

variable {p q : R[X]}
/-
**Polynomial.finiteMultiplicity_of_degree_pos_of_monic** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：finiteMultiplicity_of_degree_pos_of_monic (hp : (0 : WithBot Nat) < degree
 p) (hmp : Monic p) (hq : q != 0) : FiniteMultiplicity p q
参数：hp : (0 : WithBot Nat) < degree p；hmp : Monic p；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `lt_add_of_le_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddLeftStrictMono α] {a b c : α},   b ≤ c → 0 < a → b < c + a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
（共 35 条，此处仅展示前 30 条）
-/
theorem finiteMultiplicity_of_degree_pos_of_monic (hp : (0 : WithBot ℕ) < degree p) (hmp : Monic p)
    (hq : q ≠ 0) : FiniteMultiplicity p q :=
  have zn0 : (0 : R) ≠ 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p ≠ 0 := fun hp0 => by simp [hp0] at hp
    have hr0 : r ≠ 0 := fun hr0 => by subst hr0; simp [hq] at hr
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 := by simp [show _ = _ from hmp]
    have hpn0' : leadingCoeff p ^ (natDegree q + 1) ≠ 0 := hpn1.symm ▸ zn0.symm
    have hpnr0 : leadingCoeff (p ^ (natDegree q + 1)) * leadingCoeff r ≠ 0 := by
      simp only [leadingCoeff_pow' hpn0', leadingCoeff_eq_zero, hpn1, one_mul, Ne,
          hr0, not_false_eq_true]
    have hnp : 0 < natDegree p := Nat.cast_lt.1 <| by
      rw [← degree_eq_natDegree hp0]; exact hp
    have := congr_arg natDegree hr
    rw [natDegree_mul' hpnr0, natDegree_pow' hpn0', add_mul, add_assoc] at this
    exact
      ne_of_lt
        (lt_add_of_le_of_pos (le_mul_of_one_le_right (Nat.zero_le _) hnp)
          (add_pos_of_pos_of_nonneg (by rwa [one_mul]) (Nat.zero_le _)))
        this⟩

/-- See `Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le`
for the other multiplication order. That version, unlike this one, requires commutativity. -/
/-
**Polynomial.eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le** 是 Mathlib 中的一
个引理，位于命名空间 `Polynomial`。
形式化陈述：eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.M
onic) (hdvd : p ∣ q) (hdeg : q.natDegree <= p.natDegree) : q = p * C q.leadingCo
eff
参数：hp : p.Monic；hdvd : p ∣ q；hdeg : q.natDegree <= p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.natDegree_mul'`：∀ {R : Type u} [inst : Semiring R] {p q
 : Polynomial R}, p.Monic → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegre
e
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.leadingCoeff_monic_mul`：leadingCoeff_monic_mul {p q : R[X]} (
hp : Monic p) : leadingCoeff (p * q) = leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a

--- 原说明 ---
See `Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le`
for the other multiplication order. That version, unlike this one, requires comm
utativity.
-/
lemma eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = p * C q.leadingCoeff := by
  obtain ⟨r, rfl⟩ := hdvd
  obtain rfl | hr := eq_or_ne r 0
  · simp
  have : r.natDegree = 0 := by simpa [hp.natDegree_mul' hr] using hdeg
  rw [eq_C_of_natDegree_eq_zero this]
  simp [leadingCoeff_monic_mul hp]
/-
**Polynomial.eq_of_monic_of_dvd_of_natDegree_le** 是 Mathlib 中的一个引理，位于命名空间 `Polyn
omial`。
形式化陈述：eq_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic) (hq : q.Mon
ic) (hdvd : p ∣ q) (hdeg : q.natDegree <= p.natDegree) : q = p
参数：hp : p.Monic；hq : q.Monic；hdvd : p ∣ q；hdeg : q.natDegree <= p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le`：eq_mul_l
eadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic) (hdvd : 
p ∣ q) (hdeg : q.natDegree <= p.natDegree) : q = p *…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p := by
  rw [eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]
  simp [hq]

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

/-
**Polynomial.div_wf_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：div_wf_lemma (h : degree q <= degree p ∧ p != 0) (hq : Monic q) : degree (
p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) < degree p
参数：h : degree q <= degree p ∧ p != 0；hq : Monic q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.Monic.ne_zero_of_polynomial_ne`：∀ {R : Type u} [inst : Semiri
ng R] {p q r : Polynomial R}, p.Monic → q ≠ r → p ≠ 0
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.degree_sub_lt_left`：degree_sub_lt_left (hd : degree p = degre
e q) (hp0 : p != 0) (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < d
egree p
· 使用定理 `Polynomial.Monic.degree_mul_comm`：degree_mul_comm (hp : p.Monic) (q : R[
X]) : (p * q).degree = (q * p).degree
· 使用定理 `Polynomial.Monic.degree_mul`：∀ {R : Type u} [inst : Semiring R] {p q : P
olynomial R}, q.Monic → (p * q).degree = p.degree + q.degree
· 使用定理 `Polynomial.degree_C_mul_X_pow`：degree_C_mul_X_pow (n : Nat) (ha : a != 0
) : degree (C a * X ^ n) = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Polynomial.leadingCoeff_monic_mul`：leadingCoeff_monic_mul {p q : R[X]} (
hp : Monic p) : leadingCoeff (p * q) = leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_mul_X_pow`：leadingCoeff_mul_X_pow {p : R[X]} {n 
: Nat} : leadingCoeff (p * X ^ n) = leadingCoeff p
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : Monic q) :
    degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) < degree p :=
  have hp : leadingCoeff p ≠ 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q ≤ natDegree p :=
    (Nat.cast_le (α := WithBot ℕ)).1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt_left
    (by
      rw [hq.degree_mul_comm, hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_natDegree h.2,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt])
    h.2 (by rw [leadingCoeff_monic_mul hq, leadingCoeff_mul_X_pow, leadingCoeff_C])

/-- See `divByMonic`. -/
/-
**Polynomial.divModByMonicAux** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：divModByMonicAux : forall (_p : R[X]) {q : R[X]}, Monic q -> R[X] × R[X] |
 p, q, hq => letI
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `divByMonic`.
-/
noncomputable def divModByMonicAux : ∀ (_p : R[X]) {q : R[X]}, Monic q → R[X] × R[X]
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p

/-- `divByMonic`, denoted as `p /ₘ q`, gives the quotient of `p` by a monic polynomial `q`. -/
/-
**Polynomial.divByMonic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：divByMonic (p q : R[X]) : R[X]
参数：p q : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`divByMonic`, denoted as `p /ₘ q`, gives the quotient of `p` by a monic polynomi
al `q`.
-/
def divByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0

/-- `modByMonic`, denoted as `p  %ₘ q`, gives the remainder of `p` by a monic polynomial `q`. -/
/-
**Polynomial.modByMonic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：modByMonic (p q : R[X]) : R[X]
参数：p q : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`modByMonic`, denoted as `p  %ₘ q`, gives the remainder of `p` by a monic polyno
mial `q`.
-/
def modByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic
/-
**Polynomial.degree_modByMonic_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_modByMonic_lt [Nontrivial R] : forall (p : R[X]) {q : R[X]} (_hq : 
Monic q), degree (p %ₘ q) < degree q | p, q, hq => letI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_modByMonic_lt._unary`：∀ {R : Type u} [inst : Ring R] [
Nontrivial R] (_x : (_ : Polynomial R) ×' (q : Polynomial R) ×' q.Monic),   (_x.
1 %ₘ _x.2.1).degree < _x.2.1…
-/
theorem degree_modByMonic_lt [Nontrivial R] :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then by
      have _wf := div_wf_lemma ⟨h.1, h.2⟩ hq
      have :=
        degree_modByMonic_lt (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) hq
      grind [divModByMonicAux, modByMonic]
    else
      Or.casesOn (not_and_or.1 h)
        (by
          unfold modByMonic divModByMonicAux
          dsimp
          rw [dif_pos hq, if_neg h]
          exact lt_of_not_ge)
        (by
          intro hp
          unfold modByMonic divModByMonicAux
          dsimp
          rw [dif_pos hq, if_neg h, Classical.not_not.1 hp]
          exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 hq.ne_zero)))
  termination_by p => p
/-
**Polynomial.natDegree_modByMonic_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_modByMonic_lt (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q != 1
) : natDegree (p %ₘ q) < q.natDegree
参数：p : R[X]；hmq : Monic q；hq : q != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Polynomial.eq_one_of_monic_natDegree_zero`：eq_one_of_monic_natDegree_zer
o (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `Polynomial.natDegree_lt_natDegree`：natDegree_lt_natDegree {q : S[X]} (hp
 : p != 0) (hpq : p.degree < q.degree) : p.natDegree < q.natDegree
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
-/
theorem natDegree_modByMonic_lt (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q ≠ 1) :
    natDegree (p %ₘ q) < q.natDegree := by
  by_cases hpq : p %ₘ q = 0
  · rw [hpq, natDegree_zero, Nat.pos_iff_ne_zero]
    contrapose hq
    exact eq_one_of_monic_natDegree_zero hmq hq
  · have := Nontrivial.of_polynomial_ne hpq
    exact natDegree_lt_natDegree hpq (degree_modByMonic_lt p hmq)

@[simp]
/-
**Polynomial.zero_modByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：zero_modByMonic (p : R[X]) : 0 %ₘ p = 0
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_modByMonic (p : R[X]) : 0 %ₘ p = 0 := by
  grind [modByMonic, divModByMonicAux]

@[simp]
/-
**Polynomial.zero_divByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：zero_divByMonic (p : R[X]) : 0 /ₘ p = 0
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_divByMonic (p : R[X]) : 0 /ₘ p = 0 := by
  grind [divByMonic, divModByMonicAux]

@[simp]
/-
**Polynomial.modByMonic_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_zero (p : R[X]) : p %ₘ 0 = p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.monic_zero_iff_subsingleton`：monic_zero_iff_subsingleton : Mo
nic (0 : R[X]) ↔ Subsingleton R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.div_wf_lemma`：div_wf_lemma (h : degree q <= degree p ∧ p != 0
) (hq : Monic q) : degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natD
egree q))) < …
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Polynomial.divModByMonicAux.eq_def`：∀ {R : Type u} [inst : Ring R] (x x_
1 : Polynomial R) (x_2 : x_1.Monic),   x.divModByMonicAux x_2 =     match x, x_1
, x_2 with     | p, q, h…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem modByMonic_zero (p : R[X]) : p %ₘ 0 = p :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold modByMonic divModByMonicAux; rw [dif_neg h]

@[simp]
/-
**Polynomial.divByMonic_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divByMonic_zero (p : R[X]) : p /ₘ 0 = 0
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.monic_zero_iff_subsingleton`：monic_zero_iff_subsingleton : Mo
nic (0 : R[X]) ↔ Subsingleton R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.div_wf_lemma`：div_wf_lemma (h : degree q <= degree p ∧ p != 0
) (hq : Monic q) : degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natD
egree q))) < …
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Polynomial.divModByMonicAux.eq_def`：∀ {R : Type u} [inst : Ring R] (x x_
1 : Polynomial R) (x_2 : x_1.Monic),   x.divModByMonicAux x_2 =     match x, x_1
, x_2 with     | p, q, h…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem divByMonic_zero (p : R[X]) : p /ₘ 0 = 0 :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold divByMonic divModByMonicAux; rw [dif_neg h]
/-
**Polynomial.divByMonic_eq_of_not_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p /ₘ q = 0
参数：p : R[X]；hq : ¬Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p /ₘ q = 0 :=
  dif_neg hq
/-
**Polynomial.modByMonic_eq_of_not_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p %ₘ q = p
参数：p : R[X]；hq : ¬Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem modByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p %ₘ q = p :=
  dif_neg hq
/-
**Polynomial.modByMonic_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_eq_self_iff [Nontrivial R] (hq : Monic q) : p %ₘ q = p ↔ degree
 p < degree q
参数：hq : Monic q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Polynomial.div_wf_lemma`：div_wf_lemma (h : degree q <= degree p ∧ p != 0
) (hq : Monic q) : degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natD
egree q))) < …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.divModByMonicAux.eq_def`：∀ {R : Type u} [inst : Ring R] (x x_
1 : Polynomial R) (x_2 : x_1.Monic),   x.divModByMonicAux x_2 =     match x, x_1
, x_2 with     | p, q, h…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem modByMonic_eq_self_iff [Nontrivial R] (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ degree_modByMonic_lt _ hq, fun h => by
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold modByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩
/-
**Polynomial.degree_modByMonic_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Monic q) : degree (p %ₘ q
) <= degree q
参数：p : R[X]；hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
-/
theorem degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Monic q) : degree (p %ₘ q) ≤ degree q := by
  nontriviality R
  exact (degree_modByMonic_lt _ hq).le
/-
**Polynomial.degree_modByMonic_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_modByMonic_le_left : degree (p %ₘ q) <= degree p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.modByMonic_eq_self_iff`：modByMonic_eq_self_iff [Nontrivial R]
 (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_modByMonic_le`：degree_modByMonic_le (p : R[X]) {q : R[
X]} (hq : Monic q) : degree (p %ₘ q) <= degree q
· 使用定理 `Polynomial.modByMonic_eq_of_not_monic`：modByMonic_eq_of_not_monic (p : R
[X]) (hq : ¬Monic q) : p %ₘ q = p
-/
theorem degree_modByMonic_le_left : degree (p %ₘ q) ≤ degree p := by
  nontriviality R
  by_cases hq : q.Monic
  · cases lt_or_ge (degree p) (degree q)
    · rw [(modByMonic_eq_self_iff hq).mpr ‹_›]
    · exact (degree_modByMonic_le p hq).trans ‹_›
  · rw [modByMonic_eq_of_not_monic p hq]
/-
**Polynomial.natDegree_modByMonic_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_modByMonic_le (p : Polynomial R) {g : Polynomial R} (hg : g.Moni
c) : natDegree (p %ₘ g) <= g.natDegree
参数：p : Polynomial R；hg : g.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `Polynomial.degree_modByMonic_le`：degree_modByMonic_le (p : R[X]) {q : R[
X]} (hq : Monic q) : degree (p %ₘ q) <= degree q
-/
theorem natDegree_modByMonic_le (p : Polynomial R) {g : Polynomial R} (hg : g.Monic) :
    natDegree (p %ₘ g) ≤ g.natDegree :=
  natDegree_le_natDegree (degree_modByMonic_le p hg)
/-
**Polynomial.natDegree_modByMonic_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：natDegree_modByMonic_le_left : natDegree (p %ₘ q) <= natDegree p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `Polynomial.degree_modByMonic_le_left`：degree_modByMonic_le_left : degree
 (p %ₘ q) <= degree p
-/
theorem natDegree_modByMonic_le_left : natDegree (p %ₘ q) ≤ natDegree p :=
  natDegree_le_natDegree degree_modByMonic_le_left
/-
**Polynomial.X_dvd_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_dvd_sub_C : X ∣ p - C (p.coeff 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem X_dvd_sub_C : X ∣ p - C (p.coeff 0) := by
  simp [X_dvd_iff, coeff_C]
/-
**Polynomial.modByMonic_eq_sub_mul_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_eq_sub_mul_div : forall p q : R[X], p %ₘ q = p - q * (p /ₘ q) |
 p, q => letI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div._unary`：∀ {R : Type u} [inst : Ring
 R] (_x : (_ : Polynomial R) ×' Polynomial R), _x.1 %ₘ _x.2 = _x.1 - _x.2 * (_x.
1 /ₘ _x.2)
-/
theorem modByMonic_eq_sub_mul_div :
    ∀ p q : R[X], p %ₘ q = p - q * (p /ₘ q)
  | p, q =>
    letI := Classical.decEq R
    if hq : q.Monic then
      if h : degree q ≤ degree p ∧ p ≠ 0 then by
        have _wf := div_wf_lemma h hq
        have ih := modByMonic_eq_sub_mul_div
          (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) q
        unfold modByMonic divByMonic divModByMonicAux
        rw [dif_pos hq, dif_pos h]
        rw [modByMonic, dif_pos hq] at ih
        refine ih.trans ?_
        rw [divByMonic, dif_pos hq, dif_pos hq, dif_pos h, mul_add, sub_add_eq_sub_sub]
      else by
        unfold modByMonic divByMonic divModByMonicAux
        dsimp
        rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
    else by
      rw [modByMonic_eq_of_not_monic _ hq, divByMonic_eq_of_not_monic _ hq, mul_zero, sub_zero]
  termination_by p => p
/-
**Polynomial.modByMonic_add_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_add_div (p q : R[X]) : p %ₘ q + q * (p /ₘ q) = p
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
-/
theorem modByMonic_add_div (p q : R[X]) : p %ₘ q + q * (p /ₘ q) = p :=
  eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p q)
/-
**Polynomial.dvd_modByMonic_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dvd_modByMonic_sub (p q : R[X]) : q ∣ (p %ₘ q - p)
参数：p q : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `Polynomial.modByMonic_eq_of_not_monic`：modByMonic_eq_of_not_monic (p : R
[X]) (hq : ¬Monic q) : p %ₘ q = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem dvd_modByMonic_sub (p q : R[X]) : q ∣ (p %ₘ q - p) := by
  by_cases h : q.Monic
  · simp [modByMonic_eq_sub_mul_div]
  · simp [modByMonic_eq_of_not_monic, h]
/-
**Polynomial.dvd_modByMonic_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R}, q ∣ p %ₘ q ↔ q ∣ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_iff_dvd_of_dvd_sub`：dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔
 a ∣ c
· 使用定理 `Polynomial.dvd_modByMonic_sub`：dvd_modByMonic_sub (p q : R[X]) : q ∣ (p 
%ₘ q - p)
-/
@[simp] theorem dvd_modByMonic_iff_dvd : q ∣ p %ₘ q ↔ q ∣ p := by
  simpa using dvd_iff_dvd_of_dvd_sub <| dvd_modByMonic_sub p q
/-
**Polynomial.divByMonic_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divByMonic_eq_zero_iff [Nontrivial R] (hq : Monic q) : p /ₘ q = 0 ↔ degree
 p < degree q
参数：hq : Monic q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_self_iff`：modByMonic_eq_self_iff [Nontrivial R]
 (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Polynomial.div_wf_lemma`：div_wf_lemma (h : degree q <= degree p ∧ p != 0
) (hq : Monic q) : degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natD
egree q))) < …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.divModByMonicAux.eq_def`：∀ {R : Type u} [inst : Ring R] (x x_
1 : Polynomial R) (x_2 : x_1.Monic),   x.divModByMonicAux x_2 =     match x, x_1
, x_2 with     | p, q, h…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem divByMonic_eq_zero_iff [Nontrivial R] (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := modByMonic_add_div p q
    rwa [h, mul_zero, add_zero, modByMonic_eq_self_iff hq] at this,
  fun h => by
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold divByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩
/-
**Polynomial.degree_add_divByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_add_divByMonic (hq : Monic q) (h : degree q <= degree p) : degree q
 + degree (p /ₘ q) = degree p
参数：hq : Monic q；h : degree q <= degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.divByMonic_eq_zero_iff`：divByMonic_eq_zero_iff [Nontrivial R]
 (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
-/
theorem degree_add_divByMonic (hq : Monic q) (h : degree q ≤ degree p) :
    degree q + degree (p /ₘ q) = degree p := by
  nontriviality R
  have hdiv0 : p /ₘ q ≠ 0 := by rwa [Ne, divByMonic_eq_zero_iff hq, not_lt]
  have hlc : leadingCoeff q * leadingCoeff (p /ₘ q) ≠ 0 := by
    rwa [Monic.def.1 hq, one_mul, Ne, leadingCoeff_eq_zero]
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc
      degree (p %ₘ q) < degree q := degree_modByMonic_lt _ hq
      _ ≤ _ := by
        rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero, degree_eq_natDegree hdiv0, ←
            Nat.cast_add, Nat.cast_le]
        exact Nat.le_add_right _ _
  calc
    degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) := Eq.symm (degree_mul' hlc)
    _ = degree (p %ₘ q + q * (p /ₘ q)) := (degree_add_eq_right_of_degree_lt hmod).symm
    _ = _ := congr_arg _ (modByMonic_add_div _ _)
/-
**Polynomial.degree_divByMonic_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) <= degree p
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.zero_divByMonic`：zero_divByMonic (p : R[X]) : 0 /ₘ p = 0
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_add_divByMonic`：degree_add_divByMonic (hq : Monic q) (
h : degree q <= degree p) : degree q + degree (p /ₘ q) = degree p
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.divByMonic_eq_zero_iff`：divByMonic_eq_zero_iff [Nontrivial R]
 (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Polynomial.div_wf_lemma`：div_wf_lemma (h : degree q <= degree p ∧ p != 0
) (hq : Monic q) : degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natD
egree q))) < …
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Polynomial.divModByMonicAux.eq_def`：∀ {R : Type u} [inst : Ring R] (x x_
1 : Polynomial R) (x_2 : x_1.Monic),   x.divModByMonicAux x_2 =     match x, x_1
, x_2 with     | p, q, h…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Polynomial.divByMonic_eq_of_not_monic`：divByMonic_eq_of_not_monic (p : R
[X]) (hq : ¬Monic q) : p /ₘ q = 0
-/
theorem degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) ≤ degree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
  else
    if hq : Monic q then
      if h : degree q ≤ degree p then by
        have := Nontrivial.of_polynomial_ne hp0
        rw [← degree_add_divByMonic hq h, degree_eq_natDegree hq.ne_zero,
          degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 (not_lt.2 h))]
        exact WithBot.coe_le_coe.2 (Nat.le_add_left _ _)
      else by
        unfold divByMonic divModByMonicAux
        simp [dif_pos hq, h, degree_zero, bot_le]
    else (divByMonic_eq_of_not_monic p hq).symm ▸ bot_le
/-
**Polynomial.degree_divByMonic_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_divByMonic_lt (p q : R[X]) (hp0 : p != 0) (h0q : 0 < degree q) : de
gree (p /ₘ q) < degree p
参数：p q : R[X]；hp0 : p != 0；h0q : 0 < degree q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.divByMonic_eq_zero_iff`：divByMonic_eq_zero_iff [Nontrivial R]
 (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_add_divByMonic`：degree_add_divByMonic (hq : Monic q) (
h : degree q <= degree p) : degree q + degree (p /ₘ q) = degree p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.lt_add_of_pos_left`：∀ {k n : ℕ}, 0 < k → n < k + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Polynomial.divByMonic_eq_of_not_monic`：divByMonic_eq_of_not_monic (p : R
[X]) (hq : ¬Monic q) : p /ₘ q = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
-/
theorem degree_divByMonic_lt (p q : R[X]) (hp0 : p ≠ 0)
    (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
  letI := Classical.decEq R
  if hq : q.Monic then
    if hpq : degree p < degree q then by
      have := Nontrivial.of_polynomial_ne hp0
      rw [(divByMonic_eq_zero_iff hq).2 hpq, degree_eq_natDegree hp0]
      exact WithBot.bot_lt_coe _
    else by
      have := Nontrivial.of_polynomial_ne hp0
      rw [← degree_add_divByMonic hq (not_lt.1 hpq), degree_eq_natDegree hq.ne_zero,
        degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 hpq)]
      exact
        Nat.cast_lt.2
          (Nat.lt_add_of_pos_left (Nat.cast_lt.1 <|
            by simpa [degree_eq_natDegree hq.ne_zero] using! h0q))
  else by
    rwa [divByMonic_eq_of_not_monic _ hq, degree_zero, bot_lt_iff_ne_bot, degree_ne_bot]
/-
**Polynomial.natDegree_divByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_divByMonic (f : R[X]) {g : R[X]} (hg : g.Monic) : natDegree (f /
ₘ g) = natDegree f - natDegree g
参数：f : R[X]；hg : g.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.divByMonic_eq_zero_iff`：divByMonic_eq_zero_iff [Nontrivial R]
 (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q
· 使用定理 `Polynomial.degree_add_divByMonic`：degree_add_divByMonic (hq : Monic q) (
h : degree q <= degree p) : degree q + degree (p /ₘ q) = degree p
· 使用定理 `Polynomial.zero_divByMonic`：zero_divByMonic (p : R[X]) : 0 /ₘ p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem natDegree_divByMonic (f : R[X]) {g : R[X]} (hg : g.Monic) :
    natDegree (f /ₘ g) = natDegree f - natDegree g := by
  nontriviality R
  by_cases hfg : f /ₘ g = 0
  · rw [hfg, natDegree_zero]
    rw [divByMonic_eq_zero_iff hg] at hfg
    rw [tsub_eq_zero_iff_le.mpr (natDegree_le_natDegree <| le_of_lt hfg)]
  have hgf := hfg
  rw [divByMonic_eq_zero_iff hg] at hgf
  push Not at hgf
  have := degree_add_divByMonic hg hgf
  have hf : f ≠ 0 := by
    intro hf
    apply hfg
    rw [hf, zero_divByMonic]
  rw [degree_eq_natDegree hf, degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hfg,
    ← Nat.cast_add, Nat.cast_inj] at this
  rw [← this, add_tsub_cancel_left]
/-
**Polynomial.div_modByMonic_unique** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：div_modByMonic_unique {f g} (q r : R[X]) (hg : Monic g) (h : r + g * q = f
 ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r
参数：q r : R[X]；hg : Monic g；h : r + g * q = f ∧ degree r < degree g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `Polynomial.degree_sub_le`：degree_sub_le (p q : R[X]) : degree (p - q) <=
 max (degree p) (degree q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
（共 41 条，此处仅展示前 30 条）
-/
theorem div_modByMonic_unique {f g} (q r : R[X]) (hg : Monic g)
    (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r := by
  nontriviality R
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g) :=
    eq_of_sub_eq_zero
      (by
        rw [← sub_eq_zero_of_eq (h.1.trans (modByMonic_add_div f g).symm)]
        simp [mul_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)) := by simp [h₁]
  have h₄ : degree (r - f %ₘ g) < degree g :=
    calc
      degree (r - f %ₘ g) ≤ max (degree r) (degree (f %ₘ g)) := degree_sub_le _ _
      _ < degree g := max_lt_iff.2 ⟨h.2, degree_modByMonic_lt _ hg⟩
  have h₅ : q - f /ₘ g = 0 :=
    _root_.by_contradiction fun hqf =>
      not_le_of_gt h₄ <|
        calc
          degree g ≤ degree g + degree (q - f /ₘ g) := by
            rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hqf]
            norm_cast
            exact Nat.le_add_right _ _
          _ = degree (r - f %ₘ g) := by rw [h₂, degree_mul']; simpa [Monic.def.1 hg]
  exact ⟨Eq.symm <| eq_of_sub_eq_zero h₅, Eq.symm <| eq_of_sub_eq_zero <| by simpa [h₅] using h₁⟩
/-
**Polynomial.map_mod_divByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_mod_divByMonic [Ring S] (f : R ->+* S) (hq : Monic q) : (p /ₘ q).map f
 = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f
参数：f : R ->+* S；hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用引理 `Polynomial.degree_map_le`：degree_map_le : degree (p.map f) <= degree p
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Polynomial.degree_map_eq_of_leadingCoeff_ne_zero`：degree_map_eq_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : degree (p.map f)
 = degree p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_mod_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f := by
  nontriviality S
  have : Nontrivial R := f.domain_nontrivial
  have : map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q) :=
    div_modByMonic_unique ((p /ₘ q).map f) _ (hq.map f)
      ⟨Eq.symm <| by rw [← Polynomial.map_mul, ← Polynomial.map_add, modByMonic_add_div],
        calc
          _ ≤ degree (p %ₘ q) := degree_map_le
          _ < degree q := degree_modByMonic_lt _ hq
          _ = _ :=
            Eq.symm <|
              degree_map_eq_of_leadingCoeff_ne_zero _
                (by rw [Monic.def.1 hq, f.map_one]; exact one_ne_zero)⟩
  exact ⟨this.1.symm, this.2.symm⟩
/-
**Polynomial.map_divByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_divByMonic [Ring S] (f : R ->+* S) (hq : Monic q) : (p /ₘ q).map f = p
.map f /ₘ q.map f
参数：f : R ->+* S；hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.map_mod_divByMonic`：map_mod_divByMonic [Ring S] (f : R ->+* S
) (hq : Monic q) : (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map 
f %ₘ q.map f
-/
theorem map_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f :=
  (map_mod_divByMonic f hq).1
/-
**Polynomial.map_modByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_modByMonic [Ring S] (f : R ->+* S) (hq : Monic q) : (p %ₘ q).map f = p
.map f %ₘ q.map f
参数：f : R ->+* S；hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.map_mod_divByMonic`：map_mod_divByMonic [Ring S] (f : R ->+* S
) (hq : Monic q) : (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map 
f %ₘ q.map f
-/
theorem map_modByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p %ₘ q).map f = p.map f %ₘ q.map f :=
  (map_mod_divByMonic f hq).2
/-
**Polynomial.modByMonic_eq_zero_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p
参数：hq : Monic q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `exists_eq_mul_right_of_dvd`：exists_eq_mul_right_of_dvd (h : a ∣ b) : exi
sts c, b = a * c
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
-/
theorem modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p :=
  ⟨fun h => by rw [← modByMonic_add_div p q, h, zero_add]; exact dvd_mul_right _ _, fun h => by
    nontriviality R
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    by_contra hpq0
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div, mul_sub, ← hr]
    have : degree (q * (r - p /ₘ q)) < degree q := hmod ▸ degree_modByMonic_lt _ hq
    have hrpq0 : leadingCoeff (r - p /ₘ q) ≠ 0 := fun h =>
      hpq0 <|
        leadingCoeff_eq_zero.1
          (by rw [hmod, leadingCoeff_eq_zero.1 h, mul_zero, leadingCoeff_zero])
    have hlc : leadingCoeff q * leadingCoeff (r - p /ₘ q) ≠ 0 := by rwa [Monic.def.1 hq, one_mul]
    rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero,
      degree_eq_natDegree (mt leadingCoeff_eq_zero.2 hrpq0)] at this
    exact not_lt_of_ge (Nat.le_add_right _ _) (WithBot.coe_lt_coe.1 this)⟩

@[simp]
/-
**Polynomial.modByMonic_self** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_self (hp : p.Monic) : p %ₘ p = 0
参数：hp : p.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem modByMonic_self (hp : p.Monic) : p %ₘ p = 0 := by rw [modByMonic_eq_zero_iff_dvd hp]

/-- See `Polynomial.mul_self_modByMonic` for the other multiplication order. That version, unlike
this one, requires commutativity. -/
@[simp]
/-
**Polynomial.self_mul_modByMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：self_mul_modByMonic (hq : q.Monic) : (q * p) %ₘ q = 0
参数：hq : q.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b

--- 原说明 ---
See `Polynomial.mul_self_modByMonic` for the other multiplication order. That ve
rsion, unlike
this one, requires commutativity.
-/
lemma self_mul_modByMonic (hq : q.Monic) : (q * p) %ₘ q = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_right q p
/-
**Polynomial.map_dvd_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_dvd_map [Ring S] (f : R ->+* S) (hf : Function.Injective f) {x y : R[X
]} (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y
参数：f : R ->+* S；hf : Function.Injective f；hx : x.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Polynomial.map_modByMonic`：map_modByMonic [Ring S] (f : R ->+* S) (hq : 
Monic q) : (p %ₘ q).map f = p.map f %ₘ q.map f
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
-/
theorem map_dvd_map [Ring S] (f : R →+* S) (hf : Function.Injective f) {x y : R[X]}
    (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y := by
  rw [← modByMonic_eq_zero_iff_dvd hx, ← modByMonic_eq_zero_iff_dvd (hx.map f), ←
    map_modByMonic f hx]
  exact
    ⟨fun H => map_injective f hf <| by rw [H, Polynomial.map_zero], fun H => by
      rw [H, Polynomial.map_zero]⟩

@[simp]
/-
**Polynomial.modByMonic_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_one (p : R[X]) : p %ₘ 1 = 0
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `Polynomial.monic_one`：monic_one : Monic (1 : R[X])
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem modByMonic_one (p : R[X]) : p %ₘ 1 = 0 :=
  (modByMonic_eq_zero_iff_dvd (by convert! monic_one (R := R))).2 (one_dvd _)

@[simp]
/-
**Polynomial.divByMonic_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divByMonic_one (p : R[X]) : p /ₘ 1 = p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.modByMonic_one`：modByMonic_one (p : R[X]) : p %ₘ 1 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem divByMonic_one (p : R[X]) : p /ₘ 1 = p := by
  conv_rhs => rw [← modByMonic_add_div p 1]; simp
/-
**Polynomial.sum_modByMonic_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_modByMonic_coeff (hq : q.Monic) {n : Nat} (hn : q.degree <= n) : (∑ i 
: Fin n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q
参数：hq : q.Monic；hn : q.degree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.sum_fin`：sum_fin [AddCommMonoid S] (f : Nat -> R -> S) (hf : 
forall i, f i 0 = 0) {n : Nat} {p : R[X]} (hn : p.degree < n) : (∑ i : Fin n, f 
i (p.coe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
-/
theorem sum_modByMonic_coeff (hq : q.Monic) {n : ℕ} (hn : q.degree ≤ n) :
    (∑ i : Fin n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q := by
  nontriviality R
  exact
    (sum_fin (fun i c => monomial i c) (by simp) ((degree_modByMonic_lt _ hq).trans_le hn)).trans
      (sum_monomial_eq _)
/-
**Polynomial.mul_divByMonic_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mul_divByMonic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) : q * p /
ₘ q = p
参数：p : R[X]；hmo : q.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
-/
theorem mul_divByMonic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) :
    q * p /ₘ q = p := by
  nontriviality R
  refine (div_modByMonic_unique _ 0 hmo ⟨by rw [zero_add], ?_⟩).1
  rw [degree_zero]
  exact Ne.bot_lt fun h => hmo.ne_zero (degree_eq_bot.1 h)
/-
**Polynomial.coeff_divByMonic_X_sub_C_rec** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：coeff_divByMonic_X_sub_C_rec (p : R[X]) (a : R) (n : Nat) : (p /ₘ (X - C a
)).coeff n = coeff p (n + 1) + a * (p /ₘ (X - C a)).coeff (n + 1)
参数：p : R[X]；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `Polynomial.coeff_X_mul`：coeff_X_mul (p : R[X]) (n : Nat) : coeff (X * p)
 (n + 1) = coeff p n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_divByMonic_X_sub_C_rec (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = coeff p (n + 1) + a * (p /ₘ (X - C a)).coeff (n + 1) := by
  nontriviality R
  have := monic_X_sub_C a
  set q := p /ₘ (X - C a)
  rw [← p.modByMonic_add_div (X - C a)]
  have : degree (p %ₘ (X - C a)) < ↑(n + 1) := degree_X_sub_C a ▸ p.degree_modByMonic_lt this
    |>.trans_le <| WithBot.coe_le_coe.mpr le_add_self
  simp [q, sub_mul, add_sub, coeff_eq_zero_of_degree_lt this]
/-
**Polynomial.coeff_divByMonic_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_divByMonic_X_sub_C (p : R[X]) (a : R) (n : Nat) : (p /ₘ (X - C a)).c
oeff n = ∑ i in Icc (n + 1) p.natDegree, a ^ (i - (n + 1)) * p.coeff i
参数：p : R[X]；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a ≤ b → Finset.Icc a b = ∅
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.divByMonic_eq_zero_iff`：divByMonic_eq_zero_iff [Nontrivial R]
 (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Polynomial.natDegree_divByMonic`：natDegree_divByMonic (f : R[X]) {g : R[
X]} (hg : g.Monic) : natDegree (f /ₘ g) = natDegree f - natDegree g
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用引理 `Polynomial.coeff_divByMonic_X_sub_C_rec`：coeff_divByMonic_X_sub_C_rec (p
 : R[X]) (a : R) (n : Nat) : (p /ₘ (X - C a)).coeff n = coeff p (n + 1) + a * (p
 /ₘ (X - C a)).coeff (n + 1)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `Finset.Icc_eq_cons_Ioc`：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a 
b).cons a left_notMem_Ioc
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
（共 49 条，此处仅展示前 30 条）
-/
theorem coeff_divByMonic_X_sub_C (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = ∑ i ∈ Icc (n + 1) p.natDegree, a ^ (i - (n + 1)) * p.coeff i := by
  wlog h : p.natDegree ≤ n generalizing n
  · refine Nat.decreasingInduction' (fun n hn _ ih ↦ ?_) (le_of_not_ge h) ?_
    · rw [coeff_divByMonic_X_sub_C_rec, ih, eq_comm, Icc_eq_cons_Ioc (Nat.succ_le_iff.mpr hn),
          sum_cons, Nat.sub_self, pow_zero, one_mul, mul_sum]
      congr 1; refine sum_congr ?_ fun i hi ↦ ?_
      · ext; simp
      rw [← mul_assoc, ← pow_succ', eq_comm, i.sub_succ', Nat.sub_add_cancel]
      apply Nat.le_sub_of_add_le
      rw [add_comm]; exact (mem_Icc.mp hi).1
    · exact this _ le_rfl
  rw [Icc_eq_empty (Nat.lt_succ_iff.mpr h).not_ge, sum_empty]
  nontriviality R
  by_cases hp : p.natDegree = 0
  · rw [(divByMonic_eq_zero_iff <| monic_X_sub_C a).mpr, coeff_zero]
    apply degree_lt_degree; rw [hp, natDegree_X_sub_C]; simp
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C]
    exact (Nat.pred_lt hp).trans_le h

section multiplicity

/-- An algorithm for deciding polynomial divisibility.
Prefer `Classical.dec`, as the algorithm relies on `%ₘ` and so is `noncomputable`.
-/
@[deprecated Classical.dec (since := "2026-02-07")]
/-
**Polynomial.decidableDvdMonic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：decidableDvdMonic [DecidableEq R] (p : R[X]) (hq : Monic q) : Decidable (q
 ∣ p)
参数：p : R[X]；hq : Monic q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p

--- 原说明 ---
An algorithm for deciding polynomial divisibility.
Prefer `Classical.dec`, as the algorithm relies on `%ₘ` and so is `noncomputable
`.
-/
def decidableDvdMonic [DecidableEq R] (p : R[X]) (hq : Monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)
/-
**Polynomial.finiteMultiplicity_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：finiteMultiplicity_X_sub_C (a : R) (h0 : p != 0) : FiniteMultiplicity (X -
 C a) p
参数：a : R；h0 : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `Polynomial.finiteMultiplicity_of_degree_pos_of_monic`：finiteMultiplicity
_of_degree_pos_of_monic (hp : (0 : WithBot Nat) < degree p) (hmp : Monic p) (hq 
: q != 0) : FiniteMultiplicity p q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem finiteMultiplicity_X_sub_C (a : R) (h0 : p ≠ 0) : FiniteMultiplicity (X - C a) p := by
  have := Nontrivial.of_polynomial_ne h0
  refine finiteMultiplicity_of_degree_pos_of_monic ?_ (monic_X_sub_C _) h0
  rw [degree_X_sub_C]
  decide

/- TODO: stripping out classical for decidability instance parameter might
make for better ergonomics -/
/-- The largest power of `X - C a` which divides `p`. -/
/-
**Polynomial.rootMultiplicity** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity (a : R) (p : R[X]) : Nat
参数：a : R；p : R[X]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p

--- 原说明 ---
The largest power of `X - C a` which divides `p`.
-/
def rootMultiplicity (a : R) (p : R[X]) : ℕ :=
  letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := Classical.decPred _
    Nat.find (finiteMultiplicity_X_sub_C a h0)
/-
**Polynomial.rootMultiplicity_eq_natFind_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：rootMultiplicity_eq_natFind_of_ne_zero {p : R[X]} (p0 : p != 0) {a : R} [D
ecidablePred fun n : Nat => ¬(X - C a) ^ (n + 1) ∣ p] : rootMultiplicity a p = N
at.find (finiteMultiplicity_X_sub_C a p0)
参数：p0 : p != 0；X - C a；n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem rootMultiplicity_eq_natFind_of_ne_zero {p : R[X]} (p0 : p ≠ 0) {a : R}
    [DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p] :
    rootMultiplicity a p = Nat.find (finiteMultiplicity_X_sub_C a p0) := by
  dsimp [rootMultiplicity]
  rw [dif_neg p0]
  congr

@[deprecated (since := "2026-02-12")]
alias rootMultiplicity_eq_nat_find_of_nonzero := rootMultiplicity_eq_natFind_of_ne_zero
/-
**Polynomial.rootMultiplicity_eq_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：rootMultiplicity_eq_multiplicity [DecidableEq R] (p : R[X]) (a : R) : root
Multiplicity a p = if p = 0 then 0 else multiplicity (X - C a) p
参数：p : R[X]；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `untopD_coe_enat`：∀ (d n : ℕ), WithTop.untopD d ↑n = n
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem rootMultiplicity_eq_multiplicity [DecidableEq R]
    (p : R[X]) (a : R) :
    rootMultiplicity a p =
      if p = 0 then 0 else multiplicity (X - C a) p := by
  simp only [rootMultiplicity, multiplicity, emultiplicity]
  split
  · rfl
  rename_i h
  simp only [finiteMultiplicity_X_sub_C a h, ↓reduceDIte]
  rw [untopD_coe_enat]
  congr

@[simp]
/-
**Polynomial.rootMultiplicity_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_zero {x : R} : rootMultiplicity x 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p
-/
theorem rootMultiplicity_zero {x : R} : rootMultiplicity x 0 = 0 :=
  dif_pos rfl

@[simp]
/-
**Polynomial.rootMultiplicity_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_C (r a : R) : rootMultiplicity a (C r) = 0
参数：r a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `multiplicity_eq_zero`：multiplicity_eq_zero : multiplicity a b = 0 ↔ ¬a ∣
 b
· 使用定理 `Polynomial.Monic.not_dvd_of_natDegree_lt`：not_dvd_of_natDegree_lt (hp : 
Monic p) (h0 : q != 0) (hl : natDegree q < natDegree p) : ¬p ∣ q
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem rootMultiplicity_C (r a : R) : rootMultiplicity a (C r) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (C r) 0, rootMultiplicity_zero]
  classical
  rw [rootMultiplicity_eq_multiplicity]
  split_ifs with hr
  · rfl
  have h : natDegree (C r) < natDegree (X - C a) := by simp
  simp_rw [multiplicity_eq_zero.mpr ((monic_X_sub_C a).not_dvd_of_natDegree_lt hr h)]
/-
**Polynomial.pow_rootMultiplicity_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity
 a p ∣ p
参数：p : R[X]；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `pow_multiplicity_dvd`：pow_multiplicity_dvd (a b : α) : a ^ (multiplicity
 a b) ∣ b
-/
theorem pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p :=
  letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    rw [rootMultiplicity_eq_multiplicity, if_neg h]; apply pow_multiplicity_dvd
/-
**Polynomial.pow_mul_divByMonic_rootMultiplicity_eq** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：pow_mul_divByMonic_rootMultiplicity_eq (p : R[X]) (a : R) : (X - C a) ^ ro
otMultiplicity a p * (p /ₘ (X - C a) ^ rootMultiplicity a p) = p
参数：p : R[X]；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_mul_divByMonic_rootMultiplicity_eq (p : R[X]) (a : R) :
    (X - C a) ^ rootMultiplicity a p * (p /ₘ (X - C a) ^ rootMultiplicity a p) = p := by
  have : Monic ((X - C a) ^ rootMultiplicity a p) := (monic_X_sub_C _).pow _
  conv_rhs =>
    rw [← modByMonic_add_div p, (modByMonic_eq_zero_iff_dvd this).2 (pow_rootMultiplicity_dvd _ _)]
  simp
/-
**Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial`。
形式化陈述：exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a
 : R) : exists q : R[X], p = (X - C a) ^ p.rootMultiplicity a * q ∧ ¬ (X - C a) 
∣ q
参数：p : R[X]；hp : p != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd`：FiniteMultiplicity.exi
sts_eq_pow_mul_and_not_dvd (hfin : FiniteMultiplicity a b) : exists c : α, b = a
 ^ multiplicity a b * c ∧ ¬a ∣ c
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p
-/
theorem exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p ≠ 0) (a : R) :
    ∃ q : R[X], p = (X - C a) ^ p.rootMultiplicity a * q ∧ ¬ (X - C a) ∣ q := by
  classical
  rw [rootMultiplicity_eq_multiplicity, if_neg hp]
  apply (finiteMultiplicity_X_sub_C a hp).exists_eq_pow_mul_and_not_dvd

end multiplicity

end Ring

section CommRing

variable [CommRing R] {p p₁ p₂ q : R[X]}

@[simp]
/-
**Polynomial.modByMonic_X_sub_C_eq_C_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (X - C a) = C (p.ev
al a)
参数：p : R[X]；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
-/
theorem modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a) := by
  nontriviality R
  have h : (p %ₘ (X - C a)).eval a = p.eval a := by
    rw [modByMonic_eq_sub_mul_div, eval_sub, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, sub_zero]
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_modByMonic_lt p (monic_X_sub_C a)
  have : degree (p %ₘ (X - C a)) ≤ 0 := by
    revert this
    cases degree (p %ₘ (X - C a))
    · exact fun _ => bot_le
    · exact fun h => WithBot.coe_le_coe.2 (Nat.le_of_lt_succ (WithBot.coe_lt_coe.1 h))
  rw [eq_C_of_degree_le_zero this, eval_C] at h
  rw [eq_C_of_degree_le_zero this, h]
/-
**Polynomial.mul_divByMonic_eq_iff_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p
 a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `Polynomial.modByMonic_X_sub_C_eq_C_eval`：modByMonic_X_sub_C_eq_C_eval (p
 : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a)
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
-/
theorem mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a :=
  .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs => rw [← modByMonic_add_div p, modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm
/-
**Polynomial.dvd_iff_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_inj`：C_inj : C a = C b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.modByMonic_X_sub_C_eq_C_eval`：modByMonic_X_sub_C_eq_C_eval (p
 : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a)
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mul_divByMonic_eq_iff_isRoot`：mul_divByMonic_eq_iff_isRoot : 
(X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a
-/
theorem dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a :=
  ⟨fun h => by
    rwa [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩
/-
**Polynomial.X_sub_C_dvd_sub_C_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a) := by
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_C, sub_self]

-- TODO: generalize this to Ring. In general, 0 can be replaced by any element in the center of R.
/-
**Polynomial.modByMonic_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_X_sub_C_eq_C_eval`：modByMonic_X_sub_C_eq_C_eval (p
 : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a)
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0) := by
  rw [← modByMonic_X_sub_C_eq_C_eval, C_0, sub_zero]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_modByMonic_eq_self_of_root [CommRing S] {f : R →+* S} {p q : R[X]}
    {x : S} (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x := by
  rw [modByMonic_eq_sub_mul_div, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]
/-
**Polynomial.sub_dvd_eval_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b
参数：a b : R；p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b := by
  suffices X - C b ∣ p - C (p.eval b) by
    simpa only [coe_evalRingHom, eval_sub, eval_X, eval_C]
      using (_root_.map_dvd (evalRingHom a)) this
  simp [dvd_iff_isRoot]
/-
**Polynomial.IsRoot.dvd_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsRoot`
。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {p : Polynomial R} {x : R}, p.IsRoot x 
→ x ∣ p.coeff 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Polynomial.IsRoot.eq_zero`：∀ {R : Type u} [inst : Semiring R] {p : Polyn
omial R} {x : R}, p.IsRoot x → Polynomial.eval x p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Polynomial.sub_dvd_eval_sub`：sub_dvd_eval_sub (a b : R) (p : R[X]) : a -
 b ∣ p.eval a - p.eval b
-/
lemma IsRoot.dvd_coeff_zero {p : R[X]} {x : R} (h : p.IsRoot x) : x ∣ p.coeff 0 := by
  simpa [h.eq_zero, coeff_zero_eq_eval_zero] using sub_dvd_eval_sub 0 x p

@[simp]
/-
**Polynomial.rootMultiplicity_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} : rootMultiplicity x p = 0
 ↔ IsRoot p x -> p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} :
    rootMultiplicity x p = 0 ↔ IsRoot p x → p = 0 := by
  classical
  simp only [rootMultiplicity_eq_multiplicity, ite_eq_left_iff, multiplicity_eq_zero,
    dvd_iff_isRoot, not_imp_not]
/-
**Polynomial.rootMultiplicity_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : rootMultip
licity x p = 0
参数：h : ¬IsRoot p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.rootMultiplicity_eq_zero_iff`：rootMultiplicity_eq_zero_iff {p
 : R[X]} {x : R} : rootMultiplicity x p = 0 ↔ IsRoot p x -> p = 0
-/
theorem rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0 :=
  rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim

@[simp]
/-
**Polynomial.rootMultiplicity_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_pos' {p : R[X]} {x : R} : 0 < rootMultiplicity x p ↔ p !=
 0 ∧ IsRoot p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.rootMultiplicity_eq_zero_iff`：rootMultiplicity_eq_zero_iff {p
 : R[X]} {x : R} : rootMultiplicity x p = 0 ↔ IsRoot p x -> p = 0
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rootMultiplicity_pos' {p : R[X]} {x : R} :
    0 < rootMultiplicity x p ↔ p ≠ 0 ∧ IsRoot p x := by
  rw [pos_iff_ne_zero, Ne, rootMultiplicity_eq_zero_iff, Classical.not_imp, and_comm]
/-
**Polynomial.rootMultiplicity_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_pos {p : R[X]} (hp : p != 0) {x : R} : 0 < rootMultiplici
ty x p ↔ IsRoot p x
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.rootMultiplicity_pos'`：rootMultiplicity_pos' {p : R[X]} {x : 
R} : 0 < rootMultiplicity x p ↔ p != 0 ∧ IsRoot p x
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
-/
theorem rootMultiplicity_pos {p : R[X]} (hp : p ≠ 0) {x : R} :
    0 < rootMultiplicity x p ↔ IsRoot p x :=
  rootMultiplicity_pos'.trans (and_iff_right hp)
/-
**Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p !=
 0) : eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) != 0
参数：a : R；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Polynomial.pow_mul_divByMonic_rootMultiplicity_eq`：pow_mul_divByMonic_ro
otMultiplicity_eq (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p * (p /ₘ 
(X - C a) ^ rootMultiplicity a p) = p
· 使用定理 `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`：FiniteMultiplicity.no
t_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity a b) {m : Nat} (hm : multi
plicity a b < m) : ¬a ^ m ∣ b
· 使用定理 `Polynomial.finiteMultiplicity_of_degree_pos_of_monic`：finiteMultiplicity
_of_degree_pos_of_monic (hp : (0 : WithBot Nat) < degree p) (hmp : Monic p) (hq 
: q != 0) : FiniteMultiplicity p q
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p ≠ 0) :
    eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) ≠ 0 := by
  classical
  have : Nontrivial R := Nontrivial.of_polynomial_ne hp
  rw [Ne, ← IsRoot, ← dvd_iff_isRoot]
  rintro ⟨q, hq⟩
  have := pow_mul_divByMonic_rootMultiplicity_eq p a
  rw [hq, ← mul_assoc, ← pow_succ, rootMultiplicity_eq_multiplicity, if_neg hp] at this
  exact
    (finiteMultiplicity_of_degree_pos_of_monic
      (show (0 : WithBot ℕ) < degree (X - C a) by rw [degree_X_sub_C]; decide)
      (monic_X_sub_C _) hp).not_pow_dvd_of_multiplicity_lt
      (Nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)

/-- See `Polynomial.self_mul_modByMonic` for the other multiplication order. This version, unlike
that one, requires commutativity. -/
@[simp]
/-
**Polynomial.mul_self_modByMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mul_self_modByMonic (hq : q.Monic) : (p * q) %ₘ q = 0
参数：hq : q.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a

--- 原说明 ---
See `Polynomial.self_mul_modByMonic` for the other multiplication order. This ve
rsion, unlike
that one, requires commutativity.
-/
lemma mul_self_modByMonic (hq : q.Monic) : (p * q) %ₘ q = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_left q p
/-
**Polynomial.modByMonic_eq_of_dvd_sub** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_eq_of_dvd_sub (hq : q.Monic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %
ₘ q
参数：hq : q.Monic；h : q ∣ p₁ - p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
-/
lemma modByMonic_eq_of_dvd_sub (hq : q.Monic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q := by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine (div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨?_, degree_modByMonic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_add, ← add_assoc, modByMonic_add_div, add_comm]
/-
**Polynomial.add_modByMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q
参数：p₁ p₂ : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.modByMonic_eq_of_not_monic`：modByMonic_eq_of_not_monic (p : R
[X]) (hq : ¬Monic q) : p %ₘ q = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add, add_left_comm, add_assoc, modByMonic_add_div, ← add_assoc,
              add_comm (q * _), modByMonic_add_div],
            (degree_add_le _ _).trans_lt
              (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]
/-
**Polynomial.neg_modByMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：neg_modByMonic (p q : R[X]) : (-p) %ₘ q = -(p %ₘ q)
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.add_modByMonic`：add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ 
q = p₁ %ₘ q + p₂ %ₘ q
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Polynomial.zero_modByMonic`：zero_modByMonic (p : R[X]) : 0 %ₘ p = 0
-/
lemma neg_modByMonic (p q : R[X]) : (-p) %ₘ q = -(p %ₘ q) := by
  rw [eq_neg_iff_add_eq_zero, ← add_modByMonic, neg_add_cancel, zero_modByMonic]
/-
**Polynomial.sub_modByMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：sub_modByMonic (p₁ p₂ q : R[X]) : (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q
参数：p₁ p₂ q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Polynomial.add_modByMonic`：add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ 
q = p₁ %ₘ q + p₂ %ₘ q
· 使用引理 `Polynomial.neg_modByMonic`：neg_modByMonic (p q : R[X]) : (-p) %ₘ q = -(p
 %ₘ q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_modByMonic (p₁ p₂ q : R[X]) : (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q := by
  simp [sub_eq_add_neg, add_modByMonic, neg_modByMonic]
/-
**Polynomial.mul_modByMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mul_modByMonic (p₁ p₂ q : R[X]) : (p₁ * p₂) %ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %
ₘ q
参数：p₁ p₂ q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_of_not_monic`：modByMonic_eq_of_not_monic (p : R
[X]) (hq : ¬Monic q) : p %ₘ q = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.modByMonic_eq_of_dvd_sub`：modByMonic_eq_of_dvd_sub (hq : q.Mo
nic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 45 条，此处仅展示前 30 条）
-/
lemma mul_modByMonic (p₁ p₂ q : R[X]) : (p₁ * p₂) %ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %ₘ q := by
  by_cases! h : ¬ q.Monic
  · simp [Polynomial.modByMonic_eq_of_not_monic _ h]
  apply Polynomial.modByMonic_eq_of_dvd_sub h
  have : p₁ * p₂ - p₁ %ₘ q * (p₂ %ₘ q) = (p₁ %ₘ q) * (p₂ - p₂ %ₘ q) + p₂ * (p₁ - p₁ %ₘ q) := by ring
  rw [this]
  apply dvd_add
  all_goals
  · apply dvd_mul_of_dvd_right
    simp [Polynomial.modByMonic_eq_sub_mul_div]
/-
**Polynomial.eval_divByMonic_eq_trailingCoeff_comp** 是 Mathlib 中的一个引理，位于命名空间 `Po
lynomial`。
形式化陈述：eval_divByMonic_eq_trailingCoeff_comp {p : R[X]} {t : R} : (p /ₘ (X - C t)
 ^ p.rootMultiplicity t).eval t = (p.comp (X + C t)).trailingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.zero_divByMonic`：zero_divByMonic (p : R[X]) : 0 /ₘ p = 0
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `Polynomial.zero_comp`：zero_comp : comp (0 : R[X]) p = 0
· 使用定理 `Polynomial.trailingCoeff_zero`：trailingCoeff_zero : trailingCoeff (0 : R
[X]) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.pow_mul_divByMonic_rootMultiplicity_eq`：pow_mul_divByMonic_ro
otMultiplicity_eq (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p * (p /ₘ 
(X - C a) ^ rootMultiplicity a p) = p
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Polynomial.pow_comp`：pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) 
(n : Nat) : (p ^ n).comp q = p.comp q ^ n
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Polynomial.reverse_leadingCoeff`：reverse_leadingCoeff (f : R[X]) : f.rev
erse.leadingCoeff = f.trailingCoeff
· 使用定理 `Polynomial.reverse_X_pow_mul`：∀ {R : Type u_1} [inst : Semiring R] (p : 
Polynomial R) (n : ℕ), (Polynomial.X ^ n * p).reverse = p.reverse
· 使用定理 `Polynomial.trailingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : P
olynomial R), p.trailingCoeff = p.coeff p.natTrailingDegree
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`：eval_divByMonic
_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p != 0) : eval a (p /ₘ (X
 - C a) ^ rootMultiplicity a p) != 0
-/
lemma eval_divByMonic_eq_trailingCoeff_comp {p : R[X]} {t : R} :
    (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t = (p.comp (X + C t)).trailingCoeff := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_divByMonic, eval_zero, zero_comp, trailingCoeff_zero]
  have mul_eq := p.pow_mul_divByMonic_rootMultiplicity_eq t
  set m := p.rootMultiplicity t
  set g := p /ₘ (X - C t) ^ m
  have : (g.comp (X + C t)).coeff 0 = g.eval t := by
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  rw [← congr_arg (comp · <| X + C t) mul_eq, mul_comp, pow_comp, sub_comp, X_comp, C_comp,
    add_sub_cancel_right, ← reverse_leadingCoeff, reverse_X_pow_mul, reverse_leadingCoeff,
    trailingCoeff, Nat.le_zero.1 (natTrailingDegree_le_of_ne_zero <|
      this ▸ eval_divByMonic_pow_rootMultiplicity_ne_zero t hp), this]

/-- The multiplicity of `a` as root of a nonzero polynomial `p` is at least `n` iff
`(X - a) ^ n` divides `p`. -/
/-
**Polynomial.le_rootMultiplicity_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：le_rootMultiplicity_iff (p0 : p != 0) {a : R} {n : Nat} : n <= rootMultipl
icity a p ↔ (X - C a) ^ n ∣ p
参数：p0 : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n

--- 原说明 ---
The multiplicity of `a` as root of a nonzero polynomial `p` is at least `n` iff
`(X - a) ^ n` divides `p`.
-/
lemma le_rootMultiplicity_iff (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ rootMultiplicity a p ↔ (X - C a) ^ n ∣ p := by
  simp_rw [rootMultiplicity, dif_neg p0, Nat.le_find_iff, not_not]
  refine ⟨fun h => ?_, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  rcases n with - | n
  · rw [pow_zero]
    apply one_dvd
  · exact h n n.lt_succ_self
/-
**Polynomial.rootMultiplicity_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_le_iff (p0 : p != 0) (a : R) (n : Nat) : rootMultiplicity
 a p <= n ↔ ¬(X - C a) ^ (n + 1) ∣ p
参数：p0 : p != 0；a : R；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rootMultiplicity_le_iff (p0 : p ≠ 0) (a : R) (n : ℕ) :
    rootMultiplicity a p ≤ n ↔ ¬(X - C a) ^ (n + 1) ∣ p := by
  rw [← (le_rootMultiplicity_iff p0).not, not_le, Nat.lt_add_one_iff]

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
/-
**Polynomial.rootMultiplicity_add** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q != 0) : min (root
Multiplicity a p) (rootMultiplicity a q) <= rootMultiplicity a (p + q)
参数：a : R；hzero : p + q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用引理 `min_pow_dvd_add`：min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^
 min m n ∣ a + b
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p

--- 原说明 ---
The multiplicity of `p + q` is at least the minimum of the multiplicities.
-/
lemma rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) ≤ rootMultiplicity a (p + q) := by
  rw [le_rootMultiplicity_iff hzero]
  exact min_pow_dvd_add (pow_rootMultiplicity_dvd p a) (pow_rootMultiplicity_dvd q a)
/-
**Polynomial.le_rootMultiplicity_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：le_rootMultiplicity_mul {p q : R[X]} (x : R) (hpq : p * q != 0) : rootMult
iplicity x p + rootMultiplicity x q <= rootMultiplicity x (p * q)
参数：x : R；hpq : p * q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p
-/
lemma le_rootMultiplicity_mul {p q : R[X]} (x : R) (hpq : p * q ≠ 0) :
    rootMultiplicity x p + rootMultiplicity x q ≤ rootMultiplicity x (p * q) := by
  rw [le_rootMultiplicity_iff hpq, pow_add]
  gcongr <;> apply pow_rootMultiplicity_dvd
/-
**Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd** 是 Mathlib 中的一个引理，位于命名
空间 `Polynomial`。
形式化陈述：rootMultiplicity_le_rootMultiplicity_of_dvd {p q : R[X]} (hq : q != 0) (hp
q : p ∣ q) (x : R) : p.rootMultiplicity x <= q.rootMultiplicity x
参数：hq : q != 0；hpq : p ∣ q；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_add_right_le`：∀ {n m k : ℕ}, n + k ≤ m → n ≤ m
· 使用引理 `Polynomial.le_rootMultiplicity_mul`：le_rootMultiplicity_mul {p q : R[X]}
 (x : R) (hpq : p * q != 0) : rootMultiplicity x p + rootMultiplicity x q <= roo
tMultiplicity x (p * q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rootMultiplicity_le_rootMultiplicity_of_dvd {p q : R[X]} (hq : q ≠ 0) (hpq : p ∣ q) (x : R) :
    p.rootMultiplicity x ≤ q.rootMultiplicity x := by
  obtain ⟨_, rfl⟩ := hpq
  exact Nat.le_of_add_right_le <| le_rootMultiplicity_mul x hq
/-
**Polynomial.pow_rootMultiplicity_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：pow_rootMultiplicity_not_dvd (p0 : p != 0) (a : R) : ¬(X - C a) ^ (rootMul
tiplicity a p + 1) ∣ p
参数：p0 : p != 0；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.rootMultiplicity_le_iff`：rootMultiplicity_le_iff (p0 : p != 0
) (a : R) (n : Nat) : rootMultiplicity a p <= n ↔ ¬(X - C a) ^ (n + 1) ∣ p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma pow_rootMultiplicity_not_dvd (p0 : p ≠ 0) (a : R) :
    ¬(X - C a) ^ (rootMultiplicity a p + 1) ∣ p := by rw [← rootMultiplicity_le_iff p0]

/-- See `Polynomial.rootMultiplicity_eq_natTrailingDegree` for the general case. -/
/-
**Polynomial.rootMultiplicity_eq_natTrailingDegree'** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial`。
形式化陈述：rootMultiplicity_eq_natTrailingDegree' : p.rootMultiplicity 0 = p.natTrail
ingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Polynomial.rootMultiplicity_le_iff`：rootMultiplicity_le_iff (p0 : p != 0
) (a : R) (n : Nat) : rootMultiplicity a p <= n ↔ ¬(X - C a) ^ (n + 1) ∣ p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Polynomial.X_pow_dvd_iff`：X_pow_dvd_iff {f : R[X]} {n : Nat} : X ^ n ∣ f
 ↔ forall d < n, f.coeff d = 0
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.trailingCoeff_nonzero_iff_nonzero`：trailingCoeff_nonzero_iff_
nonzero : trailingCoeff p != 0 ↔ p != 0
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用定理 `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`：coeff_eq_zero_of_lt_na
tTrailingDegree {p : R[X]} {n : Nat} (h : n < p.natTrailingDegree) : p.coeff n =
 0

--- 原说明 ---
See `Polynomial.rootMultiplicity_eq_natTrailingDegree` for the general case.
-/
lemma rootMultiplicity_eq_natTrailingDegree' : p.rootMultiplicity 0 = p.natTrailingDegree := by
  by_cases h : p = 0
  · simp only [h, rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h, map_zero, sub_zero, X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
      fun h' ↦ trailingCoeff_nonzero_iff_nonzero.2 h <| h' <| Nat.lt_add_one _⟩
  · rw [le_rootMultiplicity_iff h, map_zero, sub_zero, X_pow_dvd_iff]
    exact fun _ ↦ coeff_eq_zero_of_lt_natTrailingDegree

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
/-
**Polynomial.leadingCoeff_divByMonic_of_monic** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：leadingCoeff_divByMonic_of_monic (hmonic : q.Monic) (hdegree : q.degree <=
 p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff
参数：hmonic : q.Monic；hdegree : q.degree <= p.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.divByMonic_eq_zero_iff`：divByMonic_eq_zero_iff [Nontrivial R]
 (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_add_divByMonic`：degree_add_divByMonic (hq : Monic q) (
h : degree q <= degree p) : degree q + degree (p /ₘ q) = degree p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Polynomial.leadingCoeff_monic_mul`：leadingCoeff_monic_mul {p q : R[X]} (
hp : Monic p) : leadingCoeff (p * q) = leadingCoeff q

--- 原说明 ---
Division by a monic polynomial doesn't change the leading coefficient.
-/
lemma leadingCoeff_divByMonic_of_monic (hmonic : q.Monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by
  nontriviality
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← modByMonic_add_div p q]
  rw [leadingCoeff_add_of_degree_lt, leadingCoeff_monic_mul hmonic]
  rw [degree_mul' h, degree_add_divByMonic hmonic hdegree]
  exact (degree_modByMonic_lt p hmonic).trans_le hdegree

variable [IsDomain R]
/-
**Polynomial.degree_eq_one_of_irreducible_of_root** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial`。
形式化陈述：degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : Is
Root p x) : degree p = 1
参数：hi : Irreducible p；hx : IsRoot p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_isRoot.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_isUnit h
      rw [h₁] at h₂; exact absurd h₂ (by decide))
    fun hgu => by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_isUnit hgu, add_zero]
/-
**Polynomial._root_.Irreducible.not_isRoot_of_natDegree_ne_one** 是 Mathlib 中的一个引
理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.not_isRoot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree ≠ 1) {x : R} : ¬p.IsRoot x :=
  fun hr ↦ hdeg <| natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hi hr
/-
**Polynomial._root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one** 是 Mathlib 中的
一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree ≠ 1) : p.IsRoot = ⊥ :=
  le_bot_iff.mp fun _ ↦ hi.not_isRoot_of_natDegree_ne_one hdeg
/-
**Polynomial._root_.Irreducible.subsingleton_isRoot** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.subsingleton_isRoot
    (hi : Irreducible p) : { x | p.IsRoot x }.Subsingleton :=
  fun _ hx ↦ (subsingleton_isRoot_of_natDegree_eq_one <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hi hx) hx
/-
**Polynomial.leadingCoeff_divByMonic_X_sub_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p != 0) (a : R) : 
leadingCoeff (p /ₘ (X - C a)) = leadingCoeff p
参数：p : R[X]；hp : degree p != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Nat.WithBot.lt_zero_iff`：lt_zero_iff {n : WithBot Nat} : n < 0 ↔ n = ⊥
· 使用定理 `Polynomial.zero_divByMonic`：zero_divByMonic (p : R[X]) : 0 /ₘ p = 0
· 使用引理 `Polynomial.leadingCoeff_divByMonic_of_monic`：leadingCoeff_divByMonic_of_
monic (hmonic : q.Monic) (hdegree : q.degree <= p.degree) : (p /ₘ q).leadingCoef
f = p.leadingCoeff
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Nat.WithBot.one_le_iff_zero_lt`：one_le_iff_zero_lt {x : WithBot Nat} : 1
 <= x ↔ 0 < x
-/
lemma leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (X - C a)) = leadingCoeff p := by
  nontriviality
  rcases hp.lt_or_gt with hd | hd
  · rw [degree_eq_bot.mp <| Nat.WithBot.lt_zero_iff.mp hd, zero_divByMonic]
  refine leadingCoeff_divByMonic_of_monic (monic_X_sub_C a) ?_
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]
/-
**Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff** 是 Mathlib 中的一个引理，位于命名空间
 `Polynomial`。
形式化陈述：eq_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q) (h₁ :
 q.natDegree <= p.natDegree) (h₂ : p.leadingCoeff = q.leadingCoeff) : p = q
参数：hpq : p ∣ q；h₁ : q.natDegree <= p.natDegree；h₂ : p.leadingCoeff = q.leadingCo
eff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Polynomial.natDegree_le_of_dvd`：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q
 != 0) : p.natDegree <= q.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `left_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a = a + b ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_eq_left₀`：mul_eq_left₀ [IsLeftCancelMulZero M₀] (ha : a != 0) : a * 
b = a ↔ b = 1
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma eq_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : p.leadingCoeff = q.leadingCoeff) :
    p = q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simpa using h₂
  replace h₁ := (natDegree_le_of_dvd hpq hq).antisymm h₁
  obtain ⟨u, rfl⟩ := hpq
  rw [mul_ne_zero_iff] at hq
  rw [natDegree_mul hq.1 hq.2, left_eq_add] at h₁
  rw [eq_C_of_natDegree_eq_zero h₁, leadingCoeff_mul, leadingCoeff_C,
    eq_comm, mul_eq_left₀ (leadingCoeff_ne_zero.mpr hq.1)] at h₂
  rw [eq_C_of_natDegree_eq_zero h₁, h₂, map_one, mul_one]
/-
**Polynomial.associated_of_dvd_of_natDegree_le_of_leadingCoeff** 是 Mathlib 中的一个引
理，位于命名空间 `Polynomial`。
形式化陈述：associated_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ 
q) (h₁ : q.natDegree <= p.natDegree) (h₂ : q.leadingCoeff ∣ p.leadingCoeff) : As
sociated p q
参数：hpq : p ∣ q；h₁ : q.natDegree <= p.natDegree；h₂ : q.leadingCoeff ∣ p.leadingCo
eff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff`：eq_of_dvd_of_natDe
gree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q) (h₁ : q.natDegree <= p.natDeg
ree) (h₂ : p.leadingCoeff = q.leadingCoeff…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_right_dvd`：mul_right_dvd : a * u ∣ b ↔ a ∣ b
· 使用定理 `Polynomial.natDegree_mul_C`：natDegree_mul_C (a0 : a != 0) : (p * C a).na
tDegree = p.natDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
lemma associated_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : q.leadingCoeff ∣ p.leadingCoeff) :
    Associated p q :=
  have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map C.toMonoidHom u, eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩
/-
**Polynomial.associated_of_dvd_of_natDegree_le** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial`。
形式化陈述：associated_of_dvd_of_natDegree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
 (hq : q != 0) (h₁ : q.natDegree <= p.natDegree) : Associated p q
参数：hpq : p ∣ q；hq : q != 0；h₁ : q.natDegree <= p.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.associated_of_dvd_of_natDegree_le_of_leadingCoeff`：associated
_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q) (h₁ : q.natDe
gree <= p.natDegree) (h₂ : q.leadingCoeff ∣ p.lead…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsUnit.dvd`：dvd (hu : IsUnit u) : u ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
-/
lemma associated_of_dvd_of_natDegree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q ≠ 0)
    (h₁ : q.natDegree ≤ p.natDegree) : Associated p q :=
  associated_of_dvd_of_natDegree_le_of_leadingCoeff hpq h₁
    (IsUnit.dvd (by rwa [← leadingCoeff_ne_zero, ← isUnit_iff_ne_zero] at hq))
/-
**Polynomial.associated_of_dvd_of_degree_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：associated_of_dvd_of_degree_eq {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (h
₁ : p.degree = q.degree) : Associated p q
参数：hpq : p ∣ q；h₁ : p.degree = q.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Polynomial.associated_of_dvd_of_natDegree_le`：associated_of_dvd_of_natDe
gree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q != 0) (h₁ : q.natDegree
 <= p.natDegree) : Associated p q
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma associated_of_dvd_of_degree_eq {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
    (h₁ : p.degree = q.degree) : Associated p q :=
  (Classical.em (q = 0)).elim (fun hq ↦ (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))
/-
**Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le** 是 Mathlib 中的一
个引理，位于命名空间 `Polynomial`。
形式化陈述：eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommSemiring R] {
p q : R[X]} (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree <= p.natDegree) : 
q = C q.leadingCoeff * p
参数：hp : p.Monic；hdvd : p ∣ q；hdeg : q.natDegree <= p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le`：eq_mul_l
eadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic) (hdvd : 
p ∣ q) (hdeg : q.natDegree <= p.natDegree) : q = p *…
-/
lemma eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommSemiring R] {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = C q.leadingCoeff * p := by
  rw [mul_comm, ← eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]

end CommRing

end Polynomial

