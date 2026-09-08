/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.HEval
public import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Binomial expansions of powers of Hahn Series

We introduce binomial expansions using `embDomain`.

## Main Definitions
  * `HahnSeries.binomialFamily`

## Main results
  * coefficients of powers of binomials

-/

@[expose] public section

noncomputable section

namespace HahnSeries

variable {Γ R A : Type*}

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [BinomialRing R]

namespace SummableFamily

variable [CommRing A] [Algebra R A]

/-- A summable family of Hahn series, whose `n`th term is `Ring.choose r n • (x - 1) ^ n` when
`x` is close to `1` (more precisely, when `0 < (x - 1).orderTop`), and `0 ^ n` otherwise. These
terms give a formal expansion of `x ^ r` as `(1 + (x - 1)) ^ r`. -/
/-
**HahnSeries.SummableFamily.binomialFamily** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries
.SummableFamily`。
形式化陈述：binomialFamily (x : A⟦Γ⟧) (r : R) : SummableFamily Γ A Nat
参数：x : A⟦Γ⟧；r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A summable family of Hahn series, whose `n`th term is `Ring.choose r n • (x - 1)
 ^ n` when
`x` is close to `1` (more precisely, when `0 < (x - 1).orderTop`), and `0 ^ n` o
therwise. These
terms give a formal expansion of `x ^ r` as `(1 + (x - 1)) ^ r`.
-/
def binomialFamily (x : A⟦Γ⟧) (r : R) :
    SummableFamily Γ A ℕ :=
  powerSeriesFamily (x - 1) (PowerSeries.binomialSeries A r)

@[simp]
/-
**HahnSeries.SummableFamily.binomialFamily_apply** 是 Mathlib 中的一个定理，位于命名空间 `Hahn
Series.SummableFamily`。
形式化陈述：binomialFamily_apply {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : N
at) : binomialFamily x r n = Ring.choose r n • (x - 1) ^ n
参数：hx : 0 < (x - 1).orderTop；r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `PowerSeries.binomialSeries_coeff`：binomialSeries_coeff [Semiring A] [SMu
l R A] (r : R) (n : Nat) : coeff n (binomialSeries A r) = Ring.choose r n • 1
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `HahnModule.instIsScalarTowerHahnSeries`：∀ {Γ : Type u_1} {R : Type u_3} 
{V : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid V] [inst_2 : Zero
 R]   {S : Type u_6} [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binomialFamily_apply {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : ℕ) :
    binomialFamily x r n = Ring.choose r n • (x - 1) ^ n := by
  simp [hx, binomialFamily]

@[simp]
/-
**HahnSeries.SummableFamily.binomialFamily_apply_of_orderTop_nonpos** 是 Mathlib 
中的一个定理，位于命名空间 `HahnSeries.SummableFamily`。
形式化陈述：binomialFamily_apply_of_orderTop_nonpos {x : A⟦Γ⟧} (hx : ¬ 0 < (x - 1).ord
erTop) (r : R) (n : Nat) : binomialFamily x r n = 0 ^ n
参数：hx : ¬ 0 < (x - 1).orderTop；r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.binomialFamily.eq_1`：∀ {Γ : Type u_1} {R : Typ
e u_2} {A : Type u_3} [inst : LinearOrder Γ] [inst_1 : AddCommMonoid Γ]   [inst_
2 : IsOrderedCancelAddMonoid Γ] [in…
· 使用定理 `HahnSeries.SummableFamily.powerSeriesFamily_of_not_orderTop_pos`：powerSe
riesFamily_of_not_orderTop_pos {x : V⟦Γ⟧} (hx : ¬ 0 < x.orderTop) (f : PowerSeri
es R) : powerSeriesFamily x f = powerSeriesFamily 0 f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用引理 `PowerSeries.binomialSeries_coeff`：binomialSeries_coeff [Semiring A] [SMu
l R A] (r : R) (n : Nat) : coeff n (binomialSeries A r) = Ring.choose r n • 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.choose_zero_right'`：choose_zero_right' (r : R) : choose r 0 = (r + 
1) ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HahnSeries.SummableFamily.powers_zero`：powers_zero : powers (0 : R⟦Γ⟧) =
 .single 0 1
· 使用定理 `HahnSeries.SummableFamily.single_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {ι : Type u_7}   [inst_2 : De
cidableEq ι] (i : ι) (x : Ha…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
-/
theorem binomialFamily_apply_of_orderTop_nonpos {x : A⟦Γ⟧} (hx : ¬ 0 < (x - 1).orderTop)
    (r : R) (n : ℕ) :
    binomialFamily x r n = 0 ^ n := by
  rw [binomialFamily, powerSeriesFamily_of_not_orderTop_pos hx]
  by_cases hn : n = 0 <;> simp [hn]
/-
**HahnSeries.SummableFamily.binomialFamily_orderTop_pos** 是 Mathlib 中的一个定理，位于命名空
间 `HahnSeries.SummableFamily`。
形式化陈述：binomialFamily_orderTop_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R)
 {n : Nat} (hn : 0 < n) : 0 < (binomialFamily x r n).orderTop
参数：hx : 0 < (x - 1).orderTop；r : R；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `PowerSeries.binomialSeries_coeff`：binomialSeries_coeff [Semiring A] [SMu
l R A] (r : R) (n : Nat) : coeff n (binomialSeries A r) = Ring.choose r n • 1
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `HahnModule.instIsScalarTowerHahnSeries`：∀ {Γ : Type u_1} {R : Type u_3} 
{V : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid V] [inst_2 : Zero
 R]   {S : Type u_6} [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nsmul_pos_iff`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : LinearOrd
er M] [AddLeftMono M] {x : M} {n : ℕ},   n ≠ 0 → (0 < n • x ↔ 0 < x)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `HahnSeries.orderTop_nsmul_le_orderTop_pow`：orderTop_nsmul_le_orderTop_po
w [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R] {x
 : R⟦Γ⟧} {n : Nat} : n • x.orde…
· 使用定理 `HahnSeries.orderTop_le_orderTop_smul`：orderTop_le_orderTop_smul {Γ} [Lin
earOrder Γ] (r : R) (x : V⟦Γ⟧) : x.orderTop <= (r • x).orderTop
-/
theorem binomialFamily_orderTop_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) {n : ℕ}
    (hn : 0 < n) :
    0 < (binomialFamily x r n).orderTop := by
  simp only [binomialFamily, smulFamily_toFun, PowerSeries.binomialSeries_coeff, powers_toFun, hx,
    ↓reduceIte, smul_assoc, one_smul]
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  calc
    0 < n • (x - 1).orderTop := (nsmul_pos_iff (Nat.ne_zero_of_lt hn)).mpr hx
    _ ≤ ((x - 1) ^ n).orderTop := orderTop_nsmul_le_orderTop_pow
    _ ≤ ((Ring.choose r n) • ((x - 1) ^ n)).orderTop :=
      orderTop_le_orderTop_smul (Ring.choose r n) ((x - 1) ^ n)
/-
**HahnSeries.SummableFamily.binomialFamily_mem_support** 是 Mathlib 中的一个定理，位于命名空间
 `HahnSeries.SummableFamily`。
形式化陈述：binomialFamily_mem_support {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) 
(n : Nat) {g : Γ} (hg : g in (binomialFamily x r n).support) : 0 <= g
参数：hx : 0 < (x - 1).orderTop；r : R；n : Nat；hg : g in (binomialFamily x r n).supp
ort。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.SummableFamily.binomialFamily_apply`：binomialFamily_apply {x 
: A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : Nat) : binomialFamily x r n = R
ing.choose r n • (x - 1) ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ring.choose_zero_right'`：choose_zero_right' (r : R) : choose r 0 = (r + 
1) ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_pos`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α] {a : α},
 0 < ↑a ↔ 0 < a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `HahnSeries.SummableFamily.binomialFamily_orderTop_pos`：binomialFamily_or
derTop_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) {n : Nat} (hn : 0 < n)
 : 0 < (binomialFamily x r n).orderTop
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `HahnSeries.orderTop_le_of_coeff_ne_zero`：orderTop_le_of_coeff_ne_zero {Γ
} [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.orderTop <= g
-/
theorem binomialFamily_mem_support {x : A⟦Γ⟧}
    (hx : 0 < (x - 1).orderTop) (r : R) (n : ℕ) {g : Γ}
    (hg : g ∈ (binomialFamily x r n).support) : 0 ≤ g := by
  by_cases hn : n = 0; · simp_all
  exact le_of_lt (WithTop.coe_pos.mp (lt_of_lt_of_le (binomialFamily_orderTop_pos hx r
    (Nat.pos_of_ne_zero hn)) (orderTop_le_of_coeff_ne_zero hg)))
/-
**HahnSeries.SummableFamily.orderTop_hsum_binomialFamily_pos** 是 Mathlib 中的一个定理，
位于命名空间 `HahnSeries.SummableFamily`。
形式化陈述：orderTop_hsum_binomialFamily_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r
 : R) : (0 : WithTop Γ) < (SummableFamily.hsum (binomialFamily x r) - 1).orderTo
p
参数：hx : 0 < (x - 1).orderTop；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `HahnSeries.instSubsingleton`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Par
tialOrder Γ] [inst_1 : Zero R] [Subsingleton R],   Subsingleton (HahnSeries Γ R)
· 使用定理 `HahnSeries.orderTop_of_subsingleton`：orderTop_of_subsingleton [Subsingle
ton R] : x.orderTop = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.orderTop_self_sub_one_pos_iff`：orderTop_self_sub_one_pos_iff 
[LinearOrder Γ] [Zero Γ] [NonAssocRing R] [Nontrivial R] (x : R⟦Γ⟧) : 0 < (x - 1
).orderTop ↔ x.orderTop = 0 ∧ …
· 使用定理 `HahnSeries.SummableFamily.hsum_orderTop_of_le`：hsum_orderTop_of_le {s : 
SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop) (hg : forall b :
 α, forall g' in (s b).support, g <…
· 使用定理 `HahnSeries.SummableFamily.binomialFamily_apply`：binomialFamily_apply {x 
: A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : Nat) : binomialFamily x r n = R
ing.choose r n • (x - 1) ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ring.choose_zero_right'`：choose_zero_right' (r : R) : choose r 0 = (r + 
1) ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HahnSeries.orderTop_one`：orderTop_one [Zero R] [One R] [NeZero (1 : R)] 
: orderTop (1 : R⟦Γ⟧) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.SummableFamily.binomialFamily_mem_support`：binomialFamily_mem
_support {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : Nat) {g : Γ} (hg : 
g in (binomialFamily x r n).support) : 0 <…
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用定理 `HahnSeries.SummableFamily.binomialFamily_orderTop_pos`：binomialFamily_or
derTop_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) {n : Nat} (hn : 0 < n)
 : 0 < (binomialFamily x r n).orderTop
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.SummableFamily.hsum_leadingCoeff_of_le`：hsum_leadingCoeff_of_
le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop) (hg : fo
rall b : α, forall g' in (s b).support,…
-/
theorem orderTop_hsum_binomialFamily_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop)
    (r : R) : (0 : WithTop Γ) < (SummableFamily.hsum (binomialFamily x r) - 1).orderTop := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.eq_zero ((binomialFamily x r).hsum - 1)]
  · refine (orderTop_self_sub_one_pos_iff (binomialFamily x r).hsum).mpr ?_
    constructor
    · exact hsum_orderTop_of_le (by simp [hx]) (fun b g hg => binomialFamily_mem_support
        hx r b hg) fun b hb => coeff_eq_zero_of_lt_orderTop <| binomialFamily_orderTop_pos hx r <|
        Nat.zero_lt_of_ne_zero hb
    · have : (binomialFamily x r 0).coeff 0 = 1 := by simp [hx]
      rw [← this]
      refine hsum_leadingCoeff_of_le (g := 0) (a := 0) (by simp [hx]) ?_ ?_
      · intro b g' hg'
        exact binomialFamily_mem_support hx r b hg'
      · intro b hb
        exact coeff_eq_zero_of_lt_orderTop <| binomialFamily_orderTop_pos hx r <|
        Nat.zero_lt_of_ne_zero hb

end SummableFamily

open SummableFamily

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (orderTopSubOnePos Γ R) R where
  pow x r := toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r)

@[simp]
/-
**HahnSeries.binomial_power** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：binomial_power {x : orderTopSubOnePos Γ R} {r : R} : x ^ r = toOrderTopSub
OnePos (orderTop_hsum_binomialFamily_pos x.2 r)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binomial_power {x : orderTopSubOnePos Γ R} {r : R} :
    x ^ r = toOrderTopSubOnePos (orderTop_hsum_binomialFamily_pos x.2 r) :=
  rfl
/-
**HahnSeries.pow_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：pow_add {x : orderTopSubOnePos Γ R} {r s : R} : x ^ (r + s) = x ^ r * x ^ 
s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.orderTop_hsum_binomialFamily_pos`：orderTop_hsu
m_binomialFamily_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) : (0 : WithT
op Γ) < (SummableFamily.hsum (binomialFamily x r…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `HahnSeries.SummableFamily.powerSeriesFamily.congr_simp`：∀ {Γ : Type u_1}
 {R : Type u_3} {V : Type u_4} [inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ]
   [inst_2 : IsOrderedCancelAddMonoid Γ] [in…
· 使用引理 `PowerSeries.binomialSeries_add`：binomialSeries_add [Ring A] [Algebra R A
] (r s : R) : binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s
· 使用定理 `HahnSeries.SummableFamily.hsum_powerSeriesFamily_mul`：hsum_powerSeriesFa
mily_mul {x : V⟦Γ⟧} (a b : PowerSeries R) : (powerSeriesFamily x (a * b)).hsum =
 ((powerSeriesFamily x a).mul (powerSeries…
· 使用定理 `HahnSeries.SummableFamily.hsum_mul`：hsum_mul (s : SummableFamily Γ R α) 
(t : SummableFamily Γ R β) : (mul s t).hsum = s.hsum * t.hsum
· 使用定理 `HahnSeries.toOrderTopSubOnePos.congr_simp`：∀ {Γ : Type u_1} {R : Type u_
3} [inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAd
dMonoid Γ]   [inst_3 : CommRing…
· 使用定理 `HahnSeries.val_toOrderTopSubOnePos_coe`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
-/
theorem pow_add {x : orderTopSubOnePos Γ R} {r s : R} : x ^ (r + s) = x ^ r * x ^ s := by
  suffices (x ^ (r + s)).val = (x ^ r * x ^ s).val by exact SetLike.coe_eq_coe.mp this
  suffices (x ^ (r + s)).val.val = (x ^ r * x ^ s).val.val by exact Units.val_inj.mp this
  simp [binomialFamily, hsum_powerSeriesFamily_mul, hsum_mul]
/-
**HahnSeries.coeff_toOrderTopSubOnePos_pow** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries
`。
形式化陈述：coeff_toOrderTopSubOnePos_pow {g : Γ} (hg : 0 < g) (r s : R) (k : Nat) : H
ahnSeries.coeff (toOrderTopSubOnePos (orderTop_sub_pos hg r) ^ s).val (k • g) = 
Ring.choose s k • r ^ k
参数：hg : 0 < g；r s : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.orderTop_sub_pos`：orderTop_sub_pos [PartialOrder Γ] [Zero Γ] 
[AddCommGroup R] [One R] {g : Γ} (hg : 0 < g) (r : R) : 0 < ((1 + single g r) - 
1).orderTop
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.SummableFamily.orderTop_hsum_binomialFamily_pos`：orderTop_hsu
m_binomialFamily_pos {x : A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) : (0 : WithT
op Γ) < (SummableFamily.hsum (binomialFamily x r…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `HahnSeries.SummableFamily.binomialFamily.congr_simp`：∀ {Γ : Type u_1} {R
 : Type u_2} {A : Type u_3} [inst : LinearOrder Γ] [inst_1 : AddCommMonoid Γ]   
[inst_2 : IsOrderedCancelAddMonoid Γ] [in…
· 使用定理 `HahnSeries.val_toOrderTopSubOnePos_coe`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `HahnSeries.toOrderTopSubOnePos.congr_simp`：∀ {Γ : Type u_1} {R : Type u_
3} [inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAd
dMonoid Γ]   [inst_3 : CommRing…
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `HahnSeries.SummableFamily.binomialFamily_apply`：binomialFamily_apply {x 
: A⟦Γ⟧} (hx : 0 < (x - 1).orderTop) (r : R) (n : Nat) : binomialFamily x r n = R
ing.choose r n • (x - 1) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `HahnSeries.orderTop_single`：orderTop_single (h : r != 0) : (single a r).
orderTop = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HahnSeries.coeff_smul`：coeff_smul {r : R} {x : V⟦Γ⟧} {a : Γ} : (r • x).c
oeff a = r • x.coeff a
· 使用定理 `HahnSeries.single_pow`：single_pow (a : Γ) (n : Nat) (r : R) : single a r
 ^ n = single (n • a) (r ^ n)
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `nsmul_left_strictMono`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : P
reorder M] [AddLeftStrictMono M] {a : M},   0 < a → StrictMono fun x => x • a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 37 条，此处仅展示前 30 条）
-/
theorem coeff_toOrderTopSubOnePos_pow {g : Γ} (hg : 0 < g) (r s : R) (k : ℕ) :
    HahnSeries.coeff (toOrderTopSubOnePos (orderTop_sub_pos hg r) ^ s).val (k • g) =
      Ring.choose s k • r ^ k := by
  simp only [val_toOrderTopSubOnePos_coe, binomial_power, coeff_hsum, smul_eq_mul]
  rw [finsum_eq_single _ k, binomialFamily_apply (orderTop_sub_pos hg r), add_sub_cancel_left,
    single_pow, coeff_smul, coeff_single_same (k • g) (r ^ k), smul_eq_mul]
  intro n hn
  rw [binomialFamily_apply, add_sub_cancel_left, coeff_smul, single_pow, coeff_single_of_ne,
    smul_zero]
  · contrapose hn
    apply (StrictMono.injective (nsmul_left_strictMono hg)) hn.symm
  · by_cases hr : r = 0 <;> simp [hr, hg]

end HahnSeries

