/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.GroupWithZero.Equiv
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Order.Monotone.Defs

/-!
# Associated, prime, and irreducible elements.

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`,
however this is not true in general.

We also define an equivalence relation `Associated`
saying that two elements of a monoid differ by a multiplication by a unit.
Then we show that the quotient type `Associates` is a monoid
and prove basic properties of this quotient.
-/

public section

assert_not_exists IsOrderedMonoid Multiset

variable {M N : Type*}

section Prime

variable [CommMonoidWithZero M]

section Map

variable [CommMonoidWithZero N] {F : Type*} {G : Type*} [FunLike F M N]
variable [MonoidWithZeroHomClass F M N] [FunLike G N M] [MulHomClass G N M]
variable (f : F) (g : G) {p : M}

/-
**comap_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_prime (hinv : forall a, g (f a : N) = a) (hp : Prime (f p)) : Prime 
p
参数：hinv : forall a, g (f a : N) = a；hp : Prime (f p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem comap_prime (hinv : ∀ a, g (f a : N) = a) (hp : Prime (f p)) : Prime p :=
  ⟨fun h => hp.1 <| by simp [h], fun h => hp.2.1 <| h.map f, fun a b h => by
    refine
        (hp.2.2 (f a) (f b) <| by
              convert! map_dvd f h
              simp).imp
          ?_ ?_ <;>
      · intro h
        convert! ← map_dvd g h <;> apply hinv⟩
/-
**MulEquiv.prime_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.prime_iff {E : Type*} [EquivLike E M N] [MulEquivClass E M N] (e 
: E) : Prime (e p) ↔ Prime p
参数：e : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_prime`：comap_prime (hinv : forall a, g (f a : N) = a) (hp : Prime 
(f p)) : Prime p
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
-/
theorem MulEquiv.prime_iff {E : Type*} [EquivLike E M N] [MulEquivClass E M N] (e : E) :
    Prime (e p) ↔ Prime p := by
  let e := MulEquivClass.toMulEquiv e
  exact ⟨comap_prime e e.symm fun a => by simp,
    fun h => (comap_prime e.symm e fun a => by simp) <| (e.symm_apply_apply p).substr h⟩

end Map

variable {x y : M}

/-
**prime_units_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_units_mul (u : Mˣ) : Prime (↑u * y) ↔ Prime y
参数：u : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prime_units_mul (u : Mˣ) : Prime (↑u * y) ↔ Prime y := by simp [Prime]
/-
**prime_isUnit_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_isUnit_mul (h : IsUnit x) : Prime (x * y) ↔ Prime y
参数：h : IsUnit x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prime_units_mul`：prime_units_mul (u : Mˣ) : Prime (↑u * y) ↔ Prime y
-/
theorem prime_isUnit_mul (h : IsUnit x) : Prime (x * y) ↔ Prime y :=
  let ⟨u, hu⟩ := h
  hu ▸ prime_units_mul u
/-
**prime_mul_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_mul_units (u : Mˣ) : Prime (y * ↑u) ↔ Prime y
参数：u : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `prime_units_mul`：prime_units_mul (u : Mˣ) : Prime (↑u * y) ↔ Prime y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prime_mul_units (u : Mˣ) : Prime (y * ↑u) ↔ Prime y := by
  rw [mul_comm, prime_units_mul]
/-
**prime_mul_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_mul_isUnit (h : IsUnit x) : Prime (y * x) ↔ Prime y
参数：h : IsUnit x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prime_mul_units`：prime_mul_units (u : Mˣ) : Prime (y * ↑u) ↔ Prime y
-/
theorem prime_mul_isUnit (h : IsUnit x) : Prime (y * x) ↔ Prime y :=
  let ⟨u, hu⟩ := h
  hu ▸ prime_mul_units u

end Prime

section IsCancelMulZero

variable [CommMonoidWithZero M] [IsCancelMulZero M]

/-
**Prime.left_dvd_or_dvd_right_of_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.left_dvd_or_dvd_right_of_dvd_mul {p : M} (hp : Prime p) {a b : M} : 
a ∣ p * b -> p ∣ a ∨ a ∣ b
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
theorem Prime.left_dvd_or_dvd_right_of_dvd_mul {p : M} (hp : Prime p)
    {a b : M} : a ∣ p * b → p ∣ a ∨ a ∣ b := by
  rintro ⟨c, hc⟩
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
  · exact Or.inl h
  · rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc
    exact Or.inr (hc.symm ▸ dvd_mul_right _ _)
/-
**Prime.pow_dvd_of_dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.pow_dvd_of_dvd_mul_left {p a b : M} (hp : Prime p) (n : Nat) (h : ¬p
 ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b
参数：hp : Prime p；n : Nat；h : ¬p ∣ a；h' : p ^ n ∣ a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
theorem Prime.pow_dvd_of_dvd_mul_left {p a b : M} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_dvd b
  | succ n ih =>
    obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ]
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← pow_succ, mul_left_comm]
/-
**Prime.pow_dvd_of_dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.pow_dvd_of_dvd_mul_right {p a b : M} (hp : Prime p) (n : Nat) (h : ¬
p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a
参数：hp : Prime p；n : Nat；h : ¬p ∣ b；h' : p ^ n ∣ a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.pow_dvd_of_dvd_mul_left`：Prime.pow_dvd_of_dvd_mul_left {p a b : M}
 (hp : Prime p) (n : Nat) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Prime.pow_dvd_of_dvd_mul_right {p a b : M} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a := by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'
/-
**Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd {p a b : M} {n : Nat} (
hp : Prime p) (hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n) (hb : ¬p ^ 2 ∣ b) : p ∣ a
参数：hp : Prime p；hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n；hb : ¬p ^ 2 ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd {p a b : M}
    {n : ℕ} (hp : Prime p) (hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n) (hb : ¬p ^ 2 ∣ b) : p ∣ a := by
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  rcases hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hpow) with H | hbdiv
  · exact hp.dvd_of_dvd_pow H
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
  obtain ⟨y, hy⟩ := hpow
  -- Then we can divide out a common factor of `p ^ n` from the equation `hy`.
  have : a ^ n.succ * x ^ n = p * y := by
    refine mul_left_cancel₀ (pow_ne_zero n hp.ne_zero) ?_
    rw [← mul_assoc _ p, ← pow_succ, ← hy, mul_pow, ← mul_assoc (a ^ n.succ), mul_comm _ (p ^ n),
      mul_assoc]
  -- So `p ∣ a` (and we're done) or `p ∣ x`, which can't be the case since it implies `p^2 ∣ b`.
  refine hp.dvd_of_dvd_pow ((hp.dvd_or_dvd ⟨_, this⟩).resolve_right fun hdvdx => hb ?_)
  obtain ⟨z, rfl⟩ := hp.dvd_of_dvd_pow hdvdx
  rw [pow_two, ← mul_assoc]
  exact dvd_mul_right _ _
/-
**prime_pow_succ_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_pow_succ_dvd_mul {p x y : M} (h : Prime p) {i : Nat} (hxy : p ^ (i +
 1) ∣ x * y) : p ^ (i + 1) ∣ x ∨ p ∣ y
参数：h : Prime p；hxy : p ^ (i + 1) ∣ x * y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Prime.pow_dvd_of_dvd_mul_right`：Prime.pow_dvd_of_dvd_mul_right {p a b : 
M} (hp : Prime p) (n : Nat) (h : ¬p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a
-/
theorem prime_pow_succ_dvd_mul {p x y : M} (h : Prime p)
    {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) : p ^ (i + 1) ∣ x ∨ p ∣ y := by
  rw [or_iff_not_imp_right]
  exact fun a ↦ Prime.pow_dvd_of_dvd_mul_right h (i + 1) a hxy

variable {a p : M}
/-
**succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul (hp : Prime p) {a b : M} {k l : N
at} : p ^ k ∣ a -> p ^ l ∣ b -> p ^ (k + l + 1) ∣ a * b -> p ^ (k + 1) ∣ a ∨ p ^
 (l + 1) ∣ b
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul (hp : Prime p) {a b : M} {k l : ℕ} :
    p ^ k ∣ a → p ^ l ∣ b → p ^ (k + l + 1) ∣ a * b → p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
  have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z) := by
    simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz
  have hp0 : p ^ (k + l) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpd : p ∣ x * y := ⟨z, by rwa [mul_right_inj' hp0] at h⟩
  (hp.dvd_or_dvd hpd).elim
    (fun ⟨d, hd⟩ => Or.inl ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)
    fun ⟨d, hd⟩ => Or.inr ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩
/-
**Prime.not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.not_isSquare (hp : Prime p) : ¬IsSquare p
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Irreducible.not_isSquare`：Irreducible.not_isSquare (ha : Irreducible x) 
: ¬IsSquare x
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
-/
theorem Prime.not_isSquare (hp : Prime p) : ¬IsSquare p :=
  hp.irreducible.not_isSquare
/-
**IsSquare.not_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSquare.not_prime (ha : IsSquare a) : ¬Prime a
参数：ha : IsSquare a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_isSquare`：Prime.not_isSquare (hp : Prime p) : ¬IsSquare p
-/
theorem IsSquare.not_prime (ha : IsSquare a) : ¬Prime a := fun h => h.not_isSquare ha
/-
**not_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_prime_pow {n : Nat} (hn : n != 1) : ¬Prime (a ^ n)
参数：hn : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_irreducible_pow`：not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬
 Irreducible (x ^ n) | 0, _ => by simp | n + 2, _ => by intro ⟨h₁, h₂⟩ have
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
-/
theorem not_prime_pow {n : ℕ} (hn : n ≠ 1) : ¬Prime (a ^ n) := fun hp =>
  not_irreducible_pow hn hp.irreducible

end IsCancelMulZero

section CommMonoidWithZero

/-
**DvdNotUnit.isUnit_of_irreducible_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DvdNotUnit.isUnit_of_irreducible_right [CommMonoidWithZero M] {p q : M} (h
 : DvdNotUnit p q) (hq : Irreducible q) : IsUnit p
参数：h : DvdNotUnit p q；hq : Irreducible q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `irreducible_iff`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irreducible
 p ↔ ¬IsUnit p ∧ ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
-/
theorem DvdNotUnit.isUnit_of_irreducible_right [CommMonoidWithZero M] {p q : M}
    (h : DvdNotUnit p q) (hq : Irreducible q) : IsUnit p := by
  obtain ⟨_, x, hx, hx'⟩ := h
  exact ((irreducible_iff.1 hq).right hx').resolve_right hx
/-
**not_irreducible_of_not_isUnit_of_dvdNotUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_irreducible_of_not_isUnit_of_dvdNotUnit [CommMonoidWithZero M] {p q : 
M} (hp : ¬IsUnit p) (h : DvdNotUnit p q) : ¬Irreducible q
参数：hp : ¬IsUnit p；h : DvdNotUnit p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `DvdNotUnit.isUnit_of_irreducible_right`：DvdNotUnit.isUnit_of_irreducible
_right [CommMonoidWithZero M] {p q : M} (h : DvdNotUnit p q) (hq : Irreducible q
) : IsUnit p
-/
theorem not_irreducible_of_not_isUnit_of_dvdNotUnit [CommMonoidWithZero M] {p q : M}
    (hp : ¬IsUnit p) (h : DvdNotUnit p q) : ¬Irreducible q :=
  mt h.isUnit_of_irreducible_right hp

@[deprecated (since := "2026-08-02")]
alias not_irreducible_of_not_unit_dvdNotUnit := not_irreducible_of_not_isUnit_of_dvdNotUnit
/-
**DvdNotUnit.not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DvdNotUnit.not_isUnit [CommMonoidWithZero M] {p q : M} (hp : DvdNotUnit p 
q) : ¬IsUnit q
参数：hp : DvdNotUnit p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem DvdNotUnit.not_isUnit [CommMonoidWithZero M] {p q : M} (hp : DvdNotUnit p q) :
    ¬IsUnit q := by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (isUnit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (isUnit_iff_dvd_one.mp hc)))

@[deprecated (since := "2026-08-02")]
alias DvdNotUnit.not_unit := DvdNotUnit.not_isUnit

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CommMonoidWithZero M] [IsCancelMulZero M]

/-
**DvdNotUnit.ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DvdNotUnit.ne {p q : M} (h : DvdNotUnit p q) : p != q
参数：h : DvdNotUnit p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem DvdNotUnit.ne {p q : M} (h : DvdNotUnit p q) : p ≠ q := by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  simp_all
/-
**pow_injective_of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_injective_of_not_isUnit {q : M} (hq : ¬IsUnit q) (hq' : q != 0) : Func
tion.Injective fun n : Nat => q ^ n
参数：hq : ¬IsUnit q；hq' : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_lt_imp_ne`：Function.Injective.of_lt_imp_ne [Linear
Order α] {f : α -> β} (h : forall x y, x < y -> f x != f y) : Injective f
· 使用定理 `DvdNotUnit.ne`：DvdNotUnit.ne {p q : M} (h : DvdNotUnit p q) : p != q
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `not_isUnit_of_not_isUnit_dvd`：not_isUnit_of_not_isUnit_dvd {a b : α} (ha
 : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b
· 使用引理 `dvd_pow`：dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ 
n | 0, hn => (hn rfl).elim | n + 1, _ => by rw [pow_succ']; exact hab.mul_rig…
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_mul_pow_sub`：pow_mul_pow_sub (a : M) (h : m <= n) : a ^ m * a ^ (n -
 m) = a ^ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem pow_injective_of_not_isUnit {q : M} (hq : ¬IsUnit q)
    (hq' : q ≠ 0) : Function.Injective fun n : ℕ => q ^ n := by
  refine .of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), ?_, ?_⟩
  · exact not_isUnit_of_not_isUnit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_lt h).ne')
  · exact (pow_mul_pow_sub q h.le).symm
/-
**pow_inj_of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_inj_of_not_isUnit {q : M} (hq : ¬IsUnit q) (hq' : q != 0) {m n : Nat} 
: q ^ m = q ^ n ↔ m = n
参数：hq : ¬IsUnit q；hq' : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `pow_injective_of_not_isUnit`：pow_injective_of_not_isUnit {q : M} (hq : ¬
IsUnit q) (hq' : q != 0) : Function.Injective fun n : Nat => q ^ n
-/
theorem pow_inj_of_not_isUnit {q : M} (hq : ¬IsUnit q)
    (hq' : q ≠ 0) {m n : ℕ} : q ^ m = q ^ n ↔ m = n :=
  (pow_injective_of_not_isUnit hq hq').eq_iff

end CancelCommMonoidWithZero

/-
**IsRelPrime.of_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_map {M N F : Type*} [Monoid M] [Monoid N] [FunLike F M N] [M
ulHomClass F M N] (f : F) [IsLocalHom f] {a b : M} (hab : IsRelPrime (f a) (f b)
) : IsRelPrime a b
参数：f : F；hab : IsRelPrime (f a) (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_map`：IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit 
(f a)) : IsUnit a
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
-/
lemma IsRelPrime.of_map
    {M N F : Type*} [Monoid M] [Monoid N] [FunLike F M N] [MulHomClass F M N]
    (f : F) [IsLocalHom f] {a b : M}
    (hab : IsRelPrime (f a) (f b)) : IsRelPrime a b :=
  fun _ h₁ h₂ ↦ .of_map _ _ (hab (map_dvd f h₁) (map_dvd f h₂))
