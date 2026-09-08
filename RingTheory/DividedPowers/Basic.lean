/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.Ideal.Maps

/-! # Divided powers

Let `A` be a commutative (semi)ring and `I` be an ideal of `A`.
A *divided power* structure on `I` is the datum of operations `a n ↦ dpow a n`
satisfying relations that model the intuitive formula `dpow n a = a ^ n / n !` and
collected by the structure `DividedPowers`. The list of axioms is embedded in the structure:
To avoid coercions, we rather consider `DividedPowers.dpow : ℕ → A → A`, extended by 0.

* `DividedPowers.dpow_null` asserts that `dpow n x = 0` for `x ∉ I`
* `DividedPowers.dpow_mem` : `dpow n x ∈ I` for `n ≠ 0`

For `x y : A` and `m n : ℕ` such that `x ∈ I` and `y ∈ I`, one has
* `DividedPowers.dpow_zero` : `dpow 0 x = 1`
* `DividedPowers.dpow_one` : `dpow 1 x = 1`
* `DividedPowers.dpow_add` :
  `dpow n (x + y) = (antidiagonal n).sum fun k ↦ dpow k.1 x * dpow k.2 y`,
  this is the binomial theorem without binomial coefficients.
* `DividedPowers.dpow_mul`: `dpow n (a * x) = a ^ n * dpow n x`
* `DividedPowers.mul_dpow` : `dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x`
* `DividedPowers.dpow_comp` : `dpow m (dpow n x) = uniformBell m n * dpow (m * n) x`
* `DividedPowers.dividedPowersBot` : the trivial divided powers structure on the zero ideal
* `DividedPowers.prod_dpow`: a product of divided powers is a multinomial coefficient
  times a divided power
* `DividedPowers.dpow_sum`: the multinomial theorem for divided powers,
  without multinomial coefficients.
* `DividedPowers.ofRingEquiv`: transfer divided powers along `RingEquiv`
* `DividedPowers.equiv`: the equivalence `DividedPowers I ≃ DividedPowers J`,
  for `e : R ≃+* S`, and `I : Ideal R`, `J : Ideal S` such that `I.map e = J`
* `DividedPowers.exp`: the power series `Σ (dpow n a) X ^n`
* `DividedPowers.exp_add`: its multiplicativity

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

## Discussion

* In practice, one often has a single such structure to handle on a given ideal,
  but several ideals of the same ring might be considered.
  Without any explicit mention of the ideal, it is not clear whether such structures
  should be provided as instances.

* We do not provide any notation such as `a ^[n]` for `dpow a n`.

-/

@[expose] public section

open Finset Nat Ideal

section DividedPowersDefinition
/- ## Definition of divided powers -/

variable {A : Type*} [CommSemiring A] (I : Ideal A)

/-- The divided power structure on an ideal `I` of a commutative ring `A`. -/
/-
**DividedPowers** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{A : Type u_1} → [inst : CommSemiring A] → Ideal A → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The divided power structure on an ideal `I` of a commutative ring `A`.
-/
structure DividedPowers where
  /-- The divided power function underlying a divided power structure -/
  dpow : ℕ → A → A
  dpow_null : ∀ {n x} (_ : x ∉ I), dpow n x = 0
  dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1
  dpow_one : ∀ {x} (_ : x ∈ I), dpow 1 x = x
  dpow_mem : ∀ {n x} (_ : n ≠ 0) (_ : x ∈ I), dpow n x ∈ I
  dpow_add : ∀ {n} {x y} (_ : x ∈ I) (_ : y ∈ I),
    dpow n (x + y) = (antidiagonal n).sum fun k ↦ dpow k.1 x * dpow k.2 y
  dpow_mul : ∀ {n} {a : A} {x} (_ : x ∈ I),
    dpow n (a * x) = a ^ n * dpow n x
  mul_dpow : ∀ {m n} {x} (_ : x ∈ I),
    dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
  dpow_comp : ∀ {m n x} (_ : n ≠ 0) (_ : x ∈ I),
    dpow m (dpow n x) = uniformBell m n * dpow (m * n) x

variable (A) in
/-- The canonical `DividedPowers` structure on the zero ideal -/
/-
**dividedPowersBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dividedPowersBot : DividedPowers (⊥ : Ideal A) where dpow n a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `DividedPowers` structure on the zero ideal
-/
noncomputable def dividedPowersBot : DividedPowers (⊥ : Ideal A) where
  dpow n a := open scoped Classical in ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    simp only [mem_bot] at ha
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero ha := by
    rw [mem_bot.mp ha]
    simp only [and_self, ite_true]
  dpow_one ha := by
    simp [mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a ↦ False.elim (hn a)
  dpow_add ha hb := by
    rw [mem_bot.mp ha, mem_bot.mp hb, add_zero]
    simp only [true_and, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · symm
      apply sum_eq_zero
      grind [mem_antidiagonal]
  dpow_mul {n} _ _ hx := by
    rw [mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  mul_dpow {m n x} hx := by
    rw [mem_bot.mp hx]
    simp only [true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg]
      exact not_and_of_not_right (m = 0) hn
  dpow_comp m {n a} hn ha := by
    rw [mem_bot.mp ha]
    simp only [true_and, ite_eq_right_iff, _root_.mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm : m = 0
    · simp [hm, uniformBell_zero_left, hn]
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]
/-
**dividedPowersBot_dpow_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dividedPowersBot_dpow_eq [DecidableEq A] (n : Nat) (a : A) : (dividedPower
sBot A).dpow n a = if a = 0 ∧ n = 0 then 1 else 0
参数：n : Nat；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma dividedPowersBot_dpow_eq [DecidableEq A] (n : ℕ) (a : A) :
    (dividedPowersBot A).dpow n a =
      if a = 0 ∧ n = 0 then 1 else 0 := by
  simp [dividedPowersBot]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited (DividedPowers (⊥ : Ideal A)) :=
  ⟨dividedPowersBot A⟩

/-- The coercion from the divided powers structures to functions -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from the divided powers structures to functions
-/
instance : CoeFun (DividedPowers I) fun _ ↦ ℕ → A → A := ⟨fun hI ↦ hI.dpow⟩

variable {I} in
@[ext]
/-
**DividedPowers.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DividedPowers.ext (hI : DividedPowers I) (hI' : DividedPowers I) (h_eq : f
orall (n : Nat) {x : A} (_ : x in I), hI.dpow n x = hI'.dpow n x) : hI = hI'
参数：hI : DividedPowers I；hI' : DividedPowers I；h_eq : forall (n : Nat) {x : A} (_
 : x in I), hI.dpow n x = hI'.dpow n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.mk.injEq`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (dpow : ℕ → A → A)   (dpow_null : ∀ {n : ℕ} {x : A}, x ∉ I → dpow n x = 0
) (dpow_zero…
-/
theorem DividedPowers.ext (hI : DividedPowers I) (hI' : DividedPowers I)
    (h_eq : ∀ (n : ℕ) {x : A} (_ : x ∈ I), hI.dpow n x = hI'.dpow n x) :
    hI = hI' := by
  obtain ⟨hI, h₀, _⟩ := hI
  obtain ⟨hI', h₀', _⟩ := hI'
  simp only [mk.injEq]
  grind
/-
**DividedPowers.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DividedPowers.coe_injective : Function.Injective (fun (h : DividedPowers I
) => (h : Nat -> A -> A))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.ext`：DividedPowers.ext (hI : DividedPowers I) (hI' : Divid
edPowers I) (h_eq : forall (n : Nat) {x : A} (_ : x in I), hI.dpow n x = hI'.dpo
w n x) …
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem DividedPowers.coe_injective :
    Function.Injective (fun (h : DividedPowers I) ↦ (h : ℕ → A → A)) := fun hI hI' h ↦ by
  ext n x
  exact congr_fun (congr_fun h n) x

end DividedPowersDefinition

namespace DividedPowers

section BasicLemmas

/- ## Basic lemmas for divided powers -/

variable {A : Type*} [CommSemiring A] {I : Ideal A} {a b : A}

/-- Variant of `DividedPowers.dpow_add` with a sum on `range (n + 1)` -/
/-
**DividedPowers.dpow_add'** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_add' (hI : DividedPowers I) {n : Nat} (ha : a in I) (hb : b in I) : h
I.dpow n (a + b) = (range (n + 1)).sum fun k => hI.dpow k a * hI.dpow (n - k) b
参数：hI : DividedPowers I；ha : a in I；hb : b in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.dpow_add`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {x y : A},   x ∈ I → y ∈ I → self.dpow n
 (x + y) = ∑…
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…

--- 原说明 ---
Variant of `DividedPowers.dpow_add` with a sum on `range (n + 1)`
-/
theorem dpow_add' (hI : DividedPowers I) {n : ℕ} (ha : a ∈ I) (hb : b ∈ I) :
    hI.dpow n (a + b) = (range (n + 1)).sum fun k ↦ hI.dpow k a * hI.dpow (n - k) b := by
  rw [hI.dpow_add ha hb, sum_antidiagonal_eq_sum_range_succ_mk]

/-- The exponential series of an element in the context of divided powers,
`Σ (dpow n a) X ^ n` -/
/-
**DividedPowers.exp** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers`。
形式化陈述：exp (hI : DividedPowers I) (a : A) : PowerSeries A
参数：hI : DividedPowers I；a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exponential series of an element in the context of divided powers,
`Σ (dpow n a) X ^ n`
-/
def exp (hI : DividedPowers I) (a : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ hI.dpow n a

/-- A more general of `DividedPowers.exp_add` -/
/-
**DividedPowers.exp_add'** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：exp_add' (dp : Nat -> A -> A) (dp_add : forall n, dp n (a + b) = (antidiag
onal n).sum fun k => dp k.1 a * dp k.2 b) : PowerSeries.mk (fun n => dp n (a + b
)) = (PowerSeries.mk fun n => dp n a) * (PowerSeries.mk fun n => dp n b)
参数：dp : Nat -> A -> A；dp_add : forall n, dp n (a + b) = (antidiagonal n).sum fun
 k => dp k.1 a * dp k.2 b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A more general of `DividedPowers.exp_add`
-/
theorem exp_add' (dp : ℕ → A → A)
    (dp_add : ∀ n, dp n (a + b) = (antidiagonal n).sum fun k ↦ dp k.1 a * dp k.2 b) :
    PowerSeries.mk (fun n ↦ dp n (a + b)) =
      (PowerSeries.mk fun n ↦ dp n a) * (PowerSeries.mk fun n ↦ dp n b) := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, dp_add n,
    sum_antidiagonal_eq_sum_range_succ_mk]
/-
**DividedPowers.exp_add** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：exp_add (hI : DividedPowers I) (ha : a in I) (hb : b in I) : hI.exp (a + b
) = hI.exp a * hI.exp b
参数：hI : DividedPowers I；ha : a in I；hb : b in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.exp_add'`：exp_add' (dp : Nat -> A -> A) (dp_add : forall n
, dp n (a + b) = (antidiagonal n).sum fun k => dp k.1 a * dp k.2 b) : PowerSerie
s.mk (fun n …
· 使用定理 `DividedPowers.dpow_add`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {x y : A},   x ∈ I → y ∈ I → self.dpow n
 (x + y) = ∑…
-/
theorem exp_add (hI : DividedPowers I) (ha : a ∈ I) (hb : b ∈ I) :
    hI.exp (a + b) = hI.exp a * hI.exp b :=
  exp_add' _ (fun _ ↦ hI.dpow_add ha hb)

variable (hI : DividedPowers I)

/-! ## Rewriting lemmas -/

/-
**DividedPowers.dpow_smul** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_smul {n : Nat} (ha : a in I) : hI.dpow n (b • a) = b ^ n • hI.dpow n 
a
参数：ha : a in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.dpow_mul`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {a x : A},   x ∈ I → self.dpow n (a * x)
 = a ^ n * s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
## Rewriting lemmas
-/
theorem dpow_smul {n : ℕ} (ha : a ∈ I) :
    hI.dpow n (b • a) = b ^ n • hI.dpow n a := by
  simp only [smul_eq_mul, hI.dpow_mul, ha]
/-
**DividedPowers.dpow_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_mul_right {n : Nat} (ha : a in I) : hI.dpow n (a * b) = hI.dpow n a *
 b ^ n
参数：ha : a in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `DividedPowers.dpow_mul`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {a x : A},   x ∈ I → self.dpow n (a * x)
 = a ^ n * s…
-/
theorem dpow_mul_right {n : ℕ} (ha : a ∈ I) :
    hI.dpow n (a * b) = hI.dpow n a * b ^ n := by
  rw [mul_comm, hI.dpow_mul ha, mul_comm]
/-
**DividedPowers.dpow_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_smul_right {n : Nat} (ha : a in I) : hI.dpow n (a • b) = hI.dpow n a 
• b ^ n
参数：ha : a in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `DividedPowers.dpow_mul_right`：dpow_mul_right {n : Nat} (ha : a in I) : h
I.dpow n (a * b) = hI.dpow n a * b ^ n
-/
theorem dpow_smul_right {n : ℕ} (ha : a ∈ I) :
    hI.dpow n (a • b) = hI.dpow n a • b ^ n := by
  rw [smul_eq_mul, hI.dpow_mul_right ha, smul_eq_mul]
/-
**DividedPowers.factorial_mul_dpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowe
rs`。
形式化陈述：factorial_mul_dpow_eq_pow {n : Nat} (ha : a in I) : (n ! : A) * hI.dpow n 
a = a ^ n
参数：ha : a in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_zero`：Nat.factorial 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `DividedPowers.dpow_zero`：∀ {A : Type u_1} [inst : CommSemiring A] {I : I
deal A} (self : DividedPowers I) {x : A}, x ∈ I → self.dpow 0 x = 1
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `DividedPowers.mul_dpow`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {m n : ℕ} {x : A},   x ∈ I → self.dpow m x * sel
f.dpow n x =…
· 使用定理 `DividedPowers.dpow_one`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {x : A}, x ∈ I → self.dpow 1 x = x
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem factorial_mul_dpow_eq_pow {n : ℕ} (ha : a ∈ I) :
    (n ! : A) * hI.dpow n a = a ^ n := by
  induction n with
  | zero => rw [factorial_zero, cast_one, one_mul, pow_zero, hI.dpow_zero ha]
  | succ n ih =>
    rw [factorial_succ, mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← choose_symm_add, cast_mul, mul_assoc,
      ← hI.mul_dpow ha, ← mul_assoc, ih, hI.dpow_one ha, pow_succ, mul_comm]
/-
**DividedPowers.dpow_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_eval_zero {n : Nat} (hn : n != 0) : hI.dpow n 0 = 0
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `DividedPowers.dpow_mul`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {a x : A},   x ∈ I → self.dpow n (a * x)
 = a ^ n * s…
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), hI.dpow_mul I.zero_mem,
    zero_pow hn, zero_mul, zero_mul]

/-- If an element of a divided power ideal is killed by multiplication
by some nonzero integer `n`, then its `n`th power is zero.

Proposition 1.2.7 of [Berthelot-1974], part (i). -/
/-
**DividedPowers.nilpotent_of_mem_dpIdeal** 是 Mathlib 中的一个定理，位于命名空间 `DividedPower
s`。
形式化陈述：nilpotent_of_mem_dpIdeal {n : Nat} (hn : n != 0) (hnI : forall {y}, y in I
 -> n • y = 0) (hI : DividedPowers I) (ha : a in I) : a ^ n = 0
参数：hn : n != 0；hnI : forall {y}, y in I -> n • y = 0；hI : DividedPowers I；ha : a
 in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.mul_factorial_pred`：mul_factorial_pred (hn : n != 0) : n * (n - 1)! 
= n !
· 使用定理 `DividedPowers.factorial_mul_dpow_eq_pow`：factorial_mul_dpow_eq_pow {n : 
Nat} (ha : a in I) : (n ! : A) * hI.dpow n a = a ^ n
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `DividedPowers.dpow_mem`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {x : A},   n ≠ 0 → x ∈ I → self.dpow n x
 ∈ I

--- 原说明 ---
If an element of a divided power ideal is killed by multiplication
by some nonzero integer `n`, then its `n`th power is zero.

Proposition 1.2.7 of [Berthelot-1974], part (i).
-/
theorem nilpotent_of_mem_dpIdeal {n : ℕ} (hn : n ≠ 0) (hnI : ∀ {y}, y ∈ I → n • y = 0)
    (hI : DividedPowers I) (ha : a ∈ I) : a ^ n = 0 := by
  have h_fac : (n ! : A) * hI.dpow n a = n • ((n - 1)! : A) * hI.dpow n a := by
    rw [nsmul_eq_mul, ← cast_mul, mul_factorial_pred hn]
  rw [← hI.factorial_mul_dpow_eq_pow ha, h_fac, smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1)! : A) (hI.dpow_mem hn ha))

/-- If J is another ideal of A with divided powers,
then the divided powers of I and J coincide on I • J

[Berthelot-1974], 1.6.1 (ii) -/
/-
**DividedPowers.coincide_on_smul** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : Nat} (ha : a in
 I • J) : hI.dpow n a = hJ.dpow n a
参数：hJ : DividedPowers J；ha : a in I • J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.smul_induction_on'`：smul_induction_on' {x : M} (hx : x in I • 
N) {p : forall x, x in I • N -> Prop} (smul : forall (r : A) (hr : r in I) (n : 
M) (hn : n in N), …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `DividedPowers.dpow_mul`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {a x : A},   x ∈ I → self.dpow n (a * x)
 = a ^ n * s…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DividedPowers.factorial_mul_dpow_eq_pow`：factorial_mul_dpow_eq_pow {n : 
Nat} (ha : a in I) : (n ! : A) * hI.dpow n a = a ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `DividedPowers.dpow_add`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {x y : A},   x ∈ I → y ∈ I → self.dpow n
 (x + y) = ∑…
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
If J is another ideal of A with divided powers,
then the divided powers of I and J coincide on I • J

[Berthelot-1974], 1.6.1 (ii)
-/
theorem coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : ℕ} (ha : a ∈ I • J) :
    hI.dpow n a = hJ.dpow n a := by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [smul_eq_mul, hJ.dpow_mul hb, mul_comm a b, hI.dpow_mul ha,
      ← hJ.factorial_mul_dpow_eq_pow hb, ← hI.factorial_mul_dpow_eq_pow ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add (mul_le_left hx) (mul_le_left hy),
      hJ.dpow_add (mul_le_right hx) (mul_le_right hy)]
    apply sum_congr rfl
    intro k _
    rw [hx', hy']

/-- A product of divided powers is a multinomial coefficient times the divided power

[Roby-1965], formula (III') -/
/-
**DividedPowers.prod_dpow** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：prod_dpow {ι : Type*} {s : Finset ι} {n : ι -> Nat} (ha : a in I) : (s.pro
d fun i => hI.dpow (n i) a) = multinomial s n * hI.dpow (s.sum n) a
参数：ha : a in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.multinomial_empty`：∀ {α : Type u_1} (f : α → ℕ), Nat.multinomial ∅ f
 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `DividedPowers.dpow_zero`：∀ {A : Type u_1} [inst : CommSemiring A] {I : I
deal A} (self : DividedPowers I) {x : A}, x ∈ I → self.dpow 0 x = 1
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `DividedPowers.mul_dpow`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {m n : ℕ} {x : A},   x ∈ I → self.dpow m x * sel
f.dpow n x =…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用引理 `Nat.multinomial_insert`：multinomial_insert [DecidableEq α] (ha : a ∉ s) 
(f : α -> Nat) : multinomial (insert a s) f = (f a + ∑ i in s, f i).choose (f a)
 * multinomi…
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n

--- 原说明 ---
A product of divided powers is a multinomial coefficient times the divided power

[Roby-1965], formula (III')
-/
theorem prod_dpow {ι : Type*} {s : Finset ι} {n : ι → ℕ} (ha : a ∈ I) :
    (s.prod fun i ↦ hI.dpow (n i) a) = multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert _ _ hi hrec =>
    rw [prod_insert hi, hrec, ← mul_assoc, mul_comm (hI.dpow (n _) a),
      mul_assoc, hI.mul_dpow ha, ← sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [multinomial_insert hi, mul_comm, cast_mul, sum_insert hi]

-- TODO : can probably be simplified using `DividedPowers.exp`

/-- Lemma towards `dpow_sum` when we only have partial information on a divided power ideal -/
/-
**DividedPowers.dpow_sum'** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_sum' {M : Type*} [AddCommMonoid M] {I : AddSubmonoid M} (dpow : Nat -
> M -> A) (dpow_zero : forall {x}, x in I -> dpow 0 x = 1) (dpow_add : forall {n
 x y}, x in I -> y in I -> dpow n (x + y) = (antidiagonal n).sum fun k => dpow k
.1 x * dpow k.2 y) (dpow_eval_zero : forall {n : Nat}, n != 0 -> dpow n 0 = 0) {
ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι -> M} (hx : forall i in s, x i 
in I) {n : Nat} : dpow n (s.sum x) = (s.sym n).sum fun k => s.prod fun i => dpow
 (Multiset.count i k) (x i
参数：dpow : Nat -> M -> A；dpow_zero : forall {x}, x in I -> dpow 0 x = 1；dpow_add 
: forall {n x y}, x in I -> y in I -> dpow n (x + y) = (antidiagonal n).sum fun 
k => dpow k.1 x * dpow k.2 y；dpow_eval_zero : forall {n : Nat}, n != 0 -> dpow n
 0 = 0；hx : forall i in s, x i in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddSubmonoid.zero_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : Add
Submonoid M), 0 ∈ S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.sym_eq_empty`：sym_eq_empty : s.sym n = ∅ ↔ n != 0 ∧ s = ∅
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `AddSubmonoid.sum_mem`：∀ {M : Type u_4} [inst : AddCommMonoid M] (S : Add
Submonoid M) {ι : Type u_5} {t : Finset ι} {f : ι → M},   (∀ c ∈ t, f c ∈ S) → ∑
 c ∈ t, f …
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `Finset.sum_bij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a
 : ι)…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Lemma towards `dpow_sum` when we only have partial information on a divided powe
r ideal
-/
theorem dpow_sum' {M : Type*} [AddCommMonoid M] {I : AddSubmonoid M} (dpow : ℕ → M → A)
    (dpow_zero : ∀ {x}, x ∈ I → dpow 0 x = 1)
    (dpow_add : ∀ {n x y}, x ∈ I → y ∈ I →
      dpow n (x + y) = (antidiagonal n).sum fun k ↦ dpow k.1 x * dpow k.2 y)
    (dpow_eval_zero : ∀ {n : ℕ}, n ≠ 0 → dpow n 0 = 0)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → M} (hx : ∀ i ∈ s, x i ∈ I) {n : ℕ} :
    dpow n (s.sum x) = (s.sym n).sum fun k ↦ s.prod fun i ↦ dpow (Multiset.count i k) (x i) := by
  simp only [sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn]
      rw [dpow_zero I.zero_mem]
      simp only [sym_zero, card_singleton, cast_one]
    · rw [dpow_eval_zero hn, eq_comm, ← cast_zero]
      apply congr_arg
      rw [card_eq_zero, sym_eq_empty]
      exact ⟨hn, rfl⟩
  | insert a s ha ih =>
    -- This should be golfable using `Finset.symInsertEquiv`
    have hx' : ∀ i, i ∈ s → x i ∈ I := fun i hi ↦ hx i (mem_insert_of_mem hi)
    simp_rw [sum_insert ha,
      dpow_add (hx a (mem_insert_self a s)) (I.sum_mem fun i ↦ hx' i),
      sum_range, ih hx', mul_sum, sum_sigma', eq_comm]
    apply sum_bij'
      (fun m _ ↦ m.filterNe a)
      (fun m _ ↦ m.2.fill a m.1)
      (fun m hm ↦ mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm ↦ by
        simp only [succ_eq_add_one, mem_sym_iff, mem_insert, Sym.mem_fill_iff]
        simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
        intro b
        apply Or.imp (fun h ↦ h.2) (fun h ↦ hm b h))
      (fun m _ ↦ m.fill_filterNe a)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 ↦ ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← m.fill_filterNe a]
      exact Sym.count_coe_fill_of_ne (ne_of_mem_of_not_mem hi ha)
    · intro m hm
      convert! sym_filterNe_mem a hm
      rw [erase_insert ha]

variable {ι : Type*} [DecidableEq ι]

/-- A “multinomial” theorem for divided powers — without multinomial coefficients. -/
/-
**DividedPowers.dpow_sum** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_sum {s : Finset ι} {x : ι -> A} (hx : forall i in s, x i in I) {n : N
at} : hI.dpow n (s.sum x) = (s.sym n).sum fun k => s.prod fun i => hI.dpow (Mult
iset.count i k) (x i)
参数：hx : forall i in s, x i in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.dpow_sum'`：dpow_sum' {M : Type*} [AddCommMonoid M] {I : Ad
dSubmonoid M} (dpow : Nat -> M -> A) (dpow_zero : forall {x}, x in I -> dpow 0 x
 = 1) (dpow_a…
· 使用定理 `DividedPowers.dpow_zero`：∀ {A : Type u_1} [inst : CommSemiring A] {I : I
deal A} (self : DividedPowers I) {x : A}, x ∈ I → self.dpow 0 x = 1
· 使用定理 `DividedPowers.dpow_add`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {x y : A},   x ∈ I → y ∈ I → self.dpow n
 (x + y) = ∑…
· 使用定理 `DividedPowers.dpow_eval_zero`：dpow_eval_zero {n : Nat} (hn : n != 0) : h
I.dpow n 0 = 0

--- 原说明 ---
A “multinomial” theorem for divided powers — without multinomial coefficients.
-/
theorem dpow_sum {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) {n : ℕ} :
    hI.dpow n (s.sum x) =
      (s.sym n).sum fun k ↦ s.prod fun i ↦ hI.dpow (Multiset.count i k) (x i) :=
  dpow_sum' hI.dpow hI.dpow_zero hI.dpow_add hI.dpow_eval_zero hx

/-- A "multinomial" theorem for divided powers — without multinomial coefficients — for finitely
supported functions. -/
/-
**DividedPowers.dpow_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_finsupp_sum {x : ι ->₀ A} (hx : forall i, x i in I) {n : Nat} : hI.dp
ow n (x.sum fun _ r => r) = ∑ k in (x.support.sym n), x.prod fun i r => hI.dpow 
(Multiset.count i k) r
参数：hx : forall i, x i in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DividedPowers.dpow_sum`：dpow_sum {s : Finset ι} {x : ι -> A} (hx : foral
l i in s, x i in I) {n : Nat} : hI.dpow n (s.sum x) = (s.sym n).sum fun k => s.p
rod fun i =>…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A "multinomial" theorem for divided powers — without multinomial coefficients — 
for finitely
supported functions.
-/
theorem dpow_finsupp_sum {x : ι →₀ A} (hx : ∀ i, x i ∈ I) {n : ℕ} :
    hI.dpow n (x.sum fun _ r ↦ r) =
      ∑ k ∈ (x.support.sym n), x.prod fun i r ↦ hI.dpow (Multiset.count i k) r := by
  simp [Finsupp.sum, hI.dpow_sum (fun i _ ↦ hx i), Finsupp.prod]
/-
**DividedPowers.dpow_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`
。
形式化陈述：dpow_linearCombination {S : Type*} [CommSemiring S] [Algebra A S] {J : Ide
al S} (hJ : DividedPowers J) {b : ι -> S} {x : ι ->₀ A} (hx : forall i in x.supp
ort, b i in J) {n : Nat} : hJ.dpow n (x.sum fun i r => r • (b i)) = ∑ k in x.sup
port.sym n, x.prod fun i r => r ^ (Multiset.count i k) • hJ.dpow (Multiset.count
 i k) (b i)
参数：hJ : DividedPowers J；hx : forall i in x.support, b i in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `DividedPowers.dpow_sum`：dpow_sum {s : Finset ι} {x : ι -> A} (hx : foral
l i in s, x i in I) {n : Nat} : hI.dpow n (s.sum x) = (s.sym n).sum fun k => s.p
rod fun i =>…
· 使用定理 `Submodule.smul_of_tower_mem`：smul_of_tower_mem [SMul S R] [SMul S M] [Is
ScalarTower S R M] (r : S) (h : x in p) : r • x in p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `DividedPowers.dpow_mul`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {a x : A},   x ∈ I → self.dpow n (a * x)
 = a ^ n * s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem dpow_linearCombination {S : Type*} [CommSemiring S] [Algebra A S] {J : Ideal S}
    (hJ : DividedPowers J) {b : ι → S} {x : ι →₀ A} (hx : ∀ i ∈ x.support, b i ∈ J) {n : ℕ} :
    hJ.dpow n (x.sum fun i r ↦ r • (b i)) =
      ∑ k ∈ x.support.sym n,
        x.prod fun i r ↦ r ^ (Multiset.count i k) • hJ.dpow (Multiset.count i k) (b i) := by
  rw [Finsupp.sum, hJ.dpow_sum (fun i hi ↦ Submodule.smul_of_tower_mem J _ (hx i hi))]
  apply Finset.sum_congr rfl
  intros
  apply Finset.prod_congr rfl
  intro i hi
  rw [Algebra.smul_def, hJ.dpow_mul (hx i hi), ← map_pow, ← Algebra.smul_def]

/-- Given a nonempty `s : Finset ι` and a family `r : ι → R` such that `r i ∈ I` for all `i ∈ S`,
  one has `hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.dpow n (r i))`
  for all `n : ℕ`. -/
/-
**DividedPowers.dpow_prod** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_prod {ι : Type*} {r : ι -> A} {s : Finset ι} (hs : s.Nonempty) (hs' :
 forall i in s, r i in I) {n : Nat} : hI.dpow n (∏ i in s, r i) = n.factorial ^ 
(s.card - 1) • (∏ i in s, hI.dpow n (r i))
参数：hs : s.Nonempty；hs' : forall i in s, r i in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `DividedPowers.dpow_mul`：∀ {A : Type u_1} [inst : CommSemiring A] {I : Id
eal A} (self : DividedPowers I) {n : ℕ} {a x : A},   x ∈ I → self.dpow n (a * x)
 = a ^ n * s…
· 使用定理 `Finset.prod_eq_prod_sdiff_singleton_mul`：prod_eq_prod_sdiff_singleton_mu
l [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M) : ∏ x in s, f
 x = (∏ x in s \ {i}, f x) * …
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `DividedPowers.factorial_mul_dpow_eq_pow`：factorial_mul_dpow_eq_pow {n : 
Nat} (ha : a in I) : (n ! : A) * hI.dpow n a = a ^ n
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty {s : Finset 
α} : ¬s.Nonempty ↔ s = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Given a nonempty `s : Finset ι` and a family `r : ι → R` such that `r i ∈ I` for
 all `i ∈ S`,
  one has `hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.
dpow n (r i))`
  for all `n : ℕ`.
-/
theorem dpow_prod {ι : Type*} {r : ι → A} {s : Finset ι} (hs : s.Nonempty)
    (hs' : ∀ i ∈ s, r i ∈ I) {n : ℕ} :
    hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.dpow n (r i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | @insert a s has hrec =>
    rw [Finset.prod_insert has]
    by_cases h : s.Nonempty
    · rw [dpow_mul]
      · simp only [Finset.card_insert_of_notMem has, add_tsub_cancel_right, nsmul_eq_mul,
          Nat.cast_pow, Finset.prod_insert has,
          hrec h (fun i hi ↦ hs' i (mem_insert_of_mem hi)), ← mul_assoc]
        apply congr_arg₂ _ _ rfl
        have : #s = #s - 1 + 1 := by grind
        nth_rewrite 2 [this]
        rw [mul_comm, pow_succ, mul_assoc, hI.factorial_mul_dpow_eq_pow]
        exact hs' a (mem_insert_self a s)
      · obtain ⟨j, hj⟩ := h
        rw [Finset.prod_eq_prod_sdiff_singleton_mul hj]
        exact I.mul_mem_left _ (hs' j (mem_insert_of_mem hj))
    · simp [not_nonempty_iff_eq_empty.mp h]

end BasicLemmas

section Equiv
/- ## Relation of divided powers with ring equivalences -/

variable {A B : Type*} [CommSemiring A] {I : Ideal A} [CommSemiring B] {J : Ideal B}
  {e : A ≃+* B} (h : I.map e = J)

/-- Transfer divided powers under an equivalence -/
/-
**DividedPowers.ofRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers`。
形式化陈述：ofRingEquiv (hI : DividedPowers I) : DividedPowers J where dpow n b
参数：hI : DividedPowers I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer divided powers under an equivalence
-/
def ofRingEquiv (hI : DividedPowers I) : DividedPowers J where
  dpow n b := e (hI.dpow n (e.symm b))
  dpow_null hx := by
    rw [EmbeddingLike.map_eq_zero_iff, hI.dpow_null]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_zero hx := by
    rw [EmbeddingLike.map_eq_one_iff, hI.dpow_zero]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_one hx := by
    rw [dpow_one, RingEquiv.apply_symm_apply]
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_mem hn hx := by
    rw [← h, I.apply_mem_of_equiv_iff]
    apply hI.dpow_mem hn
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_add hx hy := by
    simp only [map_add]
    rw [hI.dpow_add (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))
        (symm_apply_mem_of_equiv_iff.mpr (h ▸ hy))]
    simp only [map_sum, map_mul]
  dpow_mul hx := by
    simp only [map_mul]
    rw [hI.dpow_mul (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))]
    rw [map_mul, map_pow]
    simp only [RingEquiv.apply_symm_apply]
  mul_dpow hx := by
    rw [← map_mul, hI.mul_dpow, map_mul]
    · simp only [map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_comp hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp hn]
    · simp only [map_mul, map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]

@[simp]
/-
**DividedPowers.ofRingEquiv_dpow** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：ofRingEquiv_dpow (hI : DividedPowers I) {n : Nat} {b : B} : (ofRingEquiv h
 hI).dpow n b = e (hI.dpow n (e.symm b))
参数：hI : DividedPowers I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRingEquiv_dpow (hI : DividedPowers I) {n : ℕ} {b : B} :
    (ofRingEquiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl
/-
**DividedPowers.ofRingEquiv_dpow_apply** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`
。
形式化陈述：ofRingEquiv_dpow_apply (hI : DividedPowers I) {n : Nat} {a : A} : (ofRingE
quiv h hI).dpow n (e a) = e (hI.dpow n a)
参数：hI : DividedPowers I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofRingEquiv_dpow_apply (hI : DividedPowers I) {n : ℕ} {a : A} :
    (ofRingEquiv h hI).dpow n (e a) = e (hI.dpow n a) := by
  simp

/-- Transfer divided powers under an equivalence (Equiv version) -/
/-
**DividedPowers.equiv** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers`。
形式化陈述：equiv : DividedPowers I ≃ DividedPowers J where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer divided powers under an equivalence (Equiv version)
-/
def equiv : DividedPowers I ≃ DividedPowers J where
  toFun := ofRingEquiv h
  invFun := ofRingEquiv (show map e.symm J = I by rw [← h]; exact I.map_of_equiv e)
  left_inv := fun hI ↦ by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ ↦ by ext n b; simp [ofRingEquiv]
/-
**DividedPowers.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：equiv_apply (hI : DividedPowers I) (n : Nat) (b : B) : (equiv h hI).dpow n
 b = e (hI.dpow n (e.symm b))
参数：hI : DividedPowers I；n : Nat；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_apply (hI : DividedPowers I) (n : ℕ) (b : B) :
    (equiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

/-- Variant of `DividedPowers.equiv_apply` -/
/-
**DividedPowers.equiv_apply'** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：equiv_apply' (hI : DividedPowers I) {n : Nat} {a : A} : (equiv h hI).dpow 
n (e a) = e (hI.dpow n a)
参数：hI : DividedPowers I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.ofRingEquiv_dpow_apply`：ofRingEquiv_dpow_apply (hI : Divid
edPowers I) {n : Nat} {a : A} : (ofRingEquiv h hI).dpow n (e a) = e (hI.dpow n a
)

--- 原说明 ---
Variant of `DividedPowers.equiv_apply`
-/
theorem equiv_apply' (hI : DividedPowers I) {n : ℕ} {a : A} :
    (equiv h hI).dpow n (e a) = e (hI.dpow n a) :=
  ofRingEquiv_dpow_apply h hI

end Equiv

end DividedPowers

