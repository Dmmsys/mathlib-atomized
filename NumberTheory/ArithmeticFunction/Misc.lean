/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Data.Nat.Factorization.PrimePow
/-!
# Miscellaneous arithmetic Functions

This file defines some simple examples of arithmetic functions (functions `ℕ → R` vanishing at
`0`, considered as a ring under Dirichlet convolution). Note that the Von Mangoldt and Möbius
functions are in separate files.

## Main Definitions

* `σ k` is the arithmetic function such that `σ k x = ∑ y ∈ divisors x, y ^ k` for `0 < x`.
* `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
* `id` is the identity arithmetic function on `ℕ`.
* `ω n` is the number of distinct prime factors of `n`.
* `Ω n` is the number of prime factors of `n` counted with multiplicity.

## Notation

The arithmetic functions `σ`, `ω` and `Ω` have Greek letter names.
This notation is scoped to the separate locales `ArithmeticFunction.sigma` for `σ`,
`ArithmeticFunction.omega` for `ω` and `ArithmeticFunction.Omega` for `Ω`, to allow for selective
access.

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

section SpecialFunctions

open scoped zeta

section ProdPrimeFactors

/-- The map $n \mapsto \prod_{p \mid n} f(p)$ as an arithmetic function -/
/-
**ArithmeticFunction.prodPrimeFactors** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：prodPrimeFactors [CommMonoidWithZero R] (f : Nat -> R) : ArithmeticFunctio
n R where toFun d
参数：f : Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map $n \mapsto \prod_{p \mid n} f(p)$ as an arithmetic function
-/
def prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun d := if d = 0 then 0 else ∏ p ∈ d.primeFactors, f p
  map_zero' := if_pos rfl

open Batteries.ExtendedBinder

/-- `∏ᵖ p ∣ n, f p` is custom notation for `prodPrimeFactors f n` -/
scoped syntax (name := bigproddvd) "∏ᵖ " extBinder " ∣ " term ", " term:67 : term
scoped macro_rules (kind := bigproddvd)
  | `(∏ᵖ $x:ident ∣ $n, $r) => `(prodPrimeFactors (fun $x ↦ $r) $n)

@[simp]
/-
**ArithmeticFunction.prodPrimeFactors_apply** 是 Mathlib 中的一个定理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：prodPrimeFactors_apply [CommMonoidWithZero R] {f : Nat -> R} {n : Nat} (hn
 : n != 0) : ∏ᵖ p ∣ n, f p = ∏ p in n.primeFactors, f p
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem prodPrimeFactors_apply [CommMonoidWithZero R] {f : ℕ → R} {n : ℕ} (hn : n ≠ 0) :
    ∏ᵖ p ∣ n, f p = ∏ p ∈ n.primeFactors, f p :=
  if_neg hn

namespace IsMultiplicative

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.prodPrimeFactors** 是 Mathlib 中的一个定理，位于命名空间
 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：prodPrimeFactors [CommMonoidWithZero R] (f : Nat -> R) : IsMultiplicative 
(prodPrimeFactors f)
参数：f : Nat -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.iff_ne_zero`：iff_ne_zero [MonoidWith
Zero R] {f : ArithmeticFunction R} : IsMultiplicative f ↔ f 1 = 1 ∧ forall {m n 
: Nat}, m != 0 -> n != 0 -> m.Coprime…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.prodPrimeFactors_apply`：prodPrimeFactors_apply [CommM
onoidWithZero R] {f : Nat -> R} {n : Nat} (hn : n != 0) : ∏ᵖ p ∣ n, f p = ∏ p in
 n.primeFactors, f p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.primeFactors_one`：Nat.primeFactors 1 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `Nat.primeFactors_mul`：primeFactors_mul (ha : a != 0) (hb : b != 0) : (a 
* b).primeFactors = a.primeFactors union b.primeFactors
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Nat.Coprime.disjoint_primeFactors`：∀ {a b : ℕ}, a.Coprime b → Disjoint a
.primeFactors b.primeFactors
-/
theorem prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) :
    IsMultiplicative (prodPrimeFactors f) := by
  rw [iff_ne_zero]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, prodPrimeFactors_apply, primeFactors_one,
    prod_empty, true_and]
  intro x y hx hy hxy
  have hxy₀ : x * y ≠ 0 := mul_ne_zero hx hy
  rw [prodPrimeFactors_apply hxy₀, prodPrimeFactors_apply hx, prodPrimeFactors_apply hy,
    primeFactors_mul hx hy, ← prod_union hxy.disjoint_primeFactors]
/-
**ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree** 是 Mat
hlib 中的一个定理，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：prodPrimeFactors_add_of_squarefree [CommSemiring R] {f g : ArithmeticFunct
ion R} (hf : IsMultiplicative f) (hg : IsMultiplicative g) {n : Nat} (hn : Squar
efree n) : ∏ᵖ p ∣ n, (f + g) p = (f * g) n
参数：hf : IsMultiplicative f；hg : IsMultiplicative g；hn : Squarefree n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.prodPrimeFactors_apply`：prodPrimeFactors_apply [CommM
onoidWithZero R] {f : Nat -> R} {n : Nat} (hn : n != 0) : ∏ᵖ p ∣ n, f p = ∏ p in
 n.primeFactors, f p
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ArithmeticFunction.add_apply`：add_apply {f g : ArithmeticFunction R} {n 
: Nat} : (f + g) n = f n + g n
· 使用定理 `Finset.prod_add`：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i
 + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
· 使用定理 `ArithmeticFunction.mul_apply`：mul_apply [Semiring R] {f g : ArithmeticFu
nction R} {n : Nat} : (f * g) n = ∑ x in divisorsAntidiagonal n, f x.fst * g x.s
nd
· 使用定理 `Nat.sum_divisorsAntidiagonal`：∀ {M : Type u_1} [inst : AddCommMonoid M] 
(f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.div
isors, f i (n / i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.divisors_filter_squarefree_of_squarefree`：divisors_filter_squarefree
_of_squarefree {n : Nat} (hn : Squarefree n) : {d in n.divisors | Squarefree d} 
= n.divisors
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.sum_divisors_filter_squarefree`：sum_divisors_filter_squarefree {n : 
Nat} (h0 : n != 0) {α : Type*} [AddCommMonoid α] {f : Nat -> α} : ∑ d in n.divis
ors with Squarefree d, f…
· 使用定理 `Nat.factors_eq`：∀ (n : ℕ), UniqueFactorizationMonoid.normalizedFactors n
 = ↑n.primeFactorsList
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_val`：prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.p
rod id
· 使用定理 `Function.id_def`：∀ {α : Sort u_1}, id = fun x => x
· 使用定理 `Nat.prod_primeFactors_sdiff_of_squarefree`：prod_primeFactors_sdiff_of_sq
uarefree {n : Nat} (hn : Squarefree n) {t : Finset Nat} (ht : t subseteq n.prime
Factors) : ∏ a in (n.primeFacto…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors`：map
_prod_of_subset_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R} (
h_mult : ArithmeticFunction.IsMultiplicative f) (l : Nat)…
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
-/
theorem prodPrimeFactors_add_of_squarefree [CommSemiring R] {f g : ArithmeticFunction R}
    (hf : IsMultiplicative f) (hg : IsMultiplicative g) {n : ℕ} (hn : Squarefree n) :
    ∏ᵖ p ∣ n, (f + g) p = (f * g) n := by
  rw [prodPrimeFactors_apply hn.ne_zero]
  simp_rw [add_apply (f := f) (g := g)]
  rw [prod_add, mul_apply, sum_divisorsAntidiagonal (f · * g ·),
    ← divisors_filter_squarefree_of_squarefree hn, sum_divisors_filter_squarefree hn.ne_zero,
    factors_eq]
  apply sum_congr rfl
  intro t ht
  rw [t.prod_val, Function.id_def,
    ← prod_primeFactors_sdiff_of_squarefree hn (mem_powerset.mp ht),
    hf.map_prod_of_subset_primeFactors n t (mem_powerset.mp ht),
    ← hg.map_prod_of_subset_primeFactors n (_ \ t) sdiff_subset]

end IsMultiplicative

end ProdPrimeFactors

section Id

/-- The identity on `ℕ` as an `ArithmeticFunction`. -/
/-
**ArithmeticFunction.id** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：ArithmeticFunction ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity on `ℕ` as an `ArithmeticFunction`.
-/
protected def id : ArithmeticFunction ℕ :=
  ⟨id, rfl⟩

@[simp]
/-
**ArithmeticFunction.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：id_apply {x : Nat} : ArithmeticFunction.id x = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply {x : ℕ} : ArithmeticFunction.id x = x :=
  rfl

@[arith_mult]
/-
**ArithmeticFunction.isMultiplicative_id** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：isMultiplicative_id : IsMultiplicative .id
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isMultiplicative_id : IsMultiplicative .id :=
  ⟨rfl, fun _ => rfl⟩

end Id

section Pow

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
/-
**ArithmeticFunction.pow** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：pow (k : Nat) : ArithmeticFunction Nat
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pow k n = n ^ k`, except `pow 0 0 = 0`.
-/
def pow (k : ℕ) : ArithmeticFunction ℕ :=
  ArithmeticFunction.id.ppow k

@[simp]
/-
**ArithmeticFunction.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：pow_apply {k n : Nat} : pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k
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
· 使用定理 `ArithmeticFunction.ppow_zero`：ppow_zero {f : ArithmeticFunction R} : f.p
pow 0 = ζ
· 使用定理 `ArithmeticFunction.natCoe_nat`：natCoe_nat (f : ArithmeticFunction Nat) :
 natToArithmeticFunction f = f
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.ppow_apply`：ppow_apply {f : ArithmeticFunction R} {k 
x : Nat} (kpos : 0 < k) : f.ppow k x = f x ^ k
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem pow_apply {k n : ℕ} : pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k := by
  cases k <;> simp [pow]
/-
**ArithmeticFunction.pow_zero_eq_zeta** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：pow_zero_eq_zeta : pow 0 = ζ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.pow_apply`：pow_apply {k n : Nat} : pow k n = if k = 0
 ∧ n = 0 then 0 else n ^ k
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem pow_zero_eq_zeta : pow 0 = ζ := by
  ext n
  simp
/-
**ArithmeticFunction.pow_one_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction
`。
形式化陈述：pow_one_eq_id : pow 1 = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.pow_apply`：pow_apply {k n : Nat} : pow k n = if k = 0
 ∧ n = 0 then 0 else n ^ k
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_one_eq_id : pow 1 = .id := by
  ext n
  simp

@[arith_mult]
/-
**ArithmeticFunction.isMultiplicative_pow** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction`。
形式化陈述：isMultiplicative_pow {k : Nat} : IsMultiplicative (pow k)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.IsMultiplicative.ppow`：ppow [CommSemiring R] {f : Ari
thmeticFunction R} (hf : f.IsMultiplicative) {k : Nat} : IsMultiplicative (f.ppo
w k)
· 使用定理 `ArithmeticFunction.isMultiplicative_id`：isMultiplicative_id : IsMultipli
cative .id
-/
theorem isMultiplicative_pow {k : ℕ} : IsMultiplicative (pow k) :=
  isMultiplicative_id.ppow
end Pow

section Sigma

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
/-
**ArithmeticFunction.sigma** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：sigma (k : Nat) : ArithmeticFunction Nat
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`σ k n` is the sum of the `k`th powers of the divisors of `n`
-/
def sigma (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.sigma] notation "σ" => ArithmeticFunction.sigma

open scoped sigma
/-
**ArithmeticFunction.sigma_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：sigma_apply {k n : Nat} : σ k n = ∑ d in divisors n, d ^ k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_apply {k n : ℕ} : σ k n = ∑ d ∈ divisors n, d ^ k :=
  rfl

@[simp]
/-
**ArithmeticFunction.sigma_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction
`。
形式化陈述：sigma_eq_zero {k n : Nat} : σ k n = 0 ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem sigma_eq_zero {k n : ℕ} : σ k n = 0 ↔ n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [ArithmeticFunction.sigma_apply]
    aesop

@[simp]
/-
**ArithmeticFunction.sigma_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction
`。
形式化陈述：sigma_pos_iff {k n} : 0 < σ k n ↔ 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sigma_pos_iff {k n} : 0 < σ k n ↔ 0 < n := by
  simp [pos_iff_ne_zero]
/-
**ArithmeticFunction.sigma_apply_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
形式化陈述：sigma_apply_prime_pow {k p i : Nat} (hp : p.Prime) : σ k (p ^ i) = ∑ j in 
.range (i + 1), p ^ (j * k)
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisors_prime_pow`：divisors_prime_pow {p : Nat} (pp : p.Prime) (k :
 Nat) : divisors (p ^ k) = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_in
jective pp.t…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_apply_prime_pow {k p i : ℕ} (hp : p.Prime) :
    σ k (p ^ i) = ∑ j ∈ .range (i + 1), p ^ (j * k) := by
  simp [sigma_apply, divisors_prime_pow hp, pow_mul]
/-
**ArithmeticFunction.sigma_one_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFuncti
on`。
形式化陈述：sigma_one_apply (n : Nat) : σ 1 n = ∑ d in divisors n, d
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d := by simp [sigma_apply]
/-
**ArithmeticFunction.sigma_one_apply_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：sigma_one_apply_prime_pow {p i : Nat} (hp : p.Prime) : σ 1 (p ^ i) = ∑ k i
n .range (i + 1), p ^ k
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sigma_apply_prime_pow`：sigma_apply_prime_pow {k p i :
 Nat} (hp : p.Prime) : σ k (p ^ i) = ∑ j in .range (i + 1), p ^ (j * k)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σ 1 (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp [sigma_apply_prime_pow hp]
/-
**ArithmeticFunction.sigma_eq_sum_div** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：sigma_eq_sum_div (k n : Nat) : sigma k n = ∑ d in divisors n, (n / d) ^ k
参数：k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sigma_apply`：sigma_apply {k n : Nat} : σ k n = ∑ d in
 divisors n, d ^ k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sum_div_divisors`：∀ {α : Type u_1} [inst : AddCommMonoid α] (n : ℕ) 
(f : ℕ → α), ∑ d ∈ n.divisors, f (n / d) = n.divisors.sum f
-/
theorem sigma_eq_sum_div (k n : ℕ) : sigma k n = ∑ d ∈ divisors n, (n / d) ^ k := by
  rw [sigma_apply, ← sum_div_divisors]
/-
**ArithmeticFunction.sigma_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：sigma_zero_apply (n : Nat) : σ 0 n = #n.divisors
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_zero_apply (n : ℕ) : σ 0 n = #n.divisors := by simp [sigma_apply]
/-
**ArithmeticFunction.sigma_zero_apply_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Arith
meticFunction`。
形式化陈述：sigma_zero_apply_prime_pow {p i : Nat} (hp : p.Prime) : σ 0 (p ^ i) = i + 
1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sigma_apply_prime_pow`：sigma_apply_prime_pow {k p i :
 Nat} (hp : p.Prime) : σ k (p ^ i) = ∑ j in .range (i + 1), p ^ (j * k)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : σ 0 (p ^ i) = i + 1 := by
  simp [sigma_apply_prime_pow hp]

@[simp]
/-
**ArithmeticFunction.sigma_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：sigma_one (k : Nat) : σ k 1 = 1
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisors_one`：divisors_one : divisors 1 = {1}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_one (k : ℕ) : σ k 1 = 1 := by
  simp only [sigma_apply, divisors_one, sum_singleton, one_pow]
/-
**ArithmeticFunction.sigma_pos** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：sigma_pos (k n : Nat) (hn0 : n != 0) : 0 < σ k n
参数：k n : Nat；hn0 : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sigma_pos_iff`：sigma_pos_iff {k n} : 0 < σ k n ↔ 0 < 
n
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem sigma_pos (k n : ℕ) (hn0 : n ≠ 0) : 0 < σ k n := by
  rwa [sigma_pos_iff, pos_iff_ne_zero]
/-
**ArithmeticFunction.sigma_mono** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：sigma_mono (k k' n : Nat) (hk : k <= k') : σ k n <= σ k' n
参数：k k' n : Nat；hk : k <= k'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.pos_of_mem_divisors`：pos_of_mem_divisors {m : Nat} (h : m in n.divis
ors) : 0 < m
-/
theorem sigma_mono (k k' n : ℕ) (hk : k ≤ k') : σ k n ≤ σ k' n := by
  simp_rw [sigma_apply]
  gcongr with d hd
  exact pos_of_mem_divisors hd
/-
**ArithmeticFunction.zeta_mul_pow_eq_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
形式化陈述：zeta_mul_pow_eq_sigma {k : Nat} : ζ * pow k = σ k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sigma.eq_1`：∀ (k : ℕ), ArithmeticFunction.sigma k = {
 toFun := fun n => ∑ d ∈ n.divisors, d ^ k, map_zero' := ⋯ }
· 使用定理 `ArithmeticFunction.zeta_mul_apply`：zeta_mul_apply {f : ArithmeticFunctio
n Nat} {x : Nat} : (ζ * f) x = ∑ i in divisors x, f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.pow_apply`：pow_apply {k n : Nat} : pow k n = if k = 0
 ∧ n = 0 then 0 else n ^ k
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k := by
  ext
  rw [sigma, zeta_mul_apply]
  apply sum_congr rfl
  aesop

@[arith_mult]
/-
**ArithmeticFunction.isMultiplicative_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：isMultiplicative_sigma {k : Nat} : IsMultiplicative (σ k)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.zeta_mul_pow_eq_sigma`：zeta_mul_pow_eq_sigma {k : Nat
} : ζ * pow k = σ k
· 使用定理 `ArithmeticFunction.IsMultiplicative.mul`：mul [CommSemiring R] {f g : Ari
thmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : IsMulti
plicative (f * g)
· 使用定理 `ArithmeticFunction.isMultiplicative_zeta`：isMultiplicative_zeta : IsMult
iplicative ζ
· 使用定理 `ArithmeticFunction.isMultiplicative_pow`：isMultiplicative_pow {k : Nat} 
: IsMultiplicative (pow k)
-/
theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow
/-
**ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul*
* 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul {k n : Nat} (hn
 : n != 0) : σ k n = ∏ p in n.primeFactors, ∑ i in .range (n.factorization p + 1
), p ^ (i * k)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.multiplicative_factorization`：multip
licative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R) (hf : f
.IsMultiplicative) {n : Nat} (hn : n != 0) : f n = n.f…
· 使用定理 `ArithmeticFunction.isMultiplicative_sigma`：isMultiplicative_sigma {k : N
at} : IsMultiplicative (σ k)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.support_factorization`：∀ (n : ℕ), n.factorization.support = n.primeF
actors
· 使用定理 `ArithmeticFunction.sigma_apply_prime_pow`：sigma_apply_prime_pow {k p i :
 Nat} (hp : p.Prime) : σ k (p ^ i) = ∑ j in .range (i + 1), p ^ (j * k)
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
-/
theorem sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul {k n : ℕ} (hn : n ≠ 0) :
    σ k n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), p ^ (i * k) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h ↦
    sigma_apply_prime_pow <| prime_of_mem_primeFactors h

/-- A crude upper bound: `σ_k(n) ≤ n ^ (k + 1)`. -/
/-
**ArithmeticFunction.sigma_le_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：sigma_le_pow_succ (k n : Nat) : σ k n <= n ^ (k + 1)
参数：k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Nat.divisor_le`：divisor_le {m : Nat} : n in divisors m -> n <= m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `Nat.card_divisors_le_self`：card_divisors_le_self (n : Nat) : #n.divisors
 <= n

--- 原说明 ---
A crude upper bound: `σ_k(n) ≤ n ^ (k + 1)`.
-/
theorem sigma_le_pow_succ (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  simp only [sigma_apply, pow_succ']
  refine (Finset.sum_le_sum fun d hd ↦ Nat.pow_le_pow_left (Nat.divisor_le hd) k).trans ?_
  simpa [Finset.sum_const] using Nat.mul_le_mul_right (n ^ k) (Nat.card_divisors_le_self n)

end Sigma

open scoped sigma

/-
**ArithmeticFunction._root_.Nat.card_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.card_divisors {n : ℕ} (hn : n ≠ 0) :
    #n.divisors = n.primeFactors.prod (n.factorization · + 1) := by
  rw [← sigma_zero_apply, isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
    sigma_zero_apply_prime_pow <| prime_of_mem_primeFactors h

@[simp]
/-
**ArithmeticFunction._root_.Nat.divisors_card_eq_one_iff** 是 Mathlib 中的一个定理，位于命名
空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.divisors_card_eq_one_iff (n : ℕ) : #n.divisors = 1 ↔ n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    exact (card_le_one.mp h.le 1 (one_mem_divisors.mpr hn) n (n.mem_divisors_self hn)).symm

/-- `sigma_eq_one_iff` is to be preferred. -/
/-
**ArithmeticFunction.sigma_zero_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sigma_eq_one_iff` is to be preferred.
-/
private theorem sigma_zero_eq_one_iff (n : ℕ) : σ 0 n = 1 ↔ n = 1 := by
  simp [sigma_zero_apply]

@[simp]
/-
**ArithmeticFunction.sigma_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：sigma_eq_one_iff (k n : Nat) : σ k n = 1 ↔ n = 1
参数：k n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.NumberTheory.ArithmeticFunction.Misc.0.ArithmeticFuncti
on.sigma_zero_eq_one_iff`：∀ (n : ℕ), (ArithmeticFunction.sigma 0) n = 1 ↔ n = 1
· 使用定理 `ArithmeticFunction.sigma_pos`：sigma_pos (k n : Nat) (hn0 : n != 0) : 0 <
 σ k n
· 使用定理 `ArithmeticFunction.sigma_mono`：sigma_mono (k k' n : Nat) (hk : k <= k') 
: σ k n <= σ k' n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ArithmeticFunction.sigma_one`：sigma_one (k : Nat) : σ k 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sigma_eq_one_iff (k n : ℕ) : σ k n = 1 ↔ n = 1 := by
  by_cases hn0 : n = 0
  · aesop
  constructor
  · intro h
    rw [← sigma_zero_eq_one_iff]
    have zero_lt_sigma := sigma_pos 0 n hn0
    have sigma_zero_le_sigma := sigma_mono 0 k n k.zero_le
    lia
  · simp +contextual
/-
**ArithmeticFunction._root_.Nat.sum_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.sum_divisors {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, d = ∏ p ∈ n.primeFactors, ∑ k ∈ .range (n.factorization p + 1), p ^ k := by
  rw [← sigma_one_apply, isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
    sigma_one_apply_prime_pow <| prime_of_mem_primeFactors h

/-- `Ω n` is the number of prime factors of `n`. -/
/-
**ArithmeticFunction.cardFactors** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：cardFactors : ArithmeticFunction Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ω n` is the number of prime factors of `n`.
-/
def cardFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.primeFactorsList.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Omega] notation "Ω" => ArithmeticFunction.cardFactors

open scoped Omega
/-
**ArithmeticFunction.cardFactors_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：cardFactors_apply {n : Nat} : Ω n = n.primeFactorsList.length
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cardFactors_apply {n : ℕ} : Ω n = n.primeFactorsList.length :=
  rfl
/-
**ArithmeticFunction.cardFactors_zero** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：cardFactors_zero : Ω 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardFactors_zero : Ω 0 = 0 := by simp
/-
**ArithmeticFunction.cardFactors_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFuncti
on`。
形式化陈述：ArithmeticFunction.cardFactors 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem cardFactors_one : Ω 1 = 0 := by simp [cardFactors_apply]

@[simp]
/-
**ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one** 是 Mathlib 中的一个定理，位
于命名空间 `ArithmeticFunction`。
形式化陈述：cardFactors_eq_zero_iff_eq_zero_or_one {n : Nat} : Ω n = 0 ↔ n = 0 ∨ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardFactors_apply`：cardFactors_apply {n : Nat} : Ω n 
= n.primeFactorsList.length
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `Nat.primeFactorsList_eq_nil`：primeFactorsList_eq_nil (n : Nat) : n.prime
FactorsList = [] ↔ n = 0 ∨ n = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cardFactors_eq_zero_iff_eq_zero_or_one {n : ℕ} : Ω n = 0 ↔ n = 0 ∨ n = 1 := by
  rw [cardFactors_apply, List.length_eq_zero_iff, primeFactorsList_eq_nil]

@[simp]
/-
**ArithmeticFunction.cardFactors_pos_iff_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Arith
meticFunction`。
形式化陈述：cardFactors_pos_iff_one_lt {n : Nat} : 0 < Ω n ↔ 1 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardFactors_apply`：cardFactors_apply {n : Nat} : Ω n 
= n.primeFactorsList.length
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `Nat.primeFactorsList_ne_nil`：primeFactorsList_ne_nil (n : Nat) : n.prime
FactorsList != [] ↔ 1 < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cardFactors_pos_iff_one_lt {n : ℕ} : 0 < Ω n ↔ 1 < n := by
  rw [cardFactors_apply, List.length_pos_iff, primeFactorsList_ne_nil]

@[simp]
/-
**ArithmeticFunction.cardFactors_eq_one_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ari
thmeticFunction`。
形式化陈述：cardFactors_eq_one_iff_prime {n : Nat} : Ω n = 1 ↔ n.Prime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_one_iff`：∀ {α : Type u_1} {l : List α}, l.length = 1 ↔ ∃ 
a, l = [a]
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `Nat.add_one_ne_zero`：∀ (n : ℕ), n + 1 ≠ 0
· 使用定理 `List.prod_singleton`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [S
td.LawfulRightIdentity (fun x1 x2 => x1 * x2) 1] {x : α},   [x].prod = x
· 使用定理 `Std.LawfulIdentity.toLawfulRightIdentity`：∀ {α : Sort u} {op : α → α → α
} {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulRightIdentity op 
o
· 使用定理 `Nat.instLawfulIdentityHMulOfNat`：Std.LawfulIdentity (fun x1 x2 => x1 * x
2) 1
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.primeFactorsList_prime`：primeFactorsList_prime {p : Nat} (hp : Nat.P
rime p) : p.primeFactorsList = [p]
-/
theorem cardFactors_eq_one_iff_prime {n : ℕ} : Ω n = 1 ↔ n.Prime := by
  refine ⟨fun h => ?_, fun h => List.length_eq_one_iff.2 ⟨n, primeFactorsList_prime h⟩⟩
  cases n with | zero => simp at h | succ n =>
  rcases List.length_eq_one_iff.1 h with ⟨x, hx⟩
  rw [← prod_primeFactorsList n.add_one_ne_zero, hx, List.prod_singleton]
  apply prime_of_mem_primeFactorsList
  rw [hx, List.mem_singleton]
/-
**ArithmeticFunction.cardFactors_mul** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFuncti
on`。
形式化陈述：cardFactors_mul {m n : Nat} (m0 : m != 0) (n0 : n != 0) : Ω (m * n) = Ω m 
+ Ω n
参数：m0 : m != 0；n0 : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardFactors_apply`：cardFactors_apply {n : Nat} : Ω n 
= n.primeFactorsList.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_card`：coe_card (l : List α) : card (l : Multiset α) = lengt
h l
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.factors_eq`：∀ (n : ℕ), UniqueFactorizationMonoid.normalizedFactors n
 = ↑n.primeFactorsList
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用定理 `Multiset.card_add`：card_add (s t : Multiset α) : card (s + t) = card s +
 card t
-/
theorem cardFactors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : Ω (m * n) = Ω m + Ω n := by
  rw [cardFactors_apply, cardFactors_apply, cardFactors_apply, ← Multiset.coe_card, ← factors_eq,
    UniqueFactorizationMonoid.normalizedFactors_mul m0 n0, factors_eq, factors_eq,
    Multiset.card_add, Multiset.coe_card, Multiset.coe_card]
/-
**ArithmeticFunction.cardFactors_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：cardFactors_multiset_prod {s : Multiset Nat} (h0 : s.prod != 0) : Ω s.prod
 = (Multiset.map Ω s).sum
参数：h0 : s.prod != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardFactors_one`：ArithmeticFunction.cardFactors 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `ArithmeticFunction.cardFactors_mul`：cardFactors_mul {m n : Nat} (m0 : m 
!= 0) (n0 : n != 0) : Ω (m * n) = Ω m + Ω n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
-/
theorem cardFactors_multiset_prod {s : Multiset ℕ} (h0 : s.prod ≠ 0) :
    Ω s.prod = (Multiset.map Ω s).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp_all [cardFactors_mul, not_or]

@[simp]
/-
**ArithmeticFunction.cardFactors_apply_prime** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：cardFactors_apply_prime {p : Nat} (hp : p.Prime) : Ω p = 1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.cardFactors_eq_one_iff_prime`：cardFactors_eq_one_iff_
prime {n : Nat} : Ω n = 1 ↔ n.Prime
-/
theorem cardFactors_apply_prime {p : ℕ} (hp : p.Prime) : Ω p = 1 :=
  cardFactors_eq_one_iff_prime.2 hp
/-
**ArithmeticFunction.cardFactors_pow** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFuncti
on`。
形式化陈述：cardFactors_pow {m k : Nat} : Ω (m ^ k) = k * Ω m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ArithmeticFunction.cardFactors_one`：ArithmeticFunction.cardFactors 1 = 0
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `ArithmeticFunction.cardFactors_mul`：cardFactors_mul {m n : Nat} (m0 : m 
!= 0) (n0 : n != 0) : Ω (m * n) = Ω m + Ω n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
（共 40 条，此处仅展示前 30 条）
-/
lemma cardFactors_pow {m k : ℕ} : Ω (m ^ k) = k * Ω m := by
  by_cases hm : m = 0
  · cases k <;> aesop
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, cardFactors_mul (pow_ne_zero n hm) hm, ih]
    ring

@[simp]
/-
**ArithmeticFunction.cardFactors_apply_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：cardFactors_apply_prime_pow {p k : Nat} (hp : p.Prime) : Ω (p ^ k) = k
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ArithmeticFunction.cardFactors_pow`：cardFactors_pow {m k : Nat} : Ω (m ^
 k) = k * Ω m
· 使用定理 `ArithmeticFunction.cardFactors_apply_prime`：cardFactors_apply_prime {p :
 Nat} (hp : p.Prime) : Ω p = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) : Ω (p ^ k) = k := by
  simp [cardFactors_pow, hp]
/-
**ArithmeticFunction.cardFactors_eq_sum_factorization** 是 Mathlib 中的一个定理，位于命名空间 
`ArithmeticFunction`。
形式化陈述：cardFactors_eq_sum_factorization {n : Nat} : Ω n = n.factorization.sum fun
 _ k => k
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
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardFactors_eq_sum_factorization {n : ℕ} :
    Ω n = n.factorization.sum fun _ k => k := by
  simp [cardFactors_apply, ← List.sum_toFinset_count_eq_length, Finsupp.sum]

/-- `ω n` is the number of distinct prime factors of `n`. -/
/-
**ArithmeticFunction.cardDistinctFactors** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：cardDistinctFactors : ArithmeticFunction Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ω n` is the number of distinct prime factors of `n`.
-/
def cardDistinctFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.primeFactorsList.dedup.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.omega] notation "ω" => ArithmeticFunction.cardDistinctFactors

open scoped omega
/-
**ArithmeticFunction.cardDistinctFactors_zero** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：cardDistinctFactors_zero : ω 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardDistinctFactors_zero : ω 0 = 0 := by simp

@[simp]
/-
**ArithmeticFunction.cardDistinctFactors_one** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：cardDistinctFactors_one : ω 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardDistinctFactors_one : ω 1 = 0 := by simp [cardDistinctFactors]
/-
**ArithmeticFunction.cardDistinctFactors_apply** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：cardDistinctFactors_apply {n : Nat} : ω n = n.primeFactorsList.dedup.lengt
h
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cardDistinctFactors_apply {n : ℕ} : ω n = n.primeFactorsList.dedup.length :=
  rfl

@[simp]
/-
**ArithmeticFunction.cardDistinctFactors_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：cardDistinctFactors_eq_zero {n : Nat} : ω n = 0 ↔ n <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cardDistinctFactors_eq_zero {n : ℕ} : ω n = 0 ↔ n ≤ 1 := by
  simp [cardDistinctFactors_apply, le_one_iff_eq_zero_or_eq_one]

@[simp]
/-
**ArithmeticFunction.cardDistinctFactors_pos** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：cardDistinctFactors_pos {n : Nat} : 0 < ω n ↔ 1 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cardDistinctFactors_pos {n : ℕ} : 0 < ω n ↔ 1 < n := by simp [pos_iff_ne_zero]
/-
**ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree** 是 Mathl
ib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：cardDistinctFactors_eq_cardFactors_iff_squarefree {n : Nat} (h0 : n != 0) 
: ω n = Ω n ↔ Squarefree n
参数：h0 : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.squarefree_iff_nodup_primeFactorsList`：squarefree_iff_nodup_primeFac
torsList {n : Nat} (h0 : n != 0) : Squarefree n ↔ n.primeFactorsList.Nodup
· 使用定理 `ArithmeticFunction.cardDistinctFactors_apply`：cardDistinctFactors_apply 
{n : Nat} : ω n = n.primeFactorsList.dedup.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Sublist.eq_of_length`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist
 l₂ → l₁.length = l₂.length → l₁ = l₂
· 使用定理 `List.dedup_sublist`：dedup_sublist : forall l : List α, dedup l <+ l
· 使用定理 `List.nodup_dedup`：nodup_dedup : forall l : List α, Nodup (dedup l)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {l : List α}, 
l.Nodup → l.dedup = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardDistinctFactors_eq_cardFactors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) :
    ω n = Ω n ↔ Squarefree n := by
  rw [squarefree_iff_nodup_primeFactorsList h0, cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.primeFactorsList.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · simp [h.dedup, cardFactors]
/-
**ArithmeticFunction.cardDistinctFactors_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：cardDistinctFactors_eq_one_iff {n : Nat} : ω n = 1 ↔ IsPrimePow n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardDistinctFactors_apply`：cardDistinctFactors_apply 
{n : Nat} : ω n = n.primeFactorsList.dedup.length
· 使用定理 `isPrimePow_iff_card_primeFactors_eq_one`：isPrimePow_iff_card_primeFactor
s_eq_one {n : Nat} : IsPrimePow n ↔ n.primeFactors.card = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.toFinset_factors`：∀ (n : ℕ), n.primeFactorsList.toFinset = n.primeFa
ctors
· 使用定理 `List.card_toFinset`：List.card_toFinset : #l.toFinset = l.dedup.length
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cardDistinctFactors_eq_one_iff {n : ℕ} : ω n = 1 ↔ IsPrimePow n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, isPrimePow_iff_card_primeFactors_eq_one,
    ← toFinset_factors, List.card_toFinset]

@[simp]
/-
**ArithmeticFunction.cardDistinctFactors_apply_prime_pow** 是 Mathlib 中的一个定理，位于命名
空间 `ArithmeticFunction`。
形式化陈述：cardDistinctFactors_apply_prime_pow {p k : Nat} (hp : p.Prime) (hk : k != 
0) : ω (p ^ k) = 1
参数：hp : p.Prime；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.cardDistinctFactors_eq_one_iff`：cardDistinctFactors_e
q_one_iff {n : Nat} : ω n = 1 ↔ IsPrimePow n
· 使用定理 `IsPrimePow.pow`：IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : Nat} (hk
 : k != 0) : IsPrimePow (n ^ k)
· 使用定理 `Nat.Prime.isPrimePow`：Nat.Prime.isPrimePow {p : Nat} (hp : p.Prime) : Is
PrimePow p
-/
theorem cardDistinctFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ω (p ^ k) = 1 :=
  cardDistinctFactors_eq_one_iff.mpr <| hp.isPrimePow.pow hk

@[simp]
/-
**ArithmeticFunction.cardDistinctFactors_apply_prime** 是 Mathlib 中的一个定理，位于命名空间 `
ArithmeticFunction`。
形式化陈述：cardDistinctFactors_apply_prime {p : Nat} (hp : p.Prime) : ω p = 1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ArithmeticFunction.cardDistinctFactors_apply_prime_pow`：cardDistinctFact
ors_apply_prime_pow {p k : Nat} (hp : p.Prime) (hk : k != 0) : ω (p ^ k) = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cardDistinctFactors_apply_prime {p : ℕ} (hp : p.Prime) : ω p = 1 := by
  rw [← pow_one p, cardDistinctFactors_apply_prime_pow hp one_ne_zero]
/-
**ArithmeticFunction.cardDistinctFactors_mul** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：cardDistinctFactors_mul {m n : Nat} (h : m.Coprime n) : ω (m * n) = ω m + 
ω n
参数：h : m.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.Perm.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ : List α
}, l₁.Perm l₂ → l₁.dedup.Perm l₂.dedup
· 使用定理 `Nat.perm_primeFactorsList_mul_of_coprime`：perm_primeFactorsList_mul_of_c
oprime {a b : Nat} (hab : Coprime a b) : (a * b).primeFactorsList ~ a.primeFacto
rsList ++ b.primeFactorsList
· 使用定理 `List.Disjoint.dedup_append`：∀ {α : Type u_1} [inst : DecidableEq α] {xs 
ys : List α}, xs.Disjoint ys → (xs ++ ys).dedup = xs.dedup ++ ys.dedup
· 使用定理 `Nat.coprime_primeFactorsList_disjoint`：coprime_primeFactorsList_disjoint
 {a b : Nat} (hab : a.Coprime b) : List.Disjoint a.primeFactorsList b.primeFacto
rsList
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardDistinctFactors_mul {m n : ℕ} (h : m.Coprime n) : ω (m * n) = ω m + ω n := by
  simp [cardDistinctFactors_apply, perm_primeFactorsList_mul_of_coprime h |>.dedup |>.length_eq,
    coprime_primeFactorsList_disjoint h |>.dedup_append]

open scoped Function in
/-
**ArithmeticFunction.cardDistinctFactors_prod** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：cardDistinctFactors_prod {ι : Type*} {s : Finset ι} {f : ι -> Nat} (h : (s
 : Set ι).Pairwise (Coprime on f)) : ω (∏ i in s, f i) = ∑ i in s, ω (f i)
参数：h : (s : Set ι).Pairwise (Coprime on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardDistinctFactors_one`：cardDistinctFactors_one : ω 
1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `ArithmeticFunction.cardDistinctFactors_mul`：cardDistinctFactors_mul {m n
 : Nat} (h : m.Coprime n) : ω (m * n) = ω m + ω n
· 使用定理 `Nat.Coprime.prod_right`：∀ {ι : Type u_1} {x : ℕ} {t : Finset ι} {s : ι →
 ℕ}, (∀ i ∈ t, x.Coprime (s i)) → x.Coprime (∏ i ∈ t, s i)
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem cardDistinctFactors_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : (s : Set ι).Pairwise (Coprime on f)) : ω (∏ i ∈ s, f i) = ∑ i ∈ s, ω (f i) := by
  induction s using cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons, sum_cons, cardDistinctFactors_mul, ih]
    · exact fun x hx y hy hxy => h (by simp [hx]) (by simp [hy]) hxy
    · exact Coprime.prod_right fun i hi =>
        h (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi ha).symm

end SpecialFunctions

section Sum

/-
**ArithmeticFunction.sum_Ioc_zeta** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：sum_Ioc_zeta (N : Nat) : ∑ n in Ioc 0 N, zeta n = N
参数：N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.card_Ioc`：∀ (a b : ℕ), (Finset.Ioc a b).card = b - a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_Ioc_zeta (N : ℕ) : ∑ n ∈ Ioc 0 N, zeta n = N := by
  simp only [zeta_apply, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  rw [show {x ∈ Ioc 0 N | ¬x = 0} = Ioc 0 N by ext; simp; lia]
  simp

variable {R : Type*} [Semiring R]
/-
**ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：sum_Ioc_mul_eq_sum_prod_filter (f g : ArithmeticFunction R) (N : Nat) : ∑ 
n in Ioc 0 N, (f * g) n = ∑ x in Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 <= N, f x.1 *
 g x.2
参数：f g : ArithmeticFunction R；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.divisorsAntidiagonal_eq_prod_filter_of_le`：divisorsAntidiagonal_eq_p
rod_filter_of_le {n N : Nat} (n_ne_zero : n != 0) (hn : n <= N) : n.divisorsAnti
diagonal = (Ioc 0 N ×ˢ Ioc 0 N).fil…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_Ioc_mul_eq_sum_prod_filter (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n = ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, f x.1 * g x.2 := by
  simp only [mul_apply]
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, f x.1 * g x.2
  · refine sum_congr rfl fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    rw [divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ (by simp_all)
/-
**ArithmeticFunction.sum_Ioc_mul_eq_sum_sum** 是 Mathlib 中的一个定理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：sum_Ioc_mul_eq_sum_sum (f g : ArithmeticFunction R) (N : Nat) : ∑ n in Ioc
 0 N, (f * g) n = ∑ n in Ioc 0 N, f n * ∑ m in Ioc 0 (N / n), g m
参数：f g : ArithmeticFunction R；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter`：sum_Ioc_mul_eq_sum_pr
od_filter (f g : ArithmeticFunction R) (N : Nat) : ∑ n in Ioc 0 N, (f * g) n = ∑
 x in Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2…
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.div_le_div_right`：∀ {a b c : ℕ}, a ≤ b → a / c ≤ b / c
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem sum_Ioc_mul_eq_sum_sum (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n = ∑ n ∈ Ioc 0 N, f n * ∑ m ∈ Ioc 0 (N / n), g m := by
  rw [sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product]
  refine sum_congr rfl fun n hn ↦ ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero, mul_sum]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro ⟨_, h⟩
    grw [← h, Nat.mul_div_cancel_left _ (by lia)]
  · intro hm
    grw [hm]
    simp [mul_div_le, div_le_self]
/-
**ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：sum_Ioc_mul_zeta_eq_sum (f : ArithmeticFunction R) (N : Nat) : ∑ n in Ioc 
0 N, (f * zeta) n = ∑ n in Ioc 0 N, f n * ↑(N / n)
参数：f : ArithmeticFunction R；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`：sum_Ioc_mul_eq_sum_sum (f g :
 ArithmeticFunction R) (N : Nat) : ∑ n in Ioc 0 N, (f * g) n = ∑ n in Ioc 0 N, f
 n * ∑ m in Ioc 0 (N / n), g m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.sum_Ioc_zeta`：sum_Ioc_zeta (N : Nat) : ∑ n in Ioc 0 N
, zeta n = N
-/
theorem sum_Ioc_mul_zeta_eq_sum (f : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * zeta) n = ∑ n ∈ Ioc 0 N, f n * ↑(N / n) := by
  rw [sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [natCoe_apply]
  rw_mod_cast [sum_Ioc_zeta]

--TODO: Dirichlet hyperbola method to get sums of length `sqrt N`
/-- An `O(N)` formula for the sum of the number of divisors function. -/
/-
**ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：sum_Ioc_sigma0_eq_sum_div (N : Nat) : ∑ n in Ioc 0 N, sigma 0 n = ∑ n in I
oc 0 N, (N / n)
参数：N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.zeta_mul_pow_eq_sigma`：zeta_mul_pow_eq_sigma {k : Nat
} : ζ * pow k = σ k
· 使用定理 `ArithmeticFunction.pow_zero_eq_zeta`：pow_zero_eq_zeta : pow 0 = ζ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum`：sum_Ioc_mul_zeta_eq_sum (f :
 ArithmeticFunction R) (N : Nat) : ∑ n in Ioc 0 N, (f * zeta) n = ∑ n in Ioc 0 N
, f n * ↑(N / n)

--- 原说明 ---
An `O(N)` formula for the sum of the number of divisors function.
-/
theorem sum_Ioc_sigma0_eq_sum_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, sigma 0 n = ∑ n ∈ Ioc 0 N, (N / n) := by
  rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  convert! sum_Ioc_mul_zeta_eq_sum zeta N using 1
  simpa using sum_congr rfl (by grind)

end Sum

end ArithmeticFunction

namespace Nat.Coprime

open ArithmeticFunction

/-
**Nat.Coprime.card_divisors_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：card_divisors_mul {m n : Nat} (hmn : m.Coprime n) : #(m * n).divisors = #m
.divisors * #n.divisors
参数：hmn : m.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`：map_mul_of_copri
me {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat} (h : m.gcd n
 = 1) : f (m * n) = f m * f n
· 使用定理 `ArithmeticFunction.isMultiplicative_sigma`：isMultiplicative_sigma {k : N
at} : IsMultiplicative (σ k)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    #(m * n).divisors = #m.divisors * #n.divisors := by
  simp only [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]
/-
**Nat.Coprime.sum_divisors_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：sum_divisors_mul {m n : Nat} (hmn : m.Coprime n) : ∑ d in (m * n).divisors
, d = (∑ d in m.divisors, d) * ∑ d in n.divisors, d
参数：hmn : m.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`：map_mul_of_copri
me {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat} (h : m.gcd n
 = 1) : f (m * n) = f m * f n
· 使用定理 `ArithmeticFunction.isMultiplicative_sigma`：isMultiplicative_sigma {k : N
at} : IsMultiplicative (σ k)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * ∑ d ∈ n.divisors, d := by
  simp only [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

end Nat.Coprime

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `ArithmeticFunction.sigma`. -/
@[positivity ArithmeticFunction.sigma _ _]
meta def evalArithmeticFunctionSigma : PositivityExt where eval {u α} z p? e :=
  match p? with | none => throwError "no PartialOrder instance" | some p => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(ArithmeticFunction.sigma $k $n) =>
    assumeInstancesCommute
    let rn ← core z p n
    match rn with
    | .positive pn => return .positive q(Iff.mpr ArithmeticFunction.sigma_pos_iff $pn)
    | _ => return .nonnegative q(Nat.zero_le _)
  | _, _, _ => throwError "not ArithmeticFunction.sigma"


end Mathlib.Meta.Positivity

