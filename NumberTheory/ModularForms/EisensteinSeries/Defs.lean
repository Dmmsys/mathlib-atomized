/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Eisenstein Series

## Main definitions

* We define Eisenstein series of level `Γ(N)` for any `N : ℕ` and weight `k : ℤ` as the infinite sum
  `∑' v : (Fin 2 → ℤ), (1 / (v 0 * z + v 1) ^ k)`, where `z : ℍ` and `v` ranges over all pairs of
  coprime integers congruent to a fixed pair `(a, b)` modulo `N`. Note that by using `(Fin 2 → ℤ)`
  instead of `ℤ × ℤ` we can state all of the required equivalences using matrices and vectors, which
  makes working with them more convenient.

* We show that they define a slash invariant form of level `Γ(N)` and weight `k`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
-/

@[expose] public section

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix CongruenceSubgroup Set

open scoped MatrixGroups

namespace EisensteinSeries

variable (N r : ℕ) (a : Fin 2 → ZMod N)

section gammaSet_def

/-- The set of pairs of integers congruent to `a` mod `N` and with `gcd` equal to `r`. -/
/-
**EisensteinSeries.gammaSet** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：gammaSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of pairs of integers congruent to `a` mod `N` and with `gcd` equal to `r
`.
-/
def gammaSet := {v : Fin 2 → ℤ | (↑) ∘ v = a ∧ (v 0).gcd (v 1) = r}

open scoped Function in -- required for scoped `on` notation
/-
**EisensteinSeries.pairwise_disjoint_gammaSet** 是 Mathlib 中的一个引理，位于命名空间 `Eisenst
einSeries`。
形式化陈述：pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N r) := by
  refine fun u v huv ↦ ?_
  contrapose huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

/-- For level `N = 1`, the gamma sets are all equal. -/
/-
**EisensteinSeries.gammaSet_one_const** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSerie
s`。
形式化陈述：gammaSet_one_const (a a' : Fin 2 -> ZMod 1) : gammaSet 1 r a = gammaSet 1 
r a'
参数：a a' : Fin 2 -> ZMod 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
For level `N = 1`, the gamma sets are all equal.
-/
lemma gammaSet_one_const (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a = gammaSet 1 r a' :=
  congr_arg _ (Subsingleton.elim _ _)

/-- For level `N = 1`, the gamma sets simplify to only a `gcd` condition. -/
/-
**EisensteinSeries.gammaSet_one_eq** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：gammaSet_one_eq (a : Fin 2 -> ZMod 1) : gammaSet 1 r a = {v : Fin 2 -> Int
 | (v 0).gcd (v 1) = r}
参数：a : Fin 2 -> ZMod 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
For level `N = 1`, the gamma sets simplify to only a `gcd` condition.
-/
lemma gammaSet_one_eq (a : Fin 2 → ZMod 1) :
    gammaSet 1 r a = {v : Fin 2 → ℤ | (v 0).gcd (v 1) = r} := by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 → ZMod 1)]
/-
**EisensteinSeries.gammaSet_one_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSer
ies`。
形式化陈述：gammaSet_one_mem_iff (v : Fin 2 -> Int) : v in gammaSet 1 r 0 ↔ (v 0).gcd 
(v 1) = r
参数：v : Fin 2 -> Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma gammaSet_one_mem_iff (v : Fin 2 → ℤ) : v ∈ gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r := by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 → ZMod 1)]

/-- For level `N = 1`, the gamma sets are all equivalent; this is the equivalence. -/
/-
**EisensteinSeries.gammaSet_one_equiv** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSerie
s`。
形式化陈述：gammaSet_one_equiv (a a' : Fin 2 -> ZMod 1) : gammaSet 1 r a ≃ gammaSet 1 
r a'
参数：a a' : Fin 2 -> ZMod 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.gammaSet_one_const`：gammaSet_one_const (a a' : Fin 2 ->
 ZMod 1) : gammaSet 1 r a = gammaSet 1 r a'

--- 原说明 ---
For level `N = 1`, the gamma sets are all equivalent; this is the equivalence.
-/
def gammaSet_one_equiv (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a ≃ gammaSet 1 r a' :=
  Equiv.setCongr (gammaSet_one_const r a a')

/-- The map from `Fin 2 → ℤ` sending `![a,b]` to `a.gcd b`. -/
/-
**EisensteinSeries.finGcdMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `EisensteinSeries`。
形式化陈述：finGcdMap (v : Fin 2 -> Int) : Nat
参数：v : Fin 2 -> Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `Fin 2 → ℤ` sending `![a,b]` to `a.gcd b`.
-/
abbrev finGcdMap (v : Fin 2 → ℤ) : ℕ := (v 0).gcd (v 1)
/-
**EisensteinSeries.finGcdMap_div** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：finGcdMap_div {r : Nat} [NeZero r] (v : Fin 2 -> Int) (hv : finGcdMap v = 
r) : IsCoprime ((v / r) 0) ((v / r) 1)
参数：v : Fin 2 -> Int；hv : finGcdMap v = r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCoprime_div_gcd_div_gcd_of_gcd_ne_zero`：isCoprime_div_gcd_div_gcd_of_g
cd_ne_zero (hpq : GCDMonoid.gcd p q != 0) : IsCoprime (p / GCDMonoid.gcd p q) (q
 / GCDMonoid.gcd p q)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma finGcdMap_div {r : ℕ} [NeZero r] (v : Fin 2 → ℤ) (hv : finGcdMap v = r) :
    IsCoprime ((v / r) 0) ((v / r) 1) := by
  rw [← hv]
  apply isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
  have := NeZero.ne r
  aesop
/-
**EisensteinSeries.finGcdMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：finGcdMap_smul {r : Nat} (a : Int) {v : Fin 2 -> Int} (hv : finGcdMap v = 
r) : finGcdMap (a • v) = a.natAbs * r
参数：a : Int；hv : finGcdMap v = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.gcd_mul_left`：∀ (m n k : ℤ), (m * n).gcd (m * k) = m.natAbs * n.gcd 
k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finGcdMap_smul {r : ℕ} (a : ℤ) {v : Fin 2 → ℤ} (hv : finGcdMap v = r) :
    finGcdMap (a • v) = a.natAbs * r := by
  simp [finGcdMap, Int.gcd_mul_left, hv]

/-- An abbreviation of the map which divides an integer vector by an integer. -/
/-
**EisensteinSeries.divIntMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `EisensteinSeries`。
形式化陈述：divIntMap (r : Int) {m : Nat} (v : Fin m -> Int) : Fin m -> Int
参数：r : Int；v : Fin m -> Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation of the map which divides an integer vector by an integer.
-/
abbrev divIntMap (r : ℤ) {m : ℕ} (v : Fin m → ℤ) : Fin m → ℤ := v / r
/-
**EisensteinSeries.mem_gammaSet_one** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`
。
形式化陈述：mem_gammaSet_one (v : Fin 2 -> Int) : v in gammaSet 1 1 0 ↔ IsCoprime (v 0
) (v 1)
参数：v : Fin 2 -> Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EisensteinSeries.gammaSet_one_mem_iff`：gammaSet_one_mem_iff (v : Fin 2 -
> Int) : v in gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_gammaSet_one (v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  rw [gammaSet_one_mem_iff, Int.isCoprime_iff_gcd_eq_one]
/-
**EisensteinSeries.gammaSet_div_gcd** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`
。
形式化陈述：gammaSet_div_gcd {r : Nat} {v : Fin 2 -> Int} (hv : v in (gammaSet 1 r 0))
 (i : Fin 2) : (r : Int) ∣ v i
参数：hv : v in (gammaSet 1 r 0)；i : Fin 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma gammaSet_div_gcd {r : ℕ} {v : Fin 2 → ℤ} (hv : v ∈ (gammaSet 1 r 0)) (i : Fin 2) :
   (r : ℤ) ∣ v i := by
  fin_cases i <;> simp [← hv.2, Int.gcd_dvd_left, Int.gcd_dvd_right]
/-
**EisensteinSeries.gammaSet_div_gcd_to_gammaSet10_bijection** 是 Mathlib 中的一个引理，位
于命名空间 `EisensteinSeries`。
形式化陈述：gammaSet_div_gcd_to_gammaSet10_bijection (r : Nat) [NeZero r] : Set.BijOn 
(divIntMap r) (gammaSet 1 r 0) (gammaSet 1 1 0)
参数：r : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.finGcdMap_div`：finGcdMap_div {r : Nat} [NeZero r] (v : 
Fin 2 -> Int) (hv : finGcdMap v = r) : IsCoprime ((v / r) 0) ((v / r) 1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.ediv_left_inj`：∀ {a b d : ℤ}, d ∣ a → d ∣ b → (a / d = b / d ↔ a = b
)
· 使用引理 `EisensteinSeries.gammaSet_div_gcd`：gammaSet_div_gcd {r : Nat} {v : Fin 2
 -> Int} (hv : v in (gammaSet 1 r 0)) (i : Fin 2) : (r : Int) ∣ v i
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.gcd_mul_left`：∀ (m n k : ℤ), (m * n).gcd (m * k) = m.natAbs * n.gcd 
k
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
· 使用引理 `EisensteinSeries.mem_gammaSet_one`：mem_gammaSet_one (v : Fin 2 -> Int) :
 v in gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma gammaSet_div_gcd_to_gammaSet10_bijection (r : ℕ) [NeZero r] :
    Set.BijOn (divIntMap r) (gammaSet 1 r 0) (gammaSet 1 1 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [divIntMap, mem_gammaSet_one] at *
    exact finGcdMap_div _ hx.2
  · intro x hx v hv hv2
    ext i
    exact (Int.ediv_left_inj (gammaSet_div_gcd hx i) (gammaSet_div_gcd hv i)).mp
      (congr_fun hv2 i)
  · intro x hx
    use r • x
    simp only [nsmul_eq_mul, divIntMap, Int.cast_natCast]
    constructor
    · rw [mem_gammaSet_one, Int.isCoprime_iff_gcd_eq_one] at hx
      exact ⟨Subsingleton.eq_zero _, by simp [Int.gcd_mul_left, hx]⟩
    · ext i
      simp_all [NeZero.ne r]
/-
**EisensteinSeries.gammaSet_eq_gcd_mul_divIntMap** 是 Mathlib 中的一个引理，位于命名空间 `Eise
nsteinSeries`。
形式化陈述：gammaSet_eq_gcd_mul_divIntMap {r : Nat} {v : Fin 2 -> Int} (hv : v in gamm
aSet 1 r 0) : v = r • (divIntMap r v)
参数：hv : v in gammaSet 1 r 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.mul_ediv_assoc`：∀ (a : ℤ) {b c : ℤ}, c ∣ b → a * b / c = a * (b / c)
· 使用引理 `EisensteinSeries.gammaSet_div_gcd`：gammaSet_div_gcd {r : Nat} {v : Fin 2
 -> Int} (hv : v in (gammaSet 1 r 0)) (i : Fin 2) : (r : Int) ∣ v i
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma gammaSet_eq_gcd_mul_divIntMap {r : ℕ} {v : Fin 2 → ℤ} (hv : v ∈ gammaSet 1 r 0) :
    v = r • (divIntMap r v) := by
  by_cases hr : r = 0
  · have hv := hv.2
    simp only [hr, Fin.isValue, Int.gcd_eq_zero_iff, CharP.cast_eq_zero, zero_smul] at *
    ext i
    fin_cases i <;> simp [hv]
  · ext i
    simp_all [Pi.smul_apply, divIntMap, ← Int.mul_ediv_assoc _ (gammaSet_div_gcd hv i)]

/-- The equivalence between `gammaSet 1 r 0` and `gammaSet 1 1 0` for non-zero `r`. -/
/-
**EisensteinSeries.gammaSetDivGcdEquiv** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeri
es`。
形式化陈述：gammaSetDivGcdEquiv (r : Nat) [NeZero r] : gammaSet 1 r 0 ≃ gammaSet 1 1 0
参数：r : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.gammaSet_div_gcd_to_gammaSet10_bijection`：gammaSet_div_
gcd_to_gammaSet10_bijection (r : Nat) [NeZero r] : Set.BijOn (divIntMap r) (gamm
aSet 1 r 0) (gammaSet 1 1 0)

--- 原说明 ---
The equivalence between `gammaSet 1 r 0` and `gammaSet 1 1 0` for non-zero `r`.
-/
def gammaSetDivGcdEquiv (r : ℕ) [NeZero r] : gammaSet 1 r 0 ≃ gammaSet 1 1 0 :=
    Set.BijOn.equiv _ (gammaSet_div_gcd_to_gammaSet10_bijection r)

@[simp]
/-
**EisensteinSeries.gammaSetDivGcdEquiv_eq** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinS
eries`。
形式化陈述：gammaSetDivGcdEquiv_eq (r : Nat) [NeZero r] (v : gammaSet 1 r 0) : (gammaS
etDivGcdEquiv r) v = divIntMap r v.1
参数：r : Nat；v : gammaSet 1 r 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma gammaSetDivGcdEquiv_eq (r : ℕ) [NeZero r] (v : gammaSet 1 r 0) :
    (gammaSetDivGcdEquiv r) v = divIntMap r v.1 := rfl

/-- The equivalence between `(Fin 2 → ℤ)` and `Σ n : ℕ, gammaSet 1 n 0)` . -/
/-
**EisensteinSeries.gammaSetDivGcdSigmaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Eisenstei
nSeries`。
形式化陈述：gammaSetDivGcdSigmaEquiv : (Fin 2 -> Int) ≃ (Σ r : Nat, gammaSet 1 r 0)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between `(Fin 2 → ℤ)` and `Σ n : ℕ, gammaSet 1 n 0)` .
-/
def gammaSetDivGcdSigmaEquiv : (Fin 2 → ℤ) ≃ (Σ r : ℕ, gammaSet 1 r 0) := by
  apply (Equiv.sigmaFiberEquiv finGcdMap).symm.trans
  refine Equiv.sigmaCongrRight fun b => ?_
  apply Equiv.subtypeEquivProp
  simp [gammaSet_one_eq]

@[simp]
/-
**EisensteinSeries.gammaSetDivGcdSigmaEquiv_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `E
isensteinSeries`。
形式化陈述：gammaSetDivGcdSigmaEquiv_symm_eq (v : Σ r : Nat, gammaSet 1 r 0) : (gammaS
etDivGcdSigmaEquiv.symm v) = v.2
参数：v : Σ r : Nat, gammaSet 1 r 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma gammaSetDivGcdSigmaEquiv_symm_eq (v : Σ r : ℕ, gammaSet 1 r 0) :
    (gammaSetDivGcdSigmaEquiv.symm v) = v.2 := rfl

end gammaSet_def

variable {N a r} [NeZero r]

section gamma_action

/-- Right-multiplying a vector by a matrix in `SL(2, ℤ)` doesn't change its gcd. -/
/-
**EisensteinSeries.vecMulSL_gcd** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：vecMulSL_gcd {v : Fin 2 -> Int} (hab : finGcdMap v = r) (A : SL(2, Int)) :
 finGcdMap (v ᵥ* A.1) = r
参数：hab : finGcdMap v = r；A : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.mul_ediv_cancel'`：∀ {a b : ℤ}, a ∣ b → a * (b / a) = b
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Matrix.smul_vecMul`：smul_vecMul [Fintype m] [DistribSMul R α] [IsScalarT
ower R α α] (b : R) (v : m -> α) (M : Matrix m n α) : (b • v) ᵥ* M = b • v ᵥ* M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `EisensteinSeries.finGcdMap_smul`：finGcdMap_smul {r : Nat} (a : Int) {v :
 Fin 2 -> Int} (hv : finGcdMap v = r) : finGcdMap (a • v) = a.natAbs * r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
· 使用引理 `IsCoprime.vecMulSL`：vecMulSL {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 
1)) (A : SL(2, R)) : IsCoprime ((v ᵥ* A.1) 0) ((v ᵥ* A.1) 1)
· 使用引理 `EisensteinSeries.finGcdMap_div`：finGcdMap_div {r : Nat} [NeZero r] (v : 
Fin 2 -> Int) (hv : finGcdMap v = r) : IsCoprime ((v / r) 0) ((v / r) 1)

--- 原说明 ---
Right-multiplying a vector by a matrix in `SL(2, ℤ)` doesn't change its gcd.
-/
lemma vecMulSL_gcd {v : Fin 2 → ℤ} (hab : finGcdMap v = r) (A : SL(2, ℤ)) :
    finGcdMap (v ᵥ* A.1) = r := by
  have hvr : v = r • (v / r) := by
    ext i
    refine Eq.symm (Int.mul_ediv_cancel' ?_)
    fin_cases i <;> simp [← hab, Int.gcd_dvd_left, Int.gcd_dvd_right]
  rw [hvr, smul_vecMul]
  simpa using finGcdMap_smul r (Int.isCoprime_iff_gcd_eq_one.mp ((finGcdMap_div v hab).vecMulSL A))

/-- Right-multiplying by `γ ∈ SL(2, ℤ)` sends `gammaSet N a` to `gammaSet N (a ᵥ* γ)`. -/
/-
**EisensteinSeries.vecMul_SL2_mem_gammaSet** 是 Mathlib 中的一个引理，位于命名空间 `Eisenstein
Series`。
形式化陈述：vecMul_SL2_mem_gammaSet {v : Fin 2 -> Int} (hv : v in gammaSet N r a) (γ :
 SL(2, Int)) : v ᵥ* γ in gammaSet N r (a ᵥ* γ)
参数：hv : v in gammaSet N r a；γ : SL(2, Int)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_vecMul`：map_vecMul [NonAssocSemiring R] [NonAssocSemiring S]
 (f : R ->+* S) (M : Matrix n m R) (v : n -> R) (i : m) : f ((v ᵥ* M) i) = ((f ∘
 v) ᵥ* M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `EisensteinSeries.vecMulSL_gcd`：vecMulSL_gcd {v : Fin 2 -> Int} (hab : fi
nGcdMap v = r) (A : SL(2, Int)) : finGcdMap (v ᵥ* A.1) = r
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Right-multiplying by `γ ∈ SL(2, ℤ)` sends `gammaSet N a` to `gammaSet N (a ᵥ* γ)
`.
-/
lemma vecMul_SL2_mem_gammaSet {v : Fin 2 → ℤ} (hv : v ∈ gammaSet N r a)
    (γ : SL(2, ℤ)) : v ᵥ* γ ∈ gammaSet N r (a ᵥ* γ) := by
  refine ⟨?_, vecMulSL_gcd hv.2 γ⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, hv.1]
  simp

variable (a) in
/-- The bijection between `GammaSets` given by multiplying by an element of `SL(2, ℤ)`. -/
/-
**EisensteinSeries.gammaSetEquiv** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：gammaSetEquiv (γ : SL(2, Int)) : gammaSet N r a ≃ gammaSet N r (a ᵥ* γ) wh
ere toFun v
参数：γ : SL(2, Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between `GammaSets` given by multiplying by an element of `SL(2, ℤ
)`.
-/
def gammaSetEquiv (γ : SL(2, ℤ)) : gammaSet N r a ≃ gammaSet N r (a ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_SL2_mem_gammaSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_SL2_mem_gammaSet v.2 γ⁻¹
      rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul] at this
      simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
        map_inv, mul_inv_cancel, SpecialLinearGroup.coe_one, vecMul_one]⟩
  left_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]
  right_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]

end gamma_action

section eisSummand

/-- The function on `(Fin 2 → ℤ)` whose sum defines an Eisenstein series. -/
/-
**EisensteinSeries.eisSummand** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：eisSummand (k : Int) (v : Fin 2 -> Int) (z : ℍ) : Complex
参数：k : Int；v : Fin 2 -> Int；z : ℍ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function on `(Fin 2 → ℤ)` whose sum defines an Eisenstein series.
-/
def eisSummand (k : ℤ) (v : Fin 2 → ℤ) (z : ℍ) : ℂ := (v 0 * z + v 1) ^ (-k)

/-- How the `eisSummand` function changes under the Moebius action. -/
/-
**EisensteinSeries.eisSummand_SL2_apply** 是 Mathlib 中的一个定理，位于命名空间 `EisensteinSer
ies`。
形式化陈述：eisSummand_SL2_apply (k : Int) (i : (Fin 2 -> Int)) (A : SL(2, Int)) (z : 
ℍ) : eisSummand k i (A • z) = (denom A z) ^ k * eisSummand k (i ᵥ* A) z
参数：k : Int；i : (Fin 2 -> Int)；A : SL(2, Int)；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `UpperHalfPlane.specialLinearGroup_apply`：specialLinearGroup_apply {R : T
ype*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : g • z = mk (((algeb
raMap R Real (g 0 0) : Comple…
· 使用定理 `Matrix.vec2_dotProduct`：vec2_dotProduct (v w : Fin 2 -> α) : v ⬝ᵥ w = v 
0 * w 0 + v 1 * w 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
How the `eisSummand` function changes under the Moebius action.
-/
theorem eisSummand_SL2_apply (k : ℤ) (i : (Fin 2 → ℤ)) (A : SL(2, ℤ)) (z : ℍ) :
    eisSummand k i (A • z) = (denom A z) ^ k * eisSummand k (i ᵥ* A) z := by
  simp only [eisSummand, vecMul, vec2_dotProduct, denom, UpperHalfPlane.specialLinearGroup_apply]
  have h (a b c d u v : ℂ) (hc : c * z + d ≠ 0) : (u * ((a * z + b) / (c * z + d)) + v) ^ (-k) =
      (c * z + d) ^ k * ((u * a + v * c) * z + (u * b + v * d)) ^ (-k) := by
    replace hc : z * c + d ≠ 0 := by convert! hc using 1; ring
    field_simp
    simp [div_zpow]
    ring_nf
  simpa using h (hc := denom_ne_zero A z) ..

end eisSummand

variable (a)

/-- An Eisenstein series of weight `k` and level `Γ(N)`, with congruence condition `a`. -/
/-
**EisensteinSeries._root_.eisensteinSeries** 是 Mathlib 中的一个定义，位于命名空间 `Eisenstein
Series`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Eisenstein series of weight `k` and level `Γ(N)`, with congruence condition `
a`.
-/
def _root_.eisensteinSeries (k : ℤ) (z : ℍ) : ℂ := ∑' x : gammaSet N 1 a, eisSummand k x z
/-
**EisensteinSeries.eisensteinSeries_slash_apply** 是 Mathlib 中的一个引理，位于命名空间 `Eisen
steinSeries`。
形式化陈述：eisensteinSeries_slash_apply (k : Int) (γ : SL(2, Int)) : eisensteinSeries
 a k ∣[k] γ = eisensteinSeries (a ᵥ* γ) k
参数：k : Int；γ : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.SL_slash_apply`：SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) : (f
 ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `mul_inv_eq_iff_eq_mul₀`：mul_inv_eq_iff_eq_mul₀ (hb : b != 0) : a * b⁻¹ =
 c ↔ a = c * b
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `EisensteinSeries.eisSummand_SL2_apply`：eisSummand_SL2_apply (k : Int) (i
 : (Fin 2 -> Int)) (A : SL(2, Int)) (z : ℍ) : eisSummand k i (A • z) = (denom A 
z) ^ k * eisSummand k (i ᵥ*…
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma eisensteinSeries_slash_apply (k : ℤ) (γ : SL(2, ℤ)) :
    eisensteinSeries a k ∣[k] γ = eisensteinSeries (a ᵥ* γ) k := by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    eisensteinSeries, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (gammaSetEquiv a γ).tsum_eq (eisSummand k · z)

/-- The `SlashInvariantForm` defined by an Eisenstein series of weight `k : ℤ`, level `Γ(N)`,
and congruence condition given by `a : Fin 2 → ZMod N`. -/
/-
**EisensteinSeries.eisensteinSeriesSIF** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeri
es`。
形式化陈述：eisensteinSeriesSIF (k : Int) : SlashInvariantForm (Gamma N) k where toFun
参数：k : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SlashInvariantForm` defined by an Eisenstein series of weight `k : ℤ`, leve
l `Γ(N)`,
and congruence condition given by `a : Fin 2 → ZMod N`.
-/
def eisensteinSeriesSIF (k : ℤ) : SlashInvariantForm (Gamma N) k where
  toFun := eisensteinSeries a k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, eisensteinSeries_slash_apply, Gamma_mem'.mp hA]

@[deprecated (since := "2026-02-10")]
noncomputable alias eisensteinSeries_SIF := eisensteinSeriesSIF
/-
**EisensteinSeries.eisensteinSeriesSIF_apply** 是 Mathlib 中的一个引理，位于命名空间 `Eisenste
inSeries`。
形式化陈述：eisensteinSeriesSIF_apply (k : Int) (z : ℍ) : eisensteinSeriesSIF a k z = 
eisensteinSeries a k z
参数：k : Int；z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eisensteinSeriesSIF_apply (k : ℤ) (z : ℍ) :
    eisensteinSeriesSIF a k z = eisensteinSeries a k z := rfl

@[deprecated (since := "2026-02-10")] alias eisensteinSeries_SIF_apply := eisensteinSeriesSIF_apply

end EisensteinSeries

