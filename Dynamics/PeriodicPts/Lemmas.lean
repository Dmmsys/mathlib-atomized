/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Lattice.Nat

/-!
# Extra lemmas about periodic points
-/

public section

open Nat Set

namespace Function
variable {α : Type*} {f : α → α} {x y : α}

open Function (Commute)

/-
**Function.directed_ptsOfPeriod_pnat** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：directed_ptsOfPeriod_pnat (f : α -> α) : Directed (· subseteq ·) fun n : N
at+ => ptsOfPeriod f n
参数：f : α -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.mul_const`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (m * n) 
x
· 使用定理 `Function.IsPeriodicPt.const_mul`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (n * m) 
x
-/
theorem directed_ptsOfPeriod_pnat (f : α → α) : Directed (· ⊆ ·) fun n : ℕ+ => ptsOfPeriod f n :=
  fun m n => ⟨m * n, fun _ hx => hx.mul_const n, fun _ hx => hx.const_mul m⟩

variable (f) in
/-
**Function.bijOn_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：bijOn_periodicPts : BijOn f (periodicPts f) (periodicPts f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bijOn_iUnion_of_directed`：bijOn_iUnion_of_directed {s : ι -> Set α} 
(hs : Directed (· subseteq ·) s) {t : ι -> Set β} {f : α -> β} (H : forall i, Bi
jOn f (s i) (t i))…
· 使用定理 `Function.directed_ptsOfPeriod_pnat`：directed_ptsOfPeriod_pnat (f : α -> 
α) : Directed (· subseteq ·) fun n : Nat+ => ptsOfPeriod f n
· 使用定理 `Function.bijOn_ptsOfPeriod`：bijOn_ptsOfPeriod (f : α -> α) {n : Nat} (hn
 : 0 < n) : BijOn f (ptsOfPeriod f n) (ptsOfPeriod f n)
· 使用定理 `PNat.pos`：pos (n : Nat+) : 0 < (n : Nat)
· 使用定理 `Function.iUnion_pnat_ptsOfPeriod`：iUnion_pnat_ptsOfPeriod : ⋃ n : Nat+, 
ptsOfPeriod f n = periodicPts f
-/
theorem bijOn_periodicPts : BijOn f (periodicPts f) (periodicPts f) :=
  iUnion_pnat_ptsOfPeriod f ▸
    bijOn_iUnion_of_directed (directed_ptsOfPeriod_pnat f) fun i => bijOn_ptsOfPeriod f i.pos
/-
**Function.minimalPeriod_eq_prime_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_eq_prime_iff {p : Nat} [hp : Fact p.Prime] : minimalPeriod f
 x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.isPeriodicPt_iff_minimalPeriod_dvd`：isPeriodicPt_iff_minimalPer
iod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Function.minimalPeriod_eq_one_iff_isFixedPt`：minimalPeriod_eq_one_iff_is
FixedPt : minimalPeriod f x = 1 ↔ IsFixedPt f x
· 使用定理 `or_and_right`：∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
· 使用定理 `and_not_self_iff`：∀ (a : Prop), a ∧ ¬a ↔ False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self_and`：∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
-/
theorem minimalPeriod_eq_prime_iff {p : ℕ} [hp : Fact p.Prime] :
    minimalPeriod f x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt f x := by
  rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, Nat.dvd_prime hp.out,
    ← minimalPeriod_eq_one_iff_isFixedPt.not, or_and_right, and_not_self_iff, false_or,
    iff_self_and]
  exact fun h ↦ ne_of_eq_of_ne h hp.out.ne_one
/-
**Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt** 是 Mathlib 中的一个定理，位于命名空间 `F
unction`。
形式化陈述：minimalPeriod_eq_sInf_n_pos_IsPeriodicPt : minimalPeriod f x = sInf { n > 
0 | IsPeriodicPt f n x }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem minimalPeriod_eq_sInf_n_pos_IsPeriodicPt :
    minimalPeriod f x = sInf { n > 0 | IsPeriodicPt f n x } := by
  dsimp +instances [minimalPeriod, periodicPts, sInf]
  grind

/-- The backward direction of `minimalPeriod_eq_prime_iff`. -/
/-
**Function.minimalPeriod_eq_prime** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_eq_prime {p : Nat} [hp : Fact p.Prime] (hper : IsPeriodicPt 
f p x) (hfix : ¬IsFixedPt f x) : minimalPeriod f x = p
参数：hper : IsPeriodicPt f p x；hfix : ¬IsFixedPt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.minimalPeriod_eq_prime_iff`：minimalPeriod_eq_prime_iff {p : Nat
} [hp : Fact p.Prime] : minimalPeriod f x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt 
f x

--- 原说明 ---
The backward direction of `minimalPeriod_eq_prime_iff`.
-/
theorem minimalPeriod_eq_prime {p : ℕ} [hp : Fact p.Prime] (hper : IsPeriodicPt f p x)
    (hfix : ¬IsFixedPt f x) : minimalPeriod f x = p :=
  minimalPeriod_eq_prime_iff.mpr ⟨hper, hfix⟩
/-
**Function.minimalPeriod_eq_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_eq_prime_pow {p k : Nat} [hp : Fact p.Prime] (hk : ¬IsPeriod
icPt f (p ^ k) x) (hk1 : IsPeriodicPt f (p ^ (k + 1)) x) : minimalPeriod f x = p
 ^ (k + 1)
参数：hk : ¬IsPeriodicPt f (p ^ k) x；hk1 : IsPeriodicPt f (p ^ (k + 1)) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_prime_pow_of_dvd_least_prime_pow`：eq_prime_pow_of_dvd_least_prime
_pow {a p k : Nat} (pp : Prime p) (h₁ : ¬a ∣ p ^ k) (h₂ : a ∣ p ^ (k + 1)) : a =
 p ^ (k + 1)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.isPeriodicPt_iff_minimalPeriod_dvd`：isPeriodicPt_iff_minimalPer
iod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n
-/
theorem minimalPeriod_eq_prime_pow {p k : ℕ} [hp : Fact p.Prime] (hk : ¬IsPeriodicPt f (p ^ k) x)
    (hk1 : IsPeriodicPt f (p ^ (k + 1)) x) : minimalPeriod f x = p ^ (k + 1) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;>
    rwa [← isPeriodicPt_iff_minimalPeriod_dvd]
/-
**Function.Commute.minimalPeriod_of_comp_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.Commute`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {g : α → α},   Function.Commute f g →
 Function.minimalPeriod (f ∘ g) x ∣ Function.minimalPeriod f x * Function.minima
lPeriod g x
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Function.Commute.minimalPeriod_of_comp_dvd_lcm`：∀ {α : Type u_1} {f : α 
→ α} {x : α} {g : α → α},   Function.Commute f g →     Function.minimalPeriod (f
 ∘ g) x ∣ (Function.minimalPeriod f …
· 使用定理 `Nat.lcm_dvd_mul`：∀ (m n : ℕ), m.lcm n ∣ m * n
-/
theorem Commute.minimalPeriod_of_comp_dvd_mul {g : α → α} (h : Commute f g) :
    minimalPeriod (f ∘ g) x ∣ minimalPeriod f x * minimalPeriod g x :=
  dvd_trans h.minimalPeriod_of_comp_dvd_lcm (Nat.lcm_dvd_mul _ _)
/-
**Function.Commute.minimalPeriod_of_comp_eq_mul_of_coprime** 是 Mathlib 中的一个定理，位于
命名空间 `Function.Commute`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {g : α → α},   Function.Commute f g →
     (Function.minimalPeriod f x).Coprime (Function.minimalPeriod g x) →       F
unction.minimalPeriod (f ∘ g) x = Function.minimalPeriod f x * Function.minimalP
eriod g x
参数：Function.minimalPeriod f x；Function.minimalPeriod g x；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.antisymm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCanc
elMulZero α] {a b : α} [Subsingleton αˣ], a ∣ b → b ∣ a → a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Function.Commute.minimalPeriod_of_comp_dvd_mul`：∀ {α : Type u_1} {f : α 
→ α} {x : α} {g : α → α},   Function.Commute f g → Function.minimalPeriod (f ∘ g
) x ∣ Function.minimalPeriod f x * F…
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_left`：∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n 
→ k ∣ n
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_dvd`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, Function.IsPeriodicPt f n x → Function.minimalPeriod f x ∣ n
· 使用定理 `Function.IsPeriodicPt.left_of_comp`：left_of_comp {g : α -> α} (hco : Com
mute f g) (hfg : IsPeriodicPt (f ∘ g) n x) (hg : IsPeriodicPt g n x) : IsPeriodi
cPt f n x
· 使用定理 `Function.IsPeriodicPt.const_mul`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (n * m) 
x
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
· 使用定理 `Function.IsPeriodicPt.mul_const`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (m * n) 
x
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
-/
theorem Commute.minimalPeriod_of_comp_eq_mul_of_coprime {g : α → α} (h : Commute f g)
    (hco : Coprime (minimalPeriod f x) (minimalPeriod g x)) :
    minimalPeriod (f ∘ g) x = minimalPeriod f x * minimalPeriod g x := by
  apply h.minimalPeriod_of_comp_dvd_mul.antisymm
  suffices ∀ {f g : α → α},
      Commute f g →
        Coprime (minimalPeriod f x) (minimalPeriod g x) →
          minimalPeriod f x ∣ minimalPeriod (f ∘ g) x from
    hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm)
  intro f g h hco
  refine hco.dvd_of_dvd_mul_left (IsPeriodicPt.left_of_comp h ?_ ?_).minimalPeriod_dvd
  · exact (isPeriodicPt_minimalPeriod _ _).const_mul _
  · exact (isPeriodicPt_minimalPeriod _ _).mul_const _

section Fintype

open Fintype

/-
**Function.minimalPeriod_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_le_card [Fintype α] : minimalPeriod f x <= card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.periodicOrbit_length`：periodicOrbit_length : (periodicOrbit f x
).length = minimalPeriod f x
· 使用定理 `List.Nodup.length_le_card`：List.Nodup.length_le_card {α : Type*} [Fintyp
e α] {l : List α} (h : l.Nodup) : l.length <= Fintype.card α
· 使用定理 `Function.nodup_periodicOrbit`：nodup_periodicOrbit : (periodicOrbit f x).
Nodup
-/
theorem minimalPeriod_le_card [Fintype α] : minimalPeriod f x ≤ card α := by
  rw [← periodicOrbit_length]
  exact List.Nodup.length_le_card nodup_periodicOrbit
/-
**Function.isPeriodicPt_factorial_card_of_mem_periodicPts** 是 Mathlib 中的一个定理，位于命
名空间 `Function`。
形式化陈述：isPeriodicPt_factorial_card_of_mem_periodicPts [Fintype α] (h : x in perio
dicPts f) : IsPeriodicPt f (card α)! x
参数：h : x in periodicPts f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.isPeriodicPt_iff_minimalPeriod_dvd`：isPeriodicPt_iff_minimalPer
iod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n
· 使用定理 `Nat.dvd_factorial`：∀ {m n : ℕ}, 0 < m → m ≤ n → m ∣ n.factorial
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
· 使用定理 `Function.minimalPeriod_le_card`：minimalPeriod_le_card [Fintype α] : mini
malPeriod f x <= card α
-/
theorem isPeriodicPt_factorial_card_of_mem_periodicPts [Fintype α] (h : x ∈ periodicPts f) :
    IsPeriodicPt f (card α)! x :=
  isPeriodicPt_iff_minimalPeriod_dvd.mpr
    (Nat.dvd_factorial (minimalPeriod_pos_of_mem_periodicPts h) minimalPeriod_le_card)
/-
**Function.mem_periodicPts_iff_isPeriodicPt_factorial_card** 是 Mathlib 中的一个定理，位于
命名空间 `Function`。
形式化陈述：mem_periodicPts_iff_isPeriodicPt_factorial_card [Fintype α] : x in periodi
cPts f ↔ IsPeriodicPt f (card α)! x where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isPeriodicPt_factorial_card_of_mem_periodicPts`：isPeriodicPt_fa
ctorial_card_of_mem_periodicPts [Fintype α] (h : x in periodicPts f) : IsPeriodi
cPt f (card α)! x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.minimalPeriod_pos_iff_mem_periodicPts`：minimalPeriod_pos_iff_me
m_periodicPts : 0 < minimalPeriod f x ↔ x in periodicPts f
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_pos`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → 0 < Function.minimalPeriod 
f x
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
theorem mem_periodicPts_iff_isPeriodicPt_factorial_card [Fintype α] :
    x ∈ periodicPts f ↔ IsPeriodicPt f (card α)! x where
  mp := isPeriodicPt_factorial_card_of_mem_periodicPts
  mpr h := minimalPeriod_pos_iff_mem_periodicPts.mp
    (IsPeriodicPt.minimalPeriod_pos (Nat.factorial_pos _) h)
/-
**Function.Injective.mem_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injecti
ve`。
形式化陈述：∀ {α : Type u_1} {f : α → α} [Finite α], Function.Injective f → ∀ (x : α),
 x ∈ Function.periodicPts f
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_injective_infinite_finite`：not_injective_infinite_finite {α β} [Infi
nite α] [Finite β] (f : α -> β) : ¬Injective f
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Function.mk_mem_periodicPts`：mk_mem_periodicPts (hn : 0 < n) (hx : IsPer
iodicPt f n x) : x in periodicPts f
· 使用引理 `Function.iterate_cancel`：iterate_cancel (hf : Injective f) (ha : f^[m] a
 = f^[n] a) : f^[m - n] a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Injective.mem_periodicPts [Finite α] (h : Injective f) (x : α) : x ∈ periodicPts f := by
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, f^[m] x = f^[n] x ∧ m ≠ n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq.symm)
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq)
/-
**Function.injective_iff_periodicPts_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Function
`。
形式化陈述：injective_iff_periodicPts_eq_univ [Finite α] : Injective f ↔ periodicPts f
 = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Function.Injective.mem_periodicPts`：∀ {α : Type u_1} {f : α → α} [Finite
 α], Function.Injective f → ∀ (x : α), x ∈ Function.periodicPts f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Function.periodicPts_subset_range`：periodicPts_subset_range : periodicPt
s f subseteq range f
-/
theorem injective_iff_periodicPts_eq_univ [Finite α] : Injective f ↔ periodicPts f = univ := by
  refine ⟨fun h ↦ eq_univ_iff_forall.mpr h.mem_periodicPts, fun h ↦ ?_⟩
  rw [Finite.injective_iff_surjective, ← range_eq_univ, ← univ_subset_iff, ← h]
  apply periodicPts_subset_range
/-
**Function.injective_iff_iterate_factorial_card_eq_id** 是 Mathlib 中的一个定理，位于命名空间 
`Function`。
形式化陈述：injective_iff_iterate_factorial_card_eq_id [Fintype α] : Injective f ↔ f^[
(card α)!] = id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem injective_iff_iterate_factorial_card_eq_id [Fintype α] :
    Injective f ↔ f^[(card α)!] = id := by
  simp only [injective_iff_periodicPts_eq_univ, mem_periodicPts_iff_isPeriodicPt_factorial_card,
    funext_iff, eq_univ_iff_forall, IsPeriodicPt, id, IsFixedPt]

end Fintype

end Function

namespace Function

section Prod

variable {α β : Type*} {f : α → α} {g : β → β} {x : α × β} {a : α} {b : β} {m n : ℕ}

/-
**Function.minimalPeriod_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_prodMap (f : α -> α) (g : β -> β) (x : α × β) : minimalPerio
d (Prod.map f g) x = (minimalPeriod f x.1).lcm (minimalPeriod g x.2)
参数：f : α -> α；g : β -> β；x : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_dvd`：eq_of_forall_dvd (h : forall c, a ∣ c ↔ b ∣ c) : a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem minimalPeriod_prodMap (f : α → α) (g : β → β) (x : α × β) :
    minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm (minimalPeriod g x.2) :=
  eq_of_forall_dvd <| by simp [← isPeriodicPt_iff_minimalPeriod_dvd, Nat.lcm_dvd_iff]
/-
**Function.minimalPeriod_fst_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_fst_dvd : minimalPeriod f x.1 ∣ minimalPeriod (Prod.map f g)
 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.minimalPeriod_prodMap`：minimalPeriod_prodMap (f : α -> α) (g : 
β -> β) (x : α × β) : minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm
 (minimalPeriod g x.…
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
-/
theorem minimalPeriod_fst_dvd : minimalPeriod f x.1 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_left _ _
/-
**Function.minimalPeriod_snd_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_snd_dvd : minimalPeriod g x.2 ∣ minimalPeriod (Prod.map f g)
 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.minimalPeriod_prodMap`：minimalPeriod_prodMap (f : α -> α) (g : 
β -> β) (x : α × β) : minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm
 (minimalPeriod g x.…
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
-/
theorem minimalPeriod_snd_dvd : minimalPeriod g x.2 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_right _ _

end Prod

section Pi

variable {ι : Type*} {α : ι → Type*} {f : ∀ i, α i → α i} {x : ∀ i, α i}

/-- This `sInf` can be regarded as a generalized version of LCM
for possibly infinite sets and types. -/
/-
**Function.minimalPeriod_piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_piMap : minimalPeriod (Pi.map f) x = sInf { n > 0 | forall i
, minimalPeriod (f i) (x i) ∣ n }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt`：minimalPeriod_eq_sInf
_n_pos_IsPeriodicPt : minimalPeriod f x = sInf { n > 0 | IsPeriodicPt f n x }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This `sInf` can be regarded as a generalized version of LCM
for possibly infinite sets and types.
-/
theorem minimalPeriod_piMap :
    minimalPeriod (Pi.map f) x = sInf { n > 0 | ∀ i, minimalPeriod (f i) (x i) ∣ n } := by
  conv_lhs => simp [minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  simp [← isPeriodicPt_iff_minimalPeriod_dvd]
/-
**Function.minimalPeriod_piMap_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_piMap_fintype [Fintype ι] : minimalPeriod (Pi.map f) x = Fin
set.univ.lcm (fun i => minimalPeriod (f i) (x i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_dvd`：eq_of_forall_dvd (h : forall c, a ∣ c ↔ b ∣ c) : a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem minimalPeriod_piMap_fintype [Fintype ι] :
    minimalPeriod (Pi.map f) x = Finset.univ.lcm (fun i => minimalPeriod (f i) (x i)) :=
  eq_of_forall_dvd <| by simp [← isPeriodicPt_iff_minimalPeriod_dvd]
/-
**Function.minimalPeriod_single_dvd_minimalPeriod_piMap** 是 Mathlib 中的一个定理，位于命名空
间 `Function`。
形式化陈述：minimalPeriod_single_dvd_minimalPeriod_piMap (i : ι) : minimalPeriod (f i)
 (x i) ∣ minimalPeriod (Pi.map f) x
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.minimalPeriod_piMap`：minimalPeriod_piMap : minimalPeriod (Pi.ma
p f) x = sInf { n > 0 | forall i, minimalPeriod (f i) (x i) ∣ n }
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Nat.sInf_empty`：sInf_empty : sInf ∅ = 0
-/
theorem minimalPeriod_single_dvd_minimalPeriod_piMap (i : ι) :
    minimalPeriod (f i) (x i) ∣ minimalPeriod (Pi.map f) x := by
  simp only [minimalPeriod_piMap]
  by_cases h : {n | 0 < n ∧ ∀ (i : ι), minimalPeriod (f i) (x i) ∣ n}.Nonempty
  · exact (Nat.sInf_mem h).2 i
  · simp [not_nonempty_iff_eq_empty.mp h]

end Pi

end Function

