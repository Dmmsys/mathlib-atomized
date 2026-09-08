/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Ramification index

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx' p P` is the multiplicity of `P` in `map f p`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`.

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index of `P` over `p`, leaving `p` and `P` implicit.

-/

@[expose] public section


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

/-- The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramificationIdx'` is
defined to be 0.

Note: This definition of ramification index will eventually be replaced by `Ideal.ramificationIdx`.
-/
/-
**Ideal.ramificationIdx'** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx' : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 
0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramificationIdx'` 
is
defined to be 0.

Note: This definition of ramification index will eventually be replaced by `Idea
l.ramificationIdx`.
-/
noncomputable def ramificationIdx' : ℕ := sSup {n | map f p ≤ P ^ n}

variable {p P}

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ideal.ramificationIdx'_eq_find** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : DecidablePred fun n =
> ∀ (k : ℕ), Ideal.map (algebraMap R S) p ≤ P ^ k → k ≤ n]   (h : ∃ n, ∀ (k : ℕ)
, Ideal.map (algebraMap R S) p ≤ P ^ k → k ≤ n), p.ramificationIdx' P = Nat.find
 h
参数：k : ℕ；algebraMap R S；h : ∃ n, ∀ (k : ℕ), Ideal.map (algebraMap R S) p ≤ P ^ k
 → k ≤ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Nat.sSup_def`：sSup_def {s : Set Nat} (h : exists n, forall a in s, a <= 
n) : sSup s = @Nat.find (fun n => forall a in s, a <= n) _ h
-/
theorem ramificationIdx'_eq_find [DecidablePred fun n ↦ ∀ (k : ℕ), map f p ≤ P ^ k → k ≤ n]
    (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) :
    ramificationIdx' p P = Nat.find h := by
  convert! Nat.sSup_def h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_find := ramificationIdx'_eq_find
/-
**Ideal.ramificationIdx'_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R}   {P : Ideal S}, (∀ (n : ℕ), ∃ k, Ideal.map (al
gebraMap R S) p ≤ P ^ k ∧ n < k) → p.ramificationIdx' P = 0
参数：∀ (n : ℕ), ∃ k, Ideal.map (algebraMap R S) p ≤ P ^ k ∧ n < k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ramificationIdx'_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) :
    ramificationIdx' p P = 0 :=
  dif_neg (by push Not; exact h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_zero := ramificationIdx'_eq_zero
/-
**Ideal.ramificationIdx'_spec** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   {n : ℕ}, Ideal.map (algebraMap 
R S) p ≤ P ^ n → ¬Ideal.map (algebraMap R S) p ≤ P ^ (n + 1) → p.ramificationIdx
' P = n
参数：algebraMap R S；algebraMap R S；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx'_eq_find`：∀ {R : Type u} [inst : CommRing R] {S : 
Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}
   [inst_3 : Decidab…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem ramificationIdx'_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx' p P = n := by
  classical
  let Q : ℕ → Prop := fun m => ∀ k : ℕ, map f p ≤ P ^ k → k ≤ m
  have : Q n := by
    intro k hk
    refine le_of_not_gt fun hnk => ?_
    exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [ramificationIdx'_eq_find ⟨n, this⟩]
  refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => ?_)
  obtain this' := Nat.find_spec ⟨n, this⟩
  exact h.not_ge (this' _ hle)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_spec := ramificationIdx'_spec
/-
**Ideal.ramificationIdx'_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   {n : ℕ}, ¬Ideal.map (algebraMap
 R S) p ≤ P ^ n → p.ramificationIdx' P < n
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Ideal.ramificationIdx'_eq_find`：∀ {R : Type u} [inst : CommRing R] {S : 
Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}
   [inst_3 : Decidab…
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
theorem ramificationIdx'_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx' p P < n := by
  classical
  rcases n with - | n
  · simp at hgt
  · rw [Nat.lt_succ_iff]
    have : ∀ k, map f p ≤ P ^ k → k ≤ n := by
      refine fun k hk => le_of_not_gt fun hnk => ?_
      exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
    rw [ramificationIdx'_eq_find ⟨n, this⟩]
    exact Nat.find_min' ⟨n, this⟩ this

@[deprecated (since := "2026-07-01")] alias ramificationIdx_lt := ramificationIdx'_lt

@[simp]
/-
**Ideal.ramificationIdx'_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Ideal S},   ⊥.ramificationIdx' P = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
-/
theorem ramificationIdx'_bot : ramificationIdx' (⊥ : Ideal R) P = 0 :=
  dif_neg <| not_exists.mpr fun n hn => n.lt_succ_self.not_ge (hn _ (by simp))

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot := ramificationIdx'_bot

@[simp]
/-
**Ideal.ramificationIdx'_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R}   {P : Ideal S}, ¬Ideal.map (algebraMap R S) p 
≤ P → p.ramificationIdx' P = 0
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ramificationIdx'_spec`：∀ {R : Type u} [inst : CommRing R] {S : Typ
e v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   
{n : ℕ}, Ideal.ma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem ramificationIdx'_of_not_le (h : ¬map f p ≤ P) : ramificationIdx' p P = 0 :=
  ramificationIdx'_spec (by simp) (by simpa using h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_of_not_le := ramificationIdx'_of_not_le
/-
**Ideal.ramificationIdx'_bot'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R},   p ≠ ⊥ → Function.Injective ⇑(algebraMap R S)
 → p.ramificationIdx' ⊥ = 0
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ramificationIdx'_of_not_le`：∀ {R : Type u} [inst : CommRing R] {S 
: Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R}   {P : Idea
l S}, ¬Ideal.map (alge…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
-/
theorem ramificationIdx'_bot' (hp : p ≠ ⊥) (hf : Function.Injective f) :
    ramificationIdx' p (⊥ : Ideal S) = 0 :=
  ramificationIdx'_of_not_le <| le_bot_iff.not.mpr <| (map_eq_bot_iff_of_injective hf).not.mpr hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot' := ramificationIdx'_bot'
/-
**Ideal.ramificationIdx'_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   {e : ℕ},   e ≠ 0 → Ideal.map (a
lgebraMap R S) p ≤ P ^ e → ¬Ideal.map (algebraMap R S) p ≤ P ^ (e + 1) → p.ramif
icationIdx' P ≠ 0
参数：algebraMap R S；algebraMap R S；e + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx'_spec`：∀ {R : Type u} [inst : CommRing R] {S : Typ
e v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   
{n : ℕ}, Ideal.ma…
-/
theorem ramificationIdx'_ne_zero {e : ℕ} (he : e ≠ 0) (hle : map f p ≤ P ^ e)
    (hnle : ¬map f p ≤ P ^ (e + 1)) : ramificationIdx' p P ≠ 0 := by
  rwa [ramificationIdx'_spec hle hnle]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero
/-
**Ideal.le_pow_of_le_ramificationIdx'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_pow_of_le_ramificationIdx' {n : Nat} (hn : n <= ramificationIdx' p P) :
 map f p <= P ^ n
参数：hn : n <= ramificationIdx' p P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.ramificationIdx'_lt`：∀ {R : Type u} [inst : CommRing R] {S : Type 
v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   {n
 : ℕ}, ¬Ideal.m…
-/
theorem le_pow_of_le_ramificationIdx' {n : ℕ} (hn : n ≤ ramificationIdx' p P) :
    map f p ≤ P ^ n := by
  contrapose! hn
  exact ramificationIdx'_lt hn

@[deprecated (since := "2026-07-01")] alias le_pow_of_le_ramificationIdx :=
  le_pow_of_le_ramificationIdx'
/-
**Ideal.le_pow_ramificationIdx'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_pow_ramificationIdx' : map f p <= P ^ ramificationIdx' p P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.le_pow_of_le_ramificationIdx'`：le_pow_of_le_ramificationIdx' {n : 
Nat} (hn : n <= ramificationIdx' p P) : map f p <= P ^ n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem le_pow_ramificationIdx' : map f p ≤ P ^ ramificationIdx' p P :=
  le_pow_of_le_ramificationIdx' (le_refl _)

@[deprecated (since := "2026-07-01")] alias le_pow_ramificationIdx := le_pow_ramificationIdx'
/-
**Ideal.le_comap_pow_ramificationIdx'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_comap_pow_ramificationIdx' : p <= comap f (P ^ ramificationIdx' p P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.le_pow_ramificationIdx'`：le_pow_ramificationIdx' : map f p <= P ^ 
ramificationIdx' p P
-/
theorem le_comap_pow_ramificationIdx' : p ≤ comap f (P ^ ramificationIdx' p P) :=
  map_le_iff_le_comap.mp le_pow_ramificationIdx'

@[deprecated (since := "2026-07-01")] alias le_comap_pow_ramificationIdx :=
  le_comap_pow_ramificationIdx'
/-
**Ideal.le_comap_of_ramificationIdx'_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R}   {P : Ideal S}, p.ramificationIdx' P ≠ 0 → p ≤
 Ideal.comap (algebraMap R S) P
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.le_pow_ramificationIdx'`：le_pow_ramificationIdx' : map f p <= P ^ 
ramificationIdx' p P
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
-/
theorem le_comap_of_ramificationIdx'_ne_zero (h : ramificationIdx' p P ≠ 0) : p ≤ comap f P :=
  Ideal.map_le_iff_le_comap.mp <| le_pow_ramificationIdx'.trans <| Ideal.pow_le_self <| h

@[deprecated (since := "2026-07-01")] alias le_comap_of_ramificationIdx_ne_zero :=
  le_comap_of_ramificationIdx'_ne_zero

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

variable (p) in
/-
**Ideal.ramificationIdx'_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   {S₁ : Type u_1} [inst_3 : CommRing S₁] [inst_
4 : Algebra R S₁] (e : S ≃ₐ[R] S₁) (P : Ideal S₁),   p.ramificationIdx' (Ideal.c
omap e P) = p.ramificationIdx' P
参数：p : Ideal R；e : S ≃ₐ[R] S₁；P : Ideal S₁；Ideal.comap e P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `AlgEquiv.toRingEquiv_toRingHom`：toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂)
 : A₁ ->+* A₂) = e
· 使用定理 `RingEquiv.symm_symm`：symm_symm (e : R ≃+* S) : e.symm.symm = e
· 使用定理 `Ideal.map_comap_of_equiv`：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S)
 : I.map (f : R ->+* S) = I.comap f.symm
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用引理 `AlgEquiv.toAlgHom_toRingHom`：toAlgHom_toRingHom : ((e : A₁ ->ₐ[R] A₂) : 
A₁ ->+* A₂) = e
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ramificationIdx'_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    ramificationIdx' p (P.comap e) = ramificationIdx' p P := by
  dsimp only [ramificationIdx']
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Ideal.map_le_iff_le_comap]
  rw [← comap_coe e, ← e.toRingEquiv_toRingHom, comap_coe, ← RingEquiv.symm_symm (e : S ≃+* S₁),
    ← map_comap_of_equiv, ← Ideal.map_pow, map_comap_of_equiv, ← comap_coe (RingEquiv.symm _),
    comap_comap, RingEquiv.symm_symm, e.toRingEquiv_toRingHom, ← e.toAlgHom_toRingHom,
    AlgHom.comp_algebraMap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_comap_eq := ramificationIdx'_comap_eq

variable (p) in
/-
**Ideal.ramificationIdx'_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   {S₁ : Type u_1} [inst_3 : CommRing S₁] [inst_
4 : Algebra R S₁] {E : Type u_2} [inst_5 : EquivLike E S S₁]   [AlgEquivClass E 
R S S₁] (P : Ideal S) (e : E), p.ramificationIdx' (Ideal.map e P) = p.ramificati
onIdx' P
参数：p : Ideal R；P : Ideal S；e : E；Ideal.map e P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_comap_of_equiv`：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S)
 : I.map (f : R ->+* S) = I.comap f.symm
· 使用定理 `Ideal.ramificationIdx'_comap_eq`：∀ {R : Type u} [inst : CommRing R] {S :
 Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   {S₁ : Type
 u_1} [inst_3 : CommR…
-/
lemma ramificationIdx'_map_eq {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁]
    (P : Ideal S) (e : E) :
    ramificationIdx' p (P.map e) = ramificationIdx' p P := by
  rw [show P.map e = _ from P.map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.ramificationIdx'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_eq := ramificationIdx'_map_eq
/-
**Ideal.ramificationIdx'_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R}   {P : Ideal S}, Ideal.map (algebraMap R S) p ≤
 P → (p.ramificationIdx' P ≠ 1 ↔ Ideal.map (algebraMap R S) p ≤ P ^ 2)
参数：algebraMap R S；p.ramificationIdx' P ≠ 1 ↔ Ideal.map (algebraMap R S) p ≤ P ^ 
2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.ramificationIdx'_eq_zero`：∀ {R : Type u} [inst : CommRing R] {S : 
Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R}   {P : Ideal 
S}, (∀ (n : ℕ), ∃ k,…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.ramificationIdx'_eq_find`：∀ {R : Type u} [inst : CommRing R] {S : 
Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}
   [inst_3 : Decidab…
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
-/
lemma ramificationIdx'_ne_one_iff (hp : map f p ≤ P) :
    ramificationIdx' p P ≠ 1 ↔ p.map f ≤ P ^ 2 := by
  classical
  by_cases! H : ∀ n : ℕ, ∃ k, p.map f ≤ P ^ k ∧ n < k
  · obtain ⟨k, hk, h2k⟩ := H 2
    simp [Ideal.ramificationIdx'_eq_zero H, hk.trans (Ideal.pow_le_pow_right h2k.le)]
  rw [Ideal.ramificationIdx'_eq_find H]
  constructor
  · intro he
    have : 1 ≤ Nat.find H := Nat.find_spec H 1 (by simpa)
    have := Nat.find_min H (m := 1) (by lia)
    push Not at this
    obtain ⟨k, hk, h1k⟩ := this
    exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le_iff.mpr h1k))
  · intro he
    have := Nat.find_spec H 2 he
    lia

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_one_iff :=
  ramificationIdx'_ne_one_iff

open IsLocalRing in
/-- The converse is true when `S` is a Dedekind domain.
See `Ideal.ramificationIdx'_eq_one_iff_of_isDedekindDomain`. -/
/-
**Ideal.ramificationIdx'_eq_one_of_map_localization** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : P.IsPrime] [IsNoether
ianRing S],   Ideal.map (algebraMap R S) p ≤ P →     P ≠ ⊥ →       P.primeCompl 
≤ nonZeroDivisors S →         Ideal.map (algebraMap R (Localization.AtPrime P)) 
p = IsLocalRing.maximalIdeal (Localization.AtPrime P) →           p.ramification
Idx' P = 1
参数：algebraMap R S；algebraMap R (Localization.AtPrime P)；Localization.AtPrime P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Ideal.ramificationIdx'_ne_one_iff`：∀ {R : Type u} [inst : CommRing R] {S
 : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R}   {P : Ide
al S}, Ideal.map (algeb…
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`：eq_bot_of_le_smul_of_le_
jacobson_bot (I : Ideal R) (N : Submodule R M) (hN : N.FG) (hIN : N <= I • N) (h
Ijac : I <= jacobson ⊥) : N = ⊥
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `IsLocalization.instIsNoetherianRingLocalization`：∀ {R : Type u_3} [inst 
: CommRing R] [IsNoetherianRing R] (S : Submonoid R), IsNoetherianRing (Localiza
tion S)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…

--- 原说明 ---
The converse is true when `S` is a Dedekind domain.
See `Ideal.ramificationIdx'_eq_one_iff_of_isDedekindDomain`.
-/
lemma ramificationIdx'_eq_one_of_map_localization
    {p : Ideal R} {P : Ideal S} [P.IsPrime] [IsNoetherianRing S]
    (hpP : map (algebraMap R S) p ≤ P) (hp : P ≠ ⊥) (hp' : P.primeCompl ≤ nonZeroDivisors S)
    (H : p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P)) :
    ramificationIdx' p P = 1 := by
  rw [← not_ne_iff (b := 1), Ideal.ramificationIdx'_ne_one_iff hpP]
  intro h₂
  replace h₂ := Ideal.map_mono («f» := algebraMap S (Localization.AtPrime P)) h₂
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, H, pow_two] at h₂
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
    (maximalIdeal_le_jacobson _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_eq_bot_iff_of_injective] at this
  · exact hp this
  · exact IsLocalization.injective _ hp'

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_of_map_localization :=
  ramificationIdx'_eq_one_of_map_localization
/-
**Ideal.ramificationIdx'_map_self_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R}   [IsDedekindDomain S],   Ideal.map (algebraMap
 R S) p ≠ ⊤ →     Ideal.map (algebraMap R S) p ≠ ⊥ → p.ramificationIdx' (Ideal.m
ap (algebraMap R S) p) = 1
参数：algebraMap R S；algebraMap R S；Ideal.map (algebraMap R S) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ramificationIdx'_spec`：∀ {R : Type u} [inst : CommRing R] {S : Typ
e v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   
{n : ℕ}, Ideal.ma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsMulTorsionFree.pow_right_injective₀`：IsMulTorsionFree.pow_right_inject
ive₀ {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M] [IsMulTorsionFree M]
 {x : M} (hx : x != 1) (hx'…
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.instIsMulTorsionFree`：∀ {M : Type u_1} [inst :
 CommMonoidWithZero M] [UniqueFactorizationMonoid M] [NormalizationMonoid M]   [
IsMulTorsionFree Mˣ], IsMulTorsionFr…
· 使用定理 `Subsingleton.to_isMulTorsionFree`：∀ {M : Type u_1} [inst : Monoid M] [Su
bsingleton M], IsMulTorsionFree M
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
theorem ramificationIdx'_map_self_eq_one [IsDedekindDomain S]
    (h₁ : map f p ≠ ⊤) (h₂ : map f p ≠ ⊥) : ramificationIdx' p (map f p) = 1 := by
  refine ramificationIdx'_spec (by simp) fun h ↦ ?_
  have : map f p ^ 1 = (map f p) ^ 2 := by
    rw [pow_one]
    exact le_antisymm h <| pow_le_self two_ne_zero
  have := IsMulTorsionFree.pow_right_injective₀ (by rwa [one_eq_top]) h₂ this
  simp_all

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_self_eq_one :=
  ramificationIdx'_map_self_eq_one

variable (p P) in
/-
**Ideal.ramificationIdx'_le_ramificationIdx'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   {T : Type u_2} [inst_3 : CommRi
ng T] [inst_4 : Algebra R T] [inst_5 : Algebra S T] [IsScalarTower R S T]   (Q :
 Ideal T),   p = Ideal.comap (algebraMap R S) P → p.ramificationIdx' Q ≠ 0 → P.r
amificationIdx' Q ≤ p.ramificationIdx' Q
参数：p : Ideal R；P : Ideal S；Q : Ideal T；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le_csSup'`：csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s
 subseteq t) : sSup s <= sSup t
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `Nat.sSup_of_not_bddAbove`：sSup_of_not_bddAbove {s : Set Nat} (h : ¬BddAb
ove s) : sSup s = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
-/
theorem ramificationIdx'_le_ramificationIdx' {T : Type*} [CommRing T] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (Q : Ideal T) (hp : p = comap f P)
    (h : ramificationIdx' p Q ≠ 0) : ramificationIdx' P Q ≤ ramificationIdx' p Q := by
  simp_rw [ramificationIdx', Ne] at *
  refine csSup_le_csSup' (h.imp_symm Nat.sSup_of_not_bddAbove) fun n hn ↦ ?_
  simp_rw [hp, IsScalarTower.algebraMap_eq R S T, ← map_map, map_le_iff_le_comap]
  exact comap_mono <| by rwa [← map_le_iff_le_comap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'

namespace IsDedekindDomain

variable [IsDedekindDomain S]

/-
**Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count** 是 Mathlib
 中的一个定理，位于命名空间 `Ideal.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : IsDedekindDomain S], 
  Ideal.map (algebraMap R S) p ≠ ⊥ →     P.IsPrime →       P ≠ ⊥ →         p.ram
ificationIdx' P =           Multiset.count P (UniqueFactorizationMonoid.normaliz
edFactors (Ideal.map (algebraMap R S) p))
参数：algebraMap R S；UniqueFactorizationMonoid.normalizedFactors (Ideal.map (algebr
aMap R S) p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `Ideal.ramificationIdx'_spec`：∀ {R : Type u} [inst : CommRing R] {S : Typ
e v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   
{n : ℕ}, Ideal.ma…
· 使用定理 `Ideal.le_of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R},
 I ∣ J → J ≤ I
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_pow`：normalizedFactors_pow {
x : α} (n : Nat) : normalizedFactors (x ^ n) = n • normalizedFactors x
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_irreducible`：normalizedFacto
rs_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a
}
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用引理 `Multiset.nsmul_singleton`：nsmul_singleton (a : α) (n) : n • ({a} : Multi
set α) = replicate n a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.le_count_iff_replicate_le`：le_count_iff_replicate_le {a : α} {s
 : Multiset α} {n : Nat} : n <= count a s ↔ replicate n a <= s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem ramificationIdx'_eq_normalizedFactors_count
    (hp0 : map f p ≠ ⊥) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : ramificationIdx' p P = (normalizedFactors (map f p)).count P := by
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  refine ramificationIdx'_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
      normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]
  exact (Nat.lt_succ_self _).not_ge
/-
**Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity** 是 Mathlib 中的一个定理，位于命
名空间 `Ideal.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   [IsDedekindDomain S],   Ideal.m
ap (algebraMap R S) p ≠ ⊥ → P.IsPrime → p.ramificationIdx' P = multiplicity P (I
deal.map (algebraMap R S) p)
参数：algebraMap R S；Ideal.map (algebraMap R S) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `multiplicity_zero_eq_zero_of_ne_zero`：multiplicity_zero_eq_zero_of_ne_ze
ro (a : α) (ha : a != 0) : multiplicity 0 a = 0
· 使用定理 `Ideal.ramificationIdx'_of_not_le`：∀ {R : Type u} [inst : CommRing R] {S 
: Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R}   {P : Idea
l S}, ¬Ideal.map (alge…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count`：∀ {R
 : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Alge
bra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : IsDedek…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
-/
theorem ramificationIdx'_eq_multiplicity (hp : map f p ≠ ⊥) (hP : P.IsPrime) :
    ramificationIdx' p P = multiplicity P (Ideal.map f p) := by
  by_cases hP₂ : P = ⊥
  · rw [hP₂, ← Ideal.zero_eq_bot, multiplicity_zero_eq_zero_of_ne_zero _ hp]
    exact Ideal.ramificationIdx'_of_not_le (mt le_bot_iff.mp hp)
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [ramificationIdx'_eq_normalizedFactors_count hp hP hP₂, ← normalize_eq P,
    ← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp, normalize_eq]
  exact irreducible_iff_prime.mpr <| prime_of_isPrime hP₂ hP
/-
**Ideal.IsDedekindDomain.ramificationIdx'_eq_factors_count** 是 Mathlib 中的一个定理，位于
命名空间 `Ideal.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : IsDedekindDomain S], 
  Ideal.map (algebraMap R S) p ≠ ⊥ →     P.IsPrime →       P ≠ ⊥ → p.ramificatio
nIdx' P = Multiset.count P (UniqueFactorizationMonoid.factors (Ideal.map (algebr
aMap R S) p))
参数：algebraMap R S；UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) 
p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count`：∀ {R
 : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Alge
bra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : IsDedek…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.factors_eq_normalizedFactors`：factors_eq_norma
lizedFactors {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [S
ubsingleton Mˣ] (x : M) : factors x = normal…
-/
theorem ramificationIdx'_eq_factors_count
    (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx' p P = (factors (map f p)).count P := by
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0,
    factors_eq_normalizedFactors]
/-
**Ideal.IsDedekindDomain.ramificationIdx'_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {p : Ideal R} {P : Ideal S}   [IsDedekindDomain S],   Ideal.m
ap (algebraMap R S) p ≠ ⊥ → P.IsPrime → Ideal.map (algebraMap R S) p ≤ P → p.ram
ificationIdx' P ≠ 0
参数：algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count`：∀ {R
 : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Alge
bra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : IsDedek…
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用引理 `Multiset.count_ne_zero`：count_ne_zero {a : α} : count a s != 0 ↔ a in s
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem ramificationIdx'_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (le : map f p ≤ P) :
    ramificationIdx' p P ≠ 0 := by
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hp0 (le_bot_iff.mp le)
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero
/-
**Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver** 是 Mathlib 中的一个定理
，位于命名空间 `Ideal.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] [IsDedekindDomain S]   [IsDomain R] [Module.IsTorsionFree R S
] (P : Ideal S) [hP : P.IsPrime] {p : Ideal R},   p ≠ ⊥ → ∀ [hPp : P.LiesOver p]
, p.ramificationIdx' P ≠ 0
参数：P : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero`：∀ {R : Type u} [inst : 
CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal
 R} {P : Ideal S}   [IsDedekindDomain…
· 使用定理 `Ideal.map_ne_bot_of_ne_bot`：map_ne_bot_of_ne_bot {R S : Type*} [CommSemi
ring R] [Semiring S] [Algebra R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥)
 : map (algebraM…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
-/
theorem ramificationIdx'_ne_zero_of_liesOver [IsDomain R] [IsTorsionFree R S]
    (P : Ideal S) [hP : P.IsPrime] {p : Ideal R} (hp : p ≠ ⊥) [hPp : P.LiesOver p] :
    ramificationIdx' p P ≠ 0 :=
  IsDedekindDomain.ramificationIdx'_ne_zero (map_ne_bot_of_ne_bot hp) hP <|
    map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff _ _).mp hPp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero_of_liesOver :=
  ramificationIdx'_ne_zero_of_liesOver

set_option backward.isDefEq.respectTransparency.types false in
open IsLocalRing in
/-
**Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Ideal.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] [IsDedekindDomain S]   {p : Ideal R} {P : Ideal S} [inst_4 : 
P.IsPrime],   P ≠ ⊥ →     Ideal.map (algebraMap R S) p ≤ P →       (p.ramificati
onIdx' P = 1 ↔         Ideal.map (algebraMap R (Localization.AtPrime P)) p = IsL
ocalRing.maximalIdeal (Localization.AtPrime P))
参数：algebraMap R S；p.ramificationIdx' P = 1 ↔         Ideal.map (algebraMap R (Lo
calization.AtPrime P)) p = IsLocalRing.maximalIdeal (Localization.AtPrime P)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Ideal.ramificationIdx'_ne_one_iff`：∀ {R : Type u} [inst : CommRing R] {S
 : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R}   {P : Ide
al S}, Ideal.map (algeb…
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Ideal.mul_mono_right`：mul_mono_right (h : J <= K) : I * J <= I * K
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Ideal.map_mul`：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R 
: Type u_2} [inst_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S
] (…
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `IsLocalization.map_algebraMap_ne_top_iff_disjoint`：map_algebraMap_ne_top
_iff_disjoint (I : Ideal R) : I.map (algebraMap R S) != ⊤ ↔ Disjoint (M : Set R)
 (I : Set R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.ramificationIdx'_eq_one_of_map_localization`：∀ {R : Type u} [inst 
: CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ide
al R} {P : Ideal S}   [inst_3 : P.IsPri…
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
lemma ramificationIdx'_eq_one_iff
    {p : Ideal R} {P : Ideal S} [P.IsPrime]
    (hp : P ≠ ⊥) (hpP : p.map (algebraMap R S) ≤ P) :
    ramificationIdx' p P = 1 ↔
      p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P) := by
  refine ⟨?_, ramificationIdx'_eq_one_of_map_localization hpP hp (primeCompl_le_nonZeroDivisors _)⟩
  let Sₚ := Localization.AtPrime P
  rw [← not_ne_iff (b := 1), ramificationIdx'_ne_one_iff hpP, pow_two]
  intro H₁
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap R S) := Ideal.dvd_iff_le.mpr hpP
  have ha' : ¬ a ≤ P := fun h ↦ H₁ (ha.trans_le (Ideal.mul_mono_right h))
  rw [IsScalarTower.algebraMap_eq _ S, ← Ideal.map_map, ha, Ideal.map_mul,
    Localization.AtPrime.map_eq_maximalIdeal]
  convert! Ideal.mul_top _
  on_goal 2 => infer_instance
  rw [← not_ne_iff, IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl]
  simpa [primeCompl, Set.disjoint_compl_left_iff_subset]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_iff :=
  ramificationIdx'_eq_one_iff
/-
**Ideal.IsDedekindDomain.ramificationIdx'_le_ramificationIdx'** 是 Mathlib 中的一个定理
，位于命名空间 `Ideal.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] [IsDedekindDomain S]   [IsDomain R] [Module.IsTorsionFree R S
] {S₀ : Type u_2} [inst_6 : CommRing S₀] [inst_7 : Algebra R S₀]   [inst_8 : Alg
ebra S₀ S] [IsScalarTower R S₀ S] (p : Ideal R) (P : Ideal S₀) (Q : Ideal S) [Q.
LiesOver p]   [hP : P.LiesOver p] [Q.IsPrime], p ≠ ⊥ → P.ramificationIdx' Q ≤ p.
ramificationIdx' Q
参数：p : Ideal R；P : Ideal S₀；Q : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ramificationIdx'_le_ramificationIdx'`：∀ {R : Type u} [inst : CommR
ing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (
P : Ideal S)   {T : Type u_2} [i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`：∀ {R : Type
 u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S
] [IsDedekindDomain S]   [IsDomain R] [Module.IsT…
-/
theorem ramificationIdx'_le_ramificationIdx' [IsDomain R] [IsTorsionFree R S] {S₀ : Type*}
    [CommRing S₀] [Algebra R S₀] [Algebra S₀ S] [IsScalarTower R S₀ S] (p : Ideal R)
    (P : Ideal S₀) (Q : Ideal S) [Q.LiesOver p] [hP : P.LiesOver p] [Q.IsPrime] (hp : p ≠ ⊥) :
    Ideal.ramificationIdx' P Q ≤ Ideal.ramificationIdx' p Q :=
  p.ramificationIdx'_le_ramificationIdx' P Q ((liesOver_iff ..).mp hP) <|
    ramificationIdx'_ne_zero_of_liesOver _ hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'
/-
**Ideal.IsDedekindDomain.emultiplicity_map_eq_zero_of_ne** 是 Mathlib 中的一个定理，位于命名
空间 `Ideal.IsDedekindDomain`。
形式化陈述：emultiplicity_map_eq_zero_of_ne [IsDedekindDomain R] {v : Ideal R} {w : Id
eal S} {p : Ideal R} (hv : Irreducible v) (hp : Prime p) (hvp : v != p) [w.LiesO
ver v] : emultiplicity w (p.map (algebraMap R S)) = 0
参数：hv : Irreducible v；hp : Prime p；hvp : v != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_zero`：emultiplicity_eq_zero : emultiplicity a b = 0 ↔ ¬
a ∣ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Irreducible.prime`：Irreducible.prime [DecompositionMonoid M] {a : M} (ir
r : Irreducible a) : Prime a
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
-/
theorem emultiplicity_map_eq_zero_of_ne [IsDedekindDomain R] {v : Ideal R}
    {w : Ideal S} {p : Ideal R} (hv : Irreducible v) (hp : Prime p) (hvp : v ≠ p) [w.LiesOver v] :
    emultiplicity w (p.map (algebraMap R S)) = 0 := by
  refine emultiplicity_eq_zero.2 fun h ↦ hvp.symm ?_
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← under_def, ← Ideal.over_def w v] at h
  exact ((isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le (isPrime_of_prime hv.prime).ne_top h

/-- Use the more general result `emultiplicity_map_eq_ramificationIdx'_mul`.
This is a helper lemma. -/
/-
**Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul_of_prime** 是 
Mathlib 中的一个定理，位于命名空间 `Ideal.IsDedekindDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the more general result `emultiplicity_map_eq_ramificationIdx'_mul`.
This is a helper lemma.
-/
private theorem emultiplicity_map_eq_ramificationIdx'_mul_of_prime [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} {p : Ideal R}
    (hv : Irreducible v) (hp : Prime p) (hw : Irreducible w) (hw_bot : w ≠ ⊥)
    [w.LiesOver v] : emultiplicity w (p.map (algebraMap R S)) =
      v.ramificationIdx' w * emultiplicity v p := by
  have hp_bot : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp.ne_zero
  by_cases hvp : v = p
  · simp [hvp, (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self,
      ramificationIdx'_eq_normalizedFactors_count hp_bot (isPrime_of_prime hw.prime) hw_bot,
      emultiplicity_eq_count_normalizedFactors hw hp_bot]
  · rw [emultiplicity_eq_zero_of_irreducible_ne hv hp.irreducible hvp, mul_zero,
      emultiplicity_map_eq_zero_of_ne hv hp hvp]

/-- If `v` is an irreducible ideal of `R`, `w` is an irreducible ideal of `S` lying over `v`, and
`I` is an ideal of `R`, then the multiplicity of `w` in `I.map (algebraMap R S)` is given by
the multiplicity of `v` in `I` multiplied by the ramification index of `w` over `v`. -/
/-
**Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul** 是 Mathlib 中
的一个定理，位于命名空间 `Ideal.IsDedekindDomain`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] [IsDedekindDomain S]   [IsDedekindDomain R] [FaithfulSMul R S
] {v : Ideal R} {w : Ideal S} {I : Ideal R},   I ≠ ⊥ →     Irreducible v →      
 Irreducible w →         w ≠ ⊥ →           ∀ [w.LiesOver v], emultiplicity w (Id
eal.map (algebraMap R S) I) = ↑(v.ramificationIdx' w) * emultiplicity v I
参数：Ideal.map (algebraMap R S) I；v.ramificationIdx' w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.induction_on_prime`：induction_on_prime {P : α 
-> Prop} (a : α) (h₁ : P 0) (h₂ : forall x : α, IsUnit x -> P x) (h₃ : forall a 
p : α, a != 0 -> Prime p -> P a ->…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.congr_simp`：∀ {α : Type u_1}
 [inst : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : Unique
FactorizationMonoid α]   (a a_1 : α), a = a_…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_one`：normalizedFactors_one :
 normalizedFactors (1 : α) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_mul`：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R 
: Type u_2} [inst_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S
] (…
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `Irreducible.prime`：Irreducible.prime [DecompositionMonoid M] {a : M} (ir
r : Irreducible a) : Prime a
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `v` is an irreducible ideal of `R`, `w` is an irreducible ideal of `S` lying 
over `v`, and
`I` is an ideal of `R`, then the multiplicity of `w` in `I.map (algebraMap R S)`
 is given by
the multiplicity of `v` in `I` multiplied by the ramification index of `w` over 
`v`.
-/
theorem emultiplicity_map_eq_ramificationIdx'_mul [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} {I : Ideal R} (h : I ≠ ⊥)
    (hv : Irreducible v) (hw : Irreducible w) (hw_bot : w ≠ ⊥) [w.LiesOver v] :
    emultiplicity w (I.map (algebraMap R S)) =
      v.ramificationIdx' w * emultiplicity v I := by
  induction I using induction_on_prime with
  | h₁ => aesop
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp_rw [Ideal.map_top, emultiplicity_eq_count_normalizedFactors hw top_ne_bot,
      emultiplicity_eq_count_normalizedFactors hv h, ← Ideal.one_eq_top, normalizedFactors_one]
    simp
  | h₃ I p hI hp IH =>
    rw [Ideal.map_mul, emultiplicity_mul hw.prime, emultiplicity_mul hv.prime, IH hI, mul_add,
      emultiplicity_map_eq_ramificationIdx'_mul_of_prime hv hp hw hw_bot]

@[deprecated (since := "2026-07-01")] alias emultiplicity_map_eq_ramificationIdx_mul :=
  emultiplicity_map_eq_ramificationIdx'_mul

end IsDedekindDomain

end DecEq

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Let `T / S / R` be a tower of algebras, `p, P, Q` be ideals in `R, S, T` respectively,
  and `P` and `Q` are prime. If `P = Q ∩ S`, then `e (Q | p) = e (P | p) * e (Q | P)`. -/
/-
**Ideal.ramificationIdx'_algebra_tower** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
S T] [inst_5 : Algebra R T] [IsScalarTower R S T] [IsDedekindDomain S]   [IsDede
kindDomain T] {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime] [hqm :
 Q.IsPrime],   Ideal.map (algebraMap S T) P ≠ ⊥ →     Ideal.map (algebraMap R T)
 p ≠ ⊥ →       Ideal.map (algebraMap S T) P ≤ Q → p.ramificationIdx' Q = p.ramif
icationIdx' P * P.ramificationIdx' Q
参数：algebraMap S T；algebraMap R T；algebraMap S T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ne_bot_of_map_ne_bot`：ne_bot_of_map_ne_bot (hI : map f I != ⊥) : I
 != ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Ring.DimensionLEOne.maximalOfPrime`：∀ {R : Type u_1} {inst : CommRing R}
 [self : Ring.DimensionLEOne R] {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count`：∀ {R
 : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Alge
bra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : IsDedek…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.eq_prime_pow_mul_coprime`：eq_prime_pow_mul_coprime {I : Ideal T} (
hI : I != ⊥) (P : Ideal T) [hpm : P.IsMaximal] : exists Q : Ideal T, P ⊔ Q = ⊤ ∧
 I = P ^ (Multiset.c…
· 使用定理 `Ideal.map_sup`：map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `trivial`：True
· 使用定理 `Ideal.map_mul`：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R 
: Type u_2} [inst_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S
] (…
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_pow`：normalizedFactors_pow {
x : α} (n : Nat) : normalizedFactors (x ^ n) = n • normalizedFactors x
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Let `T / S / R` be a tower of algebras, `p, P, Q` be ideals in `R, S, T` respect
ively,
  and `P` and `Q` are prime. If `P = Q ∩ S`, then `e (Q | p) = e (P | p) * e (Q 
| P)`.
-/
theorem ramificationIdx'_algebra_tower [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime] [hqm : Q.IsPrime]
    (hg0 : map (algebraMap S T) P ≠ ⊥)
    (hfg : map (algebraMap R T) p ≠ ⊥) (hg : map (algebraMap S T) P ≤ Q) :
    ramificationIdx' p Q =
    ramificationIdx' p P * ramificationIdx' P Q := by
  have hf0 : map (algebraMap R S) p ≠ ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S T, ← map_map] at hfg
    exact ne_bot_of_map_ne_bot hfg
  have hp0 : P ≠ ⊥ := ne_bot_of_map_ne_bot hg0
  have hq0 : Q ≠ ⊥ := ne_bot_of_le_ne_bot hg0 hg
  let : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpm
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hf0 hpm hp0,
    IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hg0 hqm hq0,
    IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hfg hqm hq0,
    IsScalarTower.algebraMap_eq R S T, ← map_map]
  rcases eq_prime_pow_mul_coprime hf0 P with ⟨I, hcp, heq⟩
  have hcp : ⊤ = map (algebraMap S T) P ⊔ map (algebraMap S T) I := by rw [← map_sup, hcp, map_top]
  have hntq : ¬ ⊤ ≤ Q := fun ht ↦ IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
  nth_rw 1 [heq, Ideal.map_mul, Ideal.map_pow, normalizedFactors_mul (pow_ne_zero _ hg0) <| by
    by_contra h
    simp only [h, Submodule.zero_eq_bot, bot_le, sup_of_le_left] at hcp
    exact hntq (hcp.trans_le hg), Multiset.count_add, normalizedFactors_pow, Multiset.count_nsmul]
  exact add_eq_left.mpr <| Decidable.byContradiction fun h ↦ hntq <| hcp.trans_le <|
    sup_le hg <| le_of_dvd <| dvd_of_mem_normalizedFactors <| Multiset.count_ne_zero.mp h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower :=
  ramificationIdx'_algebra_tower
/-
**Ideal.ramificationIdx'_algebra_tower'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
S T] [inst_5 : Algebra R T] [IsScalarTower R S T] [IsDedekindDomain S]   [IsDede
kindDomain T] [IsDomain R] [Module.IsTorsionFree R S] [Module.IsTorsionFree S T]
 (p : Ideal R) (P : Ideal S)   (Q : Ideal T) [Q.IsPrime] [Q.LiesOver P] [P.LiesO
ver p],   p.ramificationIdx' Q = p.ramificationIdx' P * P.ramificationIdx' Q
参数：p : Ideal R；P : Ideal S；Q : Ideal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx'_bot`：∀ {R : Type u} [inst : CommRing R] {S : Type
 v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Ideal S},   ⊥.ramification
Idx' P = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.isPrime_of_liesOver`：isPrime_of_liesOver [P.LiesOver p] [P.IsPrime
] : p.IsPrime
· 使用引理 `Module.IsTorsionFree.of_smul_eq_zero`：Module.IsTorsionFree.of_smul_eq_ze
ro [Nontrivial R] (h : forall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0) : IsT
orsionFree R M where isSMu…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `algebra_compatible_smul`：algebra_compatible_smul (r : R) (m : M) : r • m
 = (algebraMap R A) r • m
· 使用定理 `Ideal.ne_bot_of_liesOver_of_ne_bot`：ne_bot_of_liesOver_of_ne_bot (hp : p
 != ⊥) (P : Ideal B) [P.LiesOver p] : P != ⊥
· 使用定理 `Ideal.ramificationIdx'_algebra_tower`：∀ {R : Type u_1} {S : Type u_2} {T
 : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [
inst_3 : Algebra R S] [ins…
· 使用定理 `Ideal.map_ne_bot_of_ne_bot`：map_ne_bot_of_ne_bot {R S : Type*} [CommSemi
ring R] [Semiring S] [Algebra R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥)
 : map (algebraM…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
-/
theorem ramificationIdx'_algebra_tower' [IsDedekindDomain S] [IsDedekindDomain T] [IsDomain R]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree S T] (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] :
    ramificationIdx' p Q =
      ramificationIdx' p P * ramificationIdx' P Q := by
  obtain rfl | hp := eq_or_ne p ⊥
  · simp
  have : P.IsPrime := isPrime_of_liesOver Q P
  have : Module.IsTorsionFree R T := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h ↦ ?_
    rwa [algebra_compatible_smul S, smul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at h
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  exact ramificationIdx'_algebra_tower (map_ne_bot_of_ne_bot hP) (map_ne_bot_of_ne_bot hp)
    <| map_le_iff_le_comap.mpr <| le_of_eq <| over_def Q P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower' :=
  ramificationIdx'_algebra_tower'

end tower

end Ideal

