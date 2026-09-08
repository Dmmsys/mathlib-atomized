/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.Identities

/-!

# Witt vectors over a domain

This file builds to the proof `WittVector.instIsDomain`,
an instance that says if `R` is an integral domain, then so is `𝕎 R`.
It depends on the API around iterated applications
of `WittVector.verschiebung` and `WittVector.frobenius`
found in `Identities.lean`.

The [proof sketch](https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723)
goes as follows:
any nonzero $x$ is an iterated application of $V$
to some vector $w_x$ whose 0th component is nonzero (`WittVector.verschiebung_nonzero`).
Known identities (`WittVector.iterate_verschiebung_mul`) allow us to transform
the product of two such $x$ and $y$
to the form $V^{m+n}\left(F^n(w_x) \cdot F^m(w_y)\right)$,
the 0th component of which must be nonzero.

## Main declarations

* `WittVector.iterate_verschiebung_mul_coeff` : an identity from [Haze09]
* `WittVector.instIsDomain`

-/

@[expose] public section


noncomputable section

namespace WittVector

open Function

variable {p : ℕ} {R : Type*}

local notation "𝕎" => WittVector p -- type as `\bbW`

/-!
## The `shift` operator
-/


/--
`WittVector.verschiebung` translates the entries of a Witt vector upward, inserting 0s in the gaps.
`WittVector.shift` does the opposite, removing the first entries.
This is mainly useful as an auxiliary construction for `WittVector.verschiebung_nonzero`.
-/
/-
**WittVector.shift** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：shift (x : 𝕎 R) (n : Nat) : 𝕎 R
参数：x : 𝕎 R；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WittVector.verschiebung` translates the entries of a Witt vector upward, insert
ing 0s in the gaps.
`WittVector.shift` does the opposite, removing the first entries.
This is mainly useful as an auxiliary construction for `WittVector.verschiebung_
nonzero`.
-/
def shift (x : 𝕎 R) (n : ℕ) : 𝕎 R :=
  @mk' p R fun i => x.coeff (n + i)
/-
**WittVector.shift_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：shift_coeff (x : 𝕎 R) (n k : Nat) : (x.shift n).coeff k = x.coeff (n + k)
参数：x : 𝕎 R；n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shift_coeff (x : 𝕎 R) (n k : ℕ) : (x.shift n).coeff k = x.coeff (n + k) :=
  rfl

variable [hp : Fact p.Prime] [CommRing R]
/-
**WittVector.verschiebung_shift** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_shift (x : 𝕎 R) (k : Nat) (h : forall i < k + 1, x.coeff i = 
0) : verschiebung (x.shift k.succ) = x.shift k
参数：x : 𝕎 R；k : Nat；h : forall i < k + 1, x.coeff i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.verschiebung_coeff_zero`：verschiebung_coeff_zero (x : 𝕎 R) : 
(verschiebung x).coeff 0 = 0
· 使用定理 `WittVector.shift_coeff`：shift_coeff (x : 𝕎 R) (n k : Nat) : (x.shift n).
coeff k = x.coeff (n + k)
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem verschiebung_shift (x : 𝕎 R) (k : ℕ) (h : ∀ i < k + 1, x.coeff i = 0) :
    verschiebung (x.shift k.succ) = x.shift k := by
  ext ⟨j⟩
  · rw [verschiebung_coeff_zero, shift_coeff, h]
    apply Nat.lt_succ_self
  · simp only [verschiebung_coeff_succ, shift]
    congr 1
    rw [Nat.add_succ, add_comm, Nat.add_succ, add_comm]
/-
**WittVector.eq_iterate_verschiebung** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：eq_iterate_verschiebung {x : 𝕎 R} {n : Nat} (h : forall i < n, x.coeff i =
 0) : x = verschiebung^[n] (x.shift n)
参数：h : forall i < n, x.coeff i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.verschiebung_shift`：verschiebung_shift (x : 𝕎 R) (k : Nat) (h
 : forall i < k + 1, x.coeff i = 0) : verschiebung (x.shift k.succ) = x.shift k
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem eq_iterate_verschiebung {x : 𝕎 R} {n : ℕ} (h : ∀ i < n, x.coeff i = 0) :
    x = verschiebung^[n] (x.shift n) := by
  induction n with
  | zero => cases x; simp [shift]
  | succ k ih =>
    dsimp; rw [verschiebung_shift]
    · exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_self _))
    · exact h
/-
**WittVector.verschiebung_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_nonzero {x : 𝕎 R} (hx : x != 0) : exists n : Nat, exists x' :
 𝕎 R, x'.coeff 0 != 0 ∧ x = verschiebung^[n] x'
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `WittVector.eq_iterate_verschiebung`：eq_iterate_verschiebung {x : 𝕎 R} {n
 : Nat} (h : forall i < n, x.coeff i = 0) : x = verschiebung^[n] (x.shift n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
-/
theorem verschiebung_nonzero {x : 𝕎 R} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ x' : 𝕎 R, x'.coeff 0 ≠ 0 ∧ x = verschiebung^[n] x' := by
  classical
  have hex : ∃ k : ℕ, x.coeff k ≠ 0 := by
    by_contra! hall
    apply hx
    ext i
    simp only [hall, zero_coeff]
  let n := Nat.find hex
  use n, x.shift n
  refine ⟨Nat.find_spec hex, eq_iterate_verschiebung fun i hi => not_not.mp ?_⟩
  exact Nat.find_min hex hi

/-!
## Witt vectors over a domain

If `R` is an integral domain, then so is `𝕎 R`.
This argument is adapted from
<https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723>.
-/


/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## Witt vectors over a domain

If `R` is an integral domain, then so is `𝕎 R`.
This argument is adapted from
<https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-i
ntegral-domain/4118723#4118723>.
-/
instance [CharP R p] [NoZeroDivisors R] : NoZeroDivisors (𝕎 R) :=
  ⟨fun {x y} => by
    contrapose!
    rintro ⟨ha, hb⟩
    rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, rfl⟩
    rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, rfl⟩
    refine ne_of_apply_ne (fun x => x.coeff (na + nb)) ?_
    rw [iterate_verschiebung_mul_coeff, zero_coeff]
    exact mul_ne_zero (pow_ne_zero _ hwa0) (pow_ne_zero _ hwb0)⟩
/-
**WittVector.instIsDomain** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：instIsDomain [CharP R p] [IsDomain R] : IsDomain (𝕎 R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `WittVector.instNontrivial`：∀ {p : ℕ} {R : Type u_1} [CommRing R] [Fact (
Nat.Prime p)] [Nontrivial R], Nontrivial (WittVector p R)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `WittVector.instNoZeroDivisorsOfCharP`：∀ {p : ℕ} {R : Type u_1} [hp : Fac
t (Nat.Prime p)] [inst : CommRing R] [CharP R p] [NoZeroDivisors R],   NoZeroDiv
isors (WittVector p R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
instance instIsDomain [CharP R p] [IsDomain R] : IsDomain (𝕎 R) :=
  NoZeroDivisors.to_isDomain _

end WittVector

