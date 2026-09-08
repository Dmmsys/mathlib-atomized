/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FinCases

/-!
# Sets of tuples with a fixed product

This file defines the finite set of `d`-tuples of natural numbers with a fixed product `n` as
`Nat.finMulAntidiag`.

## Main Results
* There are `d^(ω n)` ways to write `n` as a product of `d` natural numbers, when `n` is squarefree
  (`card_finMulAntidiag_of_squarefree`)
* There are `3^(ω n)` pairs of natural numbers whose `lcm` is `n`, when `n` is squarefree
  (`card_pair_lcm_eq`)
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction
namespace PNat

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.instHasAntidiagonal** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：instHasAntidiagonal : Finset.HasAntidiagonal (Additive Nat+)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasAntidiagonal : Finset.HasAntidiagonal (Additive ℕ+) :=
  /- The set of divisors of a positive natural number.
This is `Nat.divisorsAntidiagonal` without a special case for `n = 0`. -/
  let divisorsAntidiagonal (n : ℕ+) : Finset (ℕ+ × ℕ+) :=
    (Nat.divisorsAntidiagonal n).attach.map
      ⟨fun x =>
        (⟨x.val.1, Nat.pos_of_mem_divisors <| Nat.fst_mem_divisors_of_mem_antidiagonal x.prop⟩,
        ⟨x.val.2, Nat.pos_of_mem_divisors <| Nat.snd_mem_divisors_of_mem_antidiagonal x.prop⟩),
      fun _ _ h => Subtype.ext <| Prod.ext (congr_arg (·.1.val) h) (congr_arg (·.2.val) h)⟩
  have mem_divisorsAntidiagonal {n : ℕ+} (x : ℕ+ × ℕ+) :
    x ∈ divisorsAntidiagonal n ↔ x.1 * x.2 = n := by
    simp_rw [divisorsAntidiagonal, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
      Prod.ext_iff, true_and, ← coe_inj, Subtype.exists]
    simp
  { antidiagonal := fun n ↦ divisorsAntidiagonal (Additive.toMul n) |>.map
      (.prodMap (Additive.ofMul.toEmbedding) (Additive.ofMul.toEmbedding))
    mem_antidiagonal := by simp [← ofMul_mul, mem_divisorsAntidiagonal] }

end PNat

namespace Nat

/-- The `Finset` of all `d`-tuples of natural numbers whose product is `n`. Defined to be `∅` when
`n = 0`. -/
/-
**Nat.finMulAntidiag** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：finMulAntidiag (d : Nat) (n : Nat) : Finset (Fin d -> Nat)
参数：d : Nat；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.coe_injective`：coe_injective : Function.Injective PNat.val

--- 原说明 ---
The `Finset` of all `d`-tuples of natural numbers whose product is `n`. Defined 
to be `∅` when
`n = 0`.
-/
def finMulAntidiag (d : ℕ) (n : ℕ) : Finset (Fin d → ℕ) :=
  if hn : 0 < n then
    (Finset.finAntidiagonal d (Additive.ofMul (α := ℕ+) ⟨n, hn⟩)).map <|
      .arrowCongrRight <| Additive.toMul.toEmbedding.trans <| ⟨PNat.val, PNat.coe_injective⟩
  else
    ∅

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Nat.mem_finMulAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat} : f in finMulAntidiag d 
n ↔ ∏ i, f i = n ∧ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.coe_injective`：coe_injective : Function.Injective PNat.val
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Equiv.piCongrRight_apply`：∀ {α : Sort u_1} {β₁ : α → Sort u_9} {β₂ : α →
 Sort u_10} (F : (a : α) → β₁ a ≃ β₂ a) (a : (i : α) → β₁ i) (i : α),   (Equiv.p
iCongrRight F)…
· 使用定理 `Finset.PNat.coe_prod`：∀ {ι : Type u_4} (f : ι → ℕ+) (s : Finset ι), ↑(∏ 
i ∈ s, f i) = ∏ i ∈ s, ↑(f i)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
（共 31 条，此处仅展示前 30 条）
-/
theorem mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ finMulAntidiag d n ↔ ∏ i, f i = n ∧ n ≠ 0 := by
  unfold finMulAntidiag
  split_ifs with h
  · simp_rw [mem_map, mem_finAntidiagonal, Function.Embedding.arrowCongrRight_apply,
      Function.comp_def, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coeFn_mk, ← Additive.ofMul.symm_apply_eq, Additive.ofMul_symm_eq,
      toMul_sum, (Equiv.piCongrRight fun _ => Additive.ofMul).surjective.exists,
      Equiv.piCongrRight_apply, Pi.map_apply, toMul_ofMul, ← PNat.coe_inj, PNat.mk_coe,
      PNat.coe_prod]
    constructor
    · rintro ⟨a, ha_mem, rfl⟩
      exact ⟨ha_mem, h.ne.symm⟩
    · rintro ⟨rfl, _⟩
      refine ⟨fun i ↦ ⟨f i, ?_⟩, rfl, funext fun _ => rfl⟩
      apply Nat.pos_of_ne_zero
      exact Finset.prod_ne_zero_iff.mp h.ne.symm _ (mem_univ _)
  · simp only [not_lt, nonpos_iff_eq_zero] at h
    simp only [h, notMem_empty, ne_eq, not_true_eq_false, and_false]

@[simp]
/-
**Nat.finMulAntidiag_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：finMulAntidiag_zero_right (d : Nat) : finMulAntidiag d 0 = ∅
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finMulAntidiag_zero_right (d : ℕ) :
    finMulAntidiag d 0 = ∅ := rfl
/-
**Nat.finMulAntidiag_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：finMulAntidiag_one {d : Nat} : finMulAntidiag d 1 = {fun _ => 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem finMulAntidiag_one {d : ℕ} :
    finMulAntidiag d 1 = {fun _ => 1} := by
  ext
  simp only [mem_finMulAntidiag, prod_eq_one_iff, mem_univ, forall_const, ne_eq, one_ne_zero,
    not_false_eq_true, and_true, mem_singleton]
  grind
/-
**Nat.finMulAntidiag_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：finMulAntidiag_zero_left {n : Nat} (hn : n != 1) : finMulAntidiag 0 n = ∅
参数：hn : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finMulAntidiag_zero_left {n : ℕ} (hn : n ≠ 1) :
    finMulAntidiag 0 n = ∅ := by
  ext
  simp [hn.symm]
/-
**Nat.dvd_of_mem_finMulAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_mem_finMulAntidiag {n d : Nat} {f : Fin d -> Nat} (hf : f in finMul
Antidiag d n) (i : Fin d) : f i ∣ n
参数：hf : f in finMulAntidiag d n；i : Fin d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mem_finMulAntidiag`：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat
} : f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem dvd_of_mem_finMulAntidiag {n d : ℕ} {f : Fin d → ℕ} (hf : f ∈ finMulAntidiag d n)
    (i : Fin d) : f i ∣ n := by
  rw [mem_finMulAntidiag] at hf
  rw [← hf.1]
  exact dvd_prod_of_mem f (mem_univ i)
/-
**Nat.ne_zero_of_mem_finMulAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ne_zero_of_mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat} (hf : f in fi
nMulAntidiag d n) (i : Fin d) : f i != 0
参数：hf : f in finMulAntidiag d n；i : Fin d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_finMulAntidiag`：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat
} : f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0
· 使用定理 `Nat.dvd_of_mem_finMulAntidiag`：dvd_of_mem_finMulAntidiag {n d : Nat} {f 
: Fin d -> Nat} (hf : f in finMulAntidiag d n) (i : Fin d) : f i ∣ n
-/
theorem ne_zero_of_mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiag d n) (i : Fin d) : f i ≠ 0 :=
  ne_zero_of_dvd_ne_zero (mem_finMulAntidiag.mp hf).2 (dvd_of_mem_finMulAntidiag hf i)
/-
**Nat.prod_eq_of_mem_finMulAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_eq_of_mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat} (hf : f in fi
nMulAntidiag d n) : ∏ i, f i = n
参数：hf : f in finMulAntidiag d n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_finMulAntidiag`：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat
} : f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0
-/
theorem prod_eq_of_mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiag d n) : ∏ i, f i = n :=
  (mem_finMulAntidiag.mp hf).1
/-
**Nat.finMulAntidiag_eq_piFinset_divisors_filter** 是 Mathlib 中的一个定理，位于命名空间 `Nat`
。
形式化陈述：finMulAntidiag_eq_piFinset_divisors_filter {d m n : Nat} (hmn : m ∣ n) (hn
 : n != 0) : finMulAntidiag d m = {f in Fintype.piFinset fun _ : Fin d => n.divi
sors | ∏ i, f i = m}
参数：hmn : m ∣ n；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_of_mem_finMulAntidiag`：dvd_of_mem_finMulAntidiag {n d : Nat} {f 
: Fin d -> Nat} (hf : f in finMulAntidiag d n) (i : Fin d) : f i ∣ n
· 使用定理 `Nat.prod_eq_of_mem_finMulAntidiag`：prod_eq_of_mem_finMulAntidiag {d n : 
Nat} {f : Fin d -> Nat} (hf : f in finMulAntidiag d n) : ∏ i, f i = n
· 使用定理 `Nat.mem_finMulAntidiag`：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat
} : f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
-/
theorem finMulAntidiag_eq_piFinset_divisors_filter {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    finMulAntidiag d m =
      {f ∈ Fintype.piFinset fun _ : Fin d => n.divisors | ∏ i, f i = m} := by
  ext f
  simp only [ne_eq,
    Fintype.mem_piFinset, mem_divisors, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, prod_eq_of_mem_finMulAntidiag hf⟩
    exact fun i => ⟨(dvd_of_mem_finMulAntidiag hf i).trans hmn, hn⟩
  · rw [mem_finMulAntidiag]
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hn hmn⟩
/-
**Nat.image_apply_finMulAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：image_apply_finMulAntidiag {d n : Nat} {i : Fin d} (hd : d != 1) : (finMul
Antidiag d n).image (fun f => f i) = divisors n
参数：hd : d != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.dvd_of_mem_finMulAntidiag`：dvd_of_mem_finMulAntidiag {n d : Nat} {f 
: Fin d -> Nat} (hf : f in finMulAntidiag d n) (i : Fin d) : f i ∣ n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_finMulAntidiag`：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat
} : f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.nontrivial_iff_two_le`：nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 
2 <= n
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
（共 38 条，此处仅展示前 30 条）
-/
lemma image_apply_finMulAntidiag {d n : ℕ} {i : Fin d} (hd : d ≠ 1) :
    (finMulAntidiag d n).image (fun f => f i) = divisors n := by
  ext k
  simp only [mem_image, ne_eq, mem_divisors]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨dvd_of_mem_finMulAntidiag hf _, (mem_finMulAntidiag.mp hf).2⟩
  · simp_rw [mem_finMulAntidiag]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d) := by
      rw [Fin.nontrivial_iff_two_le]
      obtain rfl | hd' := eq_or_ne d 0
      · exact i.elim0
      lia
    obtain ⟨i', hi_ne⟩ := exists_ne i
    use fun j => if j = i then k else if j = i' then r else 1
    simp only [ite_true, and_true]
    rw [← Finset.mul_prod_erase (h := mem_univ i),
      ← Finset.mul_prod_erase (a := i')]
    · simp_all
    exact mem_erase.mpr ⟨hi_ne, mem_univ _⟩
/-
**Nat.image_piFinTwoEquiv_finMulAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：image_piFinTwoEquiv_finMulAntidiag {n : Nat} : (finMulAntidiag 2 n).image 
(piFinTwoEquiv <| fun _ => Nat) = divisorsAntidiagonal n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `piFinTwoEquiv_apply`：∀ (α : Fin 2 → Type u), ⇑(piFinTwoEquiv α) = fun f 
=> (f 0, f 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `piFinTwoEquiv_symm_apply`：∀ (α : Fin 2 → Type u), ⇑(piFinTwoEquiv α).sym
m = fun p => Fin.cons p.1 (Fin.cons p.2 finZeroElim)
· 使用定理 `Matrix.finZeroElim_eq_zero`：∀ {α : Type u_1} [inst : Zero α], finZeroEli
m = 0
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `Matrix.Fin.cons_vecEmpty`：∀ {α : Type u_1} (x : α), Fin.cons x ![] = ![x
]
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_piFinTwoEquiv_finMulAntidiag {n : ℕ} :
    (finMulAntidiag 2 n).image (piFinTwoEquiv <| fun _ => ℕ) = divisorsAntidiagonal n := by
  ext x
  simp [(piFinTwoEquiv <| fun _ => ℕ).symm.surjective.exists]
/-
**Nat.finMulAntidiag_existsUnique_prime_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：finMulAntidiag_existsUnique_prime_dvd {d n p : Nat} (hn : Squarefree n) (h
p : p in n.primeFactorsList) (f : Fin d -> Nat) (hf : f in finMulAntidiag d n) :
 exists! i, p ∣ f i
参数：hn : Squarefree n；hp : p in n.primeFactorsList；f : Fin d -> Nat；hf : f in fin
MulAntidiag d n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prime.dvd_finsetProd_iff`：Prime.dvd_finsetProd_iff {S : Finset M₀} {p : 
M} (pp : Prime p) (g : M₀ -> M) : p ∣ S.prod g ↔ exists a in S, p ∣ g a
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mem_finMulAntidiag`：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat
} : f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n
· 使用定理 `Nat.coprime_of_squarefree_mul`：coprime_of_squarefree_mul {m n : Nat} (h 
: Squarefree (m * n)) : m.Coprime n
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
-/
lemma finMulAntidiag_existsUnique_prime_dvd {d n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactorsList) (f : Fin d → ℕ) (hf : f ∈ finMulAntidiag d n) :
    ∃! i, p ∣ f i := by
  rw [mem_finMulAntidiag] at hf
  rw [mem_primeFactorsList hf.2, ← hf.1, hp.1.prime.dvd_finsetProd_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul
  apply hn.squarefree_of_dvd
  rw [← hf.1, ← Finset.mul_prod_erase _ _ his,
    ← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, mem_univ _⟩), ← mul_assoc]
  apply Nat.dvd_mul_right
/-
**Nat.primeFactorsPiBij** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def primeFactorsPiBij (d n : ℕ) :
    ∀ f ∈ (n.primeFactors.pi fun _ => (univ : Finset <| Fin d)), Fin d → ℕ :=
  fun f _ i => ∏ p ∈ {p ∈ n.primeFactors.attach | f p.1 p.2 = i}, p
/-
**Nat.primeFactorsPiBij_img** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem primeFactorsPiBij_img (d n : ℕ) (hn : Squarefree n)
    (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf ∈ finMulAntidiag d n := by
  rw [mem_finMulAntidiag]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.primeFactorsPiBij
  rw [prod_fiberwise_of_maps_to, prod_attach (f := fun x => x)]
  · apply prod_primeFactors_of_squarefree hn
  · apply fun _ _ => mem_univ _
/-
**Nat.primeFactorsPiBij_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem primeFactorsPiBij_inj (d n : ℕ)
    (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => univ)
    (g : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hg : g ∈ pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf = Nat.primeFactorsPiBij d n g hg → f = g := by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.primeFactorsPiBij]
  apply ne_of_mem_of_not_mem (s := {x | p ∣ x}) <;> simp_rw [Set.mem_ofPred_eq]
  · rw [Finset.prod_filter]
    convert! Finset.dvd_prod_of_mem _ (mem_attach (n.primeFactors) ⟨p, hp⟩)
    rw [if_pos rfl]
  · rw [mem_primeFactors] at hp
    rw [Prime.dvd_finsetProd_iff hp.1.prime]
    push Not
    intro q hq
    rw [Nat.prime_dvd_prime_iff_eq hp.1 (Nat.prime_of_mem_primeFactorsList
      <| List.mem_toFinset.mp q.2)]
    rintro rfl
    rw [(mem_filter.mp hq).2] at hfg
    exact hfg rfl
/-
**Nat.primeFactorsPiBij_surj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem primeFactorsPiBij_surj (d n : ℕ) (hn : Squarefree n)
    (t : Fin d → ℕ) (ht : t ∈ finMulAntidiag d n) : ∃ (g : _)
    (hg : g ∈ pi n.primeFactors fun _ => univ), Nat.primeFactorsPiBij d n g hg = t := by
  have existsUnique := fun (p : ℕ) (hp : p ∈ n.primeFactors) =>
    (finMulAntidiag_existsUnique_prime_dvd hn
      (mem_primeFactors_iff_mem_primeFactorsList.mp hp) t ht)
  choose f hf hf_unique using existsUnique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi, mem_univ, forall_true_iff]
  funext i
  have : t i ∣ n := dvd_of_mem_finMulAntidiag ht _
  trans (∏ p ∈ n.primeFactors.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.primeFactorsPiBij, ← prod_filter]
    congr
    grind
  rw [prod_attach (f := fun p => if p ∣ t i then p else 1), ← Finset.prod_filter]
  rw [primeFactors_filter_dvd_of_dvd hn.ne_zero this]
  exact prod_primeFactors_of_squarefree <| hn.squarefree_of_dvd this
/-
**Nat.card_finMulAntidiag_pi** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem card_finMulAntidiag_pi (d n : ℕ) (hn : Squarefree n) :
    #(n.primeFactors.pi fun _ => (univ : Finset <| Fin d)) =
      #(finMulAntidiag d n) := by
  apply Finset.card_bij (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)

open scoped ArithmeticFunction.omega in -- access notation `ω`
/-
**Nat.card_finMulAntidiag_of_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_finMulAntidiag_of_squarefree {d n : Nat} (hn : Squarefree n) : #(finM
ulAntidiag d n) = d ^ ω n
参数：hn : Squarefree n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Order.Antidiag.Nat.0.Nat.card_finMulAntidiag_pi
`：∀ (d n : ℕ), Squarefree n → (n.primeFactors.pi fun x => Finset.univ).card = (d
.finMulAntidiag n).card
· 使用定理 `Finset.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq 
ι] (s : Finset ι) (t : (i : ι) → Finset (α i)),   (s.pi t).card = ∏ i ∈ s, (t i)
.car…
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `ArithmeticFunction.cardDistinctFactors_apply`：cardDistinctFactors_apply 
{n : Nat} : ω n = n.primeFactorsList.dedup.length
· 使用定理 `List.card_toFinset`：List.card_toFinset : #l.toFinset = l.dedup.length
· 使用定理 `Nat.toFinset_factors`：∀ (n : ℕ), n.primeFactorsList.toFinset = n.primeFa
ctors
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
-/
theorem card_finMulAntidiag_of_squarefree {d n : ℕ} (hn : Squarefree n) :
    #(finMulAntidiag d n) = d ^ ω n := by
  rw [← card_finMulAntidiag_pi d n hn, Finset.card_pi, Finset.prod_const,
    ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, toFinset_factors,
    Finset.card_fin]
/-
**Nat.finMulAntidiag_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：finMulAntidiag_three {n : Nat} (a) (ha : a in finMulAntidiag 3 n) : a 0 * 
a 1 * a 2 = n
参数：a；ha : a in finMulAntidiag 3 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_finMulAntidiag`：mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat
} : f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0
· 使用定理 `Fin.prod_univ_three`：prod_univ_three (f : Fin 3 -> M) : ∏ i, f i = f 0 *
 f 1 * f 2
-/
theorem finMulAntidiag_three {n : ℕ} (a) (ha : a ∈ finMulAntidiag 3 n) : a 0 * a 1 * a 2 = n := by
  rw [← (mem_finMulAntidiag.mp ha).1, Fin.prod_univ_three a]

namespace card_pair_lcm_eq

/-!
The following private declarations are ingredients for the proof of `card_pair_lcm_eq`.
-/

@[reducible]
/-
**Nat.card_pair_lcm_eq.f** 是 Mathlib 中的一个定义，位于命名空间 `Nat.card_pair_lcm_eq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The following private declarations are ingredients for the proof of `card_pair_l
cm_eq`.
-/
private def f {n : ℕ} : ∀ a ∈ finMulAntidiag 3 n, ℕ × ℕ := fun a _ => (a 0 * a 1, a 0 * a 2)
/-
**Nat.card_pair_lcm_eq.f_img** 是 Mathlib 中的一个定理，位于命名空间 `Nat.card_pair_lcm_eq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem f_img {n : ℕ} (hn : Squarefree n) (a : Fin 3 → ℕ)
    (ha : a ∈ finMulAntidiag 3 n) :
    f a ha ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) := by
  rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ← finMulAntidiag_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left, Nat.Coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [← finMulAntidiag_three a ha]; ring
/-
**Nat.card_pair_lcm_eq.f_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.card_pair_lcm_eq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem f_inj {n : ℕ} (a : Fin 3 → ℕ) (ha : a ∈ finMulAntidiag 3 n)
    (b : Fin 3 → ℕ) (hb : b ∈ finMulAntidiag 3 n) (hfab : f a ha = f b hb) :
    a = b := by
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2 := by
    rw [finMulAntidiag_three a ha, hfab1, finMulAntidiag_three b hb]
  have hab2 : a 2 = b 2 := by
    rw [← mul_right_inj' <| mul_ne_zero (ne_zero_of_mem_finMulAntidiag ha 0)
      (ne_zero_of_mem_finMulAntidiag ha 1)]
    exact hprods
  have hab0 : a 0 = b 0 := by
    rw [hab2] at hfab2
    exact (mul_left_inj' <| ne_zero_of_mem_finMulAntidiag hb 2).mp hfab2;
  have hab1 : a 1 = b 1 := by
    rw [hab0] at hfab1
    exact (mul_right_inj' <| ne_zero_of_mem_finMulAntidiag hb 0).mp hfab1;
  funext i; fin_cases i <;> assumption
/-
**Nat.card_pair_lcm_eq.f_surj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.card_pair_lcm_eq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem f_surj {n : ℕ} (hn : n ≠ 0) (b : ℕ × ℕ)
    (hb : b ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors)) :
    ∃ (a : Fin 3 → ℕ) (ha : a ∈ finMulAntidiag 3 n), f a ha = b := by
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst / g, b.snd / g]
  have ha : a ∈ finMulAntidiag 3 n := by
    rw [mem_finMulAntidiag]
    rw [mem_filter, Finset.mem_product] at hb
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      dsimp only [a, Matrix.cons_val]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _), ← hb.2, lcm,
        Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
  use a; use ha
  apply Prod.ext <;> dsimp only [a, Matrix.cons_val]
    <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left
  · apply Nat.gcd_dvd_right

end card_pair_lcm_eq

open card_pair_lcm_eq in
open scoped ArithmeticFunction.omega in -- access notation `ω`
/-
**Nat.card_pair_lcm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_pair_lcm_eq {n : Nat} (hn : Squarefree n) : #{p in (n.divisors ×ˢ n.d
ivisors) | p.1.lcm p.2 = n} = 3 ^ ω n
参数：hn : Squarefree n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_finMulAntidiag_of_squarefree`：card_finMulAntidiag_of_squarefree
 {d n : Nat} (hn : Squarefree n) : #(finMulAntidiag d n) = d ^ ω n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `_private.Mathlib.Algebra.Order.Antidiag.Nat.0.Nat.card_pair_lcm_eq.f_img
`：∀ {n : ℕ},   Squarefree n →     ∀ (a : Fin 3 → ℕ) (ha : a ∈ Nat.finMulAntidiag
 3 n),       Nat.card_pair_lcm_eq.f✝ a ha ∈         {x ∈ n.div…
· 使用定理 `_private.Mathlib.Algebra.Order.Antidiag.Nat.0.Nat.card_pair_lcm_eq.f_inj
`：∀ {n : ℕ} (a : Fin 3 → ℕ) (ha : a ∈ Nat.finMulAntidiag 3 n) (b : Fin 3 → ℕ) (h
b : b ∈ Nat.finMulAntidiag 3 n),   Nat.card_pair_lcm_eq.f✝ a h…
· 使用定理 `_private.Mathlib.Algebra.Order.Antidiag.Nat.0.Nat.card_pair_lcm_eq.f_sur
j`：∀ {n : ℕ},   n ≠ 0 →     ∀       b ∈         {x ∈ n.divisors ×ˢ n.divisors | 
          match x with           | (x, y) => x.lcm y = n},     …
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
-/
theorem card_pair_lcm_eq {n : ℕ} (hn : Squarefree n) :
    #{p ∈ (n.divisors ×ˢ n.divisors) | p.1.lcm p.2 = n} = 3 ^ ω n := by
  rw [← card_finMulAntidiag_of_squarefree hn, eq_comm]
  apply Finset.card_bij f (f_img hn) f_inj (f_surj hn.ne_zero)

end Nat

