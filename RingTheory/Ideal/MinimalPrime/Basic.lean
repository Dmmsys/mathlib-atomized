/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Order.Minimal

/-!

# Minimal primes

We provide various results concerning the minimal primes above an ideal.

## Main results
- `Ideal.minimalPrimes`: `I.minimalPrimes` is the set of ideals that are minimal primes over `I`.
- `minimalPrimes`: `minimalPrimes R` is the set of minimal primes of `R`.
- `Ideal.exists_minimalPrimes_le`: Every prime ideal over `I` contains a minimal prime over `I`.
- `Ideal.radical_minimalPrimes`: The minimal primes over `I.radical` are precisely
  the minimal primes over `I`.
- `Ideal.sInf_minimalPrimes`: The intersection of minimal primes over `I` is `I.radical`.

Further results that need the theory of localizations can be found in
`Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean`.

-/

@[expose] public section

assert_not_exists Localization -- See `Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean`

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (I J : Ideal R)

/-- `IsMinimalPrime I p` says that `p` is a minimal prime over `I`. -/
/-
**Ideal.IsMinimalPrime** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：{R : Type u_1} → [inst : CommSemiring R] → Ideal R → Ideal R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsMinimalPrime I p` says that `p` is a minimal prime over `I`.
-/
protected def Ideal.IsMinimalPrime (p : Ideal R) : Prop := Minimal (fun q ↦ q.IsPrime ∧ I ≤ q) p

variable {I} in
/-
**Ideal.IsMinimalPrime.isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.IsMinimalPrime.isPrime {p : Ideal R} (h : I.IsMinimalPrime p) : p.Is
Prime
参数：h : I.IsMinimalPrime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Ideal.IsMinimalPrime.isPrime {p : Ideal R} (h : I.IsMinimalPrime p) : p.IsPrime := h.1.1

variable {I} in
/-
**Ideal.IsMinimalPrime.le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.IsMinimalPrime p) : I <= p
参数：h : I.IsMinimalPrime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.IsMinimalPrime p) : I ≤ p := h.1.2

/-- `IsMinimalPrime p` says that `p` is a minimal prime of the ring. -/
/-
**IsMinimalPrime** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsMinimalPrime (p : Ideal R) : Prop
参数：p : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsMinimalPrime p` says that `p` is a minimal prime of the ring.
-/
abbrev IsMinimalPrime (p : Ideal R) : Prop := (⊥ : Ideal R).IsMinimalPrime p
/-
**IsMinimalPrime.isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMinimalPrime.isPrime {p : Ideal R} (h : IsMinimalPrime p) : p.IsPrime
参数：h : IsMinimalPrime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsMinimalPrime.isPrime {p : Ideal R} (h : IsMinimalPrime p) : p.IsPrime := h.1.1
/-
**IsMinimalPrime.iff_minimal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMinimalPrime.iff_minimal (p : Ideal R) : IsMinimalPrime p ↔ Minimal Idea
l.IsPrime p
参数：p : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsMinimalPrime.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (I p
 : Ideal R), I.IsMinimalPrime p = Minimal (fun q => q.IsPrime ∧ I ≤ q) p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsMinimalPrime.iff_minimal (p : Ideal R) : IsMinimalPrime p ↔ Minimal Ideal.IsPrime p := by
  simp [Ideal.IsMinimalPrime]

/-- `I.minimalPrimes` is the set of ideals that are minimal primes over `I`. -/
/-
**Ideal.minimalPrimes** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：{R : Type u_1} → [inst : CommSemiring R] → Ideal R → Set (Ideal R)
参数：Ideal R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I.minimalPrimes` is the set of ideals that are minimal primes over `I`.
-/
protected abbrev Ideal.minimalPrimes : Set (Ideal R) :=
  {p | I.IsMinimalPrime p}

variable (R) in
/-- `minimalPrimes R` is the set of minimal primes of `R`.
This is defined as `Ideal.minimalPrimes ⊥`. -/
/-
**minimalPrimes** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：minimalPrimes : Set (Ideal R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`minimalPrimes R` is the set of minimal primes of `R`.
This is defined as `Ideal.minimalPrimes ⊥`.
-/
abbrev minimalPrimes : Set (Ideal R) :=
  {p | IsMinimalPrime p}
/-
**minimalPrimes_eq_minimals** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minimalPrimes_eq_minimals : minimalPrimes R = {x | Minimal Ideal.IsPrime x
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma minimalPrimes_eq_minimals : minimalPrimes R = {x | Minimal Ideal.IsPrime x} :=
  congr_arg Minimal (by simp)

variable {I J}

@[deprecated "Use `Ideal.IsMinimalPrime.isPrime` instead." (since := "2026-05-08")]
/-
**Ideal.minimalPrimes_isPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_isPrime {p : Ideal R} (h : p in minimalPrimes R) : p.I
sPrime
参数：h : p in minimalPrimes R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Ideal.minimalPrimes_isPrime {p : Ideal R} (h : p ∈ minimalPrimes R) : p.IsPrime :=
  h.1.1
/-
**Ideal.exists_minimalPrimes_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.exists_minimalPrimes_le [J.IsPrime] (e : I <= J) : exists p in I.min
imalPrimes, p <= J
参数：e : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
· 使用定理 `Ideal.sInf_isPrime_of_isChain`：sInf_isPrime_of_isChain {s : Set (Ideal α
)} (hs : s.Nonempty) (hs' : IsChain (· <= ·) s) (H : forall p in s, p.IsPrime) :
 (sInf s).IsPrime
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderDual.ofDual_toDual`：∀ {α : Type u_1} (a : α), OrderDual.ofDual (Ord
erDual.toDual a) = a
· 使用定理 `le_sInf_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OrderDual.le_toDual`：le_toDual [LE α] {a : αᵒᵈ} {b : α} : a <= toDual b 
↔ b <= ofDual a
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Maximal.le_of_ge`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x y : α
}, Maximal P x → P y → x ≤ y → y ≤ x
-/
theorem Ideal.exists_minimalPrimes_le [J.IsPrime] (e : I ≤ J) : ∃ p ∈ I.minimalPrimes, p ≤ J := by
  set S := { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ OrderDual.ofDual p }
  suffices h : ∃ m, OrderDual.toDual J ≤ m ∧ Maximal (· ∈ S) m by
    obtain ⟨p, hJp, hp⟩ := h
    exact ⟨p, ⟨hp.prop, fun q hq hle ↦ hp.le_of_ge hq hle⟩, hJp⟩
  apply zorn_le_nonempty₀
  swap
  · refine ⟨show J.IsPrime by infer_instance, e⟩
  rintro (c : Set (Ideal R)) hc hc' J' hJ'
  refine
    ⟨OrderDual.toDual (sInf c),
      ⟨Ideal.sInf_isPrime_of_isChain ⟨J', hJ'⟩ hc'.symm fun x hx => (hc hx).1, ?_⟩, ?_⟩
  · rw [OrderDual.ofDual_toDual, le_sInf_iff]
    exact fun _ hx => (hc hx).2
  · rintro z hz
    rw [OrderDual.le_toDual]
    exact sInf_le hz
/-
**Ideal.nonempty_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.nonempty_minimalPrimes (h : I != ⊤) : Nonempty I.minimalPrimes
参数：h : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
-/
theorem Ideal.nonempty_minimalPrimes (h : I ≠ ⊤) : Nonempty I.minimalPrimes := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I h
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨p, hp⟩
/-
**Ideal.eq_bot_of_minimalPrimes_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.eq_bot_of_minimalPrimes_eq_empty (h : I.minimalPrimes = ∅) : I = ⊤
参数：h : I.minimalPrimes = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.nonempty_minimalPrimes`：Ideal.nonempty_minimalPrimes (h : I != ⊤) 
: Nonempty I.minimalPrimes
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem Ideal.eq_bot_of_minimalPrimes_eq_empty (h : I.minimalPrimes = ∅) : I = ⊤ := by
  by_contra hI
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  exact Set.notMem_empty p (h ▸ hp)

@[simp]
/-
**Ideal.radical_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.radical_minimalPrimes : I.radical.minimalPrimes = I.minimalPrimes
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.minimalPrimes.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (I : 
Ideal R), I.minimalPrimes = {p | I.IsMinimalPrime p}
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {I 
J : Ideal R}, J.IsPrime → (I.radical ≤ J ↔ I ≤ J)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Ideal.radical_minimalPrimes : I.radical.minimalPrimes = I.minimalPrimes := by
  rw [Ideal.minimalPrimes, Ideal.minimalPrimes]
  ext p
  refine ⟨?_, ?_⟩ <;> rintro ⟨⟨a, ha⟩, b⟩
  · refine ⟨⟨a, a.radical_le_iff.1 ha⟩, ?_⟩
    simp only [and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.2 h3) h4
  · refine ⟨⟨a, a.radical_le_iff.2 ha⟩, ?_⟩
    simp only [and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.1 h3) h4

@[simp]
/-
**Ideal.sInf_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.sInf_minimalPrimes : sInf I.minimalPrimes = I.radical
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Ideal.sInf_minimalPrimes : sInf I.minimalPrimes = I.radical := by
  rw [I.radical_eq_sInf]
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_sInf] at hx ⊢
    rintro J ⟨e, hJ⟩
    obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le e
    exact hp' (hx hp)
  · apply sInf_le_sInf _
    intro I hI
    exact hI.1.symm

end

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {I J : Ideal R}

/-
**Ideal.minimalPrimes_eq_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_eq_subsingleton (hI : I.IsPrimary) : I.minimalPrimes =
 {I.radical}
参数：hI : I.IsPrimary。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsPrime.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {I 
J : Ideal R}, J.IsPrime → (I.radical ≤ J ↔ I ≤ J)
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.isPrime_radical`：isPrime_radical {I : Ideal R} (hi : I.IsPrimary) 
: IsPrime (radical I)
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Ideal.minimalPrimes_eq_subsingleton (hI : I.IsPrimary) : I.minimalPrimes = {I.radical} := by
  ext J
  constructor
  · intro H
    have le := H.out.isPrime.radical_le_iff.mpr H.le
    exact (H.2 ⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩ le).antisymm le
  · rintro (rfl : J = I.radical)
    exact ⟨⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩
/-
**Ideal.minimalPrimes_eq_subsingleton_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_eq_subsingleton_self [I.IsPrime] : I.minimalPrimes = {
I}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
-/
theorem Ideal.minimalPrimes_eq_subsingleton_self [I.IsPrime] : I.minimalPrimes = {I} := by
  ext J
  refine ⟨fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.le).antisymm H.le, ?_⟩
  rintro (rfl : J = I)
  exact ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩

variable (R) in
/-
**IsDomain.minimalPrimes_eq_singleton_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDomain.minimalPrimes_eq_singleton_bot [IsDomain R] : minimalPrimes R = {
⊥}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.minimalPrimes_eq_subsingleton_self`：Ideal.minimalPrimes_eq_subsing
leton_self [I.IsPrime] : I.minimalPrimes = {I}
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem IsDomain.minimalPrimes_eq_singleton_bot [IsDomain R] :
    minimalPrimes R = {⊥} :=
  Ideal.minimalPrimes_eq_subsingleton_self

end

section

variable {R : Type*} [CommSemiring R]

/-
**Ideal.minimalPrimes_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
-/
theorem Ideal.minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext p
  simp only [Set.notMem_empty, iff_false]
  intro h
  exact h.isPrime.ne_top (top_le_iff.mp h.le)
/-
**Ideal.minimalPrimes_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_eq_empty_iff (I : Ideal R) : I.minimalPrimes = ∅ ↔ I =
 ⊤
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.minimalPrimes_top`：Ideal.minimalPrimes_top : (⊤ : Ideal R).minimal
Primes = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Ideal.minimalPrimes_eq_empty_iff (I : Ideal R) :
    I.minimalPrimes = ∅ ↔ I = ⊤ := by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    rw [e] at hp
    apply Set.notMem_empty _ hp.1
  · rintro rfl
    exact Ideal.minimalPrimes_top
/-
**Ideal.mem_minimalPrimes_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.mem_minimalPrimes_sup {R : Type*} [CommRing R] {p I J : Ideal R} [p.
IsPrime] (hle : I <= p) (h : p.map (Ideal.Quotient.mk I) in (J.map (Ideal.Quotie
nt.mk I)).minimalPrimes) : p in (I ⊔ J).minimalPrimes
参数：hle : I <= p；h : p.map (Ideal.Quotient.mk I) in (J.map (Ideal.Quotient.mk I))
.minimalPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Ideal.comap_map_quotientMk`：comap_map_quotientMk (I J : Ideal R) [I.IsTw
oSided] : (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Ideal.isPrime_map_quotientMk_of_isPrime`：isPrime_map_quotientMk_of_isPri
me {I : Ideal R} [I.IsTwoSided] {p : Ideal R} [p.IsPrime] (hIP : I <= p) : (p.ma
p (Ideal.Quotient.mk I)).IsPr…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
-/
lemma Ideal.mem_minimalPrimes_sup {R : Type*} [CommRing R] {p I J : Ideal R} [p.IsPrime]
    (hle : I ≤ p) (h : p.map (Ideal.Quotient.mk I) ∈ (J.map (Ideal.Quotient.mk I)).minimalPrimes) :
    p ∈ (I ⊔ J).minimalPrimes := by
  refine ⟨⟨‹_›, ?_⟩, fun q ⟨_, hq⟩ hqp ↦ ?_⟩
  · rw [sup_le_iff]
    refine ⟨hle, by simpa [hle] using Ideal.comap_mono (f := Ideal.Quotient.mk I) h.le⟩
  · rw [sup_le_iff] at hq
    have h2 : p.map (Quotient.mk I) ≤ q.map (Quotient.mk I) :=
      h.2 ⟨isPrime_map_quotientMk_of_isPrime hq.1, map_mono hq.2⟩ (map_mono hqp)
    simpa [comap_map_quotientMk, hq.1, sup_le_iff] using comap_mono (f := Ideal.Quotient.mk I) h2

variable {S : Type*} [CommRing S] [Algebra R S]

/-- If `P` lies over `p`, `p` is a minimal prime over `I` and the image of `P` is
a minimal prime over the image of `J` in `S ⧸ p S`, then `P` is a minimal prime
over `I S ⊔ J`. -/
/-
**Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes** 是 Mathli
b 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes {I p :
 Ideal R} {P : Ideal S} [P.IsPrime] [P.LiesOver p] (hI : p in I.minimalPrimes) {
J : Ideal S} (hJP : J <= P) (hJ : P.map (Ideal.Quotient.mk _) in (J.map (Ideal.Q
uotient.mk (p.map (algebraMap R S)))).minimalPrimes) : P in (I.map (algebraMap R
 S) ⊔ J).minimalPrimes
参数：hI : p in I.minimalPrimes；hJP : J <= P；hJ : P.map (Ideal.Quotient.mk _) in (J
.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).minimalPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用引理 `Ideal.isPrime_map_quotientMk_of_isPrime`：isPrime_map_quotientMk_of_isPri
me {I : Ideal R} [I.IsTwoSided] {p : Ideal R} [p.IsPrime] (hIP : I <= p) : (p.ma
p (Ideal.Quotient.mk I)).IsPr…
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Ideal.comap_map_quotientMk`：comap_map_quotientMk (I J : Ideal R) [I.IsTw
oSided] : (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
If `P` lies over `p`, `p` is a minimal prime over `I` and the image of `P` is
a minimal prime over the image of `J` in `S ⧸ p S`, then `P` is a minimal prime
over `I S ⊔ J`.
-/
lemma Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes
    {I p : Ideal R} {P : Ideal S} [P.IsPrime] [P.LiesOver p]
    (hI : p ∈ I.minimalPrimes) {J : Ideal S} (hJP : J ≤ P)
    (hJ : P.map (Ideal.Quotient.mk _) ∈
      (J.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).minimalPrimes) :
    P ∈ (I.map (algebraMap R S) ⊔ J).minimalPrimes := by
  refine ⟨⟨inferInstance, sup_le_iff.mpr ?_⟩, fun q ⟨_, hleq⟩ hqle ↦ ?_⟩
  · refine ⟨?_, hJP⟩
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← Ideal.over_def P p]
    exact hI.le
  · simp only [sup_le_iff] at hleq
    have h1 : p.map (algebraMap R S) ≤ q := by
      rw [Ideal.map_le_iff_le_comap]
      refine hI.2 ⟨inferInstance, le_trans Ideal.le_comap_map (Ideal.comap_mono hleq.1)⟩ ?_
      convert! Ideal.comap_mono hqle
      exact Ideal.LiesOver.over
    have h2 : P.map (Ideal.Quotient.mk (p.map (algebraMap R S))) ≤
        q.map (Ideal.Quotient.mk (p.map (algebraMap R S))) :=
      hJ.2 ⟨Ideal.isPrime_map_quotientMk_of_isPrime h1, Ideal.map_mono hleq.2⟩
        (Ideal.map_mono hqle)
    simpa [h1] using Ideal.comap_mono (f := Ideal.Quotient.mk (p.map (algebraMap R S))) h2

end

