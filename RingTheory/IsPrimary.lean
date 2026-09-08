/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary submodules

A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.

## Main results

* `Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul`:
  A `N : Submodule R M` is primary if any zero divisor on `M ⧸ N` is nilpotent.
  See https://mathoverflow.net/questions/3910/primary-decomposition-for-modules
  for a comparison of this definition (a la Atiyah-Macdonald) vs "locally nilpotent" (Matsumura).

## Implementation details

This is a generalization of `Ideal.IsPrimary`. For brevity, the pointwise instances are used
to define the nilpotency of `r : R`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
  Chapter 4, Exercise 21.

-/

@[expose] public section

open scoped Pointwise

namespace Submodule

open Ideal

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.
  This generalizes `Ideal.IsPrimary`. -/
/-
**Submodule.IsPrimary** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] → [inst_1 
: AddCommMonoid M] → [inst_2 : _root_.Module R M] → Submodule R M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.
  This generalizes `Ideal.IsPrimary`.
-/
protected def IsPrimary (S : Submodule R M) : Prop :=
  S ≠ ⊤ ∧ ∀ {r : R} {x : M}, r • x ∈ S → x ∈ S ∨ ∃ n : ℕ, (r ^ n • ⊤ : Submodule R M) ≤ S

variable {S T : Submodule R M}
/-
**Submodule.IsPrimary.ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsPrimary`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {S : Submodule R M}, S.IsPrimary → S ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsPrimary.ne_top (h : S.IsPrimary) : S ≠ ⊤ := h.left
/-
**Submodule.IsPrimary.mem_or_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsPrimary`
。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {S : Submodule R M}, S.IsPrimary → ∀ {r 
: R} {m : M}, r • m ∈ S → m ∈ S ∨ r ∈ (S.colon Set.univ).radical
参数：S.colon Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsPrimary.mem_or_mem (h : S.IsPrimary) {r : R} {m : M} (hrm : r • m ∈ S) :
    m ∈ S ∨ r ∈ (S.colon Set.univ).radical :=
  h.right hrm
/-
**Submodule.IsPrimary.inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsPrimary`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {S T : Submodule R M},   S.IsPrimary → T
.IsPrimary → (S.colon Set.univ).radical = (T.colon Set.univ).radical → (S ⊓ T).I
sPrimary
参数：S.colon Set.univ；T.colon Set.univ；S ⊓ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.inf_colon`：inf_colon : (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.col
on S
· 使用定理 `Ideal.radical_inf`：radical_inf : radical (I ⊓ J) = radical I ⊓ radical J
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected lemma IsPrimary.inf (hS : S.IsPrimary) (hT : T.IsPrimary)
    (h : (S.colon Set.univ).radical = (T.colon Set.univ).radical) :
    (S ⊓ T).IsPrimary := by
  obtain ⟨_, hS⟩ := hS
  obtain ⟨_, hT⟩ := hT
  refine ⟨by grind, fun ⟨hS', hT'⟩ ↦ ?_⟩
  simp_rw [← mem_colon_iff_le, ← Ideal.mem_radical_iff, inf_colon, Ideal.radical_inf,
    top_coe, h, inf_idem, mem_inf, and_or_right] at hS hT ⊢
  exact ⟨hS hS', hT hT'⟩

open Finset in
/-
**Submodule.isPrimary_finsetInf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：isPrimary_finsetInf {ι : Type*} {s : Finset ι} {f : ι -> Submodule R M} {i
 : ι} (hi : i in s) (hs : forall ⦃y⦄, y in s -> (f y).IsPrimary) (hs' : forall ⦃
y⦄, y in s -> ((f y).colon Set.univ).radical = ((f i).colon Set.univ).radical) :
 (s.inf f).IsPrimary
参数：hi : i in s；hs : forall ⦃y⦄, y in s -> (f y).IsPrimary；hs' : forall ⦃y⦄, y in
 s -> ((f y).colon Set.univ).radical = ((f i).colon Set.univ).radical。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.inf_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eInf α] [inst_1 : OrderTop α] {f : β → α} {b : β}, {b}.inf f = f b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Submodule.IsPrimary.inf`：∀ {R : Type u_1} {M : Type u_2} [inst : CommSem
iring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S T : Submod
ule R M},   S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `Submodule.colon_finsetInf`：colon_finsetInf {ι : Type*} (s : Finset ι) (f
 : ι -> Submodule R M) : (s.inf f).colon S = s.inf (fun i => (f i).colon S)
· 使用引理 `Ideal.radical_finset_inf`：radical_finset_inf {ι} {s : Finset ι} {f : ι -
> Ideal R} {i : ι} (hi : i in s) (hs : forall ⦃y⦄, y in s -> (f y).radical = (f 
i).radical) : …
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
lemma isPrimary_finsetInf {ι : Type*} {s : Finset ι} {f : ι → Submodule R M} {i : ι} (hi : i ∈ s)
    (hs : ∀ ⦃y⦄, y ∈ s → (f y).IsPrimary)
    (hs' : ∀ ⦃y⦄, y ∈ s → ((f y).colon Set.univ).radical = ((f i).colon Set.univ).radical) :
    (s.inf f).IsPrimary := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty => simp at hi
  | insert a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [insert_empty_eq, mem_singleton] at hi
      simpa [hi] using hs
    simp only [inf_insert]
    have H ⦃x⦄ (hx : x ∈ s) : ((f x).colon Set.univ).radical = ((f y).colon Set.univ).radical := by
      rw [hs' (mem_insert_of_mem hx), hs' (mem_insert_of_mem hy)]
    refine IsPrimary.inf (hs (by simp)) (IH hy (fun x hx ↦ hs (by simp [hx])) H) ?_
    rw [colon_finsetInf, Ideal.radical_finset_inf hy H,
      hs' (mem_insert_self _ _), hs' (mem_insert_of_mem hy)]
/-
**Submodule.IsPrimary.isPrime_radical_colon** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
.IsPrimary`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {S : Submodule R M}, S.IsPrimary → (S.co
lon Set.univ).radical.IsPrime
参数：S.colon Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isPrime_iff`：isPrime_iff {I : Ideal α} : IsPrime I ↔ I != ⊤ ∧ fora
ll {x y : α}, x * y in I -> x in I ∨ y in I
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ideal.mem_radical_of_pow_mem`：mem_radical_of_pow_mem {I : Ideal R} {x : 
R} {m : Nat} (hx : x ^ m in radical I) : x in radical I
-/
theorem IsPrimary.isPrime_radical_colon (hI : S.IsPrimary) : (S.colon .univ).radical.IsPrime := by
  refine isPrime_iff.mpr <| hI.imp (by simp) fun h x y ⟨n, hn⟩ ↦ ?_
  simp_rw [← mem_colon_iff_le, ← mem_radical_iff] at h
  refine or_iff_not_imp_left.mpr fun hx ↦ ⟨n, ?_⟩
  simp only [mul_pow, mem_colon, Set.mem_univ, true_imp_iff, mul_smul] at hn ⊢
  exact fun p ↦ (h (hn p)).resolve_right (mt mem_radical_of_pow_mem hx)
/-
**Submodule.IsPrimary.radical_colon_singleton_of_notMem** 是 Mathlib 中的一个定理，位于命名空
间 `Submodule.IsPrimary`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {S : Submodule R M}, S.IsPrimary → ∀ {m 
: M}, m ∉ S → (S.colon {m}).radical = (S.colon Set.univ).radical
参数：S.colon {m}；S.colon Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.radical_le_radical_iff`：radical_le_radical_iff : radical I <= radi
cal J ↔ I <= radical J
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_colon_singleton`：mem_colon_singleton {x : M} {r : R} : r i
n N.colon {x} ↔ r • x in N
· 使用定理 `Ideal.radical_mono`：radical_mono (H : I <= J) : radical I <= radical J
· 使用定理 `Submodule.colon_mono`：colon_mono (hn : N₁ <= N₂) (hs : S₁ subseteq S₂) :
 N₁.colon S₂ <= N₂.colon S₁
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem IsPrimary.radical_colon_singleton_of_notMem (hI : S.IsPrimary) {m : M} (hm : m ∉ S) :
    (S.colon {m}).radical = (S.colon Set.univ).radical :=
  le_antisymm (radical_le_radical_iff.mpr fun _ hy ↦
    (hI.2 (Submodule.mem_colon_singleton.mp hy)).resolve_left hm)
    (radical_mono (Submodule.colon_mono le_rfl (Set.subset_univ {m})))
/-
**Submodule.IsPrimary.radical_colon_singleton_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule.IsPrimary`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {S : Submodule R M},   S.IsPrimary →    
 ∀ (m : M) [inst_3 : Decidable (m ∈ S)], (S.colon {m}).radical = if m ∈ S then ⊤
 else (S.colon Set.univ).radical
参数：m : M；m ∈ S；S.colon {m}；S.colon Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ideal.radical_eq_top`：radical_eq_top : radical I = ⊤ ↔ I = ⊤
· 使用引理 `Submodule.colon_eq_top_iff_subset`：colon_eq_top_iff_subset (S : Set M) :
 N.colon S = ⊤ ↔ S subseteq N
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Submodule.IsPrimary.radical_colon_singleton_of_notMem`：∀ {R : Type u_1} 
{M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _roo
t_.Module R M]   {S : Submodule R M}, S.IsP…
-/
theorem IsPrimary.radical_colon_singleton_eq_ite (hS : S.IsPrimary) (m : M) [Decidable (m ∈ S)] :
    radical (S.colon {m}) = if m ∈ S then ⊤ else radical (S.colon Set.univ) := by
  split_ifs with hm
  · rwa [radical_eq_top, colon_eq_top_iff_subset, Set.singleton_subset_iff]
  · exact hS.radical_colon_singleton_of_notMem hm

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M}

set_option backward.isDefEq.respectTransparency false in
/-
**Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul** 是 Mathlib 中
的一个引理，位于命名空间 `Submodule`。
形式化陈述：isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul : S.IsPrimary ↔ S !
= ⊤ ∧ forall (r : R) (x : M ⧸ S), x != 0 -> r • x = 0 -> exists n : Nat, r ^ n •
 (⊤ : Submodule R (M ⧸ S)) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul :
    S.IsPrimary ↔ S ≠ ⊤ ∧ ∀ (r : R) (x : M ⧸ S), x ≠ 0 → r • x = 0 →
      ∃ n : ℕ, r ^ n • (⊤ : Submodule R (M ⧸ S)) = ⊥ := by
  refine (and_congr_right fun _ ↦ ?_)
  simp_rw [S.mkQ_surjective.forall, ← map_smul, ne_eq, ← LinearMap.mem_ker, ker_mkQ]
  congr! 2
  rw [forall_comm, ← or_iff_not_imp_left,
    ← LinearMap.range_eq_top.mpr S.mkQ_surjective, ← map_top]
  simp_rw [eq_bot_iff, ← map_pointwise_smul, map_le_iff_le_comap, comap_bot, ker_mkQ]

end CommRing

end Submodule

