/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.LTSeries

/-!

# Krull Dimension of quotient regular sequence

## Main results

- `Module.supportDim_add_length_eq_supportDim_of_isRegular`: If `M` is a finite module over a
  Noetherian local ring `R`, `r₁, …, rₙ` is an `M`-sequence, then
  `dim M/(r₁, …, rₙ)M + n = dim M`.
-/

public section

namespace Module

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

open RingTheory Sequence IsLocalRing Ideal PrimeSpectrum Pointwise

set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherianRing R] [Module.Finite R M] in
/-
**Module.exists_ltSeries_support_isMaximal_last_of_ltSeries_support** 是 Mathlib 
中的一个引理，位于命名空间 `Module`。
形式化陈述：exists_ltSeries_support_isMaximal_last_of_ltSeries_support (q : LTSeries (
support R M)) : exists p : LTSeries (support R M), q.length <= p.length ∧ p.last
.1.1.IsMaximal
参数：q : LTSeries (support R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用引理 `Module.mem_support_mono`：Module.mem_support_mono {p q : PrimeSpectrum R}
 (H : p <= q) (hp : p in Module.support R M) : q in Module.support R M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.snoc_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).length = 
p.length + …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `RelSeries.last_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newL
ast
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma exists_ltSeries_support_isMaximal_last_of_ltSeries_support (q : LTSeries (support R M)) :
    ∃ p : LTSeries (support R M), q.length ≤ p.length ∧ p.last.1.1.IsMaximal := by
  obtain ⟨m, hmm, hm⟩ := exists_le_maximal _ q.last.1.2.1
  obtain hlt | rfl := lt_or_eq_of_le hm
  · use q.snoc ⟨⟨m, inferInstance⟩, mem_support_mono hm q.last.2⟩ hlt
    simpa
  · use q
/-
**Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson** 是 Mathlib 中
的一个定理，位于命名空间 `Module`。
形式化陈述：supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson {x : R} (h : x i
n (annihilator R M).jacobson) : supportDim R M <= supportDim R (QuotSMulTop x M)
 + 1
参数：h : x in (annihilator R M).jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.supportDim_eq_bot_of_subsingleton`：supportDim_eq_bot_of_subsingle
ton [Subsingleton M] : supportDim R M = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.Quotient.instSubsingletonQuotient`：∀ {R : Type u_1} {M : Type 
u_2} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p
 : Submodule R M} [Subsingleton M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last`：exist_ltSeries_mem_one
_of_mem_last (p : LTSeries (PrimeSpectrum R)) {x : R} (hx : x in p.last.asIdeal)
 : exists q : LTSeries (PrimeSpectrum …
· 使用引理 `Module.supportDim_ne_bot_iff_nontrivial`：supportDim_ne_bot_iff_nontrivia
l : supportDim R M != ⊥ ↔ Nontrivial M
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator`：top_ne_poin
twise_smul_of_mem_jacobson_annihilator [Nontrivial M] [Module.Finite R M] {r} (h
 : r in (Module.annihilator R M).jacobson) : (⊤ :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Module.support_quotSMulTop`：Module.support_quotSMulTop (x : R) : support
 R (QuotSMulTop x M) = support R M inter zeroLocus {x}
· 使用引理 `Module.mem_support_mono`：Module.mem_support_mono {p q : PrimeSpectrum R}
 (H : p <= q) (hp : p in Module.support R M) : q in Module.support R M
（共 65 条，此处仅展示前 30 条）
-/
theorem supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson {x : R}
    (h : x ∈ (annihilator R M).jacobson) : supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 := by
  nontriviality M
  refine iSup_le_iff.mpr (fun p ↦ ?_)
  wlog hxp : x ∈ p.last.1.1 generalizing p
  · obtain ⟨p, hle, hm⟩ := exists_ltSeries_support_isMaximal_last_of_ltSeries_support p
    have hj : (annihilator R M).jacobson ≤ p.last.1.1 :=
      sInf_le ⟨mem_support_iff_of_finite.mp p.last.2, inferInstance⟩
    exact (Nat.cast_le.mpr hle).trans <| this _ (hj h)
  -- `q` is a chain of primes such that `x ∈ q 1`, `p.length = q.length` and `p.head = q.head`.
  obtain ⟨q, hxq, hq, h0, _⟩ : ∃ q : LTSeries (PrimeSpectrum R), _ ∧ _ ∧ p.head = q.head ∧ _ :=
    exist_ltSeries_mem_one_of_mem_last (p.map Subtype.val (fun ⦃_ _⦄ lt ↦ lt)) hxp
  by_cases hp0 : p.length = 0
  · have hb : supportDim R (QuotSMulTop x M) ≠ ⊥ :=
      (supportDim_ne_bot_iff_nontrivial R (QuotSMulTop x M)).mpr <|
        Submodule.Quotient.nontrivial_iff.mpr <|
          (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator h).symm
    rw [hp0, ← WithBot.coe_unbot (supportDim R (QuotSMulTop x M)) hb]
    exact WithBot.coe_le_coe.mpr zero_le
  -- Let `q' i := q (i + 1)`, then `q'` is a chain of prime ideals in `Supp(M/xM)`.
  let q' : LTSeries (support R (QuotSMulTop x M)) := {
    length := p.length - 1
    toFun := by
      intro ⟨i, hi⟩
      have hi : i + 1 < q.length + 1 :=
        Nat.succ_lt_succ (hi.trans_eq ((Nat.sub_add_cancel (Nat.pos_of_ne_zero hp0)).trans hq))
      exact ⟨q ⟨i + 1, hi⟩, by simpa using!
        ⟨mem_support_mono (by simpa [h0] using! q.monotone (Fin.zero_le _)) p.head.2, q.monotone
          ((Fin.natCast_eq_mk (Nat.lt_of_add_left_lt hi)).trans_le (Nat.le_add_left 1 i)) hxq⟩⟩
    step := by exact fun _ ↦ q.strictMono (by simp)
  }
  grw [le_tsub_add (b := p.length) (a := 1), Nat.cast_add_one, supportDim, Order.krullDim,
    ← le_iSup _ q']

set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherianRing R] in
/-- If `M` is a finite module over a commutative ring `R`, `x ∈ M` is not in any minimal prime of
  `M`, then `dim M/xM + 1 ≤ dim M`. -/
/-
**Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes** 是 Mathlib 中的一个
定理，位于命名空间 `Module`。
形式化陈述：supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes {x : R} (hn : foral
l p in (annihilator R M).minimalPrimes, x ∉ p) : supportDim R (QuotSMulTop x M) 
+ 1 <= supportDim R M
参数：hn : forall p in (annihilator R M).minimalPrimes, x ∉ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Module.supportDim_eq_bot_of_subsingleton`：supportDim_eq_bot_of_subsingle
ton [Subsingleton M] : supportDim R M = ⊥
· 使用定理 `Submodule.Quotient.instSubsingletonQuotient`：∀ {R : Type u_1} {M : Type 
u_2} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p
 : Submodule R M} [Subsingleton M…
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用引理 `Module.nonempty_support_of_nontrivial`：Module.nonempty_support_of_nontri
vial [Nontrivial M] : (Module.support R M).Nonempty
· 使用引理 `Order.krullDim_eq_iSup_length`：krullDim_eq_iSup_length [Nonempty α] : kr
ullDim α = ⨆ (p : LTSeries α), (p.length : Nat∞)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用引理 `ENat.iSup_add`：iSup_add [Nonempty ι] (f : ι -> Nat∞) : (⨆ i, f i) + a = 
⨆ i, f i + a
· 使用定理 `RelSeries.instNonempty`：∀ {α : Type u_1} (r : SetRel α α) [Nonempty α], 
Nonempty (RelSeries r)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Module.support_quotSMulTop`：Module.support_quotSMulTop (x : R) : support
 R (QuotSMulTop x M) = support R M inter zeroLocus {x}
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.mem_support_iff_of_finite`：Module.mem_support_iff_of_finite : p i
n Module.support R M ↔ Module.annihilator R M <= p.asIdeal
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `RelSeries.cons_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newHead : α) (rel : (newHead, p.head) ∈ r),   (p.cons newHead rel).length = 
p.length + …
· 使用定理 `LTSeries.map_length`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] (p : LTSeries α) (f : α → β)   (hf : StrictMono f), (p.ma
p f hf).l…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `M` is a finite module over a commutative ring `R`, `x ∈ M` is not in any min
imal prime of
  `M`, then `dim M/xM + 1 ≤ dim M`.
-/
theorem supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) :
    supportDim R (QuotSMulTop x M) + 1 ≤ supportDim R M := by
  nontriviality M
  nontriviality (QuotSMulTop x M)
  have : Nonempty (Module.support R M) := nonempty_support_of_nontrivial.to_subtype
  have : Nonempty (Module.support R (QuotSMulTop x M)) := nonempty_support_of_nontrivial.to_subtype
  simp only [supportDim, Order.krullDim_eq_iSup_length]
  apply WithBot.coe_le_coe.mpr
  simp only [ENat.iSup_add, iSup_le_iff]
  intro p
  have hp := p.head.2
  simp only [support_quotSMulTop, Set.mem_inter_iff, mem_zeroLocus, Set.singleton_subset_iff] at hp
  have le : support R (QuotSMulTop x M) ⊆ support R M := by simp
  -- Since `Supp(M/xM) ⊆ Supp M`, `p` can be viewed as a chain of prime ideals in `Supp M`,
  -- which we denote by `q`.
  let q : LTSeries (support R M) :=
    p.map (Set.MapsTo.restrict id (support R (QuotSMulTop x M)) (support R M) le) (fun _ _ h ↦ h)
  obtain ⟨r, hrm, hr⟩ := exists_minimalPrimes_le (mem_support_iff_of_finite.mp q.head.2)
  let r : support R M := ⟨⟨r, hrm.isPrime⟩, mem_support_iff_of_finite.mpr hrm.1.2⟩
  have hr : r < q.head := lt_of_le_of_ne hr (fun h ↦ hn q.head.1.1 (by rwa [← h]) hp.2)
  exact le_of_eq_of_le (by simp [q]) (le_iSup _ (q.cons r hr))
/-
**Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson*
* 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson {x 
: R} (hn : forall p in (annihilator R M).minimalPrimes, x ∉ p) (hx : x in (annih
ilator R M).jacobson) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M
参数：hn : forall p in (annihilator R M).minimalPrimes, x ∉ p；hx : x in (annihilato
r R M).jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`：supportDi
m_quotSMulTop_succ_le_of_notMem_minimalPrimes {x : R} (hn : forall p in (annihil
ator R M).minimalPrimes, x ∉ p) : supportDim R (Quo…
· 使用定理 `Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson`：suppor
tDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson {x : R} (h : x in (annihilat
or R M).jacobson) : supportDim R M <= supportDim R (Qu…
-/
theorem supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) (hx : x ∈ (annihilator R M).jacobson) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  le_antisymm (supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes hn)
    (supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson hx)
/-
**Module.supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson** 是 Mathlib 中的一个
定理，位于命名空间 `Module`。
形式化陈述：supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson {x : R} (reg : IsSM
ulRegular M x) (hx : x in (annihilator R M).jacobson) : supportDim R (QuotSMulTo
p x M) + 1 = supportDim R M
参数：reg : IsSMulRegular M x；hx : x in (annihilator R M).jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jac
obson`：supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson {x
 : R} (hn : forall p in (annihilator R M).minimalPrimes, x ∉ p) (hx…
· 使用定理 `IsSMulRegular.notMem_of_mem_minimalPrimes`：IsSMulRegular.notMem_of_mem_m
inimalPrimes {M : Type*} [AddCommMonoid M] [Module R M] {x : R} (reg : IsSMulReg
ular M x) {p : Ideal R} (hp : p…
-/
theorem supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ (annihilator R M).jacobson) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
    (fun _ ↦ reg.notMem_of_mem_minimalPrimes) hx
/-
**Module._root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson** 
是 Mathlib 中的一个引理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
  exact supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson reg
    ((annihilator R R).ringJacobson_le_jacobson hx)
/-
**Module._root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem
_jacobson** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h : span {x} = x • (⊤ : Ideal R) := by simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
    ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson reg hx]

/-- If `r` is a nonzerodivisor contained in an ideal of maximal height,
`dim (R / (r)) + 1 = dim R`. -/
/-
**Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors** 是 Mathlib 中的一个引理
，位于命名空间 `Module`。
形式化陈述：ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors {r : R} (hr : r in no
nZeroDivisors R) {p : Ideal R} [p.IsPrime] (h : p.height = ringKrullDim R) (hp :
 r in p) : ringKrullDim (R ⧸ span {r}) + 1 = ringKrullDim R
参数：hr : r in nonZeroDivisors R；h : p.height = ringKrullDim R；hp : r in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`：ringKrullDim_quotient_s
ucc_le_of_nonZeroDivisor {r : R} (hr : r in R⁰) : ringKrullDim (R ⧸ Ideal.span {
r}) + 1 <= ringKrullDim R
· 使用引理 `Ideal.height_le_ringKrullDim_quotient_add_one`：Ideal.height_le_ringKrull
Dim_quotient_add_one {r : R} {p : Ideal R} [p.IsPrime] (hrp : r in p) : p.height
 <= ringKrullDim (R ⧸ span {r}) + 1

--- 原说明 ---
If `r` is a nonzerodivisor contained in an ideal of maximal height,
`dim (R / (r)) + 1 = dim R`.
-/
lemma ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors R)
    {p : Ideal R} [p.IsPrime] (h : p.height = ringKrullDim R) (hp : r ∈ p) :
    ringKrullDim (R ⧸ span {r}) + 1 = ringKrullDim R := by
  refine le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr) (h ▸ ?_)
  exact Ideal.height_le_ringKrullDim_quotient_add_one hp

variable [IsLocalRing R]

/-- If `M` is a finite module over a Noetherian local ring `R`, then `dim M ≤ dim M/xM + 1`
  for every `x` in the maximal ideal of the local ring `R`. -/
@[stacks 0B52 "the second inequality"]
/-
**Module.supportDim_le_supportDim_quotSMulTop_succ** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dule`。
形式化陈述：supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x in maximalIdeal 
R) : supportDim R M <= supportDim R (QuotSMulTop x M) + 1
参数：hx : x in maximalIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson`：suppor
tDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson {x : R} (h : x in (annihilat
or R M).jacobson) : supportDim R M <= supportDim R (Qu…
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson

--- 原说明 ---
If `M` is a finite module over a Noetherian local ring `R`, then `dim M ≤ dim M/
xM + 1`
  for every `x` in the maximal ideal of the local ring `R`.
-/
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 :=
  supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson ((maximalIdeal_le_jacobson _) hx)
/-
**Module._root_.ringKrullDim_le_ringKrullDim_quotSMulTop_succ** 是 Mathlib 中的一个引理
，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_le_ringKrullDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ x • (⊤ : Ideal R)) + 1 := by
  rw [← Module.supportDim_self_eq_ringKrullDim, ← Module.supportDim_quotient_eq_ringKrullDim]
  exact supportDim_le_supportDim_quotSMulTop_succ hx

@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_card (since := "2026-01-12")]
/-
**Module._root_.ringKrullDim_le_ringKrullDim_add_card** 是 Mathlib 中的一个引理，位于命名空间 
`Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_le_ringKrullDim_add_card {S : Finset R}
    (hS : (S : Set R) ⊆ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span (SetLike.coe S)) + S.card := by
  apply ringKrullDim_le_ringKrullDim_quotient_add_card
  rwa [IsLocalRing.ringJacobson_eq_maximalIdeal]

@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (since := "2026-01-12")]
/-
**Module._root_.ringKrullDim_le_ringKrullDim_add_spanFinrank** 是 Mathlib 中的一个引理，
位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_le_ringKrullDim_add_spanFinrank {I : Ideal R} (h : I ≠ ⊤) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ I) + I.spanFinrank := by
  apply ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
  exact le_maximalIdeal h

@[stacks 0B52 "the equality case"]
/-
**Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalId
eal** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
 {x : R} (hn : forall p in (annihilator R M).minimalPrimes, x ∉ p) (hx : x in ma
ximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M
参数：hn : forall p in (annihilator R M).minimalPrimes, x ∉ p；hx : x in maximalIdea
l R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jac
obson`：supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson {x
 : R} (hn : forall p in (annihilator R M).minimalPrimes, x ∉ p) (hx…
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
-/
theorem supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) (hx : x ∈ maximalIdeal R) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson hn <|
    (maximalIdeal_le_jacobson _) hx
/-
**Module.supportDim_quotSMulTop_succ_eq_supportDim** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dule`。
形式化陈述：supportDim_quotSMulTop_succ_eq_supportDim {x : R} (reg : IsSMulRegular M x
) (hx : x in maximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R
 M
参数：reg : IsSMulRegular M x；hx : x in maximalIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson`：supportDi
m_quotSMulTop_succ_eq_supportDim_mem_jacobson {x : R} (reg : IsSMulRegular M x) 
(hx : x in (annihilator R M).jacobson) : supportDim…
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
-/
theorem supportDim_quotSMulTop_succ_eq_supportDim {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson reg ((maximalIdeal_le_jacobson _) hx)
/-
**Module._root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim** 是 Mathlib 中的一个引理
，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim {x : R} (reg : IsSMulRegular R x)
    (hx : x ∈ maximalIdeal R) : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R :=
  ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson reg <| by
    simpa [ringJacobson_eq_maximalIdeal R]
/-
**Module._root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim** 是 Ma
thlib 中的一个引理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson reg <| by
    rwa [ringJacobson_eq_maximalIdeal R]

open nonZeroDivisors in
@[stacks 00KW]
/-
**Module._root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem
_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    {x : R} (reg : x ∈ R⁰) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (Module.Flat.isSMulRegular_of_nonZeroDivisors reg) hx

/-- If `M` is a finite module over a Noetherian local ring `R`, `r₁, …, rₙ` is an
  `M`-sequence, then `dim M/(r₁, …, rₙ)M + n = dim M`. -/
/-
**Module.supportDim_add_length_eq_supportDim_of_isRegular** 是 Mathlib 中的一个定理，位于命
名空间 `Module`。
形式化陈述：supportDim_add_length_eq_supportDim_of_isRegular (rs : List R) (reg : IsRe
gular M rs) : supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length = s
upportDim R M
参数：rs : List R；reg : IsRegular M rs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ofList_nil`：∀ {R : Type u_1} [inst : Semiring R], Ideal.ofList [] 
= ⊥
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Module.supportDim_eq_of_equiv`：supportDim_eq_of_equiv (e : M ≃ₗ[R] N) : 
supportDim R M = supportDim R N
· 使用定理 `RingTheory.Sequence.IsRegular.top_ne_smul`：∀ {R : Type u_1} {M : Type u_
3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
{rs : List R}, RingTheory.Seque…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.ofList_cons`：∀ {R : Type u_1} [inst : Semiring R] (r : R) (rs : Li
st R), Ideal.ofList (r :: rs) = Ideal.span {r} ⊔ Ideal.ofList rs
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_eq_top`：span_singleton_eq_top {x} : span ({x} : Set
 α) = ⊤ ↔ IsUnit x
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.supportDim_quotSMulTop_succ_eq_supportDim`：supportDim_quotSMulTop
_succ_eq_supportDim {x : R} (reg : IsSMulRegular M x) (hx : x in maximalIdeal R)
 : supportDim R (QuotSMulTop x M) + 1 …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingTheory.Sequence.isRegular_cons_iff`：isRegular_cons_iff (r : R) (rs :
 List R) : IsRegular M (r :: rs) ↔ IsSMulRegular M r ∧ IsRegular (QuotSMulTop r 
M) rs
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `M` is a finite module over a Noetherian local ring `R`, `r₁, …, rₙ` is an
  `M`-sequence, then `dim M/(r₁, …, rₙ)M + n = dim M`.
-/
theorem supportDim_add_length_eq_supportDim_of_isRegular (rs : List R) (reg : IsRegular M rs) :
    supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  induction rs generalizing M with
  | nil =>
    rw [ofList_nil, Submodule.bot_smul]
    simpa using supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)
  | cons x rs' ih =>
    have mem : x ∈ maximalIdeal R := by
      simpa using fun isu ↦ reg.2 (by simp [span_singleton_eq_top.mpr isu])
    simp [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x _),
      ← supportDim_quotSMulTop_succ_eq_supportDim ((isRegular_cons_iff M _ _).mp reg).1 mem,
      ← ih ((isRegular_cons_iff M _ _).mp reg).2, ← add_assoc]
/-
**Module._root_.ringKrullDim_add_length_eq_ringKrullDim_of_isRegular** 是 Mathlib
 中的一个引理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ringKrullDim_add_length_eq_ringKrullDim_of_isRegular (rs : List R)
    (reg : IsRegular R rs) : ringKrullDim (R ⧸ ofList rs) + rs.length = ringKrullDim R := by
  have eq : ofList rs = ofList rs • (⊤ : Ideal R) := by simp
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R eq).toRingEquiv,
    ← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
  exact supportDim_add_length_eq_supportDim_of_isRegular rs reg

end Module

