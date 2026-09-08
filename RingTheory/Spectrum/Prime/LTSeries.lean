/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Lemmas about `LTSeries` in the prime spectrum

## Main results

* `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last`: Let $R$ be a Noetherian ring,
  $\mathfrak{p}_0 < \dots < \mathfrak{p}_n$ be a chain of primes, $x \in \mathfrak{p}_n$.
  Then we can find another chain of primes $\mathfrak{q}_0 < \dots < \mathfrak{q}_n$ such that
  $x \in \mathfrak{q}_1$, $\mathfrak{p}_0 = \mathfrak{q}_0$ and $\mathfrak{p}_n = \mathfrak{q}_n$.
-/

public section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R

open Ideal IsLocalRing

namespace PrimeSpectrum

set_option backward.isDefEq.respectTransparency.types false in
/-
**PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal** 是 Mathlib 中的一个定理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：exist_mem_one_of_mem_maximal_ideal [IsLocalRing R] {p₁ p₀ : PrimeSpectrum 
R} (h₀ : p₀ < p₁) (h₁ : p₁ < closedPoint R) {x : R} (hx : x in 𝔪) : exists q : P
rimeSpectrum R, x in q.asIdeal ∧ p₀ < q ∧ q.asIdeal < 𝔪
参数：h₀ : p₀ < p₁；h₁ : p₁ < closedPoint R；hx : x in 𝔪。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ideal.nonempty_minimalPrimes`：Ideal.nonempty_minimalPrimes (h : I != ⊤) 
: Nonempty I.minimalPrimes
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `IsLocalRing.le_maximalIdeal_of_isPrime`：le_maximalIdeal_of_isPrime (p : 
Ideal R) [hp : p.IsPrime] : p <= maximalIdeal R
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ideal.map_height_le_one_of_mem_minimalPrimes`：Ideal.map_height_le_one_of
_mem_minimalPrimes {I p : Ideal R} {x : R} (hp : p in (I ⊔ span {x}).minimalPrim
es) : (p.map (Ideal.Quotient.mk I)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_one_iff_nonpos`：lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEO
neClass α] [NeZero (1 : α)] [SuccAddOrder α] : x < 1 ↔ x <= 0
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用引理 `Ideal.height_le_iff`：Ideal.height_le_iff {p : Ideal R} {n : Nat} [p.IsPr
ime] : p.height <= n ↔ forall q : Ideal R, q.IsPrime -> q < p -> q.height < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 36 条，此处仅展示前 30 条）
-/
theorem exist_mem_one_of_mem_maximal_ideal [IsLocalRing R] {p₁ p₀ : PrimeSpectrum R}
    (h₀ : p₀ < p₁) (h₁ : p₁ < closedPoint R) {x : R} (hx : x ∈ 𝔪) :
    ∃ q : PrimeSpectrum R, x ∈ q.asIdeal ∧ p₀ < q ∧ q.asIdeal < 𝔪 := by
  by_cases hn : x ∈ p₀.1
  · exact ⟨p₁, h₀.le hn, h₀, h₁⟩
  let e := p₀.1.primeSpectrumQuotientOrderIsoZeroLocus.symm
  obtain ⟨q, hq⟩ := (p₀.1 + span {x}).nonempty_minimalPrimes <|
    sup_le (IsLocalRing.le_maximalIdeal_of_isPrime p₀.1) ((span_singleton_le_iff_mem 𝔪).mpr hx)
      |>.trans_lt (IsMaximal.isPrime' 𝔪).1.lt_top |>.ne
  let q : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have : q.1.IsPrime := q.2
  have hxq : x ∈ q.1 := le_sup_right.trans hq.1.2 (mem_span_singleton_self x)
  refine ⟨q, hxq, lt_of_le_not_ge (le_sup_left.trans hq.1.2) fun h ↦ hn (h hxq), ?_⟩
  refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q.1) fun hqm ↦ ?_
  have h : (e ⟨q, le_sup_left.trans hq.1.2⟩).1.height ≤ 1 :=
    map_height_le_one_of_mem_minimalPrimes hq
  simp_rw [show q = closedPoint R from PrimeSpectrum.ext hqm] at h
  have hph : (e ⟨p₁, h₀.le⟩).1.height ≤ 0 :=
    Order.lt_one_iff_nonpos.mp (height_le_iff.mp h _ inferInstance (by simpa using h₁))
  refine not_lt_zero (a := (e ⟨p₀, le_refl p₀⟩).1.height) (height_le_iff.mp hph _ inferInstance ?_)
  simpa using h₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**PrimeSpectrum.exist_mem_one_of_mem_two** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：exist_mem_one_of_mem_two {p₁ p₀ p₂ : PrimeSpectrum R} (h₀ : p₀ < p₁) (h₁ :
 p₁ < p₂) {x : R} (hx : x in p₂.asIdeal) : exists q : (PrimeSpectrum R), x in q.
asIdeal ∧ p₀ < q ∧ q < p₂
参数：h₀ : p₀ < p₁；h₁ : p₁ < p₂；hx : x in p₂.asIdeal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal`：exist_mem_one_of_mem_m
aximal_ideal [IsLocalRing R] {p₁ p₀ : PrimeSpectrum R} (h₀ : p₀ < p₁) (h₁ : p₁ <
 closedPoint R) {x : R} (hx : x in 𝔪) …
· 使用定理 `IsLocalization.instIsNoetherianRingLocalization`：∀ {R : Type u_3} [inst 
: CommRing R] [IsNoetherianRing R] (S : Submonoid R), IsNoetherianRing (Localiza
tion S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Ideal.under_map_of_isLocalizationAtPrime`：Ideal.under_map_of_isLocalizat
ionAtPrime {p : Ideal R} [p.IsPrime] (hpq : p <= q) : (p.map (algebraMap R S)).u
nder R = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem exist_mem_one_of_mem_two {p₁ p₀ p₂ : PrimeSpectrum R}
    (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) {x : R} (hx : x ∈ p₂.asIdeal) :
    ∃ q : (PrimeSpectrum R), x ∈ q.asIdeal ∧ p₀ < q ∧ q < p₂ := by
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime p₂.1) p₂.1
  have hm : closedPoint (Localization.AtPrime p₂.1) =
    e.symm ⟨p₂, le_refl p₂⟩ := (PrimeSpectrum.ext Localization.AtPrime.map_eq_maximalIdeal).symm
  obtain ⟨q, hxq, h₀, h₁⟩ :=
    @exist_mem_one_of_mem_maximal_ideal (Localization.AtPrime p₂.1) _ _ _
      (e.symm ⟨p₁, h₁.le⟩) (e.symm ⟨p₀, (h₀.trans h₁).le⟩) (e.symm.lt_iff_lt.mpr h₀)
        (by simp [hm, h₁]) (algebraMap R (Localization.AtPrime p₂.1) x) <| by
          rw [← Localization.AtPrime.map_eq_maximalIdeal]
          exact mem_map_of_mem (algebraMap R (Localization.AtPrime p₂.1)) hx
  rw [← e.symm_apply_apply q] at h₀ h₁ hxq
  have hq : (e q).1 < p₂ := by
    have h : e.symm (e q) < e.symm ⟨p₂, le_refl p₂⟩ :=
      h₁.trans_eq Localization.AtPrime.map_eq_maximalIdeal.symm
    rwa [OrderIso.lt_iff_lt, Subtype.mk_lt_mk] at h
  exact Exists.intro (e q).1
    ⟨(p₂.1.under_map_of_isLocalizationAtPrime hq.le).le hxq, e.symm.lt_iff_lt.mp h₀, hq⟩

set_option backward.isDefEq.respectTransparency false in
/-- Let $R$ be a Noetherian ring, $\mathfrak{p}_0 < \dots < \mathfrak{p}_n$ be a
  chain of primes, $x \in \mathfrak{p}_n$. Then we can find another chain of primes
  $\mathfrak{q}_0 < \dots < \mathfrak{q}_n$ such that $x \in \mathfrak{q}_1$,
  $\mathfrak{p}_0 = \mathfrak{q}_0$ and $\mathfrak{p}_n = \mathfrak{q}_n$. -/
/-
**PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last** 是 Mathlib 中的一个定理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：exist_ltSeries_mem_one_of_mem_last (p : LTSeries (PrimeSpectrum R)) {x : R
} (hx : x in p.last.asIdeal) : exists q : LTSeries (PrimeSpectrum R), x in (q 1)
.asIdeal ∧ p.length = q.length ∧ p.head = q.head ∧ p.last = q.last
参数：p : LTSeries (PrimeSpectrum R)；hx : x in p.last.asIdeal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.singleton_toFun`：∀ {α : Type u_1} (r : SetRel α α) (a : α) (x 
: Fin (0 + 1)), (RelSeries.singleton r a).toFun x = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `RelSeries.singleton_length`：∀ {α : Type u_1} (r : SetRel α α) (a : α), (
RelSeries.singleton r a).length = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RelSeries.last_singleton`：last_singleton {r : SetRel α α} (x : α) : (sin
gleton r x).last = x
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Fin.zero_eq_mk`：∀ {n a : ℕ} {ha : a < n} [inst : NeZero n], 0 = ⟨a, ha⟩ 
↔ a = 0
· 使用定理 `RelSeries.last.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.last = x.toFun (Fin.last x.length)
· 使用定理 `Fin.last.eq_1`：∀ (n : ℕ), Fin.last n = ⟨n, ⋯⟩
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.natCast_eq_mk`：natCast_eq_mk {m n : Nat} (h : m < n) : have : NeZero
 n
· 使用定理 `Nat.one_lt_succ_succ`：∀ (n : ℕ), 1 < n.succ.succ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `PrimeSpectrum.exist_mem_one_of_mem_two`：exist_mem_one_of_mem_two {p₁ p₀ 
p₂ : PrimeSpectrum R} (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) {x : R} (hx : x in p₂.asIdea
l) : exists q : (PrimeSpectr…
· 使用定理 `Nat.sub_lt_succ`：∀ (a b : ℕ), a - b < a.succ
· 使用引理 `LTSeries.strictMono`：strictMono (x : LTSeries α) : StrictMono x
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Let $R$ be a Noetherian ring, $\mathfrak{p}_0 < \dots < \mathfrak{p}_n$ be a
  chain of primes, $x \in \mathfrak{p}_n$. Then we can find another chain of pri
mes
  $\mathfrak{q}_0 < \dots < \mathfrak{q}_n$ such that $x \in \mathfrak{q}_1$,
  $\mathfrak{p}_0 = \mathfrak{q}_0$ and $\mathfrak{p}_n = \mathfrak{q}_n$.
-/
theorem exist_ltSeries_mem_one_of_mem_last (p : LTSeries (PrimeSpectrum R))
    {x : R} (hx : x ∈ p.last.asIdeal) : ∃ q : LTSeries (PrimeSpectrum R),
    x ∈ (q 1).asIdeal ∧ p.length = q.length ∧ p.head = q.head ∧ p.last = q.last := by
  generalize hp : p.length = n
  induction n generalizing p with
  | zero =>
    use RelSeries.singleton _ p.last
    simp only [RelSeries.singleton_toFun, hx, RelSeries.singleton_length, RelSeries.head,
      RelSeries.last_singleton, and_true, true_and]
    rw [show 0 = Fin.last p.length from Fin.zero_eq_mk.mpr hp, RelSeries.last]
  | succ n hn => ?_
  by_cases h0 : n = 0
  · use p
    have h1 : 1 = Fin.last p.length := by
      rw [Fin.last, hp, h0, zero_add]
      exact Fin.natCast_eq_mk (Nat.one_lt_succ_succ 0)
    simpa [h1, hp] using! hx
  obtain ⟨q, hxq, h2, hq⟩ : ∃ q : PrimeSpectrum R, x ∈ q.1 ∧ p ⟨p.length - 2, _⟩ < q ∧ q < p.last :=
    (p ⟨p.length - 1, p.length.sub_lt_succ 1⟩).exist_mem_one_of_mem_two
      (p.strictMono (Nat.pred_lt (by simpa [hp]))) (p.strictMono (Nat.pred_lt (by simp [hp]))) hx
  obtain ⟨Q, hx, hQ, hh, hl⟩ := hn (p.eraseLast.eraseLast.snoc q h2) (by simpa using! hxq) <| by
    simpa [hp] using! Nat.succ_pred_eq_of_ne_zero h0
  have h1 : 1 < Q.length + 1 := Nat.lt_of_sub_ne_zero (hQ.symm.trans_ne h0)
  have h : 1 = (1 : Fin (Q.length + 1)).castSucc := by simp [Fin.one_eq_mk_of_lt h1]
  exact ⟨Q.snoc p.last (by simpa [← hl] using! hq), by simpa [h], by simpa, by simp [← hh], by simp⟩

end PrimeSpectrum

