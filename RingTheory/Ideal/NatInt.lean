/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Prime ideals in ℕ and ℤ

## Main results

* `Ideal.isPrime_nat_iff`: the prime ideals in ℕ are ⟨0⟩, ⟨p⟩ (for prime `p`), and `⟨2, 3⟩ = {1}ᶜ`.
  The proof follows https://math.stackexchange.com/a/4224486.

* `Ideal.isPrime_int_iff` : the prime ideals in ℤ are ⟨0⟩ and ⟨p⟩ (for prime `p`).
-/

public section

/-- The natural numbers form a local semiring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural numbers form a local semiring.
-/
instance : IsLocalRing ℕ where
  isUnit_or_isUnit_of_add_one {a b} hab := by
    have h : a = 1 ∨ b = 1 := by lia
    apply h.imp <;> simp +contextual

open IsLocalRing Ideal
/-
**Nat.mem_maximalIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.mem_maximalIdeal_iff {n : Nat} : n in maximalIdeal Nat ↔ n != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsLocalRingNat`：IsLocalRing ℕ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Nat.mem_maximalIdeal_iff {n : ℕ} : n ∈ maximalIdeal ℕ ↔ n ≠ 1 := by simp
/-
**Nat.coe_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.coe_maximalIdeal : (maximalIdeal Nat : Set Nat) = {1}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instIsLocalRingNat`：IsLocalRing ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Nat.coe_maximalIdeal : (maximalIdeal ℕ : Set ℕ) = {1}ᶜ := by ext; simp
/-
**Nat.maximalIdeal_eq_span_two_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.maximalIdeal_eq_span_two_three : maximalIdeal Nat = span {2, 3}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `instIsLocalRingNat`：IsLocalRing ℕ
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_maximalIdeal_iff`：Nat.mem_maximalIdeal_iff {n : Nat} : n in maxi
malIdeal Nat ↔ n != 1
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_span_pair`：mem_span_pair {x y z : α} : z in span ({x, y} : Set
 α) ↔ exists a b, a * x + b * y = z
· 使用定理 `Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le`：Nat.exists_add_mul_eq_o
f_gcd_dvd_of_mul_pred_le (p q n : Nat) (dvd : p.gcd q ∣ n) (le : p.pred * q.pred
 <= n) : exists a b : Nat, a * p + b …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.pair_subset`：pair_subset (ha : a in s) (hb : b in s) : {a, b} subset
eq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Nat.maximalIdeal_eq_span_two_three : maximalIdeal ℕ = span {2, 3} := by
  refine le_antisymm (fun n h ↦ ?_) (span_le.mpr <| Set.pair_subset (by simp) (by simp))
  obtain lt | lt := (mem_maximalIdeal_iff.mp h).lt_or_gt
  · obtain rfl := lt_one_iff.mp lt; exact zero_mem _
  exact mem_span_pair.mpr <|
    exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le 2 3 n (by simp) (show 2 ≤ n by lia)
/-
**Nat.one_mem_span_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.one_mem_span_iff {s : Set Nat} : 1 in span s ↔ 1 in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `instIsLocalRingNat`：IsLocalRing ℕ
· 使用定理 `Nat.coe_maximalIdeal`：Nat.coe_maximalIdeal : (maximalIdeal Nat : Set Nat
) = {1}ᶜ
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nat.one_mem_span_iff {s : Set ℕ} : 1 ∈ span s ↔ 1 ∈ s := by
  rw [← SetLike.mem_coe, ← not_iff_not]
  simp_rw [← Set.mem_compl_iff, ← Set.singleton_subset_iff, Set.subset_compl_comm]
  rw [Set.subset_compl_comm, ← coe_maximalIdeal, SetLike.coe_subset_coe, span_le]
/-
**Nat.one_mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.one_mem_closure_iff {s : Set Nat} : 1 in AddSubmonoid.closure s ↔ 1 in
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_nat_eq_addSubmonoidClosure`：span_nat_eq_addSubmonoidClosu
re (s : Set M) : (span Nat s).toAddSubmonoid = AddSubmonoid.closure s
· 使用定理 `Nat.one_mem_span_iff`：Nat.one_mem_span_iff {s : Set Nat} : 1 in span s ↔
 1 in s
-/
theorem Nat.one_mem_closure_iff {s : Set ℕ} : 1 ∈ AddSubmonoid.closure s ↔ 1 ∈ s := by
  rw [← Submodule.span_nat_eq_addSubmonoidClosure]
  exact one_mem_span_iff
/-
**Ideal.isPrime_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.isPrime_nat_iff {P : Ideal Nat} : P.IsPrime ↔ P = ⊥ ∨ P = maximalIde
al Nat ∨ exists p : Nat, p.Prime ∧ P = span {p}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `instIsLocalRingNat`：IsLocalRing ℕ
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `SetLike.not_le_iff_exists`：not_le_iff_exists : ¬p <= q ↔ exists x in p, 
x ∉ q
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
· 使用定理 `Nat.prime_iff_not_exists_mul_eq`：prime_iff_not_exists_mul_eq {p : Nat} :
 p.Prime ↔ 2 <= p ∧ ¬ exists m n, m < p ∧ n < p ∧ m * n = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
（共 57 条，此处仅展示前 30 条）
-/
theorem Ideal.isPrime_nat_iff {P : Ideal ℕ} :
    P.IsPrime ↔ P = ⊥ ∨ P = maximalIdeal ℕ ∨ ∃ p : ℕ, p.Prime ∧ P = span {p} := by
  refine .symm ⟨?_, fun h ↦ or_iff_not_imp_left.mpr fun h0 ↦ or_iff_not_imp_right.mpr fun hsp ↦
    (le_maximalIdeal h.ne_top).antisymm fun n hn ↦ ?_⟩
  · rintro (rfl | rfl | ⟨p, hp, rfl⟩)
    · exact isPrime_bot
    · exact (maximalIdeal.isMaximal ℕ).isPrime
    · rwa [span_singleton_prime (by simp [hp.ne_zero]), ← Nat.prime_iff]
  rw [← le_bot_iff, SetLike.not_le_iff_exists] at h0
  classical
  let p := Nat.find h0
  have ⟨(hp : p ∈ P), (hp0 : p ≠ 0)⟩ := Nat.find_spec h0
  have : p ≠ 1 := ne_of_mem_of_not_mem hp P.one_notMem
  have prime : p.Prime := Nat.prime_iff_not_exists_mul_eq.mpr <| .intro (by lia)
    fun ⟨m, n, hm, hn, eq⟩ ↦ have := mul_ne_zero_iff.mp (eq ▸ hp0)
    (h.mem_or_mem (eq ▸ hp)).elim (Nat.find_min h0 hm ⟨·, this.1⟩) (Nat.find_min h0 hn ⟨·, this.2⟩)
  push Not at hsp
  have ⟨q, hq, hqp⟩ := SetLike.exists_of_lt
    ((P.span_singleton_le_iff_mem.mpr hp).lt_of_ne (hsp p prime).symm)
  obtain rfl | hn1 := eq_or_ne n 0
  · exact Ideal.zero_mem _
  have : n ≠ 1 := Nat.mem_maximalIdeal_iff.mp hn
  have ⟨a, b, eq⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le p q _
    (by simp [prime.coprime_iff_not_dvd.mpr (Ideal.mem_span_singleton.not.mp hqp)])
    (Nat.lt_pow_self (show 1 < n by lia)).le
  exact h.mem_of_pow_mem _ (eq ▸ add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hq))
/-
**Ideal.map_comap_natCastRingHom_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.map_comap_natCastRingHom_int {I : Ideal Int} : (I.comap (Nat.castRin
gHom Int)).map (Nat.castRingHom Int) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Int.sign_mul_natAbs`：∀ (a : ℤ), a.sign * ↑a.natAbs = a
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Int.sign_mul_self`：∀ (i : ℤ), i.sign * i = ↑i.natAbs
-/
theorem Ideal.map_comap_natCastRingHom_int {I : Ideal ℤ} :
    (I.comap (Nat.castRingHom ℤ)).map (Nat.castRingHom ℤ) = I :=
  map_comap_le.antisymm fun n hn ↦ n.sign_mul_natAbs ▸ mul_mem_left _ _ <| mem_map_of_mem _
    (mem_comap.mpr <| show (n.natAbs : ℤ) ∈ I from n.sign_mul_self ▸ mul_mem_left _ _ hn)
/-
**Ideal.isPrime_int_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.isPrime_int_iff {P : Ideal Int} : P.IsPrime ↔ P = ⊥ ∨ exists p : Nat
, p.Prime ∧ P = span {(p : Int)}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ideal.isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors`：isPrime_iff
_of_isPrincipalIdealRing_of_noZeroDivisors [NoZeroDivisors α] [Nontrivial α] {P 
: Ideal α} : P.IsPrime ↔ P = ⊥ ∨ exists p, Prime …
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `or_congr_right`：∀ {b c a : Prop}, (b ↔ c) → (a ∨ b ↔ a ∨ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.prime_iff_natAbs_prime`：prime_iff_natAbs_prime {k : Int} : Prime k ↔
 Nat.Prime k.natAbs
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.span_natAbs`：span_natAbs (a : Int) : Ideal.span ({(a.natAbs : Int)} 
: Set Int) = Ideal.span {a}
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
-/
theorem Ideal.isPrime_int_iff {P : Ideal ℤ} :
    P.IsPrime ↔ P = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ P = span {(p : ℤ)} :=
  isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors.trans <| or_congr_right
  ⟨fun ⟨p, hp, eq⟩ ↦ ⟨_, Int.prime_iff_natAbs_prime.mp hp, eq.trans
    p.span_natAbs.symm⟩, fun ⟨_p, hp, eq⟩ ↦ ⟨_, Nat.prime_iff_prime_int.mp hp, eq⟩⟩
/-
**ringKrullDim_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringKrullDim_nat : ringKrullDim Nat = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用引理 `three_ne_zero`：three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) != 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `instIsLocalRingNat`：IsLocalRing ℕ
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.isPrime_nat_iff`：Ideal.isPrime_nat_iff {P : Ideal Nat} : P.IsPrime
 ↔ P = ⊥ ∨ P = maximalIdeal Nat ∨ exists p : Nat, p.Prime ∧ P = span {p}
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `IsLocalRing.le_maximalIdeal_of_isPrime`：le_maximalIdeal_of_isPrime (p : 
Ideal R) [hp : p.IsPrime] : p <= maximalIdeal R
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `DvdNotUnit.isUnit_of_irreducible_right`：DvdNotUnit.isUnit_of_irreducible
_right [CommMonoidWithZero M] {p q : M} (h : DvdNotUnit p q) (hq : Irreducible q
) : IsUnit p
· 使用定理 `Ideal.span_singleton_lt_span_singleton`：span_singleton_lt_span_singleton
 [IsDomain α] {x y : α} : span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y
 x
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 63 条，此处仅展示前 30 条）
-/
theorem ringKrullDim_nat : ringKrullDim ℕ = 2 := by
  refine le_antisymm (iSup_le fun s ↦ le_of_not_gt fun hs ↦ ?_) ?_
  · replace hs : 2 < s.length := ENat.natCast_lt_natCast.mp (WithBot.coe_lt_coe.mp hs)
    let s := s.take ⟨3, by lia⟩
    have : NeZero s.length := ⟨three_ne_zero⟩
    have h1 : ⊥ < (s 1).asIdeal := bot_le.trans_lt (s.step 0)
    obtain hmax | ⟨p, hp, hsp⟩ := (Ideal.isPrime_nat_iff.mp (s 1).2).resolve_left h1.ne'
    · exact (le_maximalIdeal_of_isPrime (s 2).asIdeal).not_gt (hmax.symm.trans_lt (s.step 1))
    obtain hmax | ⟨q, hq, hsq⟩ :=
      (Ideal.isPrime_nat_iff.mp (s 2).2).resolve_left (h1.trans (s.step 1)).ne'
    · exact (le_maximalIdeal_of_isPrime (s 3).asIdeal).not_gt (hmax.symm.trans_lt (s.step 2))
    · exact hq.not_isUnit <| (Ideal.span_singleton_lt_span_singleton.mp
        ((hsp.symm.trans_lt (s.step 1)).trans_eq hsq)).isUnit_of_irreducible_right hp
  · refine le_iSup_of_le ⟨2, ![⊥, ⟨_, (span_singleton_prime two_ne_zero).mpr <| Nat.prime_iff.mp
      Nat.prime_two⟩, ⟨_, (maximalIdeal.isMaximal ℕ).isPrime⟩], fun i ↦ ?_⟩ le_rfl
    fin_cases i
    · exact bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr two_ne_zero)
    · simp_rw [Nat.maximalIdeal_eq_span_two_three]
      exact SetLike.lt_iff_le_and_exists.mpr ⟨Ideal.span_mono (by simp),
        3, Ideal.subset_span (by simp), Ideal.mem_span_singleton.not.mpr <| by simp⟩
