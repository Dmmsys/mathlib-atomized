/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Order.Hom.TypeTags
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Aut
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

/-!
# Further properties of cyclic groups

## Main statements

* `isSimpleGroup_of_prime_card`, `IsSimpleGroup.isCyclic`,
  and `IsSimpleGroup.prime_card` classify finite simple abelian groups.
* `IsCyclic.card_orderOf_eq_totient` computes the number of elements of given order
  in a cyclic group.
* `IsCyclic.exponent_eq_card`: For a finite cyclic group `G`, the exponent is equal to
  the group's cardinality.
* `IsCyclic.exponent_eq_zero_of_infinite`: Infinite cyclic groups have exponent zero.
* `IsCyclic.iff_exponent_eq_card`: A finite commutative group is cyclic iff its exponent
  is equal to its cardinality.
* `IsCyclic.card_mulAut`, cardinality of automorphisms of a finite group.
* `commGroupOfCyclicCenterQuotient`: if the quotient of a group by
  its center is cyclic, then the group is commutative.
* `Group.isCyclic_prod_iff`: the product of two finite cyclic groups is cyclic
  if and only if their orders are relatively prime.

## Tags

cyclic group, exponent, totient
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

variable {α G G' : Type*} {a : α}

section Cyclic

open Subgroup

variable [Group α] [Group G] [Group G']

open Finset Nat

section Totient

variable [DecidableEq α] [Fintype α] (hn : ∀ n : ℕ, 0 < n → #{a : α | a ^ n = 1} ≤ n)
include hn

@[to_additive]
/-
**card_pow_eq_one_eq_orderOf_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem card_pow_eq_one_eq_orderOf_aux (a : α) : #{b : α | b ^ orderOf a = 1} = orderOf a :=
  le_antisymm (hn _ (orderOf_pos a))
    (calc
      orderOf a = @Fintype.card (zpowers a) (id _) := Fintype.card_zpowers.symm
      _ ≤
          @Fintype.card (({b : α | b ^ orderOf a = 1} : Finset _) : Set α)
            (Fintype.ofFinset _ fun _ => Iff.rfl) :=
        (@Fintype.card_le_of_injective (zpowers a)
          (({b : α | b ^ orderOf a = 1} : Finset _) : Set α) (id _) (id _)
          (fun b =>
            ⟨b.1,
              mem_filter.2
                ⟨mem_univ _, by
                  let ⟨i, hi⟩ := b.2
                  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
                    pow_orderOf_eq_one, one_zpow]⟩⟩)
          fun _ _ h => Subtype.ext (Subtype.mk.inj h))
      _ = #{b : α | b ^ orderOf a = 1} := Fintype.card_ofFinset _ _)

-- Use φ for `Nat.totient`
open Nat
@[to_additive]
/-
**card_orderOf_eq_totient_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem card_orderOf_eq_totient_aux₁ {d : ℕ} (hd : d ∣ Fintype.card α)
    (hpos : 0 < #{a : α | orderOf a = d}) : #{a : α | orderOf a = d} = φ d := by
  induction d using Nat.strong_induction_on with | _ d IH
  rcases Decidable.eq_or_ne d 0 with (rfl | hd0)
  · cases Fintype.card_ne_zero (eq_zero_of_zero_dvd hd)
  rcases Finset.card_pos.1 hpos with ⟨a, ha'⟩
  have ha : orderOf a = d := (mem_filter.1 ha').2
  have h1 :
    (∑ m ∈ d.properDivisors, #{a : α | orderOf a = m}) =
      ∑ m ∈ d.properDivisors, φ m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [mem_properDivisors] at hm
    refine IH m hm.2 (hm.1.trans hd) (Finset.card_pos.2 ⟨a ^ (d / m), ?_⟩)
    rw [mem_filter_univ, orderOf_pow a, ha, Nat.gcd_eq_right (div_dvd_of_dvd hm.1),
      Nat.div_div_self hm.1 hd0]
  have h2 :
    (∑ m ∈ d.divisors, #{a : α | orderOf a = m}) =
      ∑ m ∈ d.divisors, φ m := by
    rw [sum_card_orderOf_eq_card_pow_eq_one hd0, sum_totient,
      ← ha, card_pow_eq_one_eq_orderOf_aux hn a]
  simpa [← cons_self_properDivisors hd0, ← h1] using h2

@[to_additive]
/-
**card_orderOf_eq_totient_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_orderOf_eq_totient_aux₂ {d : ℕ} (hd : d ∣ Fintype.card α) :
    #{a : α | orderOf a = d} = φ d := by
  let c := Fintype.card α
  have hc0 : 0 < c := Fintype.card_pos_iff.2 ⟨1⟩
  apply card_orderOf_eq_totient_aux₁ hn hd
  by_contra h0
  -- Must qualify `Finset.card_eq_zero` because of https://github.com/leanprover/lean4/issues/2849
  simp_rw [not_lt, Nat.le_zero, Finset.card_eq_zero] at h0
  apply lt_irrefl c
  calc
    c = ∑ m ∈ c.divisors, #{a : α | orderOf a = m} := by
      simp only [sum_card_orderOf_eq_card_pow_eq_one hc0.ne']
      apply congr_arg card
      simp [c]
    _ = ∑ m ∈ c.divisors.erase d, #{a : α | orderOf a = m} := by
      rw [eq_comm]
      refine sum_subset (erase_subset _ _) fun m hm₁ hm₂ => ?_
      have : m = d := by
        contrapose! hm₂
        exact mem_erase_of_ne_of_mem hm₂ hm₁
      simp [this, h0]
    _ ≤ ∑ m ∈ c.divisors.erase d, φ m := by
      gcongr with m hm
      have hmc : m ∣ c := by
        simp only [mem_erase, mem_divisors] at hm
        tauto
      obtain h1 | h1 := (#{a : α | orderOf a = m}).eq_zero_or_pos
      · simp [h1]
      · simp [card_orderOf_eq_totient_aux₁ hn hmc h1]
    _ < ∑ m ∈ c.divisors, φ m :=
      sum_erase_lt_of_pos (mem_divisors.2 ⟨hd, hc0.ne'⟩) (totient_pos.2 (pos_of_dvd_of_pos hd hc0))
    _ = c := sum_totient _

@[to_additive isAddCyclic_of_card_nsmul_eq_zero_le, stacks 09HX "This theorem is stronger than \
09HX. It removes the abelian condition, and requires only `≤` instead of `=`."]
/-
**isCyclic_of_card_pow_eq_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_card_pow_eq_one_le : IsCyclic α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `card_orderOf_eq_totient_aux₂`：card_orderOf_eq_totient_aux₂ {d : Nat} (hd
 : d ∣ Fintype.card α) : #{a : α | orderOf a = d} = φ d
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `isCyclic_of_orderOf_eq_card`：isCyclic_of_orderOf_eq_card [Finite α] (x :
 α) (hx : orderOf x = Nat.card α) : IsCyclic α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem isCyclic_of_card_pow_eq_one_le : IsCyclic α :=
  have : Finset.Nonempty {a : α | orderOf a = Nat.card α} :=
    card_pos.1 <| by
      rw [Nat.card_eq_fintype_card, card_orderOf_eq_totient_aux₂ hn dvd_rfl, totient_pos]
      apply Fintype.card_pos
  let ⟨x, hx⟩ := this
  isCyclic_of_orderOf_eq_card x (Finset.mem_filter.1 hx).2

end Totient

@[to_additive]
/-
**IsCyclic.card_orderOf_eq_totient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCyclic.card_orderOf_eq_totient [IsCyclic α] [Fintype α] {d : Nat} (hd : 
d ∣ Fintype.card α) : #{a : α | orderOf a = d} = totient d
参数：hd : d ∣ Fintype.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `card_orderOf_eq_totient_aux₂`：card_orderOf_eq_totient_aux₂ {d : Nat} (hd
 : d ∣ Fintype.card α) : #{a : α | orderOf a = d} = φ d
· 使用定理 `IsCyclic.card_pow_eq_one_le`：IsCyclic.card_pow_eq_one_le [DecidableEq α]
 [Fintype α] [IsCyclic α] {n : Nat} (hn0 : 0 < n) : #{a : α | a ^ n = 1} <= n
-/
lemma IsCyclic.card_orderOf_eq_totient [IsCyclic α] [Fintype α] {d : ℕ} (hd : d ∣ Fintype.card α) :
    #{a : α | orderOf a = d} = totient d := by
  classical apply card_orderOf_eq_totient_aux₂ (fun n => IsCyclic.card_pow_eq_one_le) hd

/-- A finite group of prime order is simple. -/
@[to_additive /-- A finite group of prime order is simple. -/]
/-
**isSimpleGroup_of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimpleGroup_of_prime_card {p : Nat} [hp : Fact p.Prime] (h : Nat.card α 
= p) : IsSimpleGroup α
参数：h : Nat.card α = p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Subgroup.eq_bot_or_eq_top_of_prime_card`：Subgroup.eq_bot_or_eq_top_of_pr
ime_card (H : Subgroup G) [hp : Fact (Nat.card G).Prime] : H = ⊥ ∨ H = ⊤

--- 原说明 ---
A finite group of prime order is simple.
-/
theorem isSimpleGroup_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card α = p) : IsSimpleGroup α := by
  subst h
  have : Finite α := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp hp.1.one_lt
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card⟩

end Cyclic

section QuotientCenter

open Subgroup

variable [Group G] [Group G']

/-- A group is commutative if the quotient by the center is cyclic.
  Also see `commGroupOfCyclicCenterQuotient` for the `CommGroup` instance. -/
@[to_additive
/-- A group is commutative if the quotient by the center is cyclic.
Also see `addCommGroupOfCyclicCenterQuotient` for the `AddCommGroup` instance. -/]
/-
**MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center [IsCyclic G'] (f :
 G ->* G') (hf : f.ker <= center G) : IsMulCommutative G
参数：f : G ->* G'；hf : f.ker <= center G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
（共 37 条，此处仅展示前 30 条）
-/
theorem MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center [IsCyclic G'] (f : G →* G')
    (hf : f.ker ≤ center G) : IsMulCommutative G := by
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  let ⟨⟨x, y, (hxy : f y = x)⟩, (hx : ∀ a : f.range, a ∈ zpowers _)⟩ :=
    IsCyclic.exists_generator (α := f.range)
  let ⟨m, hm⟩ := hx ⟨f a, a, rfl⟩
  let ⟨n, hn⟩ := hx ⟨f b, b, rfl⟩
  have hm : x ^ m = f a := by simpa [Subtype.ext_iff] using hm
  have hn : x ^ n = f b := by simpa [Subtype.ext_iff] using hn
  have ha : y ^ (-m) * a ∈ center G :=
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x m, hm, inv_mul_cancel])
  have hb : y ^ (-n) * b ∈ center G :=
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x n, hn, inv_mul_cancel])
  calc
    a * b = y ^ m * (y ^ (-m) * a * y ^ n) * (y ^ (-n) * b) := by simp [mul_assoc]
    _ = y ^ m * (y ^ n * (y ^ (-m) * a)) * (y ^ (-n) * b) := by rw [mem_center_iff.1 ha]
    _ = y ^ m * y ^ n * y ^ (-m) * (a * (y ^ (-n) * b)) := by simp [mul_assoc]
    _ = y ^ m * y ^ n * y ^ (-m) * (y ^ (-n) * b * a) := by rw [mem_center_iff.1 hb]
    _ = b * a := by group

@[to_additive (attr := deprecated MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
  (since := "2026-05-26"))]
/-
**commutative_of_cyclic_center_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commutative_of_cyclic_center_quotient [IsCyclic G'] (f : G ->* G') (hf : f
.ker <= center G) (a b : G) : a * b = b * a
参数：f : G ->* G'；hf : f.ker <= center G；a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`：MonoidHom.isMul
Commutative_of_isCyclic_of_ker_le_center [IsCyclic G'] (f : G ->* G') (hf : f.ke
r <= center G) : IsMulCommutative G
-/
theorem commutative_of_cyclic_center_quotient [IsCyclic G'] (f : G →* G') (hf : f.ker ≤ center G)
    (a b : G) : a * b = b * a :=
  f.isMulCommutative_of_isCyclic_of_ker_le_center hf |>.is_comm.comm a b

/-- A group is commutative if the quotient by the center is cyclic. -/
@[to_additive (attr := instance_reducible)
/-- A group is commutative if the quotient by the center is cyclic. -/]
/-
**commGroupOfCyclicCenterQuotient** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGroupOfCyclicCenterQuotient [IsCyclic G'] (f : G ->* G') (hf : f.ker <
= center G) : CommGroup G where .is_comm.comm mul_comm
参数：f : G ->* G'；hf : f.ker <= center G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commGroupOfCyclicCenterQuotient [IsCyclic G'] (f : G →* G') (hf : f.ker ≤ center G) :
    CommGroup G where
  mul_comm := f.isMulCommutative_of_isCyclic_of_ker_le_center hf |>.is_comm.comm

variable (G) in
/-- If the quotient by the center of a group is cyclic, then the group is commutative. -/
@[to_additive
/-- If the quotient by the center of a group is cyclic, then the group is commutative. -/]
/-
**isMulCommutative_of_isCyclic_quotient_center_self** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：isMulCommutative_of_isCyclic_quotient_center_self [IsCyclic (G ⧸ Subgroup.
center G)] : IsMulCommutative G
参数：G ⧸ Subgroup.center G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`：MonoidHom.isMul
Commutative_of_isCyclic_of_ker_le_center [IsCyclic G'] (f : G ->* G') (hf : f.ke
r <= center G) : IsMulCommutative G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
-/
theorem isMulCommutative_of_isCyclic_quotient_center_self [IsCyclic (G ⧸ Subgroup.center G)] :
    IsMulCommutative G := by
  simp [(QuotientGroup.mk' <| .center G).isMulCommutative_of_isCyclic_of_ker_le_center]

end QuotientCenter

namespace IsSimpleGroup

section CommSimpleGroup

variable [CommGroup α] [IsSimpleGroup α]

@[to_additive]
/-
**IsSimpleGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isCyclic : IsCyclic α := by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_ne (1 : α)
  have : Subgroup.zpowers g = ⊤ :=
    (eq_bot_or_eq_top (Subgroup.zpowers g)).resolve_left (Subgroup.zpowers_ne_bot.2 hg)
  exact ⟨⟨g, (Subgroup.eq_top_iff' _).1 this⟩⟩

@[to_additive]
/-
**IsSimpleGroup.prime_card** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleGroup`。
形式化陈述：prime_card : (Nat.card α).Prime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleGroup.toNontrivial`：∀ {G : Type u_1} {inst : Group G} [self : Is
SimpleGroup G], Nontrivial G
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `IsSimpleGroup.isCyclic`：∀ {α : Type u_1} [inst : CommGroup α] [IsSimpleG
roup α], IsCyclic α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mem_zpowers_pow_iff`：mem_zpowers_pow_iff {g : G} {k : Nat} : g in Subgro
up.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `IsSimpleGroup.instIsSimpleOrderSubgroup`：∀ {C : Type u_3} [inst : CommGr
oup C] [IsSimpleGroup C], IsSimpleOrder (Subgroup C)
· 使用定理 `Nat.prime_of_coprime`：prime_of_coprime (n : Nat) (h1 : 1 < n) (h : foral
l m < n, m != 0 -> n.Coprime m) : Prime n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
（共 33 条，此处仅展示前 30 条）
-/
theorem prime_card : (Nat.card α).Prime := by
  have hα : Nontrivial α := IsSimpleGroup.toNontrivial
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  replace hα : Nat.card α ≠ 1 := by contrapose! hα; exact (Nat.card_eq_one_iff_unique.mp hα).1
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg] at hα ⊢
  have h (n : ℕ) : orderOf g ∣ n ∨ n.Coprime (orderOf g) := by
    refine (IsSimpleOrder.eq_bot_or_eq_top (Subgroup.zpowers (g ^ n))).imp ?_ fun h ↦ ?_
    · simp [orderOf_dvd_iff_pow_eq_one]
    · simp only [Nat.coprime_iff_gcd_eq_one]
      have hgn : g ∈ Subgroup.zpowers (g ^ n) := by simp_all only [ne_eq, orderOf_eq_one_iff,
        Subgroup.mem_top]
      exact mem_zpowers_pow_iff.mp hgn
  apply Nat.prime_of_coprime
  · refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, hα⟩
    contrapose! h
    exact ⟨37, by simp [h]⟩
  · intro n hn hn0
    exact ((h n).resolve_left (Nat.not_dvd_of_pos_of_lt (Nat.pos_iff_ne_zero.mpr hn0) hn)).symm

/-- A commutative simple group is a finite group. -/
@[to_additive /-- A commutative simple group is a finite group. -/]
/-
**IsSimpleGroup.finite** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleGroup`。
形式化陈述：finite : Finite α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `IsSimpleGroup.prime_card`：prime_card : (Nat.card α).Prime

--- 原说明 ---
A commutative simple group is a finite group.
-/
theorem finite : Finite α := Nat.finite_of_card_ne_zero prime_card.ne_zero

end CommSimpleGroup

end IsSimpleGroup

open scoped IsMulCommutative in
@[to_additive]
/-
**Group.is_simple_iff_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.is_simple_iff_prime_card [Group α] [IsMulCommutative α] : IsSimpleGr
oup α ↔ (Nat.card α).Prime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleGroup.prime_card`：prime_card : (Nat.card α).Prime
· 使用定理 `isSimpleGroup_of_prime_card`：isSimpleGroup_of_prime_card {p : Nat} [hp :
 Fact p.Prime] (h : Nat.card α = p) : IsSimpleGroup α
-/
theorem Group.is_simple_iff_prime_card [Group α] [IsMulCommutative α] :
    IsSimpleGroup α ↔ (Nat.card α).Prime :=
  ⟨fun h ↦ h.prime_card, fun h ↦ isSimpleGroup_of_prime_card (hp := ⟨h⟩) rfl⟩

@[to_additive]
/-
**CommGroup.is_simple_iff_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommGroup.is_simple_iff_prime_card [CommGroup α] : IsSimpleGroup α ↔ (Nat.
card α).Prime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.is_simple_iff_prime_card`：Group.is_simple_iff_prime_card [Group α]
 [IsMulCommutative α] : IsSimpleGroup α ↔ (Nat.card α).Prime
-/
theorem CommGroup.is_simple_iff_prime_card [CommGroup α] : IsSimpleGroup α ↔ (Nat.card α).Prime :=
  Group.is_simple_iff_prime_card

section SpecificInstances

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddCyclic ℤ := ⟨1, fun n ↦ ⟨n, by simp only [smul_eq_mul, mul_one]⟩⟩
/-
**ZMod.instIsAddCyclic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZMod.instIsAddCyclic (n : Nat) : IsAddCyclic (ZMod n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isAddCyclic_of_surjective`：∀ {G : Type u_2} {G' : Type u_3} [inst : AddG
roup G] [inst_1 : AddGroup G'] {F : Type u_4} [hH : IsAddCyclic G']   [inst_2 : 
FunLike F G' G]…
· 使用定理 `instIsAddCyclicInt`：IsAddCyclic ℤ
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `ZMod.intCast_surjective`：intCast_surjective : Function.Surjective ((↑) :
 Int -> ZMod n)
-/
instance ZMod.instIsAddCyclic (n : ℕ) : IsAddCyclic (ZMod n) :=
  isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective
/-
**ZMod.instIsSimpleAddGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZMod.instIsSimpleAddGroup {p : Nat} [hp : Fact p.Prime] : IsSimpleAddGroup
 (ZMod p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.is_simple_iff_prime_card`：∀ {α : Type u_1} [inst : AddCommG
roup α], IsSimpleAddGroup α ↔ Nat.Prime (Nat.card α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
instance ZMod.instIsSimpleAddGroup {p : ℕ} [hp : Fact p.Prime] : IsSimpleAddGroup (ZMod p) :=
  AddCommGroup.is_simple_iff_prime_card.2 (by simpa using hp.out)

end SpecificInstances

section EquivInt

/-- A linearly-ordered additive abelian group is cyclic iff it is isomorphic to `ℤ` as an ordered
additive monoid. -/
/-
**LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int {A : Type*} [
AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A] [Nontrivial A] : IsAddCyc
lic A ↔ Nonempty (A ≃+o Int)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_zsmul_iff_not_isOfFinAddOrder`：∀ {G : Type u_1} [inst : AddGro
up G] {x : G}, (Function.Injective fun n => n • x) ↔ ¬IsOfFinAddOrder x
· 使用定理 `not_isOfFinAddOrder_of_isAddTorsionFree`：∀ {G : Type u_1} [inst : AddMon
oid G] {a : G} [IsAddTorsionFree G], a ≠ 0 → ¬IsOfFinAddOrder a
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a
· 使用定理 `zsmul_le_zsmul_iff_left`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_
1 : PartialOrder α] [IsOrderedAddMonoid α] {m n : ℤ} {a : α},   0 < a → (m • a ≤
 n • a ↔ m ≤ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `neg_surjective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Surj
ective Neg.neg
· 使用定理 `AddEquiv.isAddCyclic`：∀ {G : Type u_2} {G' : Type u_3} [inst : AddGroup 
G] [inst_1 : AddGroup G'] (e : G ≃+ G'),   IsAddCyclic G ↔ IsAddCyclic G'
· 使用定理 `instIsAddCyclicInt`：IsAddCyclic ℤ

--- 原说明 ---
A linearly-ordered additive abelian group is cyclic iff it is isomorphic to `ℤ` 
as an ordered
additive monoid.
-/
lemma LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int {A : Type*}
    [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A] [Nontrivial A] :
    IsAddCyclic A ↔ Nonempty (A ≃+o ℤ) := by
  refine ⟨?_, fun ⟨e⟩ ↦ e.isAddCyclic.mpr inferInstance⟩
  rintro ⟨g, hs⟩
  have h_ne : g ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨m, rfl⟩ := hs a
    aesop
  wlog hg' : 0 < g
  · exact this (g := -g) (by simpa using! neg_surjective.comp hs) (by grind) (by grind)
  have hi : (fun n : ℤ ↦ n • g).Injective := injective_zsmul_iff_not_isOfFinAddOrder.mpr
      <| not_isOfFinAddOrder_of_isAddTorsionFree h_ne
  exact ⟨.symm { Equiv.ofBijective _ ⟨hi, hs⟩ with
    map_add' := add_zsmul g
    map_le_map_iff' := zsmul_le_zsmul_iff_left hg' }⟩

set_option backward.isDefEq.respectTransparency false in
/-- A linearly-ordered abelian group is cyclic iff it is isomorphic to `Multiplicative ℤ` as an
ordered monoid. -/
/-
**LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int {G : Type*} [CommGr
oup G] [LinearOrder G] [IsOrderedMonoid G] [Nontrivial G] : IsCyclic G ↔ Nonempt
y (G ≃*o Multiplicative Int)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isAddCyclic_additive_iff`：isAddCyclic_additive_iff [DivInvMonoid α] : Is
AddCyclic (Additive α) ↔ IsCyclic α
· 使用引理 `LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int`：LinearOrde
redAddCommGroup.isAddCyclic_iff_nonempty_equiv_int {A : Type*} [AddCommGroup A] 
[LinearOrder A] [IsOrderedAddMonoid A] [Nontrivial…
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A linearly-ordered abelian group is cyclic iff it is isomorphic to `Multiplicati
ve ℤ` as an
ordered monoid.
-/
lemma LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [Nontrivial G] :
    IsCyclic G ↔ Nonempty (G ≃*o Multiplicative ℤ) := by
  rw [← isAddCyclic_additive_iff, LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int,
    OrderAddMonoidIso.toMultiplicativeRight.nonempty_congr]

end EquivInt

section Exponent

open Monoid

@[to_additive]
/-
**IsCyclic.exponent_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.exponent_eq_card [Group α] [IsCyclic α] : exponent α = Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCyclic.exists_ofOrder_eq_natCard`：IsCyclic.exists_ofOrder_eq_natCard [
h : IsCyclic α] : exists g : α, orderOf g = Nat.card α
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Group.exponent_dvd_nat_card`：Group.exponent_dvd_nat_card : Monoid.expone
nt G ∣ Nat.card G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
-/
theorem IsCyclic.exponent_eq_card [Group α] [IsCyclic α] :
    exponent α = Nat.card α := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := α)
  apply Nat.dvd_antisymm Group.exponent_dvd_nat_card
  rw [← hg]
  exact order_dvd_exponent _

@[to_additive]
/-
**IsCyclic.of_exponent_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.of_exponent_eq_card [CommGroup α] [Finite α] (h : exponent α = Na
t.card α) : IsCyclic α
参数：h : exponent α = Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `isCyclic_of_orderOf_eq_card`：isCyclic_of_orderOf_eq_card [Finite α] (x :
 α) (hx : orderOf x = Nat.card α) : IsCyclic α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.exponent_eq_max'_orderOf`：∀ {G : Type u} [inst : CancelCommMonoid
 G] [inst_1 : Fintype G],   Monoid.exponent G = (Finset.image orderOf Finset.uni
v).max' ⋯
-/
theorem IsCyclic.of_exponent_eq_card [CommGroup α] [Finite α] (h : exponent α = Nat.card α) :
    IsCyclic α :=
  let ⟨_⟩ := nonempty_fintype α
  let ⟨g, _, hg⟩ := Finset.mem_image.mp (Finset.max'_mem _ _)
  isCyclic_of_orderOf_eq_card g <| hg.trans <| exponent_eq_max'_orderOf.symm.trans h

@[to_additive]
/-
**IsCyclic.iff_exponent_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.iff_exponent_eq_card [CommGroup α] [Finite α] : IsCyclic α ↔ expo
nent α = Nat.card α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exponent_eq_card`：IsCyclic.exponent_eq_card [Group α] [IsCyclic
 α] : exponent α = Nat.card α
· 使用定理 `IsCyclic.of_exponent_eq_card`：IsCyclic.of_exponent_eq_card [CommGroup α]
 [Finite α] (h : exponent α = Nat.card α) : IsCyclic α
-/
theorem IsCyclic.iff_exponent_eq_card [CommGroup α] [Finite α] :
    IsCyclic α ↔ exponent α = Nat.card α :=
  ⟨fun _ => IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card⟩

@[to_additive]
/-
**IsCyclic.exponent_eq_zero_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.exponent_eq_zero_of_infinite [Group α] [IsCyclic α] [Infinite α] 
: exponent α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `Monoid.exponent_eq_zero_of_order_zero`：exponent_eq_zero_of_order_zero {g
 : G} (hg : orderOf g = 0) : exponent G = 0
· 使用定理 `Infinite.orderOf_eq_zero_of_forall_mem_zpowers`：Infinite.orderOf_eq_zero
_of_forall_mem_zpowers [Infinite α] {g : α} (h : forall x, x in zpowers g) : ord
erOf g = 0
-/
theorem IsCyclic.exponent_eq_zero_of_infinite [Group α] [IsCyclic α] [Infinite α] :
    exponent α = 0 :=
  let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
  exponent_eq_zero_of_order_zero <| Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg

@[simp]
/-
**ZMod.exponent** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ), AddMonoid.exponent (ZMod n) = n
参数：n : ℕ；ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAddCyclic.exponent_eq_card`：∀ {α : Type u_1} [inst : AddGroup α] [IsAd
dCyclic α], AddMonoid.exponent α = Nat.card α
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
-/
protected theorem ZMod.exponent (n : ℕ) : AddMonoid.exponent (ZMod n) = n := by
  rw [IsAddCyclic.exponent_eq_card, Nat.card_zmod]

/-- A group of order `p ^ 2` is not cyclic if and only if its exponent is `p`. -/
@[to_additive]
/-
**not_isCyclic_iff_exponent_eq_prime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_isCyclic_iff_exponent_eq_prime [Group α] {p : Nat} (hp : p.Prime) (hα 
: Nat.card α = p ^ 2) : ¬ IsCyclic α ↔ Monoid.exponent α = p
参数：hp : p.Prime；hα : Nat.card α = p ^ 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Monoid.exponent_eq_prime_iff`：exponent_eq_prime_iff {G : Type*} [Monoid 
G] [Nontrivial G] {p : Nat} (hp : p.Prime) : Monoid.exponent G = p ↔ forall g : 
G, g != 1 -> order…
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Nat.prime_zero_false`：Nat.Prime 0 → False
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.divisors_prime_pow`：divisors_prime_pow {p : Nat} (pp : p.Prime) (k :
 Nat) : divisors (p ^ k) = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_in
jective pp.t…
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
A group of order `p ^ 2` is not cyclic if and only if its exponent is `p`.
-/
lemma not_isCyclic_iff_exponent_eq_prime [Group α] {p : ℕ} (hp : p.Prime)
    (hα : Nat.card α = p ^ 2) : ¬ IsCyclic α ↔ Monoid.exponent α = p := by
  -- G is a nontrivial fintype of cardinality `p ^ 2`
  have : Finite α := Nat.finite_of_card_ne_zero (hα ▸ pow_ne_zero 2 hp.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp
    (hα ▸ one_lt_pow₀ hp.one_lt two_ne_zero)
  /- in the forward direction, we apply `exponent_eq_prime_iff`, and the reverse direction follows
  immediately because if `α` has exponent `p`, it has no element of order `p ^ 2`. -/
  refine ⟨fun h_cyc ↦ (Monoid.exponent_eq_prime_iff hp).mpr fun g hg ↦ ?_, fun h_exp h_cyc ↦ by
    obtain (rfl | rfl) := eq_zero_or_one_of_sq_eq_self <| hα ▸ h_exp ▸ (h_cyc.exponent_eq_card).symm
    · exact Nat.not_prime_zero hp
    · exact Nat.not_prime_one hp⟩
  /- we must show every non-identity element has order `p`. By Lagrange's theorem, the only possible
  orders of `g` are `1`, `p`, or `p ^ 2`. It can't be the former because `g ≠ 1`, and it can't
  the latter because the group isn't cyclic. -/
  have := (Nat.mem_divisors (m := p ^ 2)).mpr ⟨hα ▸ orderOf_dvd_natCard (x := g), by aesop⟩
  have : ∃ a < 3, p ^ a = orderOf g := by
    simpa [Nat.divisors_prime_pow hp 2] using this
  obtain ⟨a, ha, ha'⟩ := by simpa using this
  interval_cases a
  · exact False.elim <| hg <| orderOf_eq_one_iff.mp <| by simp_all
  · simp_all
  · exact False.elim <| h_cyc <| isCyclic_of_orderOf_eq_card g <| by lia

end Exponent

section ZMod

open Subgroup AddSubgroup

/-- The kernel of `zmultiplesHom G g` is equal to the additive subgroup generated by
`addOrderOf g`. -/
/-
**zmultiplesHom_ker_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmultiplesHom_ker_eq [AddGroup G] (g : G) : (zmultiplesHom G g).ker = zmul
tiples ↑(addOrderOf g)
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_eq_mul'`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ),
 n • a = a * ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The kernel of `zmultiplesHom G g` is equal to the additive subgroup generated by
`addOrderOf g`.
-/
theorem zmultiplesHom_ker_eq [AddGroup G] (g : G) :
    (zmultiplesHom G g).ker = zmultiples ↑(addOrderOf g) := by
  ext
  simp_rw [AddMonoidHom.mem_ker, mem_zmultiples_iff, zmultiplesHom_apply,
    ← addOrderOf_dvd_iff_zsmul_eq_zero, zsmul_eq_mul', Int.cast_id, dvd_def, eq_comm]

/-- The kernel of `zpowersHom G g` is equal to the subgroup generated by `orderOf g`. -/
/-
**zpowersHom_ker_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpowersHom_ker_eq [Group G] (g : G) : (zpowersHom G g).ker = zpowers (Mult
iplicative.ofAdd ↑(orderOf g))
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `zmultiplesHom_ker_eq`：zmultiplesHom_ker_eq [AddGroup G] (g : G) : (zmult
iplesHom G g).ker = zmultiples ↑(addOrderOf g)

--- 原说明 ---
The kernel of `zpowersHom G g` is equal to the subgroup generated by `orderOf g`
.
-/
theorem zpowersHom_ker_eq [Group G] (g : G) :
    (zpowersHom G g).ker = zpowers (Multiplicative.ofAdd ↑(orderOf g)) :=
  congr_arg AddSubgroup.toSubgroup <| zmultiplesHom_ker_eq (Additive.ofMul g)

section addGenerator
variable [AddGroup G] {g : G} (hg : ∀ x, x ∈ zmultiples g) {n : ℕ} (hn : Nat.card G = n)

/-- The isomorphism from `ZMod n` to any additive group of `Nat.card` equal to `n`
generated by a single element `g` which sends `1` to `g`.
See `zmodAddCyclicAddEquiv` for a version which doesn't take an explicit generator,
and instead picks one out with the axiom of choice. -/
/-
**zmodAddEquivOfGenerator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zmodAddEquivOfGenerator : ZMod n ≃+ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from `ZMod n` to any additive group of `Nat.card` equal to `n`
generated by a single element `g` which sends `1` to `g`.
See `zmodAddCyclicAddEquiv` for a version which doesn't take an explicit generat
or,
and instead picks one out with the axiom of choice.
-/
noncomputable def zmodAddEquivOfGenerator : ZMod n ≃+ G :=
  have kereq : zmultiples (n : ℤ) = ((zmultiplesHom G) g).ker := by
    rw [zmultiplesHom_ker_eq, ← Nat.card_zmultiples, ← hn,
      Nat.card_congr (Equiv.subtypeUnivEquiv hg)]
  (Int.quotientZMultiplesNatEquivZMod n).symm.trans <|
    QuotientAddGroup.liftEquiv _ (φ := zmultiplesHom G g) hg kereq

@[simp]
/-
**zmodAddEquivOfGenerator_apply_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodAddEquivOfGenerator_apply_intCast (i : Int) : zmodAddEquivOfGenerator 
hg hn i = i • g
参数：i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用定理 `Int.emod_def`：∀ (a b : ℤ), a % b = a - b * (a / b)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `sub_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m - 
n) • a = m • a + -(n • a)
· 使用定理 `Int.sub_sub_self`：∀ (a b : ℤ), a - (a - b) = b
· 使用定理 `mul_zsmul'`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (m n :
 ℤ), (m * n) • a = n • m • a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `card_nsmul_eq_zero'`：∀ {G : Type u_6} [inst : AddGroup G] {x : G}, Nat.c
ard G • x = 0
· 使用定理 `zsmul_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (n : ℤ), n • 0
 = 0
-/
theorem zmodAddEquivOfGenerator_apply_intCast (i : ℤ) :
    zmodAddEquivOfGenerator hg hn i = i • g := by
  change (ZMod.cast (i : ZMod n) : ℤ) • g = i • g
  rw [ZMod.coe_intCast, Int.emod_def, eq_comm, ← sub_eq_zero, sub_eq_add_neg, ← sub_zsmul,
    Int.sub_sub_self, mul_zsmul', natCast_zsmul, ← hn, card_nsmul_eq_zero', zsmul_zero]

@[simp]
/-
**zmodAddEquivOfGenerator_symm_apply_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodAddEquivOfGenerator_symm_apply_zsmul (i : Int) : (zmodAddEquivOfGenera
tor hg hn).symm (i • g) = i
参数：i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.symm_apply_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, e.symm x = y ↔ x = e y
· 使用定理 `zmodAddEquivOfGenerator_apply_intCast`：zmodAddEquivOfGenerator_apply_int
Cast (i : Int) : zmodAddEquivOfGenerator hg hn i = i • g
-/
theorem zmodAddEquivOfGenerator_symm_apply_zsmul (i : ℤ) :
    (zmodAddEquivOfGenerator hg hn).symm (i • g) = i := by
  rw [AddEquiv.symm_apply_eq, zmodAddEquivOfGenerator_apply_intCast]

@[simp]
/-
**zmodAddEquivOfGenerator_apply_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodAddEquivOfGenerator_apply_one : zmodAddEquivOfGenerator hg hn 1 = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zmodAddEquivOfGenerator_apply_intCast`：zmodAddEquivOfGenerator_apply_int
Cast (i : Int) : zmodAddEquivOfGenerator hg hn i = i • g
-/
theorem zmodAddEquivOfGenerator_apply_one : zmodAddEquivOfGenerator hg hn 1 = g := by
  simpa using zmodAddEquivOfGenerator_apply_intCast hg hn 1

@[simp]
/-
**zmodAddEquivOfGenerator_symm_apply_generator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodAddEquivOfGenerator_symm_apply_generator : (zmodAddEquivOfGenerator hg
 hn).symm g = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `zmodAddEquivOfGenerator_symm_apply_zsmul`：zmodAddEquivOfGenerator_symm_a
pply_zsmul (i : Int) : (zmodAddEquivOfGenerator hg hn).symm (i • g) = i
-/
theorem zmodAddEquivOfGenerator_symm_apply_generator :
    (zmodAddEquivOfGenerator hg hn).symm g = 1 := by
  simpa using zmodAddEquivOfGenerator_symm_apply_zsmul hg hn 1

end addGenerator

/-- An arbitrary isomorphism from `ZMod n` to any cyclic additive group of `Nat.card` equal to `n`.
See `zmodAddCyclicAddEquiv` for a version which doesn't require an explicit generator,
and instead picks one out with the axiom of choice. -/
/-
**zmodAddCyclicAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zmodAddCyclicAddEquiv [AddGroup G] (h : IsAddCyclic G) : ZMod (Nat.card G)
 ≃+ G
参数：h : IsAddCyclic G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddCyclic.exists_generator`：∀ {α : Type u_1} [inst : AddGroup α] [IsAd
dCyclic α], ∃ g, ∀ (x : α), x ∈ AddSubgroup.zmultiples g

--- 原说明 ---
An arbitrary isomorphism from `ZMod n` to any cyclic additive group of `Nat.card
` equal to `n`.
See `zmodAddCyclicAddEquiv` for a version which doesn't require an explicit gene
rator,
and instead picks one out with the axiom of choice.
-/
noncomputable def zmodAddCyclicAddEquiv [AddGroup G] (h : IsAddCyclic G) :
    ZMod (Nat.card G) ≃+ G :=
  zmodAddEquivOfGenerator h.exists_generator.choose_spec rfl

/-- A commutative simple group is isomorphic to `ZMod p` from some prime `p`. -/
/-
**exists_prime_addEquiv_ZMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_prime_addEquiv_ZMod [CommGroup G] [IsSimpleGroup G] : exists p : Na
t, Nat.Prime p ∧ Nonempty (Additive G ≃+ ZMod p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCyclic_iff_exists_zpowers_eq_top`：isCyclic_iff_exists_zpowers_eq_top [
Group α] : IsCyclic α ↔ exists g : α, zpowers g = ⊤
· 使用定理 `IsSimpleGroup.isCyclic`：∀ {α : Type u_1} [inst : CommGroup α] [IsSimpleG
roup α], IsCyclic α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_card_of_zpowers_eq_top`：orderOf_eq_card_of_zpowers_eq_top {g 
: G} (h : Subgroup.zpowers g = ⊤) : orderOf g = Nat.card G
· 使用定理 `IsSimpleGroup.prime_card`：prime_card : (Nat.card α).Prime

--- 原说明 ---
A commutative simple group is isomorphic to `ZMod p` from some prime `p`.
-/
theorem exists_prime_addEquiv_ZMod [CommGroup G] [IsSimpleGroup G] :
    ∃ p : ℕ, Nat.Prime p ∧ Nonempty (Additive G ≃+ ZMod p) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  use orderOf g; rw [orderOf_eq_card_of_zpowers_eq_top hg]
  constructor
  · exact IsSimpleGroup.prime_card
  · exact ⟨(zmodAddCyclicAddEquiv (G := Additive G) inferInstance).symm⟩

section mulGenerator
variable [Group G] {g : G} (hg : ∀ x, x ∈ zpowers g) {n : ℕ} (hn : Nat.card G = n)

/-- The isomorphism from `Multiplicative (ZMod n)` to any multiplicative group
of `Nat.card` equal to `n` generated by a single element `g` which sends
`Multiplicative.ofAdd 1` to `g`.
See `zmodCyclicMulEquiv` for a version which doesn't take an explicit generator,
and instead picks one out with the axiom of choice. -/
/-
**zmodMulEquivOfGenerator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zmodMulEquivOfGenerator : Multiplicative (ZMod n) ≃* G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from `Multiplicative (ZMod n)` to any multiplicative group
of `Nat.card` equal to `n` generated by a single element `g` which sends
`Multiplicative.ofAdd 1` to `g`.
See `zmodCyclicMulEquiv` for a version which doesn't take an explicit generator,
and instead picks one out with the axiom of choice.
-/
noncomputable def zmodMulEquivOfGenerator : Multiplicative (ZMod n) ≃* G :=
  AddEquiv.toMultiplicative <| zmodAddEquivOfGenerator (G := Additive G) hg hn

@[simp]
/-
**zmodMulEquivOfGenerator_apply_ofAdd_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodMulEquivOfGenerator_apply_ofAdd_intCast (i : Int) : zmodMulEquivOfGene
rator hg hn (Multiplicative.ofAdd i) = g ^ i
参数：i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zmodAddEquivOfGenerator_apply_intCast`：zmodAddEquivOfGenerator_apply_int
Cast (i : Int) : zmodAddEquivOfGenerator hg hn i = i • g
-/
theorem zmodMulEquivOfGenerator_apply_ofAdd_intCast (i : ℤ) :
    zmodMulEquivOfGenerator hg hn (Multiplicative.ofAdd i) = g ^ i :=
  zmodAddEquivOfGenerator_apply_intCast (G := Additive G) hg hn i

@[simp]
/-
**zmodMulEquivOfGenerator_symm_apply_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodMulEquivOfGenerator_symm_apply_zpow (i : Int) : (zmodMulEquivOfGenerat
or hg hn).symm (g ^ i) = Multiplicative.ofAdd (i : ZMod n)
参数：i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zmodAddEquivOfGenerator_symm_apply_zsmul`：zmodAddEquivOfGenerator_symm_a
pply_zsmul (i : Int) : (zmodAddEquivOfGenerator hg hn).symm (i • g) = i
-/
theorem zmodMulEquivOfGenerator_symm_apply_zpow (i : ℤ) :
    (zmodMulEquivOfGenerator hg hn).symm (g ^ i) = Multiplicative.ofAdd (i : ZMod n) :=
  zmodAddEquivOfGenerator_symm_apply_zsmul (G := Additive G) hg hn i

@[simp]
/-
**zmodMulEquivOfGenerator_apply_ofAdd_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodMulEquivOfGenerator_apply_ofAdd_one : zmodMulEquivOfGenerator hg hn (M
ultiplicative.ofAdd 1) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zmodAddEquivOfGenerator_apply_one`：zmodAddEquivOfGenerator_apply_one : z
modAddEquivOfGenerator hg hn 1 = g
-/
theorem zmodMulEquivOfGenerator_apply_ofAdd_one :
    zmodMulEquivOfGenerator hg hn (Multiplicative.ofAdd 1) = g :=
  zmodAddEquivOfGenerator_apply_one (G := Additive G) hg hn

@[simp]
/-
**zmodMulEquivOfGenerator_symm_apply_generator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zmodMulEquivOfGenerator_symm_apply_generator : (zmodMulEquivOfGenerator hg
 hn).symm g = Multiplicative.ofAdd 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zmodAddEquivOfGenerator_symm_apply_generator`：zmodAddEquivOfGenerator_sy
mm_apply_generator : (zmodAddEquivOfGenerator hg hn).symm g = 1
-/
theorem zmodMulEquivOfGenerator_symm_apply_generator :
    (zmodMulEquivOfGenerator hg hn).symm g = Multiplicative.ofAdd 1 :=
  zmodAddEquivOfGenerator_symm_apply_generator (G := Additive G) hg hn

end mulGenerator

/-- An arbitrary isomorphism from `Multiplicative (ZMod n)` to any cyclic group
of `Nat.card` equal to `n`.
See `zmodMulEquivOfGenerator` for a version which takes an explicit generator. -/
/-
**zmodCyclicMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zmodCyclicMulEquiv [Group G] (h : IsCyclic G) : Multiplicative (ZMod (Nat.
card G)) ≃* G
参数：h : IsCyclic G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary isomorphism from `Multiplicative (ZMod n)` to any cyclic group
of `Nat.card` equal to `n`.
See `zmodMulEquivOfGenerator` for a version which takes an explicit generator.
-/
noncomputable def zmodCyclicMulEquiv [Group G] (h : IsCyclic G) :
    Multiplicative (ZMod (Nat.card G)) ≃* G :=
  AddEquiv.toMultiplicative <| zmodAddCyclicAddEquiv <| isAddCyclic_additive_iff.2 h

/-- Two cyclic additive groups of the same cardinality are isomorphic. -/
/-
**addEquivOfAddCyclicCardEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：addEquivOfAddCyclicCardEq [AddGroup G] [AddGroup G'] [hG : IsAddCyclic G] 
[hH : IsAddCyclic G'] (hcard : Nat.card G = Nat.card G') : G ≃+ G'
参数：hcard : Nat.card G = Nat.card G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two cyclic additive groups of the same cardinality are isomorphic.
-/
noncomputable def addEquivOfAddCyclicCardEq [AddGroup G] [AddGroup G'] [hG : IsAddCyclic G]
    [hH : IsAddCyclic G'] (hcard : Nat.card G = Nat.card G') : G ≃+ G' := hcard ▸
  zmodAddCyclicAddEquiv hG |>.symm.trans (zmodAddCyclicAddEquiv hH)

/-- Two cyclic groups of the same cardinality are isomorphic. -/
@[to_additive existing]
/-
**mulEquivOfCyclicCardEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivOfCyclicCardEq [Group G] [Group G'] [hG : IsCyclic G] [hH : IsCycl
ic G'] (hcard : Nat.card G = Nat.card G') : G ≃* G'
参数：hcard : Nat.card G = Nat.card G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two cyclic groups of the same cardinality are isomorphic.
-/
noncomputable def mulEquivOfCyclicCardEq [Group G] [Group G'] [hG : IsCyclic G]
    [hH : IsCyclic G'] (hcard : Nat.card G = Nat.card G') : G ≃* G' := hcard ▸
  zmodCyclicMulEquiv hG |>.symm.trans (zmodCyclicMulEquiv hH)

/-- Two groups of the same prime cardinality are isomorphic. -/
@[to_additive /-- Two additive groups of the same prime cardinality are isomorphic. -/]
/-
**mulEquivOfPrimeCardEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivOfPrimeCardEq {p : Nat} [Group G] [Group G'] [Fact p.Prime] (hG : 
Nat.card G = p) (hH : Nat.card G' = p) : G ≃* G'
参数：hG : Nat.card G = p；hH : Nat.card G' = p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_prime_card`：isCyclic_of_prime_card {p : Nat} [hp : Fact p.Pr
ime] (h : Nat.card α = p) : IsCyclic α

--- 原说明 ---
Two groups of the same prime cardinality are isomorphic.
-/
noncomputable def mulEquivOfPrimeCardEq {p : ℕ} [Group G] [Group G']
    [Fact p.Prime] (hG : Nat.card G = p) (hH : Nat.card G' = p) : G ≃* G' := by
  have hGcyc := isCyclic_of_prime_card hG
  have hHcyc := isCyclic_of_prime_card hH
  apply mulEquivOfCyclicCardEq
  exact hG.trans hH.symm

section Infinite

variable [Infinite G]

/-
**zpowersHom_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpowersHom_bijective [Group G] {g : G} (hg : zpowers g = ⊤) : Function.Bij
ective (zpowersHom G g)
参数：hg : zpowers g = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpowersHom_ker_eq`：zpowersHom_ker_eq [Group G] (g : G) : (zpowersHom G g
).ker = zpowers (Multiplicative.ofAdd ↑(orderOf g))
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
-/
lemma zpowersHom_bijective [Group G] {g : G} (hg : zpowers g = ⊤) :
    Function.Bijective (zpowersHom G g) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, MonoidHom.range_eq_top.mp hg⟩
  simp [zpowersHom_ker_eq, ← infinite_zpowers, hg, Set.infinite_univ]

/-- The isomorphism between `Multiplicative ℤ` and the infinite cyclic group `G` sending
`Multiplicative.ofAdd 1` to the generator `g : G`. -/
@[simps! apply]
/-
**intEquivOfZPowersEqTop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：intEquivOfZPowersEqTop [Group G] (g : G) (hg : zpowers g = ⊤) : Multiplica
tive Int ≃* G
参数：g : G；hg : zpowers g = ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `zpowersHom_bijective`：zpowersHom_bijective [Group G] {g : G} (hg : zpowe
rs g = ⊤) : Function.Bijective (zpowersHom G g)

--- 原说明 ---
The isomorphism between `Multiplicative ℤ` and the infinite cyclic group `G` sen
ding
`Multiplicative.ofAdd 1` to the generator `g : G`.
-/
noncomputable def intEquivOfZPowersEqTop [Group G] (g : G) (hg : zpowers g = ⊤) :
    Multiplicative ℤ ≃* G :=
  .ofBijective (zpowersHom G g) (zpowersHom_bijective hg)

@[simp]
/-
**intEquivOfZPowersEqTop_symm_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：intEquivOfZPowersEqTop_symm_self [Group G] {g : G} (hg : zpowers g = ⊤) : 
(intEquivOfZPowersEqTop g hg).symm g = Multiplicative.ofAdd 1
参数：hg : zpowers g = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intEquivOfZPowersEqTop_apply`：∀ {G : Type u_2} [inst : Infinite G] [inst
_1 : Group G] (g : G) (hg : Subgroup.zpowers g = ⊤) (a : Multiplicative ℤ),   (i
ntEquivOfZPowersEq…
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma intEquivOfZPowersEqTop_symm_self [Group G] {g : G} (hg : zpowers g = ⊤) :
    (intEquivOfZPowersEqTop g hg).symm g = Multiplicative.ofAdd 1 := by
  simp [MulEquiv.symm_apply_eq]
/-
**mulintEquivOfZPowersEqTop_symm_apply_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulintEquivOfZPowersEqTop_symm_apply_zpow [Group G] {g : G} (hg : zpowers 
g = ⊤) (k : Int) : (intEquivOfZPowersEqTop g hg).symm (g ^ k) = Multiplicative.o
fAdd k
参数：hg : zpowers g = ⊤；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用引理 `intEquivOfZPowersEqTop_symm_self`：intEquivOfZPowersEqTop_symm_self [Grou
p G] {g : G} (hg : zpowers g = ⊤) : (intEquivOfZPowersEqTop g hg).symm g = Multi
plicative.ofAdd 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulintEquivOfZPowersEqTop_symm_apply_zpow [Group G] {g : G} (hg : zpowers g = ⊤) (k : ℤ) :
    (intEquivOfZPowersEqTop g hg).symm (g ^ k) = Multiplicative.ofAdd k := by
  simp [← ofAdd_zsmul]
/-
**mulintEquivOfZPowersEqTop_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulintEquivOfZPowersEqTop_strictMono [CommGroup G] [PartialOrder G] [IsOrd
eredMonoid G] {g : G} (hg : zpowers g = ⊤) (hg1 : 1 < g) : StrictMono (intEquivO
fZPowersEqTop g hg)
参数：hg : zpowers g = ⊤；hg1 : 1 < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.ofBijective_apply`：∀ {M : Type u_9} {N : Type u_10} {F : Type u
_11} [inst : Mul M] [inst_1 : Mul N] [inst_2 : FunLike F M N]   [inst_3 : MulHom
Class F M N] (f …
· 使用引理 `zpowersHom_bijective`：zpowersHom_bijective [Group G] {g : G} (hg : zpowe
rs g = ⊤) : Function.Bijective (zpowersHom G g)
· 使用引理 `zpow_lt_zpow_right`：zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m 
< a ^ n
-/
lemma mulintEquivOfZPowersEqTop_strictMono [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    {g : G} (hg : zpowers g = ⊤) (hg1 : 1 < g) :
    StrictMono (intEquivOfZPowersEqTop g hg) := by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_lt_zpow_right hg1 hxy
/-
**mulintEquivOfZPowersEqTop_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulintEquivOfZPowersEqTop_strictAnti [CommGroup G] [PartialOrder G] [IsOrd
eredMonoid G] {g : G} (hg : zpowers g = ⊤) (hg1 : g < 1) : StrictAnti (intEquivO
fZPowersEqTop g hg)
参数：hg : zpowers g = ⊤；hg1 : g < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.ofBijective_apply`：∀ {M : Type u_9} {N : Type u_10} {F : Type u
_11} [inst : Mul M] [inst_1 : Mul N] [inst_2 : FunLike F M N]   [inst_3 : MulHom
Class F M N] (f …
· 使用引理 `zpowersHom_bijective`：zpowersHom_bijective [Group G] {g : G} (hg : zpowe
rs g = ⊤) : Function.Bijective (zpowersHom G g)
· 使用引理 `zpow_right_strictAnti`：zpow_right_strictAnti (ha : a < 1) : StrictAnti f
un n : Int => a ^ n
-/
lemma mulintEquivOfZPowersEqTop_strictAnti [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    {g : G} (hg : zpowers g = ⊤) (hg1 : g < 1) :
    StrictAnti (intEquivOfZPowersEqTop g hg) := by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_right_strictAnti hg1 hxy

/-- An infinite cyclic group is isomorphic to `Multiplicative ℤ`. -/
noncomputable
/-
**intCyclicMulEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：intCyclicMulEquiv [Group G] [IsCyclic G] : Multiplicative Int ≃* G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev intCyclicMulEquiv [Group G] [IsCyclic G] : Multiplicative ℤ ≃* G :=
  intEquivOfZPowersEqTop _ (isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic G›).choose_spec
/-
**zmultiplesHom_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zmultiplesHom_bijective [AddGroup G] {g : G} (hg : zmultiples g = ⊤) : Fun
ction.Bijective (zmultiplesHom G g)
参数：hg : zmultiples g = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidHom.ker_eq_bot_iff`：∀ {G : Type u_1} [inst : AddGroup G] {M : T
ype u_7} [inst_1 : AddZeroClass M] (f : G →+ M),   f.ker = ⊥ ↔ Function.Injectiv
e ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zmultiplesHom_ker_eq`：zmultiplesHom_ker_eq [AddGroup G] (g : G) : (zmult
iplesHom G g).ker = zmultiples ↑(addOrderOf g)
· 使用定理 `AddMonoidHom.range_eq_top`：∀ {G : Type u_1} [inst : AddGroup G] {N : Typ
e u_7} [inst_1 : AddGroup N] {f : G →+ N},   f.range = ⊤ ↔ Function.Surjective ⇑
f
-/
lemma zmultiplesHom_bijective [AddGroup G] {g : G} (hg : zmultiples g = ⊤) :
    Function.Bijective (zmultiplesHom G g) := by
  refine ⟨(AddMonoidHom.ker_eq_bot_iff _).mp ?_, AddMonoidHom.range_eq_top.mp hg⟩
  simp [zmultiplesHom_ker_eq, ← infinite_zmultiples, hg, Set.infinite_univ]

/-- The isomorphism between `ℤ` and the infinite cyclic group `G` sending
`1` to the generator `g : G`. -/
@[simps! apply]
/-
**intEquivOfZMultiplesEqTop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：intEquivOfZMultiplesEqTop [AddGroup G] (g : G) (hg : zmultiples g = ⊤) : I
nt ≃+ G
参数：g : G；hg : zmultiples g = ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `zmultiplesHom_bijective`：zmultiplesHom_bijective [AddGroup G] {g : G} (h
g : zmultiples g = ⊤) : Function.Bijective (zmultiplesHom G g)

--- 原说明 ---
The isomorphism between `ℤ` and the infinite cyclic group `G` sending
`1` to the generator `g : G`.
-/
noncomputable def intEquivOfZMultiplesEqTop [AddGroup G] (g : G) (hg : zmultiples g = ⊤) : ℤ ≃+ G :=
  .ofBijective (zmultiplesHom G g) (zmultiplesHom_bijective hg)

@[simp]
/-
**intEquivOfZMultiplesEqTop_symm_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：intEquivOfZMultiplesEqTop_symm_self [AddGroup G] (g : G) (hg : zmultiples 
g = ⊤) : (intEquivOfZMultiplesEqTop g hg).symm g = 1
参数：g : G；hg : zmultiples g = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intEquivOfZMultiplesEqTop_apply`：∀ {G : Type u_2} [inst : Infinite G] [i
nst_1 : AddGroup G] (g : G) (hg : AddSubgroup.zmultiples g = ⊤) (a : ℤ),   (intE
quivOfZMultiplesEqTop…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma intEquivOfZMultiplesEqTop_symm_self [AddGroup G] (g : G) (hg : zmultiples g = ⊤) :
    (intEquivOfZMultiplesEqTop g hg).symm g = 1 := by
  simp [AddEquiv.symm_apply_eq]
/-
**intEquivOfZMultiplesEqTop_symm_apply_zsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：intEquivOfZMultiplesEqTop_symm_apply_zsmul [AddGroup G] {g : G} (hg : zmul
tiples g = ⊤) (k : Int) : (intEquivOfZMultiplesEqTop g hg).symm (k • g) = k
参数：hg : zmultiples g = ⊤；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用引理 `intEquivOfZMultiplesEqTop_symm_self`：intEquivOfZMultiplesEqTop_symm_self
 [AddGroup G] (g : G) (hg : zmultiples g = ⊤) : (intEquivOfZMultiplesEqTop g hg)
.symm g = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma intEquivOfZMultiplesEqTop_symm_apply_zsmul [AddGroup G]
    {g : G} (hg : zmultiples g = ⊤) (k : ℤ) :
    (intEquivOfZMultiplesEqTop g hg).symm (k • g) = k := by
  simp

/-- An infinite cyclic additive group is isomorphic to `ℤ`. -/
noncomputable
/-
**intCyclicAddEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：intCyclicAddEquiv [AddGroup G] [IsAddCyclic G] : Int ≃+ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev intCyclicAddEquiv [AddGroup G] [IsAddCyclic G] : ℤ ≃+ G :=
  intEquivOfZMultiplesEqTop _ (isAddCyclic_iff_exists_zmultiples_eq_top.mp ‹_›).choose_spec

end Infinite

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
variable (G) in
/-- The automorphism group of a cyclic group is isomorphic to the multiplicative group of ZMod. -/
@[simps!]
/-
**IsCyclic.mulAutMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCyclic.mulAutMulEquiv [Group G] [h : IsCyclic G] : MulAut G ≃* (ZMod (Na
t.card G))ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The automorphism group of a cyclic group is isomorphic to the multiplicative gro
up of ZMod.
-/
noncomputable def IsCyclic.mulAutMulEquiv [Group G] [h : IsCyclic G] :
    MulAut G ≃* (ZMod (Nat.card G))ˣ :=
  ((MulAut.congr (zmodCyclicMulEquiv h)).symm.trans
    (MulAutMultiplicative (ZMod (Nat.card G)))).trans
      (ZMod.AddAutEquivUnits (Nat.card G)).toMultiplicative

variable (G) in
/-
**IsCyclic.card_mulAut** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.card_mulAut [Group G] [Finite G] [h : IsCyclic G] : Nat.card (Mul
Aut G) = Nat.totient (Nat.card G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroCardOfNonemptyOfFinite`：∀ {α : Type u_1} [Nonempty α] [Fin
ite α], NeZero (Nat.card α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem IsCyclic.card_mulAut [Group G] [Finite G] [h : IsCyclic G] :
    Nat.card (MulAut G) = Nat.totient (Nat.card G) := by
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulAutMulEquiv G)

end ZMod

section powMonoidHom

variable (G)

-- Note. Even though cyclic groups only require `[Group G]`, we need `[CommGroup G]` for
-- `powMonoidHom` to be defined.

@[to_additive]
/-
**IsCyclic.card_powMonoidHom_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.card_powMonoidHom_range [CommGroup G] [hG : IsCyclic G] [Finite G
] (d : Nat) : Nat.card (powMonoidHom d : G ->* G).range = Nat.card G / (Nat.card
 G).gcd d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCyclic_iff_exists_zpowers_eq_top`：isCyclic_iff_exists_zpowers_eq_top [
Group α] : IsCyclic α ↔ exists g : α, zpowers g = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_zpowers`：MonoidHom.map_zpowers (f : G ->* N) (x : G) : (Su
bgroup.zpowers x).map f = Subgroup.zpowers (f x)
· 使用定理 `Nat.card_zpowers`：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
· 使用定理 `powMonoidHom_apply`：∀ {α : Type u_1} [inst : CommMonoid α] (n : ℕ) (x : 
α), (powMonoidHom n) x = x ^ n
· 使用定理 `orderOf_pow`：orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / Nat.gcd
 (orderOf x) n
· 使用定理 `orderOf_eq_card_of_zpowers_eq_top`：orderOf_eq_card_of_zpowers_eq_top {g 
: G} (h : Subgroup.zpowers g = ⊤) : orderOf g = Nat.card G
-/
theorem IsCyclic.card_powMonoidHom_range [CommGroup G] [hG : IsCyclic G] [Finite G] (d : ℕ) :
    Nat.card (powMonoidHom d : G →* G).range = Nat.card G / (Nat.card G).gcd d := by
  obtain ⟨g, h⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  rw [MonoidHom.range_eq_map, ← h, MonoidHom.map_zpowers, Nat.card_zpowers, powMonoidHom_apply,
    orderOf_pow, orderOf_eq_card_of_zpowers_eq_top h]

@[to_additive]
/-
**IsCyclic.index_powMonoidHom_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.index_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d :
 Nat) : (powMonoidHom d : G ->* G).ker.index = Nat.card G / (Nat.card G).gcd d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_ker`：index_ker (f : G ->* G') : f.ker.index = Nat.card f.
range
· 使用定理 `IsCyclic.card_powMonoidHom_range`：IsCyclic.card_powMonoidHom_range [Comm
Group G] [hG : IsCyclic G] [Finite G] (d : Nat) : Nat.card (powMonoidHom d : G -
>* G).range = Nat.card…
-/
theorem IsCyclic.index_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d : ℕ) :
    (powMonoidHom d : G →* G).ker.index = Nat.card G / (Nat.card G).gcd d := by
  rw [Subgroup.index_ker, card_powMonoidHom_range]

@[to_additive]
/-
**IsCyclic.card_powMonoidHom_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.card_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d : 
Nat) : Nat.card (powMonoidHom d : G ->* G).ker = (Nat.card G).gcd d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.index_ne_zero_of_finite`：index_ne_zero_of_finite [hH : Finite (
G ⧸ H)] : H.index != 0
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `IsCyclic.index_powMonoidHom_ker`：IsCyclic.index_powMonoidHom_ker [CommGr
oup G] [IsCyclic G] [Finite G] (d : Nat) : (powMonoidHom d : G ->* G).ker.index 
= Nat.card G / (Nat.c…
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
-/
theorem IsCyclic.card_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d : ℕ) :
    Nat.card (powMonoidHom d : G →* G).ker = (Nat.card G).gcd d := by
  have h : (powMonoidHom d : G →* G).ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← mul_left_inj' h, Subgroup.card_mul_index, index_powMonoidHom_ker, Nat.mul_div_cancel']
  exact Nat.gcd_dvd_left (Nat.card G) d

@[to_additive]
/-
**IsCyclic.index_powMonoidHom_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.index_powMonoidHom_range [CommGroup G] [IsCyclic G] [Finite G] (d
 : Nat) : (powMonoidHom d : G ->* G).range.index = (Nat.card G).gcd d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_range`：index_range {f : G ->* G} [hf : f.ker.FiniteIndex]
 : f.range.index = Nat.card f.ker
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `IsCyclic.card_powMonoidHom_ker`：IsCyclic.card_powMonoidHom_ker [CommGrou
p G] [IsCyclic G] [Finite G] (d : Nat) : Nat.card (powMonoidHom d : G ->* G).ker
 = (Nat.card G).gcd …
-/
theorem IsCyclic.index_powMonoidHom_range [CommGroup G] [IsCyclic G] [Finite G] (d : ℕ) :
    (powMonoidHom d : G →* G).range.index = (Nat.card G).gcd d := by
  rw [Subgroup.index_range, card_powMonoidHom_ker]

end powMonoidHom

section generator

/-!
### Groups with a given generator

We state some results in terms of an explicitly given generator.
The generating property is given as in `IsCyclic.exists_generator`.

The main statements are about the existence and uniqueness of homomorphisms and isomorphisms
specified by the image of the given generator.
-/

open Subgroup

variable [Group G] [Group G'] {g : G} (hg : ∀ x, x ∈ zpowers g) {g' : G'}

section monoidHom

variable (hg' : orderOf g' ∣ orderOf (g : G))

/-- If `g` generates the group `G` and `g'` is an element of another group `G'` whose order
divides that of `g`, then there is a homomorphism `G →* G'` mapping `g` to `g'`. -/
@[to_additive
/-- If `g` generates the additive group `G` and `g'` is an element of another additive group `G'`
whose order divides that of `g`, then there is a homomorphism `G →+ G'` mapping `g` to `g'`. -/]
noncomputable
/-
**monoidHomOfForallMemZpowers** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monoidHomOfForallMemZpowers : G ->* G' where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomOfForallMemZpowers : G →* G' where
  toFun x := g' ^ (Classical.choose <| mem_zpowers_iff.mp <| hg x)
  map_one' := orderOf_dvd_iff_zpow_eq_one.mp <|
                (Int.natCast_dvd_natCast.mpr hg').trans <| orderOf_dvd_iff_zpow_eq_one.mpr <|
                Classical.choose_spec <| mem_zpowers_iff.mp <| hg 1
  map_mul' x y := by
    simp only [← zpow_add, zpow_eq_zpow_iff_modEq]
    apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
    rw [← zpow_eq_zpow_iff_modEq, zpow_add]
    simp only [fun x ↦ Classical.choose_spec <| mem_zpowers_iff.mp <| hg x]

@[to_additive (attr := simp)]
/-
**monoidHomOfForallMemZpowers_apply_gen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monoidHomOfForallMemZpowers_apply_gen : monoidHomOfForallMemZpowers hg hg'
 g = g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `zpow_eq_zpow_iff_modEq`：zpow_eq_zpow_iff_modEq {m n : Int} : x ^ m = x ^
 n ↔ m ≡ n [ZMOD orderOf x]
· 使用定理 `Int.ModEq.of_dvd`：∀ {m n a b : ℤ}, m ∣ n → a ≡ b [ZMOD n] → a ≡ b [ZMOD 
m]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
-/
lemma monoidHomOfForallMemZpowers_apply_gen :
    monoidHomOfForallMemZpowers hg hg' g = g' := by
  simp only [monoidHomOfForallMemZpowers, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← zpow_one g']
  rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
  rw [← zpow_eq_zpow_iff_modEq, zpow_one]
  exact Classical.choose_spec <| mem_zpowers_iff.mp <| hg g

end monoidHom

include hg in
/-- Two group homomorphisms `G →* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
/-- Two homomorphisms `G →+ G'` of additive groups are equal if and only if they agree
on a generator of `G`. -/]
/-
**MonoidHom.eq_iff_eq_on_generator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G ->* G') : f₁ = f₂ ↔ f₁ g = f₂ 
g
参数：f₁ f₂ : G ->* G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
-/
lemma MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G →* G') : f₁ = f₂ ↔ f₁ g = f₂ g := by
  rw [DFunLike.ext_iff]
  refine ⟨fun H ↦ H g, fun H x ↦ ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp <| hg x
  rw [← hn, map_zpow, map_zpow, H]

include hg in
/-- Two group isomorphisms `G ≃* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
/-- Two isomorphisms `G ≃+ G'` of additive groups are equal if and only if they agree
on a generator of `G`. -/]
/-
**MulEquiv.eq_iff_eq_on_generator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulEquiv.eq_iff_eq_on_generator (f₁ f₂ : G ≃* G') : f₁ = f₂ ↔ f₁ g = f₂ g
参数：f₁ f₂ : G ≃* G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulEquiv.toMonoidHom_injective`：toMonoidHom_injective : Injective (toMon
oidHom : M ≃* N -> M ->* N)
· 使用引理 `MonoidHom.eq_iff_eq_on_generator`：MonoidHom.eq_iff_eq_on_generator (f₁ f
₂ : G ->* G') : f₁ = f₂ ↔ f₁ g = f₂ g
-/
lemma MulEquiv.eq_iff_eq_on_generator (f₁ f₂ : G ≃* G') : f₁ = f₂ ↔ f₁ g = f₂ g :=
  (Function.Injective.eq_iff toMonoidHom_injective).symm.trans <|
    MonoidHom.eq_iff_eq_on_generator hg ..

section mulEquiv

variable (hg' : ∀ x, x ∈ zpowers g') (h : orderOf g = orderOf g')

/-- Given two groups that are generated by elements `g` and `g'` of the same order,
we obtain an isomorphism sending `g` to `g'`. -/
@[to_additive
/-- Given two additive groups that are generated by elements `g` and `g'` of the same order,
we obtain an isomorphism sending `g` to `g'`. -/]
noncomputable
/-
**mulEquivOfOrderOfEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivOfOrderOfEq : G ≃* G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEquivOfOrderOfEq : G ≃* G' :=
  (monoidHomOfForallMemZpowers hg h.symm.dvd).toMulEquiv (monoidHomOfForallMemZpowers hg' h.dvd)
    (by simp [MonoidHom.eq_iff_eq_on_generator hg]) (by simp [MonoidHom.eq_iff_eq_on_generator hg'])

@[to_additive (attr := simp)]
/-
**mulEquivOfOrderOfEq_apply_gen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulEquivOfOrderOfEq_apply_gen : mulEquivOfOrderOfEq hg hg' h g = g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monoidHomOfForallMemZpowers_apply_gen`：monoidHomOfForallMemZpowers_apply
_gen : monoidHomOfForallMemZpowers hg hg' g = g'
· 使用定理 `Eq.dvd`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a = b → a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mulEquivOfOrderOfEq_apply_gen : mulEquivOfOrderOfEq hg hg' h g = g' :=
  monoidHomOfForallMemZpowers_apply_gen hg h.symm.dvd

@[to_additive (attr := simp)]
/-
**mulEquivOfOrderOfEq_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulEquivOfOrderOfEq_symm : (mulEquivOfOrderOfEq hg hg' h).symm = mulEquivO
fOrderOfEq hg' hg h.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulEquivOfOrderOfEq_symm :
    (mulEquivOfOrderOfEq hg hg' h).symm = mulEquivOfOrderOfEq hg' hg h.symm := rfl

@[to_additive] -- `simp` can prove this by a combination of the two preceding lemmas
/-
**mulEquivOfOrderOfEq_symm_apply_gen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulEquivOfOrderOfEq_symm_apply_gen : (mulEquivOfOrderOfEq hg hg' h).symm g
' = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monoidHomOfForallMemZpowers_apply_gen`：monoidHomOfForallMemZpowers_apply
_gen : monoidHomOfForallMemZpowers hg hg' g = g'
· 使用定理 `Eq.dvd`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a = b → a ∣ b
-/
lemma mulEquivOfOrderOfEq_symm_apply_gen : (mulEquivOfOrderOfEq hg hg' h).symm g' = g :=
  monoidHomOfForallMemZpowers_apply_gen hg' h.dvd

end mulEquiv

end generator

section prod

/-
**Group.isCyclic_of_coprime_card_range_card_ker** 是 Mathlib 中的一个定理，位于命名空间 `Group
`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : CommGroup M] [inst_1 : Group N] (f
 : M →* N),   (Nat.card ↥f.ker).Coprime (Nat.card ↥f.range) → ∀ [IsCyclic ↥f.ker
] [IsCyclic ↥f.range], IsCyclic M
参数：f : M →* N；Nat.card ↥f.ker；Nat.card ↥f.range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.isCyclic`：MulEquiv.isCyclic (e : G ≃* G') : IsCyclic G ↔ IsCycl
ic G'
· 使用定理 `MonoidHom.ker_eq_top_iff`：∀ {G : Type u_1} [inst : Group G] {M : Type u_
7} [inst_1 : MulOneClass M] {f : G →* M}, f.ker = ⊤ ↔ f = 1
· 使用定理 `MonoidHom.range_eq_bot_iff`：∀ {G : Type u_1} {G' : Type u_2} [inst : Gro
up G] [inst_1 : Group G'] {f : G →* G'}, f.range = ⊥ ↔ f = 1
· 使用定理 `Subgroup.eq_bot_iff_card`：∀ {G : Type u_1} [inst : Group G] (H : Subgrou
p G), H = ⊥ ↔ Nat.card ↥H = 1
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `Subgroup.eq_bot_of_card_eq`：eq_bot_of_card_eq (h : Nat.card H = 1) : H =
 ⊥
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.finite_iff_finite_ker_range`：∀ {G : Type u_1} {G' : Type u_2} 
[inst : Group G] [inst_1 : Group G'] (f : G →* G'),   Finite G ↔ Finite ↥f.ker ∧
 Finite ↥f.range
· 使用定理 `IsCyclic.iff_exponent_eq_card`：IsCyclic.iff_exponent_eq_card [CommGroup 
α] [Finite α] : IsCyclic α ↔ exponent α = Nat.card α
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Group.exponent_dvd_nat_card`：Group.exponent_dvd_nat_card : Monoid.expone
nt G ∣ Nat.card G
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `Subgroup.index_ker`：index_ker (f : G ->* G') : f.ker.index = Nat.card f.
range
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `IsCyclic.exponent_eq_card`：IsCyclic.exponent_eq_card [Group α] [IsCyclic
 α] : exponent α = Nat.card α
· 使用定理 `Monoid.exponent_dvd_of_monoidHom`：exponent_dvd_of_monoidHom (e : G ->* H
) (e_inj : Function.Injective e) : Monoid.exponent G ∣ Monoid.exponent H
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
· 使用定理 `MonoidHom.exponent_dvd`：MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid
 M₁] [Monoid M₂] [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {f : F} (hf : Functi
on.Surjectiv…
· 使用定理 `MonoidHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : G ->* 
N) : Function.Surjective f.rangeRestrict
-/
@[to_additive] theorem Group.isCyclic_of_coprime_card_range_card_ker {M N : Type*}
    [CommGroup M] [Group N] (f : M →* N) (h : (Nat.card f.ker).Coprime (Nat.card f.range))
    [IsCyclic f.ker] [IsCyclic f.range] : IsCyclic M := by
  cases (finite_or_infinite f.ker).symm
  · rw [Nat.card_eq_zero_of_infinite, Nat.coprime_zero_left] at h
    rw [← f.range.eq_bot_iff_card, f.range_eq_bot_iff, ← f.ker_eq_top_iff] at h
    rwa [← Subgroup.topEquiv.isCyclic, ← h]
  cases (finite_or_infinite f.range).symm
  · rw [Nat.card_eq_zero_of_infinite (α := f.range), Nat.coprime_zero_right] at h
    rwa [(f.ofInjective (f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq h))).isCyclic]
  have := f.finite_iff_finite_ker_range.mpr ⟨‹_›, ‹_›⟩
  rw [IsCyclic.iff_exponent_eq_card]
  apply dvd_antisymm Group.exponent_dvd_nat_card
  rw [← f.ker.card_mul_index, Subgroup.index_ker]
  apply h.mul_dvd_of_dvd_of_dvd <;> rw [← IsCyclic.exponent_eq_card]
  · exact Monoid.exponent_dvd_of_monoidHom _ f.ker.subtype_injective
  · exact MonoidHom.exponent_dvd f.rangeRestrict_surjective
/-
**Group.isCyclic_of_coprime_card_ker** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : CommGroup M] [inst_1 : Group N] (f
 : M →* N),   (Nat.card ↥f.ker).Coprime (Nat.card N) → ∀ [IsCyclic ↥f.ker] [hN :
 IsCyclic N], Function.Surjective ⇑f → IsCyclic M
参数：f : M →* N；Nat.card ↥f.ker；Nat.card N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.isCyclic_of_coprime_card_range_card_ker`：∀ {M : Type u_4} {N : Typ
e u_5} [inst : CommGroup M] [inst_1 : Group N] (f : M →* N),   (Nat.card ↥f.ker)
.Coprime (Nat.card ↥f.range) → ∀ [I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `Subgroup.card_top`：card_top : Nat.card (⊤ : Subgroup G) = Nat.card G
· 使用定理 `MulEquiv.isCyclic`：MulEquiv.isCyclic (e : G ≃* G') : IsCyclic G ↔ IsCycl
ic G'
-/
@[to_additive] theorem Group.isCyclic_of_coprime_card_ker {M N : Type*}
    [CommGroup M] [Group N] (f : M →* N) (h : (Nat.card f.ker).Coprime (Nat.card N))
    [IsCyclic f.ker] [hN : IsCyclic N] (hf : Function.Surjective f) : IsCyclic M := by
  rw [← Subgroup.topEquiv.isCyclic, ← f.range_eq_top.mpr hf] at hN
  rw [← Subgroup.card_top (G := N), ← f.range_eq_top.mpr hf] at h
  exact isCyclic_of_coprime_card_range_card_ker f h

section

variable (M N : Type*) [Group M] [Group N] [cyc : IsCyclic (M × N)]
include M N

/-
**isCyclic_left_of_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (M : Type u_4) (N : Type u_5) [inst : Group M] [inst_1 : Group N] [cyc :
 IsCyclic (M × N)], IsCyclic M
参数：M : Type u_4；N : Type u_5；M × N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
@[to_additive isAddCyclic_left_of_prod] theorem isCyclic_left_of_prod : IsCyclic M :=
    isCyclic_of_surjective (MonoidHom.fst M N) Prod.fst_surjective
/-
**isCyclic_right_of_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (M : Type u_4) (N : Type u_5) [inst : Group M] [inst_1 : Group N] [cyc :
 IsCyclic (M × N)], IsCyclic N
参数：M : Type u_4；N : Type u_5；M × N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
@[to_additive isAddCyclic_right_of_prod] theorem isCyclic_right_of_prod : IsCyclic N :=
    isCyclic_of_surjective (MonoidHom.snd M N) Prod.snd_surjective
/-
**coprime_card_of_isCyclic_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (M : Type u_4) (N : Type u_5) [inst : Group M] [inst_1 : Group N] [cyc :
 IsCyclic (M × N)] [Finite M] [Finite N],   (Nat.card M).Coprime (Nat.card N)
参数：M : Type u_4；N : Type u_5；M × N；Nat.card M；Nat.card N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_left_of_prod`：∀ (M : Type u_4) (N : Type u_5) [inst : Group M] 
[inst_1 : Group N] [cyc : IsCyclic (M × N)], IsCyclic M
· 使用定理 `isCyclic_right_of_prod`：∀ (M : Type u_4) (N : Type u_5) [inst : Group M]
 [inst_1 : Group N] [cyc : IsCyclic (M × N)], IsCyclic N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsCyclic.iff_exponent_eq_card`：IsCyclic.iff_exponent_eq_card [CommGroup 
α] [Finite α] : IsCyclic α ↔ exponent α = Nat.card α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `lcm_eq_nat_lcm`：lcm_eq_nat_lcm (m n : Nat) : lcm m n = Nat.lcm m n
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Monoid.exponent_prod`：Monoid.exponent_prod {M₁ M₂ : Type*} [Monoid M₁] [
Monoid M₂] : exponent (M₁ × M₂) = lcm (exponent M₁) (exponent M₂)
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
-/
@[to_additive coprime_card_of_isAddCyclic_prod] theorem coprime_card_of_isCyclic_prod
    [Finite M] [Finite N] : (Nat.card M).Coprime (Nat.card N) := by
  have hM := isCyclic_left_of_prod M N
  have hN := isCyclic_right_of_prod M N
  let _ := cyc.commGroup; let _ := hM.commGroup; let _ := hN.commGroup
  rw [IsCyclic.iff_exponent_eq_card, Monoid.exponent_prod, Nat.card_prod, lcm_eq_nat_lcm] at *
  simpa only [hM, hN, Nat.lcm_eq_mul_iff, Nat.card_pos.ne', false_or] using cyc

end

/-
**not_isAddCyclic_prod_of_infinite_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isAddCyclic_prod_of_infinite_nontrivial (M N : Type*) [AddGroup M] [Ad
dGroup N] [Infinite M] [Nontrivial N] : ¬ IsAddCyclic (M × N)
参数：M N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `ZMod.castHom_surjective`：castHom_surjective (h : m ∣ n) : Function.Surje
ctive (castHom h (ZMod m))
· 使用定理 `isAddCyclic_of_surjective`：∀ {G : Type u_2} {G' : Type u_3} [inst : AddG
roup G] [inst_1 : AddGroup G'] {F : Type u_4} [hH : IsAddCyclic G']   [inst_2 : 
FunLike F G' G]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddEquiv.isAddCyclic`：∀ {G : Type u_2} {G' : Type u_3} [inst : AddGroup 
G] [inst_1 : AddGroup G'] (e : G ≃+ G'),   IsAddCyclic G ↔ IsAddCyclic G'
· 使用定理 `isAddCyclic_left_of_prod`：∀ (M : Type u_4) (N : Type u_5) [inst : AddGro
up M] [inst_1 : AddGroup N] [cyc : IsAddCyclic (M × N)], IsAddCyclic M
· 使用定理 `isAddCyclic_right_of_prod`：∀ (M : Type u_4) (N : Type u_5) [inst : AddGr
oup M] [inst_1 : AddGroup N] [cyc : IsAddCyclic (M × N)], IsAddCyclic N
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.map_surjective`：map_surjective [Nonempty γ] [Nonempty δ] {f : α -> 
γ} {g : β -> δ} : Surjective (map f g) ↔ Surjective f ∧ Surjective g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `coprime_card_of_isAddCyclic_prod`：∀ (M : Type u_4) (N : Type u_5) [inst 
: AddGroup M] [inst_1 : AddGroup N] [cyc : IsAddCyclic (M × N)] [Finite M]   [Fi
nite N], (Nat.card M).…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `Nat.instNeZeroCardOfNonemptyOfFinite`：∀ {α : Type u_1} [Nonempty α] [Fin
ite α], NeZero (Nat.card α)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
-/
theorem not_isAddCyclic_prod_of_infinite_nontrivial (M N : Type*) [AddGroup M] [AddGroup N]
    [Infinite M] [Nontrivial N] : ¬ IsAddCyclic (M × N) := fun hMN ↦ by
  rw [← ((zmodAddCyclicAddEquiv <| isAddCyclic_left_of_prod M N).prodCongr (zmodAddCyclicAddEquiv <|
    isAddCyclic_right_of_prod M N)).isAddCyclic, Nat.card_eq_zero_of_infinite] at hMN
  cases (finite_or_infinite N).symm
  · rw [Nat.card_eq_zero_of_infinite] at hMN
    let f := (ZMod.castHom (dvd_zero _) (ZMod 2)).toAddMonoidHom
    have hf := ZMod.castHom_surjective (dvd_zero 2)
    have := isAddCyclic_of_surjective (f.prodMap f) (Prod.map_surjective.mpr ⟨hf, hf⟩)
    simpa using coprime_card_of_isAddCyclic_prod (ZMod 2) (ZMod 2)
  let ZN := ZMod (Nat.card N)
  have := isAddCyclic_of_surjective ((ZMod.castHom (dvd_zero _) ZN).toAddMonoidHom.prodMap (.id ZN))
    (Prod.map_surjective.mpr ⟨ZMod.castHom_surjective (dvd_zero _), Function.surjective_id⟩)
  exact Finite.one_lt_card (α := N).ne' (by simpa [ZN] using coprime_card_of_isAddCyclic_prod ZN ZN)

@[to_additive existing not_isAddCyclic_prod_of_infinite_nontrivial]
/-
**not_isCyclic_prod_of_infinite_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isCyclic_prod_of_infinite_nontrivial (M N : Type*) [Group M] [Group N]
 [Infinite M] [Nontrivial N] : ¬ IsCyclic (M × N)
参数：M N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isAddCyclic_additive_iff`：isAddCyclic_additive_iff [DivInvMonoid α] : Is
AddCyclic (Additive α) ↔ IsCyclic α
· 使用定理 `AddEquiv.isAddCyclic`：∀ {G : Type u_2} {G' : Type u_3} [inst : AddGroup 
G] [inst_1 : AddGroup G'] (e : G ≃+ G'),   IsAddCyclic G ↔ IsAddCyclic G'
· 使用定理 `not_isAddCyclic_prod_of_infinite_nontrivial`：not_isAddCyclic_prod_of_inf
inite_nontrivial (M N : Type*) [AddGroup M] [AddGroup N] [Infinite M] [Nontrivia
l N] : ¬ IsAddCyclic (M × N)
· 使用定理 `instInfiniteAdditive`：∀ {α : Type u} [h : Infinite α], Infinite (Additiv
e α)
-/
theorem not_isCyclic_prod_of_infinite_nontrivial (M N : Type*) [Group M] [Group N]
    [Infinite M] [Nontrivial N] : ¬ IsCyclic (M × N) := by
  rw [← isAddCyclic_additive_iff, (AddEquiv.prodAdditive ..).isAddCyclic]
  apply not_isAddCyclic_prod_of_infinite_nontrivial

/-- The product of two finite groups is cyclic iff
both of them are cyclic and their orders are coprime. -/
@[to_additive AddGroup.isAddCyclic_prod_iff /-- The product of two finite additive groups is cyclic
iff both of them are cyclic and their orders are coprime. -/]
/-
**Group.isCyclic_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.isCyclic_prod_iff {M N : Type*} [Group M] [Group N] : IsCyclic (M × 
N) ↔ IsCyclic M ∧ IsCyclic N ∧ (Nat.card M).Coprime (Nat.card N)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_left_of_prod`：∀ (M : Type u_4) (N : Type u_5) [inst : Group M] 
[inst_1 : Group N] [cyc : IsCyclic (M × N)], IsCyclic M
· 使用定理 `isCyclic_right_of_prod`：∀ (M : Type u_4) (N : Type u_5) [inst : Group M]
 [inst_1 : Group N] [cyc : IsCyclic (M × N)], IsCyclic N
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Nat.coprime_one_right_eq_true`：∀ (n : ℕ), n.Coprime 1 = True
· 使用定理 `not_isCyclic_prod_of_infinite_nontrivial`：not_isCyclic_prod_of_infinite_
nontrivial (M N : Type*) [Group M] [Group N] [Infinite M] [Nontrivial N] : ¬ IsC
yclic (M × N)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulEquiv.isCyclic`：MulEquiv.isCyclic (e : G ≃* G') : IsCyclic G ↔ IsCycl
ic G'
· 使用定理 `coprime_card_of_isCyclic_prod`：∀ (M : Type u_4) (N : Type u_5) [inst : G
roup M] [inst_1 : Group N] [cyc : IsCyclic (M × N)] [Finite M] [Finite N],   (Na
t.card M).Coprime (…
· 使用引理 `MonoidHom.ker_snd`：ker_snd : ker (snd G G') = .prod ⊤ ⊥
· 使用定理 `Group.isCyclic_of_coprime_card_ker`：∀ {M : Type u_4} {N : Type u_5} [ins
t : CommGroup M] [inst_1 : Group N] (f : M →* N),   (Nat.card ↥f.ker).Coprime (N
at.card N) → ∀ [IsCyclic…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
theorem Group.isCyclic_prod_iff {M N : Type*} [Group M] [Group N] :
    IsCyclic (M × N) ↔ IsCyclic M ∧ IsCyclic N ∧ (Nat.card M).Coprime (Nat.card N) := by
  refine ⟨fun h ↦ ⟨isCyclic_left_of_prod M N, isCyclic_right_of_prod M N, ?_⟩, fun ⟨hM, hN, h⟩ ↦ ?_⟩
  · cases (finite_or_infinite M).symm
    · cases subsingleton_or_nontrivial N; · simp
      exact (not_isCyclic_prod_of_infinite_nontrivial M N h).elim
    cases (finite_or_infinite N).symm
    · cases subsingleton_or_nontrivial M; · simp
      rw [(MulEquiv.prodComm ..).isCyclic] at h
      exact (not_isCyclic_prod_of_infinite_nontrivial N M h).elim
    apply coprime_card_of_isCyclic_prod
  · let f := MonoidHom.snd M N
    let e : f.ker ≃* M := by
      rw [MonoidHom.ker_snd]
      exact ((Subgroup.prodEquiv ..).trans .prodUnique).trans Subgroup.topEquiv
    let _ := hM.commGroup; let _ := hN.commGroup
    rw [← e.isCyclic] at hM
    rw [← Nat.card_congr e.toEquiv] at h
    exact isCyclic_of_coprime_card_ker f h Prod.snd_surjective

end prod

section WithZero

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : Type*) [Group G] [IsCyclic G] : IsCyclic (WithZero G)ˣ := by
  apply isCyclic_of_injective (G := (WithZero G)ˣ) (WithZero.unitsWithZeroEquiv).toMonoidHom
  apply Equiv.injective

end WithZero

