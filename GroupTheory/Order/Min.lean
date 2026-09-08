/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Minimum order of an element

This file defines the minimum order of an element of a monoid.

## Main declarations

* `Monoid.minOrder`: The minimum order of an element of a given monoid.
* `Monoid.minOrder_eq_top`: The minimum order is infinite iff the monoid is torsion-free.
* `ZMod.minOrder`: The minimum order of $ℤ/nℤ$ is the smallest factor of `n`, unless `n = 0, 1`.
-/

@[expose] public section

open Subgroup

variable {G α : Type*}

namespace Monoid
section Monoid
variable (α) [Monoid α]

/-- The minimum order of a non-identity element. Also the minimum size of a nontrivial subgroup, see
`Monoid.le_minOrder_iff_forall_subgroup`. Returns `∞` if the monoid is torsion-free. -/
@[to_additive /-- The minimum order of a non-identity element. Also the minimum size of a nontrivial
subgroup, see `AddMonoid.le_minOrder_iff_forall_addSubgroup`. Returns `∞` if the monoid is
torsion-free. -/]
/-
**Monoid.minOrder** 是 Mathlib 中的一个定义，位于命名空间 `Monoid`。
形式化陈述：minOrder : Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def minOrder : ℕ∞ := ⨅ (a : α) (_ha : a ≠ 1) (_ha' : IsOfFinOrder a), orderOf a

variable {α} {a : α}

@[to_additive (attr := simp)]
/-
**Monoid.le_minOrder** 是 Mathlib 中的一个引理，位于命名空间 `Monoid`。
形式化陈述：le_minOrder {n : Nat∞} : n <= minOrder α ↔ forall ⦃a : α⦄, a != 1 -> IsOfF
inOrder a -> n <= orderOf a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_minOrder {n : ℕ∞} :
    n ≤ minOrder α ↔ ∀ ⦃a : α⦄, a ≠ 1 → IsOfFinOrder a → n ≤ orderOf a := by simp [minOrder]

@[to_additive]
/-
**Monoid.minOrder_le_orderOf** 是 Mathlib 中的一个引理，位于命名空间 `Monoid`。
形式化陈述：minOrder_le_orderOf (ha : a != 1) (ha' : IsOfFinOrder a) : minOrder α <= o
rderOf a
参数：ha : a != 1；ha' : IsOfFinOrder a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Monoid.le_minOrder`：le_minOrder {n : Nat∞} : n <= minOrder α ↔ forall ⦃a
 : α⦄, a != 1 -> IsOfFinOrder a -> n <= orderOf a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma minOrder_le_orderOf (ha : a ≠ 1) (ha' : IsOfFinOrder a) : minOrder α ≤ orderOf a :=
  le_minOrder.1 le_rfl ha ha'

end Monoid

section Group
variable [Group G] {s : Subgroup G}

@[to_additive]
/-
**le_minOrder_iff_forall_subgroup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_minOrder_iff_forall_subgroup {n : ℕ∞} :
    n ≤ minOrder G ↔ ∀ ⦃s : Subgroup G⦄, s ≠ ⊥ → (s : Set G).Finite → n ≤ Nat.card s := by
  rw [le_minOrder]
  refine ⟨fun h s hs hs' ↦ ?_, fun h a ha ha' ↦ ?_⟩
  · obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs
    exact
      (h ha <| finite_zpowers.1 <| hs'.subset <| zpowers_le.2 has).trans
        (WithTop.coe_le_coe.2 <| s.orderOf_le_card hs' has)
  · simpa using h (zpowers_ne_bot.2 ha) ha'.finite_zpowers

@[to_additive]
/-
**minOrder_le_natCard** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma minOrder_le_natCard (hs : s ≠ ⊥) (hs' : (s : Set G).Finite) : minOrder G ≤ Nat.card s :=
  le_minOrder_iff_forall_subgroup.1 le_rfl hs hs'

@[to_additive (attr := simp)]
/-
**minOrder_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma minOrder_eq_top [IsMulTorsionFree G] : minOrder G = ⊤ := by
  simpa [minOrder] using fun _ ↦ not_isOfFinOrder_of_isMulTorsionFree

end Group

section CommGroup
variable [CommGroup G] {s : Subgroup G}

@[to_additive (attr := simp)]
/-
**minOrder_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma minOrder_eq_top_iff : minOrder G = ⊤ ↔ IsMulTorsionFree G := by
  simp [minOrder, isMulTorsionFree_iff_not_isOfFinOrder]

end CommGroup
end Monoid

open AddMonoid AddSubgroup Nat Set

namespace ZMod

@[simp]
/-
**ZMod.minOrder** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → n ≠ 1 → AddMonoid.minOrder (ZMod n) = ↑n.minFac
参数：ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `ringChar.spec`：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
· 使用引理 `ringChar.eq`：eq (p : Nat) [C : CharP R p] : ringChar R = p
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.minFac_le`：minFac_le {n : Nat} (H : 0 < n) : minFac n <= n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AddMonoid.minOrder_le_natCard`：∀ {G : Type u_1} [inst : AddGroup G] {s :
 AddSubgroup G}, s ≠ ⊥ → (↑s).Finite → AddMonoid.minOrder G ≤ ↑(Nat.card ↥s)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `AddSubgroup.zmultiples_eq_bot`：∀ {G : Type u_1} [inst : AddGroup G] {g :
 G}, AddSubgroup.zmultiples g = ⊥ ↔ g = 0
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.card_zmultiples`：∀ {α : Type u_3} [inst : AddGroup α] (a : α), Nat.c
ard ↥(AddSubgroup.zmultiples a) = addOrderOf a
· 使用定理 `ZMod.addOrderOf_coe`：addOrderOf_coe (a : Nat) {n : Nat} (n0 : n != 0) : 
addOrderOf (a : ZMod n) = n / n.gcd a
· 使用定理 `Nat.gcd_eq_right`：∀ {m n : ℕ}, n ∣ m → m.gcd n = n
· 使用定理 `Nat.div_dvd_of_dvd`：∀ {n m : ℕ}, n ∣ m → m / n ∣ m
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.div_div_self`：∀ {n m : ℕ}, n ∣ m → m ≠ 0 → m / (m / n) = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 41 条，此处仅展示前 30 条）
-/
protected lemma minOrder {n : ℕ} (hn : n ≠ 0) (hn₁ : n ≠ 1) : minOrder (ZMod n) = n.minFac := by
  have : Fact (1 < n) := ⟨one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn, hn₁⟩⟩
  have : (↑(n / n.minFac) : ZMod n) ≠ 0 := by
    rw [Ne, ringChar.spec, ringChar.eq (ZMod n) n]
    exact
      not_dvd_of_pos_of_lt (Nat.div_pos (minFac_le hn.bot_lt) n.minFac_pos)
        (div_lt_self hn.bot_lt (minFac_prime hn₁).one_lt)
  refine ((minOrder_le_natCard (zmultiples_eq_bot.not.2 this) <| toFinite _).trans ?_).antisymm <|
    le_minOrder_iff_forall_addSubgroup.2 fun s hs _ ↦ ?_
  · rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hn,
      gcd_eq_right (div_dvd_of_dvd n.minFac_dvd), Nat.div_div_self n.minFac_dvd hn]
  · have : Nontrivial s := s.bot_or_nontrivial.resolve_left hs
    exact WithTop.coe_le_coe.2 <| minFac_le_of_dvd Finite.one_lt_card <|
      (card_addSubgroup_dvd_card _).trans n.card_zmod.dvd

@[simp]
/-
**ZMod.minOrder_of_prime** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：minOrder_of_prime {p : Nat} (hp : p.Prime) : minOrder (ZMod p) = p
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.minOrder`：∀ {n : ℕ}, n ≠ 0 → n ≠ 1 → AddMonoid.minOrder (ZMod n) = 
↑n.minFac
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.Prime.minFac_eq`：∀ {p : ℕ}, Nat.Prime p → p.minFac = p
-/
lemma minOrder_of_prime {p : ℕ} (hp : p.Prime) : minOrder (ZMod p) = p := by
  rw [ZMod.minOrder hp.ne_zero hp.ne_one, hp.minFac_eq]

end ZMod

