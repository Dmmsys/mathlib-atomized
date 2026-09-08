/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Cyclic groups

`IsCyclic` is a predicate on a group stating that the group is cyclic.
For the concrete cyclic group of order `n`, see `Data.ZMod.Basic`.

* `isCyclic_of_prime_card` proves that a finite group of prime order is cyclic.

cyclic group
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal Field

variable {α G G' : Type*} {a : α}

section Cyclic

open Subgroup

@[to_additive]
/-
**IsCyclic.exists_generator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.exists_generator [Group α] [IsCyclic α] : exists g : α, forall x,
 x in zpowers g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_zpow_surjective`：exists_zpow_surjective (G : Type*) [Pow G Int] [
IsCyclic G] : exists g : G, Function.Surjective (g ^ · : Int -> G)
-/
theorem IsCyclic.exists_generator [Group α] [IsCyclic α] : ∃ g : α, ∀ x, x ∈ zpowers g :=
  exists_zpow_surjective α

@[to_additive]
/-
**isCyclic_iff_exists_zpowers_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_iff_exists_zpowers_eq_top [Group α] : IsCyclic α ↔ exists g : α, 
zpowers g = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem isCyclic_iff_exists_zpowers_eq_top [Group α] : IsCyclic α ↔ ∃ g : α, zpowers g = ⊤ := by
  simp only [eq_top_iff', mem_zpowers_iff]
  exact ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

@[to_additive]
/-
**Subgroup.isCyclic_iff_exists_zpowers_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：∀ {α : Type u_1} [inst : Group α] (H : Subgroup α), IsCyclic ↥H ↔ ∃ g, Sub
group.zpowers g = H
参数：H : Subgroup α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCyclic_iff_exists_zpowers_eq_top`：isCyclic_iff_exists_zpowers_eq_top [
Group α] : IsCyclic α ↔ exists g : α, zpowers g = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `MonoidHom.map_zpowers`：MonoidHom.map_zpowers (f : G ->* N) (x : G) : (Su
bgroup.zpowers x).map f = Subgroup.zpowers (f x)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
-/
protected theorem Subgroup.isCyclic_iff_exists_zpowers_eq_top [Group α] (H : Subgroup α) :
    IsCyclic H ↔ ∃ g : α, Subgroup.zpowers g = H := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  simp_rw [← map_subtype_inj, ← MonoidHom.range_eq_map,
    H.range_subtype, MonoidHom.map_zpowers, Subtype.exists, coe_subtype, exists_prop]
  exact exists_congr fun g ↦ and_iff_right_of_imp fun h ↦ h ▸ mem_zpowers g

@[to_additive]
/-
**Subgroup.isCyclic_zpowers** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.isCyclic_zpowers [Group G] (g : G) : IsCyclic (Subgroup.zpowers g
)
参数：g : G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.isCyclic_iff_exists_zpowers_eq_top`：∀ {α : Type u_1} [inst : Gr
oup α] (H : Subgroup α), IsCyclic ↥H ↔ ∃ g, Subgroup.zpowers g = H
-/
instance Subgroup.isCyclic_zpowers [Group G] (g : G) :
    IsCyclic (Subgroup.zpowers g) :=
  (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨g, rfl⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isCyclic_of_subsingleton [Group α] [Subsingleton α] : IsCyclic α :=
  ⟨⟨1, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩

@[simp]
/-
**isCyclic_multiplicative_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_multiplicative_iff [SubNegMonoid α] : IsCyclic (Multiplicative α)
 ↔ IsAddCyclic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_zpow_surjective`：∀ {G : Type u} {inst : Pow G ℤ} [self :
 IsCyclic G], ∃ g, Function.Surjective fun x => g ^ x
· 使用定理 `IsAddCyclic.exists_zsmul_surjective`：∀ {G : Type u} {inst : SMul ℤ G} [s
elf : IsAddCyclic G], ∃ g, Function.Surjective fun x => x • g
-/
theorem isCyclic_multiplicative_iff [SubNegMonoid α] :
    IsCyclic (Multiplicative α) ↔ IsAddCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩
/-
**isCyclic_multiplicative** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isCyclic_multiplicative [AddGroup α] [IsAddCyclic α] : IsCyclic (Multiplic
ative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCyclic_multiplicative_iff`：isCyclic_multiplicative_iff [SubNegMonoid α
] : IsCyclic (Multiplicative α) ↔ IsAddCyclic α
-/
instance isCyclic_multiplicative [AddGroup α] [IsAddCyclic α] : IsCyclic (Multiplicative α) :=
  isCyclic_multiplicative_iff.mpr inferInstance

@[simp]
/-
**isAddCyclic_additive_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAddCyclic_additive_iff [DivInvMonoid α] : IsAddCyclic (Additive α) ↔ IsC
yclic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddCyclic.exists_zsmul_surjective`：∀ {G : Type u} {inst : SMul ℤ G} [s
elf : IsAddCyclic G], ∃ g, Function.Surjective fun x => x • g
· 使用定理 `IsCyclic.exists_zpow_surjective`：∀ {G : Type u} {inst : Pow G ℤ} [self :
 IsCyclic G], ∃ g, Function.Surjective fun x => g ^ x
-/
theorem isAddCyclic_additive_iff [DivInvMonoid α] : IsAddCyclic (Additive α) ↔ IsCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩
/-
**isAddCyclic_additive** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isAddCyclic_additive [Group α] [IsCyclic α] : IsAddCyclic (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isAddCyclic_additive_iff`：isAddCyclic_additive_iff [DivInvMonoid α] : Is
AddCyclic (Additive α) ↔ IsCyclic α
-/
instance isAddCyclic_additive [Group α] [IsCyclic α] : IsAddCyclic (Additive α) :=
  isAddCyclic_additive_iff.mpr inferInstance

@[to_additive]
/-
**IsCyclic.isMulCommutative** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsCyclic.isMulCommutative [Group α] [IsCyclic α] : IsMulCommutative α wher
e is_comm.comm x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `zpow_mul_comm`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ 
m * a ^ n = a ^ n * a ^ m
-/
instance IsCyclic.isMulCommutative [Group α] [IsCyclic α] : IsMulCommutative α where
  is_comm.comm x y :=
    let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
    let ⟨_, hx⟩ := hg x
    let ⟨_, hy⟩ := hg y
    hy ▸ hx ▸ zpow_mul_comm ..

@[deprecated (since := "2026-04-09")]
alias IsAddCyclic.commutative := IsAddCyclic.isAddCommutative
@[to_additive existing, deprecated (since := "2026-04-09")]
alias IsCyclic.commutative := IsCyclic.isMulCommutative

open scoped IsMulCommutative in
/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `CommGroup`. -/
@[to_additive (attr := instance_reducible)
      /-- A cyclic group is always commutative. This is not an `instance` because often we have
      a better proof of `AddCommGroup`. -/]
/-
**IsCyclic.commGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCyclic.commGroup [Group α] [IsCyclic α] : CommGroup α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsCyclic.commGroup [Group α] [IsCyclic α] : CommGroup α :=
  inferInstance

variable [Group α] [Group G] [Group G']

/-- A non-cyclic multiplicative group is non-trivial. -/
@[to_additive /-- A non-cyclic additive group is non-trivial. -/]
/-
**Nontrivial.of_not_isCyclic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nontrivial.of_not_isCyclic (nc : ¬IsCyclic α) : Nontrivial α
参数：nc : ¬IsCyclic α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `isCyclic_of_subsingleton`：∀ {α : Type u_1} [inst : Group α] [Subsingleto
n α], IsCyclic α

--- 原说明 ---
A non-cyclic multiplicative group is non-trivial.
-/
theorem Nontrivial.of_not_isCyclic (nc : ¬IsCyclic α) : Nontrivial α := by
  contrapose! nc
  exact isCyclic_of_subsingleton

@[to_additive]
/-
**MonoidHom.map_cyclic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_cyclic [h : IsCyclic G] (σ : G ->* G) : exists m : Int, fora
ll g : G, σ g = g ^ m
参数：σ : G ->* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用引理 `zpow_mul'`：zpow_mul' (a : α) (m n : Int) : a ^ (m * n) = (a ^ n) ^ m
-/
theorem MonoidHom.map_cyclic [h : IsCyclic G] (σ : G →* G) :
    ∃ m : ℤ, ∀ g : G, σ g = g ^ m := by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [map_zpow, ← hm, ← zpow_mul, ← zpow_mul']

@[to_additive]
/-
**isCyclic_iff_exists_orderOf_eq_natCard** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCyclic_iff_exists_orderOf_eq_natCard [Finite α] : IsCyclic α ↔ exists g 
: α, orderOf g = Nat.card α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_zpowers`：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isCyclic_iff_exists_orderOf_eq_natCard [Finite α] :
    IsCyclic α ↔ ∃ g : α, orderOf g = Nat.card α := by
  simp_rw [isCyclic_iff_exists_zpowers_eq_top, ← card_eq_iff_eq_top, Nat.card_zpowers]

@[to_additive]
/-
**isCyclic_iff_exists_natCard_le_orderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCyclic_iff_exists_natCard_le_orderOf [Finite α] : IsCyclic α ↔ exists g 
: α, Nat.card α <= orderOf g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isCyclic_iff_exists_orderOf_eq_natCard`：isCyclic_iff_exists_orderOf_eq_n
atCard [Finite α] : IsCyclic α ↔ exists g : α, orderOf g = Nat.card α
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `orderOf_le_card`：orderOf_le_card [Finite G] : orderOf x <= Nat.card G
-/
lemma isCyclic_iff_exists_natCard_le_orderOf [Finite α] :
    IsCyclic α ↔ ∃ g : α, Nat.card α ≤ orderOf g := by
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  apply exists_congr
  intro g
  exact ⟨Eq.ge, le_antisymm orderOf_le_card⟩

@[to_additive]
/-
**isCyclic_of_orderOf_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_orderOf_eq_card [Finite α] (x : α) (hx : orderOf x = Nat.card 
α) : IsCyclic α
参数：x : α；hx : orderOf x = Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isCyclic_iff_exists_orderOf_eq_natCard`：isCyclic_iff_exists_orderOf_eq_n
atCard [Finite α] : IsCyclic α ↔ exists g : α, orderOf g = Nat.card α
-/
theorem isCyclic_of_orderOf_eq_card [Finite α] (x : α) (hx : orderOf x = Nat.card α) :
    IsCyclic α :=
  isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨x, hx⟩

@[to_additive]
/-
**isCyclic_of_card_le_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_card_le_orderOf [Finite α] (x : α) (hx : Nat.card α <= orderOf
 x) : IsCyclic α
参数：x : α；hx : Nat.card α <= orderOf x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isCyclic_iff_exists_natCard_le_orderOf`：isCyclic_iff_exists_natCard_le_o
rderOf [Finite α] : IsCyclic α ↔ exists g : α, Nat.card α <= orderOf g
-/
theorem isCyclic_of_card_le_orderOf [Finite α] (x : α) (hx : Nat.card α ≤ orderOf x) :
    IsCyclic α :=
  isCyclic_iff_exists_natCard_le_orderOf.mpr ⟨x, hx⟩

@[to_additive]
/-
**Subgroup.eq_bot_or_eq_top_of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.eq_bot_or_eq_top_of_prime_card (H : Subgroup G) [hp : Fact (Nat.c
ard G).Prime] : H = ⊥ ∨ H = ⊤
参数：H : Subgroup G；Nat.card G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Subgroup.card_subgroup_dvd_card`：card_subgroup_dvd_card (s : Subgroup α)
 : Nat.card s ∣ Nat.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.card_eq_iff_eq_top`：card_eq_iff_eq_top [Finite H] : Nat.card H 
= Nat.card G ↔ H = ⊤
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.eq_bot_iff_card`：∀ {G : Type u_1} [inst : Group G] (H : Subgrou
p G), H = ⊥ ↔ Nat.card ↥H = 1
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
-/
theorem Subgroup.eq_bot_or_eq_top_of_prime_card
    (H : Subgroup G) [hp : Fact (Nat.card G).Prime] : H = ⊥ ∨ H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have := card_subgroup_dvd_card H
  rwa [Nat.dvd_prime hp.1, ← eq_bot_iff_card, card_eq_iff_eq_top] at this

/-- Any non-identity element of a finite group of prime order generates the group. -/
@[to_additive /-- Any non-identity element of a finite group of prime order generates the group. -/]
/-
**zpowers_eq_top_of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpowers_eq_top_of_prime_card {p : Nat} [hp : Fact p.Prime] (h : Nat.card G
 = p) {g : G} (hg : g != 1) : zpowers g = ⊤
参数：h : Nat.card G = p；hg : g != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.eq_bot_or_eq_top_of_prime_card`：Subgroup.eq_bot_or_eq_top_of_pr
ime_card (H : Subgroup G) [hp : Fact (Nat.card G).Prime] : H = ⊥ ∨ H = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Subgroup.zpowers_eq_bot`：zpowers_eq_bot {g : G} : zpowers g = ⊥ ↔ g = 1

--- 原说明 ---
Any non-identity element of a finite group of prime order generates the group.
-/
theorem zpowers_eq_top_of_prime_card {p : ℕ}
    [hp : Fact p.Prime] (h : Nat.card G = p) {g : G} (hg : g ≠ 1) : zpowers g = ⊤ := by
  subst h
  have := (zpowers g).eq_bot_or_eq_top_of_prime_card
  rwa [zpowers_eq_bot, or_iff_right hg] at this

@[to_additive]
/-
**mem_zpowers_of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_zpowers_of_prime_card {p : Nat} [hp : Fact p.Prime] (h : Nat.card G = 
p) {g g' : G} (hg : g != 1) : g' in zpowers g
参数：h : Nat.card G = p；hg : g != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpowers_eq_top_of_prime_card`：zpowers_eq_top_of_prime_card {p : Nat} [hp
 : Fact p.Prime] (h : Nat.card G = p) {g : G} (hg : g != 1) : zpowers g = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem mem_zpowers_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card G = p) {g g' : G} (hg : g ≠ 1) : g' ∈ zpowers g := by
  simp_rw [zpowers_eq_top_of_prime_card h hg, Subgroup.mem_top]

@[to_additive]
/-
**mem_powers_of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_powers_of_prime_card {p : Nat} [hp : Fact p.Prime] (h : Nat.card G = p
) {g g' : G} (hg : g != 1) : g' in Submonoid.powers g
参数：h : Nat.card G = p；hg : g != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_powers_iff_mem_zpowers`：mem_powers_iff_mem_zpowers : y in powers x ↔
 y in zpowers x
· 使用定理 `mem_zpowers_of_prime_card`：mem_zpowers_of_prime_card {p : Nat} [hp : Fac
t p.Prime] (h : Nat.card G = p) {g g' : G} (hg : g != 1) : g' in zpowers g
-/
theorem mem_powers_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card G = p) {g g' : G} (hg : g ≠ 1) : g' ∈ Submonoid.powers g := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  rw [mem_powers_iff_mem_zpowers]
  exact mem_zpowers_of_prime_card h hg

@[to_additive]
/-
**powers_eq_top_of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powers_eq_top_of_prime_card {p : Nat} [hp : Fact p.Prime] (h : Nat.card G 
= p) {g : G} (hg : g != 1) : Submonoid.powers g = ⊤
参数：h : Nat.card G = p；hg : g != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mem_powers_of_prime_card`：mem_powers_of_prime_card {p : Nat} [hp : Fact 
p.Prime] (h : Nat.card G = p) {g g' : G} (hg : g != 1) : g' in Submonoid.powers 
g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem powers_eq_top_of_prime_card {p : ℕ}
    [hp : Fact p.Prime] (h : Nat.card G = p) {g : G} (hg : g ≠ 1) : Submonoid.powers g = ⊤ := by
  ext x
  simp [mem_powers_of_prime_card h hg]

/-- A finite group of prime order is cyclic. -/
@[to_additive /-- A finite group of prime order is cyclic. -/]
/-
**isCyclic_of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_prime_card {p : Nat} [hp : Fact p.Prime] (h : Nat.card α = p) 
: IsCyclic α
参数：h : Nat.card α = p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `mem_zpowers_of_prime_card`：mem_zpowers_of_prime_card {p : Nat} [hp : Fac
t p.Prime] (h : Nat.card G = p) {g g' : G} (hg : g != 1) : g' in zpowers g

--- 原说明 ---
A finite group of prime order is cyclic.
-/
theorem isCyclic_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card α = p) : IsCyclic α := by
  have : Finite α := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (h ▸ hp.1.one_lt)
  obtain ⟨g, hg⟩ : ∃ g : α, g ≠ 1 := exists_ne 1
  exact ⟨g, fun g' ↦ mem_zpowers_of_prime_card h hg⟩

/-- A finite group of order dividing a prime is cyclic. -/
@[to_additive /-- A finite group of order dividing a prime is cyclic. -/]
/-
**isCyclic_of_card_dvd_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_card_dvd_prime {p : Nat} [hp : Fact p.Prime] (h : Nat.card α ∣
 p) : IsCyclic α
参数：h : Nat.card α ∣ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `isCyclic_of_subsingleton`：∀ {α : Type u_1} [inst : Group α] [Subsingleto
n α], IsCyclic α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `isCyclic_of_prime_card`：isCyclic_of_prime_card {p : Nat} [hp : Fact p.Pr
ime] (h : Nat.card α = p) : IsCyclic α

--- 原说明 ---
A finite group of order dividing a prime is cyclic.
-/
theorem isCyclic_of_card_dvd_prime {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card α ∣ p) : IsCyclic α := by
  rcases (Nat.dvd_prime hp.out).mp h with h | h
  · exact @isCyclic_of_subsingleton α _ (Nat.card_eq_one_iff_unique.mp h).1
  · exact isCyclic_of_prime_card h

@[to_additive]
/-
**isCyclic_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_surjective {F : Type*} [hH : IsCyclic G'] [FunLike F G' G] [Mo
noidHomClass F G' G] (f : F) (hf : Function.Surjective f) : IsCyclic G
参数：f : F；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
-/
theorem isCyclic_of_surjective {F : Type*} [hH : IsCyclic G']
    [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective f) :
    IsCyclic G := by
  obtain ⟨x, hx⟩ := hH
  refine ⟨f x, fun a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨n, rfl⟩ := hx a
  exact ⟨n, (map_zpow _ _ _).symm⟩

@[to_additive]
/-
**MulEquiv.isCyclic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.isCyclic (e : G ≃* G') : IsCyclic G ↔ IsCyclic G'
参数：e : G ≃* G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
theorem MulEquiv.isCyclic (e : G ≃* G') :
    IsCyclic G ↔ IsCyclic G' :=
  ⟨fun _ ↦ isCyclic_of_surjective e e.surjective,
    fun _ ↦ isCyclic_of_surjective e.symm e.symm.surjective⟩

@[to_additive]
/-
**orderOf_eq_card_of_forall_mem_zpowers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_card_of_forall_mem_zpowers {g : α} (hx : forall x, x in zpowers
 g) : orderOf g = Nat.card α
参数：hx : forall x, x in zpowers g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_zpowers`：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.eq_top_iff'`：eq_top_iff' : H = ⊤ ↔ forall x : G, x in H
· 使用定理 `Subgroup.card_top`：card_top : Nat.card (⊤ : Subgroup G) = Nat.card G
-/
theorem orderOf_eq_card_of_forall_mem_zpowers {g : α} (hx : ∀ x, x ∈ zpowers g) :
    orderOf g = Nat.card α := by
  rw [← Nat.card_zpowers, (zpowers g).eq_top_iff'.mpr hx, card_top]

@[to_additive]
/-
**orderOf_eq_card_of_forall_mem_powers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_card_of_forall_mem_powers {g : α} (hx : forall x, x in Submonoi
d.powers g) : orderOf g = Nat.card α
参数：hx : forall x, x in Submonoid.powers g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `Submonoid.powers_le_zpowers`：∀ {G : Type u_2} [inst : Group G] (g : G), 
Submonoid.powers g ≤ (Subgroup.zpowers g).toSubmonoid
-/
theorem orderOf_eq_card_of_forall_mem_powers {g : α} (hx : ∀ x, x ∈ Submonoid.powers g) :
    orderOf g = Nat.card α := by
  rw [orderOf_eq_card_of_forall_mem_zpowers]
  exact fun x ↦ Submonoid.powers_le_zpowers _ (hx _)

@[to_additive]
/-
**orderOf_eq_card_of_zpowers_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_card_of_zpowers_eq_top {g : G} (h : Subgroup.zpowers g = ⊤) : o
rderOf g = Nat.card G
参数：h : Subgroup.zpowers g = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
-/
theorem orderOf_eq_card_of_zpowers_eq_top {g : G} (h : Subgroup.zpowers g = ⊤) :
    orderOf g = Nat.card G :=
  orderOf_eq_card_of_forall_mem_zpowers fun _ ↦ h.ge (Subgroup.mem_top _)

@[to_additive]
/-
**exists_pow_ne_one_of_isCyclic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pow_ne_one_of_isCyclic [G_cyclic : IsCyclic G] {k : Nat} (k_pos : k
 != 0) (k_lt_card_G : k < Nat.card G) : exists a : G, a ^ k != 1
参数：k_pos : k != 0；k_lt_card_G : k < Nat.card G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_zpowers`：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Subgroup.card_eq_iff_eq_top`：card_eq_iff_eq_top [Finite H] : Nat.card H 
= Nat.card G ↔ H = ⊤
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `orderOf_le_of_pow_eq_one`：orderOf_le_of_pow_eq_one (hn : 0 < n) (h : x ^
 n = 1) : orderOf x <= n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem exists_pow_ne_one_of_isCyclic [G_cyclic : IsCyclic G]
    {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Nat.card G) : ∃ a : G, a ^ k ≠ 1 := by
  have : Finite G := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt k_lt_card_G)
  rcases G_cyclic with ⟨a, ha⟩
  use a
  contrapose! k_lt_card_G
  convert! orderOf_le_of_pow_eq_one k_pos.bot_lt k_lt_card_G
  rw [← Nat.card_zpowers, eq_comm, card_eq_iff_eq_top, eq_top_iff]
  exact fun x _ ↦ ha x

@[to_additive]
/-
**Infinite.orderOf_eq_zero_of_forall_mem_zpowers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Infinite.orderOf_eq_zero_of_forall_mem_zpowers [Infinite α] {g : α} (h : f
orall x, x in zpowers g) : orderOf g = 0
参数：h : forall x, x in zpowers g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
-/
theorem Infinite.orderOf_eq_zero_of_forall_mem_zpowers [Infinite α] {g : α}
    (h : ∀ x, x ∈ zpowers g) : orderOf g = 0 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers h, Nat.card_eq_zero_of_infinite]

@[to_additive]
/-
**Bot.isCyclic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bot.isCyclic : IsCyclic (⊥ : Subgroup α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance Bot.isCyclic : IsCyclic (⊥ : Subgroup α) :=
  ⟨⟨1, fun x => ⟨0, Subtype.ext <| (zpow_zero (1 : α)).trans <| Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩

@[to_additive]
/-
**Subgroup.isCyclic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.isCyclic [IsCyclic α] (H : Subgroup α) : IsCyclic H
参数：H : Subgroup α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natAbs_eq_zero`：∀ {a : ℤ}, a.natAbs = 0 ↔ a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.natAbs_negSucc`：∀ (n : ℕ), (Int.negSucc n).natAbs = n.succ
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `Subgroup.zpow_mem`：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {x
 : G}, x ∈ K → ∀ (n : ℤ), x ^ n ∈ K
· 使用定理 `Subgroup.mul_mem_cancel_right`：∀ {G : Type u_1} [inst : Group G] (H : Su
bgroup G) {x y : G}, x ∈ H → (y * x ∈ H ↔ y ∈ H)
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
（共 42 条，此处仅展示前 30 条）
-/
instance Subgroup.isCyclic [IsCyclic α] (H : Subgroup α) : IsCyclic H :=
  haveI := Classical.propDecidable
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  if hx : ∃ x : α, x ∈ H ∧ x ≠ (1 : α) then
    let ⟨x, hx₁, hx₂⟩ := hx
    let ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hex : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H :=
      ⟨k.natAbs,
        Nat.pos_of_ne_zero fun h => hx₂ <| by
          rw [← hk, Int.natAbs_eq_zero.mp h, zpow_zero], by
            rcases k with k | k
            · rw [Int.ofNat_eq_natCast, Int.natAbs_natCast k, ← zpow_natCast,
                ← Int.ofNat_eq_natCast, hk]
              exact hx₁
            · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all⟩
    ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ =>
        let ⟨k, hk⟩ := hg x
        have hk : g ^ k = x := hk
        have hk₂ : g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) ∈ H := by
          rw [zpow_mul]
          apply H.zpow_mem
          exact mod_cast (Nat.find_spec hex).2
        have hk₃ : g ^ (k % Nat.find hex : ℤ) ∈ H :=
          (Subgroup.mul_mem_cancel_right H hk₂).1 <| by
            rw [← zpow_add, Int.emod_add_mul_ediv, hk]; exact hx
        have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
          rw [Int.natAbs_of_nonneg
              (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
        have hk₅ : g ^ (k % Nat.find hex).natAbs ∈ H := by rwa [← zpow_natCast, ← hk₄]
        have hk₆ : (k % (Nat.find hex : ℤ)).natAbs = 0 :=
          by_contradiction fun h =>
            Nat.find_min hex
              (Int.ofNat_lt.1 <| by
                rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
              ⟨Nat.pos_of_ne_zero h, hk₅⟩
        ⟨k / (Nat.find hex : ℤ),
          Subtype.ext_iff.2
            (by
              suffices g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) = x by simpa [zpow_mul]
              rw [Int.mul_ediv_cancel'
                  (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆)),
                hk])⟩⟩⟩
  else by
    have : H = (⊥ : Subgroup α) :=
      Subgroup.ext fun x =>
        ⟨fun h => by simp at *; tauto, fun h => by rw [Subgroup.mem_bot.1 h]; exact H.one_mem⟩
    subst this; infer_instance

@[to_additive]
/-
**isCyclic_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_injective [IsCyclic G'] (f : G ->* G') (hf : Function.Injectiv
e f) : IsCyclic G
参数：f : G ->* G'；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
theorem isCyclic_of_injective [IsCyclic G'] (f : G →* G') (hf : Function.Injective f) :
    IsCyclic G :=
  isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MonoidHom.ofInjective hf).symm.surjective

@[to_additive]
/-
**Subgroup.isCyclic_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.isCyclic_of_le {H H' : Subgroup G} (h : H <= H') [IsCyclic H'] : 
IsCyclic H
参数：h : H <= H'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_injective`：isCyclic_of_injective [IsCyclic G'] (f : G ->* G'
) (hf : Function.Injective f) : IsCyclic G
· 使用定理 `Subgroup.inclusion_injective`：inclusion_injective {H K : Subgroup G} (h 
: H <= K) : Function.Injective inclusion h
-/
lemma Subgroup.isCyclic_of_le {H H' : Subgroup G} (h : H ≤ H') [IsCyclic H'] : IsCyclic H :=
  isCyclic_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

@[to_additive]
/-
**Subgroup.le_zpowers_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.le_zpowers_iff (g : G) (H : Subgroup G) : H <= Subgroup.zpowers g
 ↔ exists n : Nat, H = Subgroup.zpowers (g ^ n)
参数：g : G；H : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.isCyclic_iff_exists_zpowers_eq_top`：∀ {α : Type u_1} [inst : Gr
oup α] (H : Subgroup α), IsCyclic ↥H ↔ ∃ g, Subgroup.zpowers g = H
· 使用引理 `Subgroup.isCyclic_of_le`：Subgroup.isCyclic_of_le {H H' : Subgroup G} (h 
: H <= H') [IsCyclic H'] : IsCyclic H
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Subgroup.zpowers_inv`：zpowers_inv : zpowers g⁻¹ = zpowers g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.zpowers_le_of_mem`：∀ {G : Type u_1} [inst : Group G] {g : G} {H
 : Subgroup G}, g ∈ H → Subgroup.zpowers g ≤ H
· 使用定理 `Subgroup.npow_mem_zpowers`：npow_mem_zpowers (g : G) (k : Nat) : g ^ k in
 zpowers g
-/
theorem Subgroup.le_zpowers_iff (g : G) (H : Subgroup G) :
    H ≤ Subgroup.zpowers g ↔ ∃ n : ℕ, H = Subgroup.zpowers (g ^ n) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := (H.isCyclic_iff_exists_zpowers_eq_top).mp (isCyclic_of_le h)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp <| h (mem_zpowers x)
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · exact ⟨n, by rw [zpow_natCast]⟩
    · exact ⟨n, by simp⟩
  · rintro ⟨k, rfl⟩
    exact zpowers_le_of_mem <| npow_mem_zpowers g k

open Finset Nat

section Classical

open scoped Classical in
@[to_additive IsAddCyclic.card_nsmul_eq_zero_le]
/-
**IsCyclic.card_pow_eq_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α] {n : 
Nat} (hn0 : 0 < n) : #{a : α | a ^ n = 1} <= n
参数：hn0 : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `mem_powers_iff_mem_zpowers`：mem_powers_iff_mem_zpowers : y in powers x ↔
 y in zpowers x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.mul_div_cancel_left'`：∀ {a b : ℕ}, a ∣ b → a * (b / a) = b
· 使用定理 `Nat.dvd_of_mul_dvd_mul_right`：∀ {k m n : ℕ}, 0 < k → m * k ∣ n * k → m ∣
 n
· 使用定理 `Nat.gcd_pos_of_pos_left`：∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_card_eq_one`：pow_card_eq_one : x ^ Fintype.card G = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
（共 37 条，此处仅展示前 30 条）
-/
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α] {n : ℕ} (hn0 : 0 < n) :
    #{a : α | a ^ n = 1} ≤ n :=
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    #{a : α | a ^ n = 1} ≤
        #(zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset := by
      gcongr
      intro x hx
      let ⟨m, hm⟩ := show x ∈ Submonoid.powers g from mem_powers_iff_mem_zpowers.2 <| hg x
      refine Set.mem_toFinset.2 ⟨(m / (Fintype.card α / Nat.gcd n (Fintype.card α)) : ℕ), ?_⟩
      dsimp only at ⊢ hm
      rw [zpow_natCast, ← pow_mul, Nat.mul_div_cancel_left', hm]
      refine Nat.dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (Fintype.card α) hn0) ?_
      conv_lhs =>
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), ← Nat.card_eq_fintype_card,
          ← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one <| by simpa [pow_mul, hm] using (mem_filter.1 hx).2
    _ ≤ n := by
      let ⟨m, hm⟩ := Nat.gcd_dvd_right n (Fintype.card α)
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by
          rw [hm0, mul_zero, Fintype.card_eq_zero_iff] at hm
          exact hm.elim' 1
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      rw [Fintype.card_zpowers, orderOf_pow g, orderOf_eq_card_of_forall_mem_zpowers hg,
        Nat.card_eq_fintype_card]
      nth_rw 2 [hm]; nth_rw 3 [hm]
      rw [Nat.mul_div_cancel_left _ (gcd_pos_of_pos_left _ hn0), gcd_mul_left_left, hm,
        Nat.mul_div_cancel _ hm0]
      exact le_of_dvd hn0 (Nat.gcd_dvd_left _ _)

end Classical

@[to_additive]
/-
**IsCyclic.exists_monoid_generator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.exists_monoid_generator [Finite α] [IsCyclic α] : exists x : α, f
orall y : α, y in Submonoid.powers x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
-/
theorem IsCyclic.exists_monoid_generator [Finite α] [IsCyclic α] :
    ∃ x : α, ∀ y : α, y ∈ Submonoid.powers x := by
  simp_rw [mem_powers_iff_mem_zpowers]
  exact IsCyclic.exists_generator

@[to_additive]
/-
**IsCyclic.exists_ofOrder_eq_natCard** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCyclic.exists_ofOrder_eq_natCard [h : IsCyclic α] : exists g : α, orderO
f g = Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_zpowers`：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.eq_top_iff'`：eq_top_iff' : H = ⊤ ↔ forall x : G, x in H
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
lemma IsCyclic.exists_ofOrder_eq_natCard [h : IsCyclic α] : ∃ g : α, orderOf g = Nat.card α := by
  obtain ⟨g, hg⟩ := h.exists_generator
  use g
  rw [← card_zpowers g, (eq_top_iff' (zpowers g)).mpr hg]
  exact Nat.card_congr (Equiv.Set.univ α)

variable (G) in
/-- A distributive action of a monoid on a finite cyclic group of order `n` factors through an
action on `ZMod n`. -/
/-
**MulDistribMulAction.toMonoidHomZModOfIsCyclic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulDistribMulAction.toMonoidHomZModOfIsCyclic (M : Type*) [Monoid M] [IsCy
clic G] [MulDistribMulAction M G] {n : Nat} (hn : Nat.card G = n) : M ->* ZMod n
 where toFun m
参数：M : Type*；hn : Nat.card G = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distributive action of a monoid on a finite cyclic group of order `n` factors 
through an
action on `ZMod n`.
-/
noncomputable def MulDistribMulAction.toMonoidHomZModOfIsCyclic (M : Type*) [Monoid M]
    [IsCyclic G] [MulDistribMulAction M G] {n : ℕ} (hn : Nat.card G = n) : M →* ZMod n where
  toFun m := (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose
  map_one' := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff, ← hn, ← hg, ← zpow_eq_zpow_iff_modEq,
      zpow_one, ← (MulDistribMulAction.toMonoidHom G 1).map_cyclic.choose_spec,
      MulDistribMulAction.toMonoidHom_apply, one_smul]
  map_mul' m n := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff, ← hn, ← hg, ← zpow_eq_zpow_iff_modEq,
      zpow_mul', ← (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec,
      ← (MulDistribMulAction.toMonoidHom G n).map_cyclic.choose_spec,
      ← (MulDistribMulAction.toMonoidHom G (m * n)).map_cyclic.choose_spec,
      MulDistribMulAction.toMonoidHom_apply, MulDistribMulAction.toMonoidHom_apply,
      MulDistribMulAction.toMonoidHom_apply, mul_smul]
/-
**MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply {M : Type*} [Monoid M]
 [IsCyclic G] [MulDistribMulAction M G] {n : Nat} (hn : Nat.card G = n) (m : M) 
(g : G) (k : Int) (h : toMonoidHomZModOfIsCyclic G M hn m = k) : m • g = g ^ k
参数：hn : Nat.card G = n；m : M；g : G；k : Int；h : toMonoidHomZModOfIsCyclic G M hn 
m = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulDistribMulAction.toMonoidHom_apply`：∀ {M : Type u_2} (A : Type u_3) [
inst : Monoid M] [inst_1 : Monoid A] [inst_2 : MulDistribMulAction M A] (r : M) 
  (x : A), (MulDistribMulAc…
· 使用定理 `MonoidHom.map_cyclic`：MonoidHom.map_cyclic [h : IsCyclic G] (σ : G ->* G
) : exists m : Int, forall g : G, σ g = g ^ m
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `zpow_eq_zpow_iff_modEq`：zpow_eq_zpow_iff_modEq {m n : Int} : x ^ m = x ^
 n ↔ m ≡ n [ZMOD orderOf x]
· 使用定理 `Int.ModEq.of_dvd`：∀ {m n a b : ℤ}, m ∣ n → a ≡ b [ZMOD n] → a ≡ b [ZMOD 
m]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
-/
theorem MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply {M : Type*} [Monoid M] [IsCyclic G]
    [MulDistribMulAction M G] {n : ℕ} (hn : Nat.card G = n) (m : M) (g : G) (k : ℤ)
    (h : toMonoidHomZModOfIsCyclic G M hn m = k) : m • g = g ^ k := by
  rw [← MulDistribMulAction.toMonoidHom_apply,
    (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec g, zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard g))
  rwa [hn, ← ZMod.intCast_eq_intCast_iff]

section

variable [Fintype α]

@[to_additive]
/-
**IsCyclic.unique_zpow_zmod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.unique_zpow_zmod (ha : forall x : α, x in zpowers a) (x : α) : ex
ists! n : ZMod (Fintype.card α), x = a ^ n.val
参数：ha : forall x : α, x in zpowers a；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_eq_zpow_iff_modEq`：zpow_eq_zpow_iff_modEq {m n : Int} : x ^ m = x ^
 n ↔ m ≡ n [ZMOD orderOf x]
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `Int.modEq_comm`：modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n]
· 使用定理 `Int.modEq_iff_add_fac`：modEq_iff_add_fac {a b n : Int} : a ≡ b [ZMOD n] 
↔ exists t, b = a + n * t
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `ZMod.intCast_eq_iff`：intCast_eq_iff (p : Nat) (n : Int) (z : ZMod p) [Ne
Zero p] : ↑n = z ↔ exists k, n = z.val + p * k
· 使用定理 `Fintype.instNeZeroNatCardOfNonempty`：∀ {α : Type u_1} [inst : Fintype α]
 [Nonempty α], NeZero (Fintype.card α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `ZMod.intCast_cast`：intCast_cast (i : ZMod n) : ((cast i : Int) : R) = ca
st i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ZMod.cast_id'`：cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCyclic.unique_zpow_zmod (ha : ∀ x : α, x ∈ zpowers a) (x : α) :
    ∃! n : ZMod (Fintype.card α), x = a ^ n.val := by
  obtain ⟨n, rfl⟩ := ha x
  refine ⟨n, (?_ : a ^ n = _), fun y (hy : a ^ n = _) ↦ ?_⟩
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Int.modEq_comm, Int.modEq_iff_add_fac, Nat.card_eq_fintype_card, ← ZMod.intCast_eq_iff]
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Nat.card_eq_fintype_card, ← ZMod.intCast_eq_intCast_iff] at hy
    simp [hy]

variable [DecidableEq α]

@[to_additive]
/-
**IsCyclic.image_range_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.image_range_orderOf (ha : forall x : α, x in zpowers a) : Finset.
image (fun i => a ^ i) (range (orderOf a)) = univ
参数：ha : forall x : α, x in zpowers a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `image_range_orderOf`：image_range_orderOf [DecidableEq G] : letI : Fintyp
e (zpowers x)
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.toFinset_univ`：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)
] : (Set.univ : Set α).toFinset = Finset.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCyclic.image_range_orderOf (ha : ∀ x : α, x ∈ zpowers a) :
    Finset.image (fun i => a ^ i) (range (orderOf a)) = univ := by
  simp only [_root_.image_range_orderOf, Set.eq_univ_iff_forall.mpr ha, Set.toFinset_univ]

@[to_additive]
/-
**IsCyclic.image_range_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclic.image_range_card (ha : forall x : α, x in zpowers a) : Finset.ima
ge (fun i => a ^ i) (range (Nat.card α)) = univ
参数：ha : forall x : α, x in zpowers a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `IsCyclic.image_range_orderOf`：IsCyclic.image_range_orderOf (ha : forall 
x : α, x in zpowers a) : Finset.image (fun i => a ^ i) (range (orderOf a)) = uni
v
-/
theorem IsCyclic.image_range_card (ha : ∀ x : α, x ∈ zpowers a) :
    Finset.image (fun i => a ^ i) (range (Nat.card α)) = univ := by
  rw [← orderOf_eq_card_of_forall_mem_zpowers ha, IsCyclic.image_range_orderOf ha]

@[to_additive]
/-
**IsCyclic.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCyclic.ext [Finite G] [IsCyclic G] {d : Nat} {a b : ZMod d} (hGcard : Na
t.card G = d) (h : forall t : G, t ^ a.val = t ^ b.val) : a = b
参数：hGcard : Nat.card G = d；h : forall t : G, t ^ a.val = t ^ b.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `Nat.instNeZeroCardOfNonemptyOfFinite`：∀ {α : Type u_1} [Nonempty α] [Fin
ite α], NeZero (Nat.card α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ZMod.cast_id'`：cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `pow_eq_pow_iff_modEq`：pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD 
orderOf x]
-/
lemma IsCyclic.ext [Finite G] [IsCyclic G] {d : ℕ} {a b : ZMod d}
    (hGcard : Nat.card G = d) (h : ∀ t : G, t ^ a.val = t ^ b.val) : a = b := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  specialize h g
  subst hGcard
  rw [pow_eq_pow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers hg,
    ← ZMod.natCast_eq_natCast_iff] at h
  simpa [ZMod.natCast_val, ZMod.cast_id'] using h

end

end Cyclic

end

