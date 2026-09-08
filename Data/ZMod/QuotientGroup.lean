/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# `ZMod n` and quotient groups / rings

This file relates `ZMod n` to the quotient group `ℤ / AddSubgroup.zmultiples (n : ℤ)`.

## Main definitions

- `ZMod.quotientZMultiplesNatEquivZMod` and `ZMod.quotientZMultiplesEquivZMod`:
  `ZMod n` is the group quotient of `ℤ` by `n ℤ := AddSubgroup.zmultiples (n)`,
  (where `n : ℕ` and `n : ℤ` respectively)
- `ZMod.lift n f` is the map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

open QuotientAddGroup Set ZMod
open scoped IsMulCommutative

variable (n : ℕ) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

/-- `ℤ` modulo multiples of `n : ℕ` is `ZMod n`. -/
/-
**Int.quotientZMultiplesNatEquivZMod** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：quotientZMultiplesNatEquivZMod : Int ⧸ AddSubgroup.zmultiples (n : Int) ≃+
 ZMod n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.ker_intCastAddHom`：ker_intCastAddHom (n : Nat) : (Int.castAddHom (Z
Mod n)).ker = AddSubgroup.zmultiples (n : Int)
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a

--- 原说明 ---
`ℤ` modulo multiples of `n : ℕ` is `ZMod n`.
-/
def quotientZMultiplesNatEquivZMod : ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  (quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans <|
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast

/-- `ℤ` modulo multiples of `a : ℤ` is `ZMod a.natAbs`. -/
/-
**Int.quotientZMultiplesEquivZMod** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：quotientZMultiplesEquivZMod (a : Int) : Int ⧸ AddSubgroup.zmultiples a ≃+ 
ZMod a.natAbs
参数：a : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.zmultiples_natAbs`：Int.zmultiples_natAbs (a : Int) : AddSubgroup.zmu
ltiples (a.natAbs : Int) = AddSubgroup.zmultiples a

--- 原说明 ---
`ℤ` modulo multiples of `a : ℤ` is `ZMod a.natAbs`.
-/
def quotientZMultiplesEquivZMod (a : ℤ) : ℤ ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)

@[simp]
/-
**Int.index_zmultiples** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：index_zmultiples (a : Int) : (AddSubgroup.zmultiples a).index = a.natAbs
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.index.eq_1`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSub
group G), H.index = Nat.card (G ⧸ H)
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
-/
lemma index_zmultiples (a : ℤ) : (AddSubgroup.zmultiples a).index = a.natAbs := by
  rw [AddSubgroup.index, Nat.card_congr (quotientZMultiplesEquivZMod a).toEquiv, Nat.card_zmod]

end Int


namespace AddAction

open AddSubgroup AddMonoidHom AddEquiv Function

variable {α β : Type*} [AddGroup α] (a : α) [AddAction α β] (b : β)

/-- The quotient `(ℤ ∙ a) ⧸ (stabilizer b)` is cyclic of order `minimalPeriod (a +ᵥ ·) b`. -/
/-
**AddAction.zmultiplesQuotientStabilizerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddActi
on`。
形式化陈述：zmultiplesQuotientStabilizerEquiv : zmultiples a ⧸ stabilizer (zmultiples 
a) b ≃+ ZMod (minimalPeriod (a +ᵥ ·) b)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.mem_zmultiples`：∀ {G : Type u_1} [inst : AddGroup G] (g : G)
, g ∈ AddSubgroup.zmultiples g

--- 原说明 ---
The quotient `(ℤ ∙ a) ⧸ (stabilizer b)` is cyclic of order `minimalPeriod (a +ᵥ 
·) b`.
-/
noncomputable def zmultiplesQuotientStabilizerEquiv :
    zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le, mem_comap, mem_stabilizer_iff, zmultiplesHom_apply, natCast_zsmul]
              simp_rw [← vadd_iterate]
              exact isPeriodicPt_minimalPeriod (a +ᵥ ·) b))
          ⟨by
            rw [← ker_eq_bot_iff, eq_bot_iff]
            refine fun q => induction_on q fun n hn => ?_
            rw [mem_bot, eq_zero_iff, Int.mem_zmultiples_iff, ←
              zsmul_vadd_eq_iff_minimalPeriod_dvd]
            exact (eq_zero_iff _).mp hn, fun q =>
            induction_on q fun ⟨_, n, rfl⟩ => ⟨n, rfl⟩⟩).symm.trans
    (Int.quotientZMultiplesNatEquivZMod (minimalPeriod (a +ᵥ ·) b))
/-
**AddAction.zmultiplesQuotientStabilizerEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名
空间 `AddAction`。
形式化陈述：zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a +
ᵥ ·) b)) : (zmultiplesQuotientStabilizerEquiv a b).symm n = (cast n : Int) • (⟨a
, mem_zmultiples a⟩ : zmultiples a)
参数：n : ZMod (minimalPeriod (a +ᵥ ·) b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.zmultiples_isAddCommutative`：∀ {G : Type u_1} [inst : AddGro
up G] (g : G), IsAddCommutative ↥(AddSubgroup.zmultiples g)
-/
theorem zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a +ᵥ ·) b)) :
    (zmultiplesQuotientStabilizerEquiv a b).symm n =
      (cast n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
  rfl

end AddAction

namespace MulAction

open AddAction Subgroup AddSubgroup Function

variable {α β : Type*} [Group α] (a : α) [MulAction α β] (b : β)

/-- The quotient `(a ^ ℤ) ⧸ (stabilizer b)` is cyclic of order `minimalPeriod ((•) a) b`. -/
/-
**MulAction.zpowersQuotientStabilizerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`
。
形式化陈述：zpowersQuotientStabilizerEquiv : zpowers a ⧸ stabilizer (zpowers a) b ≃* M
ultiplicative (ZMod (minimalPeriod (a • ·) b))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient `(a ^ ℤ) ⧸ (stabilizer b)` is cyclic of order `minimalPeriod ((•) a
) b`.
-/
noncomputable def zpowersQuotientStabilizerEquiv :
    zpowers a ⧸ stabilizer (zpowers a) b ≃* Multiplicative (ZMod (minimalPeriod (a • ·) b)) :=
  letI f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  AddEquiv.toMultiplicative f
/-
**MulAction.zpowersQuotientStabilizerEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 
`MulAction`。
形式化陈述：zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a • ·)
 b)) : (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowe
rs a) ^ (cast n : Int)
参数：n : ZMod (minimalPeriod (a • ·) b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
-/
theorem zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a • ·) b)) :
    (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast n : ℤ) :=
  rfl

/-- The orbit `(a ^ ℤ) • b` is a cycle of order `minimalPeriod ((•) a) b`. -/
/-
**MulAction.orbitZPowersEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：orbitZPowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The orbit `(a ^ ℤ) • b` is a cycle of order `minimalPeriod ((•) a) b`.
-/
noncomputable def orbitZPowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b) :=
  (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv

/-- The orbit `(ℤ • a) +ᵥ b` is a cycle of order `minimalPeriod (a +ᵥ ·) b`. -/
/-
**MulAction._root_.AddAction.orbitZMultiplesEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Mul
Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orbit `(ℤ • a) +ᵥ b` is a cycle of order `minimalPeriod (a +ᵥ ·) b`.
-/
noncomputable def _root_.AddAction.orbitZMultiplesEquiv {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) :
    AddAction.orbit (zmultiples a) b ≃ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv

attribute [to_additive existing] orbitZPowersEquiv

@[to_additive]
/-
**MulAction.orbitZPowersEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：orbitZPowersEquiv_symm_apply (k : ZMod (minimalPeriod (a • ·) b)) : (orbit
ZPowersEquiv a b).symm k = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast k : Int) • ⟨
b, mem_orbit_self b⟩
参数：k : ZMod (minimalPeriod (a • ·) b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem orbitZPowersEquiv_symm_apply (k : ZMod (minimalPeriod (a • ·) b)) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast k : ℤ) • ⟨b, mem_orbit_self b⟩ :=
  rfl
/-
**MulAction.orbitZPowersEquiv_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：orbitZPowersEquiv_symm_apply' (k : Int) : (orbitZPowersEquiv a b).symm k =
 (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩
参数：k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.orbitZPowersEquiv_symm_apply`：orbitZPowersEquiv_symm_apply (k 
: ZMod (minimalPeriod (a • ·) b)) : (orbitZPowersEquiv a b).symm k = (⟨a, mem_zp
owers a⟩ : zpowers a) ^ (cas…
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MulAction.zpow_smul_mod_minimalPeriod`：∀ {α : Type v} {G : Type u} [inst
 : Group G] [inst_1 : MulAction G α] (a : G) (b : α) (n : ℤ),   a ^ (n % ↑(Funct
ion.minimalPeriod (fun x =>…
-/
theorem orbitZPowersEquiv_symm_apply' (k : ℤ) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ := by
  rw [orbitZPowersEquiv_symm_apply, ZMod.coe_intCast]
  exact Subtype.ext (zpow_smul_mod_minimalPeriod _ _ k)
/-
**MulAction._root_.AddAction.orbitZMultiplesEquiv_symm_apply'** 是 Mathlib 中的一个定理
，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddAction.orbitZMultiplesEquiv_symm_apply' {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) (k : ℤ) :
    (AddAction.orbitZMultiplesEquiv a b).symm k =
      k • (⟨a, mem_zmultiples a⟩ : zmultiples a) +ᵥ ⟨b, AddAction.mem_orbit_self b⟩ := by
  rw [AddAction.orbitZMultiplesEquiv_symm_apply, ZMod.coe_intCast]
  -- Making `a` explicit turns this from ~190000 heartbeats to ~700.
  exact Subtype.ext (zsmul_vadd_mod_minimalPeriod a _ k)

attribute [to_additive existing]
  orbitZPowersEquiv_symm_apply'

@[to_additive]
/-
**MulAction.minimalPeriod_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] : minimalPeriod (a •
 ·) b = Fintype.card (orbit (zpowers a) b)
参数：orbit (zpowers a) b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
-/
theorem minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] :
    minimalPeriod (a • ·) b = Fintype.card (orbit (zpowers a) b) := by
  rw [← Fintype.ofEquiv_card (orbitZPowersEquiv a b), ZMod.card]

@[to_additive]
/-
**MulAction.minimalPeriod_pos** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：minimalPeriod_pos [Finite <| orbit (zpowers a) b] : NeZero minimalPeriod (
a • ·) b
参数：zpowers a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `MulAction.nonempty_orbit`：nonempty_orbit (a : α) : Set.Nonempty (orbit M
 a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.minimalPeriod_eq_card`：minimalPeriod_eq_card [Fintype (orbit (
zpowers a) b)] : minimalPeriod (a • ·) b = Fintype.card (orbit (zpowers a) b)
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
-/
instance minimalPeriod_pos [Finite <| orbit (zpowers a) b] :
    NeZero <| minimalPeriod (a • ·) b :=
  ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    have : Nonempty (orbit (zpowers a) b) := (nonempty_orbit b).to_subtype
    rw [minimalPeriod_eq_card]
    exact Fintype.card_ne_zero⟩

end MulAction

section Group

open Subgroup

variable {α : Type*} [Group α] (a : α)

/-- See also `Fintype.card_zpowers`. -/
@[to_additive (attr := simp) /-- See also `Fintype.card_zmultiples`. -/]
/-
**Nat.card_zpowers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orbit_subgroup_one_eq_self`：orbit_subgroup_one_eq_self : MulAction.orbit
 s (1 : α) = s
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n

--- 原说明 ---
See also `Fintype.card_zpowers`.
-/
theorem Nat.card_zpowers : Nat.card (zpowers a) = orderOf a := by
  have := Nat.card_congr (MulAction.orbitZPowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this

variable {a}

@[to_additive (attr := simp)]
/-
**finite_zpowers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrder a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrder a := by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, OneMemClass.coe_nonempty, true_and]

@[to_additive (attr := simp)]
/-
**infinite_zpowers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `finite_zpowers`：finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrd
er a
-/
lemma infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a := finite_zpowers.not

@[to_additive]
protected alias ⟨_, IsOfFinOrder.finite_zpowers⟩ := finite_zpowers

end Group

namespace Subgroup
variable {G : Type*} [Group G] (H : Subgroup G) (g : G)

open Equiv Function MulAction

/-- Partition `G ⧸ H` into orbits of the action of `g : G`. -/
/-
**Subgroup.quotientEquivSigmaZMod** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientEquivSigmaZMod : G ⧸ H ≃ Σ q : orbitRel.Quotient (zpowers g) (G ⧸ 
H), ZMod (minimalPeriod (g • ·) q.out)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Partition `G ⧸ H` into orbits of the action of `g : G`.
-/
noncomputable def quotientEquivSigmaZMod :
    G ⧸ H ≃ Σ q : orbitRel.Quotient (zpowers g) (G ⧸ H), ZMod (minimalPeriod (g • ·) q.out) :=
  (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZPowersEquiv g q.out)
/-
**Subgroup.quotientEquivSigmaZMod_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup
`。
形式化陈述：quotientEquivSigmaZMod_symm_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ 
H)) (k : ZMod (minimalPeriod (g • ·) q.out)) : (quotientEquivSigmaZMod H g).symm
 ⟨q, k⟩ = g ^ (cast k : Int) • q.out
参数：q : orbitRel.Quotient (zpowers g) (G ⧸ H)；k : ZMod (minimalPeriod (g • ·) q.o
ut)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma quotientEquivSigmaZMod_symm_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    (quotientEquivSigmaZMod H g).symm ⟨q, k⟩ = g ^ (cast k : ℤ) • q.out := rfl
/-
**Subgroup.quotientEquivSigmaZMod_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：quotientEquivSigmaZMod_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (
k : Int) : quotientEquivSigmaZMod H g (g ^ k • q.out) = ⟨q, k⟩
参数：q : orbitRel.Quotient (zpowers g) (G ⧸ H)；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用引理 `Subgroup.quotientEquivSigmaZMod_symm_apply`：quotientEquivSigmaZMod_symm_
apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ZMod (minimalPeriod (g • 
·) q.out)) : (quotientEquivSigma…
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用定理 `MulAction.zpow_smul_mod_minimalPeriod`：∀ {α : Type v} {G : Type u} [inst
 : Group G] [inst_1 : MulAction G α] (a : G) (b : α) (n : ℤ),   a ^ (n % ↑(Funct
ion.minimalPeriod (fun x =>…
-/
lemma quotientEquivSigmaZMod_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ℤ) :
    quotientEquivSigmaZMod H g (g ^ k • q.out) = ⟨q, k⟩ := by
  rw [← eq_symm_apply, quotientEquivSigmaZMod_symm_apply, ZMod.coe_intCast,
    zpow_smul_mod_minimalPeriod]

set_option backward.isDefEq.respectTransparency false in
/-- The sum of minimal periods over all orbits equals the index `[G:H]`. -/
/-
**Subgroup.index_eq_sum_minimalPeriod** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_eq_sum_minimalPeriod (g : G) [Finite (G ⧸ H)] [Fintype (Quotient (Mu
lAction.orbitRel (zpowers g) (G ⧸ H)))] : H.index = ∑ q : Quotient (MulAction.or
bitRel (zpowers g) (G ⧸ H)), Function.minimalPeriod (g • ·) q.out
参数：g : G；G ⧸ H；Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulAction.minimalPeriod_eq_card`：minimalPeriod_eq_card [Fintype (orbit (
zpowers a) b)] : minimalPeriod (a • ·) b = Fintype.card (orbit (zpowers a) b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β

--- 原说明 ---
The sum of minimal periods over all orbits equals the index `[G:H]`.
-/
lemma index_eq_sum_minimalPeriod (g : G) [Finite (G ⧸ H)]
    [Fintype (Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H)))] :
    H.index = ∑ q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H)),
      Function.minimalPeriod (g • ·) q.out := by
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have (q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H))) :
      Fintype (MulAction.orbit (zpowers g) q.out) := Fintype.ofFinite _
  simp only [MulAction.minimalPeriod_eq_card, index_eq_card, Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (MulAction.selfEquivSigmaOrbits (zpowers g) (G ⧸ H))

end Subgroup

