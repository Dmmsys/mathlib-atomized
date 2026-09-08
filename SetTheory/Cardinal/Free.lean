/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Daniel Weber
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinalities of free constructions

This file shows that all the free constructions over `α` have cardinality `max #α ℵ₀`,
and are thus infinite, and specifically countable over countable generators.

Combined with the ring `Fin n` for the finite cases, this lets us show that there is a `CommRing` of
any cardinality.
-/

public section

universe u
variable (α : Type u)

section Infinite

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Infinite (FreeMonoid α) := inferInstanceAs <| Infinite (List α)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Infinite (FreeGroup α) := by
  classical
  exact Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Infinite (FreeAbelianGroup α) :=
  (FreeAbelianGroup.equivFinsupp α).toEquiv.infinite_iff.2 inferInstance

deriving instance Infinite for FreeRing, FreeCommRing

end Infinite

section Countable

variable [Countable α]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (FreeMonoid α) := inferInstanceAs <| Countable (List α)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (FreeGroup α) := inferInstanceAs <| Countable (Quot _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (FreeAbelianGroup α) := inferInstanceAs <| Countable (Quot _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (FreeRing α) := inferInstanceAs <| Countable (Quot _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (FreeCommRing α) :=
  inferInstanceAs <| Countable (FreeAbelianGroup (Multiset α))

end Countable

namespace Cardinal

/-
**Cardinal.mk_abelianization_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_abelianization_le (G : Type u) [Group G] : #(Abelianization G) <= #G
参数：G : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
theorem mk_abelianization_le (G : Type u) [Group G] :
    #(Abelianization G) ≤ #G := Cardinal.mk_le_of_surjective Quotient.mk_surjective

@[to_additive (attr := simp)]
/-
**Cardinal.mk_freeMonoid** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_freeMonoid [Nonempty α] : #(FreeMonoid α) = max #α ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_list_eq_max_mk_aleph0`：mk_list_eq_max_mk_aleph0 (α : Type u)
 [Nonempty α] : #(List α) = max #α ℵ₀
-/
theorem mk_freeMonoid [Nonempty α] : #(FreeMonoid α) = max #α ℵ₀ :=
    Cardinal.mk_list_eq_max_mk_aleph0 _

@[to_additive (attr := simp)]
/-
**Cardinal.mk_freeGroup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_freeGroup [Nonempty α] : #(FreeGroup α) = max #α ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `FreeGroup.toWord_injective`：toWord_injective : Function.Injective (toWor
d : FreeGroup α -> List (α × Bool))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_list_eq_max_mk_aleph0`：mk_list_eq_max_mk_aleph0 (α : Type u)
 [Nonempty α] : #(List α) = max #α ℵ₀
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_ofNat`：lift_ofNat (n : Nat) [n.AtLeastTwo] : lift.{u} (ofN
at(n) : Cardinal.{v}) = OfNat.ofNat n
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.mul_lt_aleph0`：mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb
 : b < ℵ₀) : a * b < ℵ₀
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.le_mul_right`：le_mul_right {a b : Cardinal} (h : b != 0) : a <=
 a * b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.mul_eq_left`：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) (hb' : b != 0) : a * b = a
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
（共 35 条，此处仅展示前 30 条）
-/
theorem mk_freeGroup [Nonempty α] : #(FreeGroup α) = max #α ℵ₀ := by
  classical
  apply le_antisymm
  · apply (mk_le_of_injective (FreeGroup.toWord_injective (α := α))).trans_eq
    simp only [mk_list_eq_max_mk_aleph0, mk_prod, lift_uzero, mk_fintype, Fintype.card_bool,
      Nat.cast_ofNat, lift_ofNat]
    obtain hα | hα := lt_or_ge #α ℵ₀
    · simp only [hα.le, max_eq_right, max_eq_right_iff]
      exact (mul_lt_aleph0 hα natCast_lt_aleph0).le
    · rw [max_eq_left hα, max_eq_left (hα.trans <| Cardinal.le_mul_right two_ne_zero),
        Cardinal.mul_eq_left hα _ (by simp)]
      exact natCast_le_aleph0.trans hα
  · apply max_le
    · exact mk_le_of_injective FreeGroup.of_injective
    · simp

@[simp]
/-
**Cardinal.mk_freeAbelianGroup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_freeAbelianGroup [Nonempty α] : #(FreeAbelianGroup α) = max #α ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite'`：mk_finsupp_lift_of_infinite' (α :
 Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_freeAbelianGroup [Nonempty α] : #(FreeAbelianGroup α) = max #α ℵ₀ := by
  rw [Cardinal.mk_congr (FreeAbelianGroup.equivFinsupp α).toEquiv]
  simp

@[simp]
/-
**Cardinal.mk_freeRing** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_freeRing : #(FreeRing α) = max #α ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableFreeAbelianGroup`：∀ (α : Type u) [Countable α], Countable (
FreeAbelianGroup α)
· 使用定理 `instCountableFreeMonoid`：∀ (α : Type u) [Countable α], Countable (FreeMo
noid α)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `instInfiniteFreeAbelianGroupOfNonempty`：∀ (α : Type u) [Nonempty α], Inf
inite (FreeAbelianGroup α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.mk_freeAbelianGroup`：mk_freeAbelianGroup [Nonempty α] : #(FreeA
belianGroup α) = max #α ℵ₀
· 使用定理 `Cardinal.mk_freeMonoid`：mk_freeMonoid [Nonempty α] : #(FreeMonoid α) = m
ax #α ℵ₀
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem mk_freeRing : #(FreeRing α) = max #α ℵ₀ := by
  cases isEmpty_or_nonempty α <;> simp [FreeRing]

@[simp]
/-
**Cardinal.mk_freeCommRing** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_freeCommRing : #(FreeCommRing α) = max #α ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableFreeAbelianGroup`：∀ (α : Type u) [Countable α], Countable (
FreeAbelianGroup α)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instInfiniteFreeAbelianGroupOfNonempty`：∀ (α : Type u) [Nonempty α], Inf
inite (FreeAbelianGroup α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.mk_freeAbelianGroup`：mk_freeAbelianGroup [Nonempty α] : #(FreeA
belianGroup α) = max #α ℵ₀
· 使用定理 `Cardinal.mk_multiset_of_nonempty`：mk_multiset_of_nonempty (α : Type u) [
Nonempty α] : #(Multiset α) = max #α ℵ₀
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem mk_freeCommRing : #(FreeCommRing α) = max #α ℵ₀ := by
  cases isEmpty_or_nonempty α <;> simp [FreeCommRing]

end Cardinal

section Nonempty

/-- A commutative ring can be constructed on any non-empty type.

See also `Infinite.nonempty_field`. -/
/-
**nonempty_commRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nonempty_commRing [Nonempty α] : Nonempty (CommRing α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Cardinal.mk_freeCommRing`：mk_freeCommRing : #(FreeCommRing α) = max #α ℵ
₀
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A commutative ring can be constructed on any non-empty type.

See also `Infinite.nonempty_field`.
-/
instance nonempty_commRing [Nonempty α] : Nonempty (CommRing α) := by
  obtain hR | hR := finite_or_infinite α
  · obtain ⟨x⟩ := nonempty_fintype α
    have : NeZero (Fintype.card α) := ⟨by simp⟩
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFin α
    exact ⟨open scoped Fin.CommRing in e.commRing⟩
  · have ⟨e⟩ : Nonempty (α ≃ FreeCommRing α) := by simp [← Cardinal.eq]
    exact ⟨e.commRing⟩

@[simp]
/-
**nonempty_commRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_commRing_iff : Nonempty (CommRing α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem nonempty_commRing_iff : Nonempty (CommRing α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => nonempty_commRing _⟩

@[simp]
/-
**nonempty_ring_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_ring_iff : Nonempty (Ring α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem nonempty_ring_iff : Nonempty (Ring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toRing)⟩

@[simp]
/-
**nonempty_commSemiring_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_commSemiring_iff : Nonempty (CommSemiring α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem nonempty_commSemiring_iff : Nonempty (CommSemiring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toCommSemiring)⟩

@[simp]
/-
**nonempty_semiring_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_semiring_iff : Nonempty (Semiring α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem nonempty_semiring_iff : Nonempty (Semiring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toSemiring)⟩

end Nonempty

