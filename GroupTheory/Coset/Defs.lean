/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
module

public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Cosets

This file develops the basic theory of left and right cosets.

When `G` is a group and `a : G`, `s : Set G`, with  `open scoped Pointwise` we can write:
* the left coset of `s` by `a` as `a • s`
* the right coset of `s` by `a` as `MulOpposite.op a • s` (or `op a • s` with `open MulOpposite`,
  or `s <• a` with `open scoped Pointwise RightActions`)

If instead `G` is an additive group, we can write (with  `open scoped Pointwise` still)
* the left coset of `s` by `a` as `a +ᵥ s`
* the right coset of `s` by `a` as `AddOpposite.op a +ᵥ s` (or `op a +ᵥ s` with `open AddOpposite`,
  or `s <+ᵥ a` with `open scoped Pointwise RightActions`)

## Main definitions

* `QuotientGroup.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `AddGroup` this is `QuotientAddGroup.quotient s`.
* `QuotientGroup.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `AddGroup` this is `QuotientAddGroup.mk`.

## Notation

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Properly merge with pointwise actions on sets, by renaming and deduplicating lemmas as appropriate.
-/

@[expose] public section

assert_not_exists Cardinal

open Function Set
open scoped Pointwise

variable {α : Type*}

/- Ensure that `@[to_additive]` uses the right namespace. -/
insert_to_additive_translation QuotientGroup QuotientAddGroup

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup. -/
@[to_additive (attr := instance_reducible)
  /-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup. -/]
/-
**QuotientGroup.leftRel** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：leftRel : Setoid α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def leftRel : Setoid α :=
  MulAction.orbitRel s.op α

variable {s} in
@[to_additive]
/-
**QuotientGroup.leftRel_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：leftRel_apply {x y : α} : leftRel s x y ↔ x⁻¹ * y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem leftRel_apply {x y : α} : leftRel s x y ↔ x⁻¹ * y ∈ s :=
  calc
    (∃ a : s.op, y * MulOpposite.unop a = x) ↔ ∃ a : s, y * a = x :=
      s.equivOp.symm.exists_congr_left
    _ ↔ ∃ a : s, x⁻¹ * y = a⁻¹ := by
      simp only [inv_mul_eq_iff_eq_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y ∈ s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]
/-
**QuotientGroup.leftRel_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：leftRel_eq : ⇑(leftRel s) = fun x y => x⁻¹ * y in s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
-/
theorem leftRel_eq : ⇑(leftRel s) = fun x y => x⁻¹ * y ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    apply leftRel_apply

@[to_additive]
/-
**QuotientGroup.leftRelDecidable** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：leftRelDecidable [DecidablePred (· in s)] : DecidableRel (leftRel s).r
参数：· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (leftRel s).r := fun x y => by
  rw [leftRel_eq]
  exact ‹DecidablePred (· ∈ s)› _

/-- `α ⧸ s` is the quotient type representing the left cosets of `s`. If `s` is a normal subgroup,
`α ⧸ s` is a group -/
@[to_additive /-- `α ⧸ s` is the quotient type representing the left cosets of `s`. If `s` is a
normal subgroup, `α ⧸ s` is a group -/]
/-
**QuotientGroup.instHasQuotientSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup
`。
形式化陈述：instHasQuotientSubgroup : HasQuotient α (Subgroup α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasQuotientSubgroup : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotient (leftRel s)⟩

@[to_additive]
/-
**QuotientGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidablePred (· ∈ s)] : DecidableEq (α ⧸ s) :=
  @Quotient.decidableEq _ _ (leftRelDecidable _)

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive (attr := instance_reducible)
  /-- The equivalence relation corresponding to the partition of a group by right cosets
  of a subgroup. -/]
/-
**QuotientGroup.rightRel** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：rightRel : Setoid α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rightRel : Setoid α :=
  MulAction.orbitRel s α

variable {s} in
@[to_additive]
/-
**QuotientGroup.rightRel_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：rightRel_apply {x y : α} : rightRel s x y ↔ y * x⁻¹ in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem rightRel_apply {x y : α} : rightRel s x y ↔ y * x⁻¹ ∈ s :=
  calc
    (∃ a : s, (a : α) * y = x) ↔ ∃ a : s, y * x⁻¹ = a⁻¹ := by
      simp only [mul_inv_eq_iff_eq_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
    _ ↔ y * x⁻¹ ∈ s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]
/-
**QuotientGroup.rightRel_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：rightRel_eq : ⇑(rightRel s) = fun x y => y * x⁻¹ in s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `QuotientGroup.rightRel_apply`：rightRel_apply {x y : α} : rightRel s x y 
↔ y * x⁻¹ in s
-/
theorem rightRel_eq : ⇑(rightRel s) = fun x y => y * x⁻¹ ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    apply rightRel_apply

@[to_additive]
/-
**QuotientGroup.rightRelDecidable** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：rightRelDecidable [DecidablePred (· in s)] : DecidableRel (rightRel s).r
参数：· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (rightRel s).r := fun x y => by
  rw [rightRel_eq]
  exact ‹DecidablePred (· ∈ s)› _

/-- Right cosets are in bijection with left cosets. -/
@[to_additive /-- Right cosets are in bijection with left cosets. -/]
/-
**QuotientGroup.quotientRightRelEquivQuotientLeftRel** 是 Mathlib 中的一个定义，位于命名空间 `
QuotientGroup`。
形式化陈述：quotientRightRelEquivQuotientLeftRel : Quotient (QuotientGroup.rightRel s)
 ≃ α ⧸ s where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
Right cosets are in bijection with left cosets.
-/
def quotientRightRelEquivQuotientLeftRel : Quotient (QuotientGroup.rightRel s) ≃ α ⧸ s where
  toFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply, rightRel_apply]
      exact fun h => (congr_arg (· ∈ s) (by simp)).mp (s.inv_mem h)
  invFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply, rightRel_apply]
      exact fun h => (congr_arg (· ∈ s) (by simp)).mp (s.inv_mem h)
  left_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)
  right_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive (attr := coe)
/-- The canonical map from an `AddGroup` `α` to the quotient `α ⧸ s`. -/]
/-
**QuotientGroup.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `QuotientGroup`。
形式化陈述：mk (a : α) : α ⧸ s
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
abbrev mk (a : α) : α ⧸ s :=
  Quotient.mk'' a

@[to_additive]
/-
**QuotientGroup.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_surjective : Function.Surjective @mk _ _ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
theorem mk_surjective : Function.Surjective <| @mk _ _ s :=
  Quotient.mk''_surjective

@[to_additive (attr := simp)]
/-
**QuotientGroup.range_mk** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：range_mk : range (QuotientGroup.mk (s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
lemma range_mk : range (QuotientGroup.mk (s := s)) = univ := range_eq_univ.mpr mk_surjective

@[to_additive (attr := elab_as_elim)]
/-
**QuotientGroup.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s) (H : forall z, C (QuotientGro
up.mk z)) : C x
参数：x : α ⧸ s；H : forall z, C (QuotientGroup.mk z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
theorem induction_on {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z, C (QuotientGroup.mk z)) : C x :=
  Quotient.inductionOn' x H

@[to_additive]
/-
**QuotientGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe α (α ⧸ s) :=
  ⟨mk⟩

@[to_additive] alias induction_on' := induction_on

@[to_additive (attr := simp)]
/-
**QuotientGroup.quotient_liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：quotient_liftOn_mk {β} (f : α -> β) (h) (x : α) : Quotient.liftOn' (x : α 
⧸ s) f h = f x
参数：f : α -> β；h；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotient_liftOn_mk {β} (f : α → β) (h) (x : α) : Quotient.liftOn' (x : α ⧸ s) f h = f x :=
  rfl

@[to_additive]
/-
**QuotientGroup.forall_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：forall_mk {C : α ⧸ s -> Prop} : (forall x : α ⧸ s, C x) ↔ forall x : α, C 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
theorem forall_mk {C : α ⧸ s → Prop} : (∀ x : α ⧸ s, C x) ↔ ∀ x : α, C x :=
  mk_surjective.forall

@[to_additive]
/-
**QuotientGroup.exists_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：exists_mk {C : α ⧸ s -> Prop} : (exists x : α ⧸ s, C x) ↔ exists x : α, C 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
theorem exists_mk {C : α ⧸ s → Prop} : (∃ x : α ⧸ s, C x) ↔ ∃ x : α, C x :=
  mk_surjective.exists

@[to_additive]
/-
**QuotientGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : Subgroup α) : Inhabited (α ⧸ s) :=
  ⟨((1 : α) : α ⧸ s)⟩

@[to_additive]
/-
**QuotientGroup.eq** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a b : α}, ↑a = ↑b ↔ a⁻
¹ * b ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s :=
  calc
    _ ↔ leftRel s a b := Quotient.eq''
    _ ↔ _ := by rw [leftRel_apply]

@[to_additive]
/-
**QuotientGroup.out_eq'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：out_eq' (a : α ⧸ s) : mk a.out = a
参数：a : α ⧸ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem out_eq' (a : α ⧸ s) : mk a.out = a :=
  Quotient.out_eq' a

variable (s)

/-- It can be useful to write `obtain ⟨h, H⟩ := mk_out_eq_mul ...`, and then `rw [H]` or
`simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work, this lemma is
stated in terms of an arbitrary `h : s`, rather than the specific `h = g⁻¹ * (mk g).out`. -/
@[to_additive]
/-
**QuotientGroup.mk_out_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_out_eq_mul (g : α) : exists h : s, (mk g : α ⧸ s).out = g * h
参数：g : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b

--- 原说明 ---
It can be useful to write `obtain ⟨h, H⟩ := mk_out_eq_mul ...`, and then `rw [H]
` or
`simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work
, this lemma is
stated in terms of an arbitrary `h : s`, rather than the specific `h = g⁻¹ * (mk
 g).out`.
-/
theorem mk_out_eq_mul (g : α) : ∃ h : s, (mk g : α ⧸ s).out = g * h :=
  ⟨⟨g⁻¹ * (mk g).out, QuotientGroup.eq.mp (mk g).out_eq'.symm⟩, by rw [mul_inv_cancel_left]⟩

variable {s} {a b : α}

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_mul_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_mul_of_mem (a : α) (hb : b in s) : (mk (a * b) : α ⧸ s) = mk a
参数：a : α；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
-/
theorem mk_mul_of_mem (a : α) (hb : b ∈ s) : (mk (a * b) : α ⧸ s) = mk a := by
  rwa [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]
/-
**QuotientGroup.preimage_image_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：preimage_image_mk (N : Subgroup α) (s : Set α) : mk ⁻¹' ((mk : α -> α ⧸ N)
 '' s) = ⋃ x : N, (· * (x : α)) ⁻¹' s
参数：N : Subgroup α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem preimage_image_mk (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) ⁻¹' s := by
  ext x
  simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_iUnion,
    Set.mem_image]
  exact
    ⟨fun ⟨y, hs, hN⟩ => ⟨_, N.inv_mem hN, by simpa using hs⟩, fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by simpa using hz⟩⟩

@[to_additive]
/-
**QuotientGroup.preimage_image_mk_eq_iUnion_image** 是 Mathlib 中的一个定理，位于命名空间 `Quo
tientGroup`。
形式化陈述：preimage_image_mk_eq_iUnion_image (N : Subgroup α) (s : Set α) : mk ⁻¹' ((
mk : α -> α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) '' s
参数：N : Subgroup α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.preimage_image_mk`：preimage_image_mk (N : Subgroup α) (s :
 Set α) : mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) ⁻¹' s
· 使用定理 `Set.iUnion_congr_of_surjective`：iUnion_congr_of_surjective {f : ι -> Set
 α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h) (h2 : forall x, g (h x) 
= f x) : ⋃ x, f x = …
· 使用定理 `inv_surjective`：inv_surjective : Function.Surjective (Inv.inv : G -> G)
· 使用定理 `Set.image_mul_right'`：image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t
-/
theorem preimage_image_mk_eq_iUnion_image (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) '' s := by
  rw [preimage_image_mk, iUnion_congr_of_surjective (·⁻¹) inv_surjective]
  exact fun x ↦ image_mul_right'

@[to_additive]
/-
**QuotientGroup.preimage_image_mk_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGrou
p`。
形式化陈述：preimage_image_mk_eq_mul (N : Subgroup α) (s : Set α) : mk ⁻¹' ((mk : α ->
 α ⧸ N) '' s) = s * N
参数：N : Subgroup α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.preimage_image_mk_eq_iUnion_image`：preimage_image_mk_eq_iU
nion_image (N : Subgroup α) (s : Set α) : mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = ⋃ x 
: N, (· * (x : α)) '' s
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_mul`：image2_mul : image2 (· * ·) s t = s * t
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_image_mk_eq_mul (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = s * N := by
  rw [preimage_image_mk_eq_iUnion_image, iUnion_subtype, ← image2_mul, ← iUnion_image_right]
  simp only [SetLike.mem_coe]

@[to_additive]
/-
**QuotientGroup.preimage_mk_one** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：preimage_mk_one (N : Subgroup α) : mk ⁻¹' {(mk : α -> α ⧸ N) 1} = N
参数：N : Subgroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `QuotientGroup.preimage_image_mk_eq_mul`：preimage_image_mk_eq_mul (N : Su
bgroup α) (s : Set α) : mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = s * N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mk_one (N : Subgroup α) :
    mk ⁻¹' {(mk : α → α ⧸ N) 1} = N := by
  rw [← image_singleton, preimage_image_mk_eq_mul]
  simp

end QuotientGroup

@[deprecated (since := "2026-07-12")]
alias QuotientAddGroup.mk_out_eq_mul := QuotientAddGroup.mk_out_eq_add

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

variable {t : Subgroup α}

/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/
@[to_additive
/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/]
/-
**Subgroup.quotientEquivOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientEquivOfEq (h : s = t) : α ⧸ s ≃ α ⧸ t where toFun
参数：h : s = t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
def quotientEquivOfEq (h : s = t) : α ⧸ s ≃ α ⧸ t where
  toFun := Quotient.map' id fun _a _b h' => h ▸ h'
  invFun := Quotient.map' id fun _a _b h' => h.symm ▸ h'
  left_inv q := induction_on q fun _g => rfl
  right_inv q := induction_on q fun _g => rfl
/-
**Subgroup.quotientEquivOfEq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：quotientEquivOfEq_mk (h : s = t) (a : α) : quotientEquivOfEq h (QuotientGr
oup.mk a) = QuotientGroup.mk a
参数：h : s = t；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquivOfEq_mk (h : s = t) (a : α) :
    quotientEquivOfEq h (QuotientGroup.mk a) = QuotientGroup.mk a :=
  rfl

end Subgroup

