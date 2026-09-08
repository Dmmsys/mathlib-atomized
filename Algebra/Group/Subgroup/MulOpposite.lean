/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.MulOpposite

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/

@[expose] public section

variable {ι : Sort*} {G : Type*} [Group G]

namespace Subgroup

/-- Pull a subgroup back to an opposite subgroup along `MulOpposite.unop` -/
@[to_additive (attr := simps)
/-- Pull an additive subgroup back to an opposite additive subgroup along `AddOpposite.unop` -/]
/-
**Subgroup.op** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_2} → [inst : Group G] → Subgroup G → Subgroup Gᵐᵒᵖ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
-/
protected def op (H : Subgroup G) : Subgroup Gᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' (H : Set G)
  one_mem' := H.one_mem
  mul_mem' ha hb := H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
/-
**Subgroup.mem_op** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x in S.op ↔ x.unop in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl
/-
**Subgroup.op_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] (H : Subgroup G), H.op.toSubmonoid = H.o
p
参数：H : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma op_toSubmonoid (H : Subgroup G) :
    H.op.toSubmonoid = H.toSubmonoid.op :=
  rfl
/-
**Subgroup.op_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] (H : Subgroup G), H.op.toSubsemigroup = 
H.op
参数：H : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma op_toSubsemigroup (H : Subgroup G) :
    H.op.toSubsemigroup = H.toSubsemigroup.op := by
  dsimp

/-- Pull an opposite subgroup back to a subgroup along `MulOpposite.op` -/
@[to_additive (attr := simps)
/-- Pull an opposite additive subgroup back to an additive subgroup along `AddOpposite.op` -/]
/-
**Subgroup.unop** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_2} → [inst : Group G] → Subgroup Gᵐᵒᵖ → Subgroup G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def unop (H : Subgroup Gᵐᵒᵖ) : Subgroup G where
  carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
  one_mem' := H.one_mem
  mul_mem' := fun ha hb => H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
/-
**Subgroup.mem_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_unop {x : G} {S : Subgroup Gᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unop {x : G} {S : Subgroup Gᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl
/-
**Subgroup.unop_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] (H : Subgroup Gᵐᵒᵖ), H.unop.toSubmonoid 
= H.unop
参数：H : Subgroup Gᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma unop_toSubmonoid (H : Subgroup Gᵐᵒᵖ) :
    H.unop.toSubmonoid = H.toSubmonoid.unop :=
  rfl
/-
**Subgroup.unop_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] (H : Subgroup Gᵐᵒᵖ), H.unop.toSubsemigro
up = H.unop
参数：H : Subgroup Gᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma unop_toSubsemigroup (H : Subgroup Gᵐᵒᵖ) :
    H.unop.toSubsemigroup = H.toSubsemigroup.unop := by
  dsimp

@[to_additive (attr := simp)]
/-
**Subgroup.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_op (S : Subgroup G) : S.op.unop = S
参数：S : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (S : Subgroup G) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S
参数：S : Subgroup Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
/-
**Subgroup.op_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_le_iff {S₁ : Subgroup G} {S₂ : Subgroup Gᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ <= S₂.
unop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)

--- 原说明 ---
### Lattice results
-/
theorem op_le_iff {S₁ : Subgroup G} {S₂ : Subgroup Gᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
/-
**Subgroup.le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_op_iff {S₁ : Subgroup Gᵐᵒᵖ} {S₂ : Subgroup G} : S₁ <= S₂.op ↔ S₁.unop <
= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem le_op_iff {S₁ : Subgroup Gᵐᵒᵖ} {S₂ : Subgroup G} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/-
**Subgroup.op_le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_le_op_iff {S₁ S₂ : Subgroup G} : S₁.op <= S₂.op ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem op_le_op_iff {S₁ S₂ : Subgroup G} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/-
**Subgroup.unop_le_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_le_unop_iff {S₁ S₂ : Subgroup Gᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem unop_le_unop_iff {S₁ S₂ : Subgroup Gᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subgroup `H` of `G` determines a subgroup `H.op` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) /-- An additive subgroup `H` of `G` determines an additive subgroup
`H.op` of the opposite additive group `Gᵃᵒᵖ`. -/]
/-
**Subgroup.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：opEquiv : Subgroup G ≃o Subgroup Gᵐᵒᵖ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.unop_op`：unop_op (S : Subgroup G) : S.op.unop = S
· 使用定理 `Subgroup.op_unop`：op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subgroup.op_le_op_iff`：op_le_op_iff {S₁ S₂ : Subgroup G} : S₁.op <= S₂.o
p ↔ S₁ <= S₂
-/
def opEquiv : Subgroup G ≃o Subgroup Gᵐᵒᵖ where
  toFun := Subgroup.op
  invFun := Subgroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
/-
**Subgroup.op_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_injective : (@Subgroup.op G _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem op_injective : (@Subgroup.op G _).Injective := opEquiv.injective

@[to_additive]
/-
**Subgroup.unop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_injective : (@Subgroup.unop G _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem unop_injective : (@Subgroup.unop G _).Injective := opEquiv.symm.injective

@[to_additive (attr := simp)]
/-
**Subgroup.op_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_inj {S T : Subgroup G} : S.op = T.op ↔ S = T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
theorem op_inj {S T : Subgroup G} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[to_additive (attr := simp)]
/-
**Subgroup.unop_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_inj {S T : Subgroup Gᵐᵒᵖ} : S.unop = T.unop ↔ S = T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
theorem unop_inj {S T : Subgroup Gᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive (attr := simps!) /-- Bijection between an additive subgroup `H` and its opposite. -/]
/-
**Subgroup.equivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：equivOp (H : Subgroup G) : H ≃ H.op
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between a subgroup `H` and its opposite.
-/
def equivOp (H : Subgroup G) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

@[to_additive]
/-
**Subgroup.op_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_normalizer (H : Subgroup G) : (normalizer H : Subgroup G).op = normaliz
er H.op
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_op`：mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x in S.op ↔ x.unop
 in S
· 使用定理 `Subgroup.mem_normalizer_iff'`：mem_normalizer_iff' : g in normalizer H ↔ 
forall n, n * g in H ↔ g * n in H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem op_normalizer (H : Subgroup G) : (normalizer H : Subgroup G).op = normalizer H.op := by
  ext x
  rw [mem_op, mem_normalizer_iff', mem_normalizer_iff']
  simp [iff_comm]

@[to_additive]
/-
**Subgroup.unop_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_normalizer (H : Subgroup Gᵐᵒᵖ) : (normalizer H).unop = normalizer (H.
unop : Set G)
参数：H : Subgroup Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.op_inj`：op_inj {S T : Subgroup G} : S.op = T.op ↔ S = T
· 使用定理 `Subgroup.op_unop`：op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subgroup.op_normalizer`：op_normalizer (H : Subgroup G) : (normalizer H :
 Subgroup G).op = normalizer H.op
-/
theorem unop_normalizer (H : Subgroup Gᵐᵒᵖ) :
    (normalizer H).unop = normalizer (H.unop : Set G) := by
  rw [← op_inj, op_unop, op_normalizer, op_unop]

end Subgroup

