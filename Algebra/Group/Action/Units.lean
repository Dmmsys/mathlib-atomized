/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-! # Group actions on and by `Mˣ`

This file provides the action of a unit on a type `α`, `SMul Mˣ α`, in the presence of
`SMul M α`, with the obvious definition stated in `Units.smul_def`. This definition preserves
`MulAction` and `DistribMulAction` structures too.

Additionally, a `MulAction G M` for some group `G` satisfying some additional properties admits a
`MulAction G Mˣ` structure, again with the obvious definition stated in `Units.coe_smul`.
These instances use a primed name.

The results are repeated for `AddUnits` and `VAdd` where relevant.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G H M N α : Type*}

namespace Units

/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Monoid M] [SMul M α] : SMul Mˣ α where smul m a := (m : M) • a
/-
**Units.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_1 : SMul M α] (m :
 Mˣ) (a : α), m • a = ↑m • a
参数：m : Mˣ；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma smul_def [Monoid M] [SMul M α] (m : Mˣ) (a : α) : m • a = (m : M) • a := rfl

@[to_additive, simp]
/-
**Units.smul_mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：smul_mk_apply {M α : Type*} [Monoid M] [SMul M α] (m n : M) (h₁) (h₂) (a :
 α) : (⟨m, n, h₁, h₂⟩ : Mˣ) • a = m • a
参数：m n : M；h₁；h₂；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_mk_apply {M α : Type*} [Monoid M] [SMul M α] (m n : M) (h₁) (h₂) (a : α) :
    (⟨m, n, h₁, h₂⟩ : Mˣ) • a = m • a := rfl

@[simp]
/-
**Units.smul_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) : hm.uni
t • a = m • a
参数：hm : IsUnit m；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) : hm.unit • a = m • a := rfl

@[to_additive]
/-
**Units._root_.IsUnit.inv_smul** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsUnit.inv_smul [Monoid α] {a : α} (h : IsUnit a) : h.unit⁻¹ • a = 1 := h.val_inv_mul

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] [SMul M α] [FaithfulSMul M α] : FaithfulSMul Mˣ α where
  eq_of_smul_eq_smul h := Units.ext <| eq_of_smul_eq_smul h

@[to_additive]
/-
**Units.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instMulAction [Monoid M] [MulAction M α] : MulAction Mˣ α where one_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
instance instMulAction [Monoid M] [MulAction M α] : MulAction Mˣ α where
  one_smul := one_smul M
  mul_smul m n := mul_smul (m : M) n

@[to_additive]
/-
**Units.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：smulCommClass_left [Monoid M] [SMul M α] [SMul N α] [SMulCommClass M N α] 
: SMulCommClass Mˣ N α where smul_comm m n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_left [Monoid M] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass Mˣ N α where smul_comm m n := smul_comm (m : M) n

@[to_additive]
/-
**Units.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：smulCommClass_right [Monoid N] [SMul M α] [SMul N α] [SMulCommClass M N α]
 : SMulCommClass M Nˣ α where smul_comm m n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_right [Monoid N] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M Nˣ α where smul_comm m n := smul_comm m (n : N)

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mˣ N α where smul_assoc m n := smul_assoc (m : M) n

/-! ### Action of a group `G` on units of `M` -/

/-- If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
action on `Mˣ`. Notably, this provides `MulAction Mˣ Nˣ` under suitable conditions. -/
@[to_additive]
/-
**Units.mulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：mulAction' [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsS
calarTower G M M] : MulAction G Mˣ where smul g m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an action `G` associates and commutes with multiplication on `M`, then it lif
ts to an
action on `Mˣ`. Notably, this provides `MulAction Mˣ Nˣ` under suitable conditio
ns.
-/
instance mulAction' [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] : MulAction G Mˣ where
  smul g m :=
    ⟨g • (m : M), (g⁻¹ • ((m⁻¹ : Mˣ) : M)),
      by rw [smul_mul_smul_comm, Units.mul_inv, mul_inv_cancel, one_smul],
      by rw [smul_mul_smul_comm, Units.inv_mul, inv_mul_cancel, one_smul]⟩
  one_smul _ := Units.ext <| one_smul _ _
  mul_smul _ _ _ := Units.ext <| mul_smul _ _ _

/-- `Units.mulAction' : MulAction G Mˣ` creates a diamond when `G = Mˣ` and `M` is commutative.

Discussed [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/units.2Emul_action'.20diamond/near/246400399). -/
/-
**Units.** 是 Mathlib 中的一个示例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Units.mulAction' : MulAction G Mˣ` creates a diamond when `G = Mˣ` and `M` is c
ommutative.

Discussed [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-gen
eral/topic/units.2Emul_action'.20diamond/near/246400399).
-/
example {M} [CommMonoid M] :
    (mulAction'.toSMul : SMul Mˣ Mˣ) = instSMulOfMul := by
  fail_if_success rfl -- there is an instance diamond here
  ext
  rfl

/-- This is not the usual `smul_eq_mul` because `mulAction'` creates a diamond.

Discussed [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/units.2Emul_action'.20diamond/near/246400399). -/
@[simp]
/-
**Units.smul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：smul_eq_mul {M} [CommMonoid M] (u₁ u₂ : Mˣ) : u₁ • u₂ = u₁ * u₂
参数：u₁ u₂ : Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v

--- 原说明 ---
This is not the usual `smul_eq_mul` because `mulAction'` creates a diamond.

Discussed [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-gen
eral/topic/units.2Emul_action'.20diamond/near/246400399).
-/
lemma smul_eq_mul {M} [CommMonoid M] (u₁ u₂ : Mˣ) :
    u₁ • u₂ = u₁ * u₂ := by
  ext
  rfl

@[to_additive (attr := simp)]
/-
**Units.val_smul** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：val_smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsSca
larTower G M M] (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M)
参数：g : G；m : Mˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M) := rfl

/-- Note that this lemma exists more generally as the global `smul_inv` -/
@[to_additive (attr := simp)]
/-
**Units.smul_inv** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：smul_inv [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsSca
larTower G M M] (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹
参数：g : G；m : Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v

--- 原说明 ---
Note that this lemma exists more generally as the global `smul_inv`
-/
lemma smul_inv [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹ := ext rfl

/-- Transfer `SMulCommClass G H M` to `SMulCommClass G H Mˣ`. -/
@[to_additive /-- Transfer `VAddCommClass G H M` to `VAddCommClass G H (AddUnits M)`. -/]
/-
**Units.smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：smulCommClass' [Group G] [Group H] [Monoid M] [MulAction G M] [SMulCommCla
ss G M M] [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M] [IsScalarT
ower H M M] [SMulCommClass G H M] : SMulCommClass G H Mˣ where smul_comm g h m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…

--- 原说明 ---
Transfer `SMulCommClass G H M` to `SMulCommClass G H Mˣ`.
-/
instance smulCommClass' [Group G] [Group H] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M] [IsScalarTower H M M]
    [SMulCommClass G H M] :
    SMulCommClass G H Mˣ where smul_comm g h m := Units.ext <| smul_comm g h (m : M)

/-- Transfer `IsScalarTower G H M` to `IsScalarTower G H Mˣ`. -/
@[to_additive /-- Transfer `VAddAssocClass G H M` to `VAddAssocClass G H (AddUnits M)`. -/]
/-
**Units.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：isScalarTower' [SMul G H] [Group G] [Group H] [Monoid M] [MulAction G M] [
SMulCommClass G M M] [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M]
 [IsScalarTower H M M] [IsScalarTower G H M] : IsScalarTower G H Mˣ where smul_a
ssoc g h m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z

--- 原说明 ---
Transfer `IsScalarTower G H M` to `IsScalarTower G H Mˣ`.
-/
instance isScalarTower' [SMul G H] [Group G] [Group H] [Monoid M] [MulAction G M]
    [SMulCommClass G M M] [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M]
    [IsScalarTower H M M] [IsScalarTower G H M] :
    IsScalarTower G H Mˣ where smul_assoc g h m := Units.ext <| smul_assoc g h (m : M)

/-- Transfer `IsScalarTower G M α` to `IsScalarTower G Mˣ α`. -/
@[to_additive /-- Transfer `VAddAssocClass G M α` to `VAddAssocClass G (AddUnits M) α`. -/]
/-
**Units.isScalarTower'_left** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {G : Type u_1} {M : Type u_3} {α : Type u_5} [inst : Group G] [inst_1 : 
Monoid M] [inst_2 : MulAction G M]   [inst_3 : SMul M α] [inst_4 : SMul G α] [in
st_5 : SMulCommClass G M M] [inst_6 : IsScalarTower G M M]   [IsScalarTower G M 
α], IsScalarTower G Mˣ α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z

--- 原说明 ---
Transfer `IsScalarTower G M α` to `IsScalarTower G Mˣ α`.
-/
instance isScalarTower'_left [Group G] [Monoid M] [MulAction G M] [SMul M α] [SMul G α]
    [SMulCommClass G M M] [IsScalarTower G M M] [IsScalarTower G M α] :
    IsScalarTower G Mˣ α where smul_assoc g m := smul_assoc g (m : M)

-- Just to prove this transfers a particularly useful instance.
/-
**Units.** 是 Mathlib 中的一个示例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Monoid M] [Monoid N] [MulAction M N] [SMulCommClass M N N] [IsScalarTower M N N] :
    MulAction Mˣ Nˣ := Units.mulAction'

section MulDistribMulAction
variable {M N : Type*} [Monoid M] [Monoid N] [MulDistribMulAction M N]

/-- Note this has different defeqs than `Units.mulAction'`, but doesn't create a diamond
with it in non-degenerate situations. Indeed, to get a diamond on `MulDistribMulAction G Mˣ`,
we would need both instances to fire. But `Units.mulAction'` assumes `SMulCommClass G M M`,
i.e. `∀ (g : G) (m₁ m₂ : M), g • (m₁ * m₂) = m₁ * g • m₂`), while
`Units.instMulDistribMulActionRight` assumes `MulDistribMulAction G M`,
i.e. `∀ (g : G) (m₁ m₂ : M), g • (m₁ * m₂) = g • m₁ * g • m₂`.
In particular, if `M` is cancellative, then we obtain `∀ (g : G) (m : M), g • m = m`,
i.e. the action is trivial!

This however does create a (propeq) diamond for `MulDistribMulAction (ConjAct Mˣ) Mˣ` with
`ConjAct.unitsMulDistribMulAction` and `ConjAct.instMulDistribMulAction`. Indeed, if we go down
one way then `u • v := ⟨ofConjAct u * v * ofConjAct u⁻¹, ofConjAct u * v⁻¹ * ofConjAct u⁻¹, _, _⟩`,
while the other way is
`u • v := ⟨ofConjAct u * v * ofConjAct u⁻¹, ofConjAct u * (v⁻¹ * ofConjAct u⁻¹), _, _⟩`. -/
/-
**Units.mulDistribMulActionRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Units`。
形式化陈述：mulDistribMulActionRight : MulDistribMulAction M Nˣ where smul m u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note this has different defeqs than `Units.mulAction'`, but doesn't create a dia
mond
with it in non-degenerate situations. Indeed, to get a diamond on `MulDistribMul
Action G Mˣ`,
we would need both instances to fire. But `Units.mulAction'` assumes `SMulCommCl
ass G M M`,
i.e. `∀ (g : G) (m₁ m₂ : M), g • (m₁ * m₂) = m₁ * g • m₂`), while
`Units.instMulDistribMulActionRight` assumes `MulDistribMulAction G M`,
i.e. `∀ (g : G) (m₁ m₂ : M), g • (m₁ * m₂) = g • m₁ * g • m₂`.
In particular, if `M` is cancellative, then we obtain `∀ (g : G) (m : M), g • m 
= m`,
i.e. the action is trivial!

This however does create a (propeq) diamond for `MulDistribMulAction (ConjAct Mˣ
) Mˣ` with
`ConjAct.unitsMulDistribMulAction` and `ConjAct.instMulDistribMulAction`. Indeed
, if we go down
one way then `u • v := ⟨ofConjAct u * v * ofConjAct u⁻¹, ofConjAct u * v⁻¹ * ofC
onjAct u⁻¹, _, _⟩`,
while the other way is
`u • v := ⟨ofConjAct u * v * ofConjAct u⁻¹, ofConjAct u * (v⁻¹ * ofConjAct u⁻¹),
 _, _⟩`.
-/
abbrev mulDistribMulActionRight : MulDistribMulAction M Nˣ where
  smul m u := ⟨m • u, m • u⁻¹, by simp [← smul_mul', smul_one], by simp [← smul_mul', smul_one]⟩
  one_smul u := Units.ext <| one_smul ..
  mul_smul m₁ m₂ u := Units.ext <| mul_smul ..
  smul_mul m₁ u₁ u₂ := Units.ext <| smul_mul' ..
  smul_one m := Units.ext <| smul_one m

attribute [local instance] mulDistribMulActionRight
/-
**Units.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_6} {N : Type u_7} [inst : Monoid M] [inst_1 : Monoid N] [ins
t_2 : MulDistribMulAction M N] (m : M)   (u : Nˣ), ↑(m • u) = m • ↑u
参数：m : M；u : Nˣ；m • u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_smul (m : M) (u : Nˣ) : (m • u).val = m • u.val := rfl
/-
**Units.coe_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_6} {N : Type u_7} [inst : Monoid M] [inst_1 : Monoid N] [ins
t_2 : MulDistribMulAction M N] (m : M)   (u : Nˣ), ↑(m • u)⁻¹ = m • ↑u⁻¹
参数：m : M；u : Nˣ；m • u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inv_smul (m : M) (u : Nˣ) : (m • u)⁻¹.val = m • u⁻¹.val := rfl

end MulDistribMulAction
end Units

@[to_additive]
/-
**IsUnit.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [Is
ScalarTower G M M] {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m)
参数：g : G；h : IsUnit m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Units.val_smul`：val_smul [Group G] [Monoid M] [MulAction G M] [SMulCommC
lass G M M] [IsScalarTower G M M] (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M)
-/
lemma IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩
