/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Hom

/-!

# Sets invariant to a `MulAction`

In this file we define `SubMulAction R M`; a subset of a `MulAction R M` which is closed with
respect to scalar multiplication.

For most uses, typically `Submodule R M` is more powerful.

## Main definitions

* `SubMulAction.mulAction` - the `MulAction R M` transferred to the subtype.
* `SubMulAction.mulAction'` - the `MulAction S M` transferred to the subtype when
  `IsScalarTower S R M`.
* `SubMulAction.isScalarTower` - the `IsScalarTower S R M` transferred to the subtype.
* `SubMulAction.inclusion` — the inclusion of a `SubMulAction`, as an equivariant map

## Tags

submodule, multiplicative action
-/

@[expose] public section


open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

/-- `SMulMemClass S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
scalar action of `R` on `M`.

Note that only `R` is marked as an `outParam` here, since `M` is supplied by the `SetLike`
class instead.
-/
/-
**SMulMemClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (R : outParam (Type u_2)) → (M : Type u_3) → [SMul R M] →
 [SetLike S M] → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SMulMemClass S R M` says `S` is a type of subsets `s ≤ M` that are closed under
 the
scalar action of `R` on `M`.

Note that only `R` is marked as an `outParam` here, since `M` is supplied by the
 `SetLike`
class instead.
-/
class SMulMemClass (S : Type*) (R : outParam Type*) (M : Type*) [SMul R M] [SetLike S M] :
    Prop where
  /-- Multiplication by a scalar on an element of the set remains in the set. -/
  smul_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r • m ∈ s

/-- `VAddMemClass S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
additive action of `R` on `M`.

Note that only `R` is marked as an `outParam` here, since `M` is supplied by the `SetLike`
/-
**instead.** 是 Mathlib 中的一个类，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class instead. -/
/-
**VAddMemClass** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：VAddMemClass (S : Type*) (R : outParam Type*) (M : Type*) [VAdd R M] [SetL
ike S M] : Prop where /-- Addition by a scalar with an element of the set remain
s in the set. -/ vadd_mem : forall {s : S} (r : R) {m : M}, m in s -> r +ᵥ m in 
s  attribute [to_additive] SMulMemClass  attribute [aesop 90% (rule_sets
参数：S : Type*；R : outParam Type*；M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`VAddMemClass S R M` says `S` is a type of subsets `s ≤ M` that are closed under
 the
additive action of `R` on `M`.

Note that only `R` is marked as an `outParam` here, since `M` is supplied by the
 `SetLike`
class instead.
-/
class VAddMemClass (S : Type*) (R : outParam Type*) (M : Type*) [VAdd R M] [SetLike S M] :
    Prop where
  /-- Addition by a scalar with an element of the set remains in the set. -/
  vadd_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r +ᵥ m ∈ s

attribute [to_additive] SMulMemClass

attribute [aesop 90% (rule_sets := [SetLike])] SMulMemClass.smul_mem VAddMemClass.vadd_mem

/-- Not registered as an instance because `R` is an `outParam` in `SMulMemClass S R M`. -/
/-
**AddSubmonoidClass.nsmulMemClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddSubmonoidClass.nsmulMemClass {S M : Type*} [AddMonoid M] [SetLike S M] 
[AddSubmonoidClass S M] : SMulMemClass S Nat M where smul_mem n _x hx
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …

--- 原说明 ---
Not registered as an instance because `R` is an `outParam` in `SMulMemClass S R 
M`.
-/
lemma AddSubmonoidClass.nsmulMemClass {S M : Type*} [AddMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] : SMulMemClass S ℕ M where
  smul_mem n _x hx := nsmul_mem hx n

/-- Not registered as an instance because `R` is an `outParam` in `SMulMemClass S R M`. -/
/-
**AddSubgroupClass.zsmulMemClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddSubgroupClass.zsmulMemClass {S M : Type*} [SubNegMonoid M] [SetLike S M
] [AddSubgroupClass S M] : SMulMemClass S Int M where smul_mem n _x hx
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …

--- 原说明 ---
Not registered as an instance because `R` is an `outParam` in `SMulMemClass S R 
M`.
-/
lemma AddSubgroupClass.zsmulMemClass {S M : Type*} [SubNegMonoid M] [SetLike S M]
    [AddSubgroupClass S M] : SMulMemClass S ℤ M where
  smul_mem n _x hx := zsmul_mem hx n

namespace SetLike

open SMulMemClass

section SMul

variable [SMul R M] [SetLike S M] [hS : SMulMemClass S R M] (s : S)

-- lower priority so other instances are found first
/-- A subset closed under the scalar action inherits that action. -/
@[to_additive /-- A subset closed under the additive action inherits that action. -/]
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset closed under the scalar action inherits that action.
-/
instance (priority := 50) smul : SMul R s :=
  ⟨fun r x => ⟨r • x.1, smul_mem r x.2⟩⟩
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance (priority := 50) [SMul T M] [SMulMemClass S T M] [SMulCommClass T R M] :
    SMulCommClass T R s where
  smul_comm _ _ _ := Subtype.ext (smul_comm ..)
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance (priority := 50) [IsLeftCancelSMul R M] : IsLeftCancelSMul R s where
  left_cancel' x _ _ eq := Subtype.ext <| IsLeftCancelSMul.left_cancel x _ _ congr($eq)
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance (priority := 50) [IsCancelSMul R M] : IsCancelSMul R s where
  right_cancel' _ _ x eq := IsCancelSMul.right_cancel _ _ x.1 congr($eq)

/-- This can't be an instance because Lean wouldn't know how to find `N`, but we can still use
this to manually derive `SMulMemClass` on specific types. -/
/-
**SetLike._root_.SMulMemClass.ofIsScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `SetLike
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can't be an instance because Lean wouldn't know how to find `N`, but we can
 still use
this to manually derive `SMulMemClass` on specific types.
-/
@[to_additive] theorem _root_.SMulMemClass.ofIsScalarTower (S M N α : Type*) [SetLike S α]
    [SMul M N] [SMul M α] [Monoid N] [MulAction N α] [SMulMemClass S N α] [IsScalarTower M N α] :
    SMulMemClass S M α :=
  { smul_mem := fun m a ha => smul_one_smul N m a ▸ SMulMemClass.smul_mem _ ha }
/-
**SetLike.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：instIsScalarTower [Mul M] [MulMemClass S M] [IsScalarTower R M M] (s : S) 
: IsScalarTower R s s where smul_assoc r x y
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower [Mul M] [MulMemClass S M] [IsScalarTower R M M]
    (s : S) : IsScalarTower R s s where
  smul_assoc r x y := Subtype.ext <| smul_assoc r (x : M) (y : M)
/-
**SetLike.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：instSMulCommClass [Mul M] [MulMemClass S M] [SMulCommClass R M M] (s : S) 
: SMulCommClass R s s where smul_comm r x y
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass [Mul M] [MulMemClass S M] [SMulCommClass R M M]
    (s : S) : SMulCommClass R s s where
  smul_comm r x y := Subtype.ext <| smul_comm r (x : M) (y : M)

@[to_additive (attr := simp, norm_cast)]
/-
**SetLike.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {S : Type u'} {R : Type u} {M : Type v} [inst : SMul R M] [inst_1 : SetL
ike S M] [hS : SMulMemClass S R M] (s : S)   (r : R) (x : ↥s), ↑(r • x) = r • ↑x
参数：s : S；r : R；x : ↥s；r • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem val_smul (r : R) (x : s) : (↑(r • x) : M) = r • (x : M) :=
  rfl

@[to_additive (attr := simp)]
/-
**SetLike.mk_smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：mk_smul_mk (r : R) (x : M) (hx : x in s) : r • (⟨x, hx⟩ : s) = ⟨r • x, smu
l_mem r hx⟩
参数：r : R；x : M；hx : x in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul_mk (r : R) (x : M) (hx : x ∈ s) : r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩ :=
  rfl

@[to_additive]
/-
**SetLike.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：smul_def (r : R) (x : s) : r • x = ⟨r • x, smul_mem r x.2⟩
参数：r : R；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def (r : R) (x : s) : r • x = ⟨r • x, smul_mem r x.2⟩ :=
  rfl

@[simp]
/-
**SetLike.forall_smul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：forall_smul_mem_iff {R M S : Type*} [Monoid R] [MulAction R M] [SetLike S 
M] [SMulMemClass S R M] {N : S} {x : M} : (forall a : R, a • x in N) ↔ x in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
-/
theorem forall_smul_mem_iff {R M S : Type*} [Monoid R] [MulAction R M] [SetLike S M]
    [SMulMemClass S R M] {N : S} {x : M} : (∀ a : R, a • x ∈ N) ↔ x ∈ N :=
  ⟨fun h => by simpa using h 1, fun h a => SMulMemClass.smul_mem a h⟩

open scoped Pointwise in
@[to_additive]
/-
**SetLike.smul_subset_self** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：smul_subset_self {S R M : Type*} [SetLike S M] [SMul R M] [SMulMemClass S 
R M] (r : R) (s : S) : (r • s : Set M) subseteq s
参数：r : R；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
-/
theorem smul_subset_self {S R M : Type*} [SetLike S M] [SMul R M] [SMulMemClass S R M]
    (r : R) (s : S) : (r • s : Set M) ⊆ s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa using SMulMemClass.smul_mem (r : R) hx

open scoped Pointwise in
@[to_additive (attr := simp)]
/-
**SetLike.units_smul** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：units_smul {S R M : Type*} [SetLike S M] [Monoid R] [MulAction R M] [SMulM
emClass S R M] (s : S) (r : Rˣ) : r • s = (s : Set M)
参数：s : S；r : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `SetLike.smul_subset_self`：smul_subset_self {S R M : Type*} [SetLike S M]
 [SMul R M] [SMulMemClass S R M] (r : R) (s : S) : (r • s : Set M) subseteq s
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem units_smul {S R M : Type*} [SetLike S M] [Monoid R] [MulAction R M] [SMulMemClass S R M]
    (s : S) (r : Rˣ) : r • s = (s : Set M) := by
  apply subset_antisymm (smul_subset_self _ s)
  rintro x hx
  exact ⟨r⁻¹ • x, SMulMemClass.smul_mem (↑r⁻¹ : R) hx, by simp [← Units.smul_def]⟩

end SMul

section OfTower

variable {N α : Type*} [SetLike S α] [SMul M N] [SMul M α] [Monoid N]
    [MulAction N α] [SMulMemClass S N α] [IsScalarTower M N α] (s : S)

-- lower priority so other instances are found first
/-- A subset closed under the scalar action inherits that action. -/
@[to_additive /-- A subset closed under the additive action inherits that action. -/]
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset closed under the scalar action inherits that action.
-/
instance (priority := 50) smul' : SMul M s where
  smul r x := ⟨r • x.1, smul_one_smul N r x.1 ▸ smul_mem _ x.2⟩
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) : IsScalarTower M N s where
  smul_assoc m n x := Subtype.ext (smul_assoc m n x.1)

@[to_additive (attr := simp, norm_cast)]
/-
**SetLike.val_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {S : Type u'} {M : Type v} {N : Type u_1} {α : Type u_2} [inst : SetLike
 S α] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : Monoid N] [inst_4 : Mu
lAction N α] [inst_5 : SMulMemClass S N α] [inst_6 : IsScalarTower M N α] (s : S
)   (r : M) (x : ↥s), ↑(r • x) = r • ↑x
参数：s : S；r : M；x : ↥s；r • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem val_smul_of_tower (r : M) (x : s) : (↑(r • x) : α) = r • (x : α) :=
  rfl

@[to_additive (attr := simp)]
/-
**SetLike.mk_smul_of_tower_mk** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：mk_smul_of_tower_mk (r : M) (x : α) (hx : x in s) : r • (⟨x, hx⟩ : s) = ⟨r
 • x, smul_one_smul N r x ▸ smul_mem _ hx⟩
参数：r : M；x : α；hx : x in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul_of_tower_mk (r : M) (x : α) (hx : x ∈ s) :
    r • (⟨x, hx⟩ : s) = ⟨r • x, smul_one_smul N r x ▸ smul_mem _ hx⟩ :=
  rfl

@[to_additive]
/-
**SetLike.smul_of_tower_def** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：smul_of_tower_def (r : M) (x : s) : r • x = ⟨r • x, smul_one_smul N r x.1 
▸ smul_mem _ x.2⟩
参数：r : M；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_of_tower_def (r : M) (x : s) :
    r • x = ⟨r • x, smul_one_smul N r x.1 ▸ smul_mem _ x.2⟩ :=
  rfl
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance (priority := 50) [SMulCommClass M N α] : SMulCommClass M N s where
  smul_comm _ _ _ := Subtype.ext (smul_comm ..)
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance (priority := 50) [SMulCommClass N M α] : SMulCommClass N M s where
  smul_comm _ _ _ := Subtype.ext (smul_comm ..)

end OfTower

end SetLike

/-- A SubAddAction is a set which is closed under scalar multiplication. -/
/-
**SubAddAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (M : Type v) → [VAdd R M] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A SubAddAction is a set which is closed under scalar multiplication.
-/
structure SubAddAction (R : Type u) (M : Type v) [VAdd R M] : Type v where
  /-- The underlying set of a `SubAddAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  vadd_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c +ᵥ x ∈ carrier

/-- A SubMulAction is a set which is closed under scalar multiplication. -/
@[to_additive]
/-
**SubMulAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (M : Type v) → [SMul R M] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A SubMulAction is a set which is closed under scalar multiplication.
-/
structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier

namespace SubMulAction

variable [SMul R M]

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (SubMulAction R M) M :=
  ⟨SubMulAction.carrier, fun p q h => by cases p; cases q; congr⟩
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : PartialOrder (SubMulAction R M) := .ofSetLike (SubMulAction R M) M

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulMemClass (SubMulAction R M) R M where smul_mem := smul_mem' _

@[to_additive (attr := simp)]
/-
**SubMulAction.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：mem_carrier {p : SubMulAction R M} {x : M} : x in p.carrier ↔ x in (p : Se
t M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {p : SubMulAction R M} {x : M} : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl

@[to_additive (attr := ext)]
/-
**SubMulAction.ext** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：ext {p q : SubMulAction R M} (h : forall x, x in p ↔ x in q) : p = q
参数：h : forall x, x in p ↔ x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {p q : SubMulAction R M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

/-- Copy of a sub_mul_action with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive /-- Copy of a sub_mul_action with a new `carrier` equal to the old one.
  Useful to fix definitional equalities. -/]
/-
**SubMulAction.copy** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction`。
形式化陈述：{R : Type u} → {M : Type v} → [inst : SMul R M] → (p : SubMulAction R M) →
 (s : Set M) → s = ↑p → SubMulAction R M
参数：p : SubMulAction R M；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : SubMulAction R M where
  carrier := s
  smul_mem' := hs.symm ▸ p.smul_mem'

@[to_additive (attr := simp)]
/-
**SubMulAction.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：coe_copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : (p.copy s hs :
 Set M) = s
参数：p : SubMulAction R M；s : Set M；hs : s = ↑p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : (p.copy s hs : Set M) = s :=
  rfl

@[to_additive]
/-
**SubMulAction.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：copy_eq (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : p.copy s hs = p
参数：p : SubMulAction R M；s : Set M；hs : s = ↑p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (SubMulAction R M) :=
  ⟨⟨∅, by simp⟩⟩

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SubMulAction R M) :=
  ⟨⊥⟩

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (SubMulAction R M) :=
  ⟨⟨Set.univ, by simp⟩⟩

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (SubMulAction R M) :=
  ⟨fun s t => ⟨s ∪ t, by aesop⟩⟩

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (SubMulAction R M) :=
  ⟨fun s t => ⟨s ∩ t, by aesop⟩⟩

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (SubMulAction R M) :=
  ⟨fun S => ⟨⋃ s ∈ S, s, by aesop⟩⟩

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (SubMulAction R M) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, by aesop⟩⟩

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (SubMulAction R M) :=
  SetLike.coe_injective.completeLattice _ .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) rfl rfl

@[to_additive (attr := simp)]
/-
**SubMulAction.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：mem_iSup {ι : Sort*} {p : ι -> SubMulAction R M} {x : M} : x in ⨆ i, p i ↔
 exists i, x in p i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iSup {ι : Sort*} {p : ι → SubMulAction R M} {x : M} :
    x ∈ ⨆ i, p i ↔ ∃ i, x ∈ p i := by
  change x ∈ ⋃ s ∈ Set.range p, s ↔ _
  simp

@[to_additive (attr := simp)]
/-
**SubMulAction.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：mem_iInf {ι : Sort*} {p : ι -> SubMulAction R M} {x : M} : x in ⨅ i, p i ↔
 forall i, x in p i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iInf {ι : Sort*} {p : ι → SubMulAction R M} {x : M} :
    x ∈ ⨅ i, p i ↔ ∀ i, x ∈ p i := by
  change x ∈ ⋂ s ∈ Set.range p, s ↔ _
  simp

end SubMulAction

namespace SubMulAction

section SMul

variable [SMul R M]
variable (p : SubMulAction R M)
variable {r : R} {x : M}

@[to_additive]
/-
**SubMulAction.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：smul_mem (r : R) (h : x in p) : r • x in p
参数：r : R；h : x in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_mem'`：∀ {R : Type u} {M : Type v} [inst : SMul R M] (s
elf : SubMulAction R M) (c : R) {x : M},   x ∈ self.carrier → c • x ∈ self.carri
er
-/
theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h

@[to_additive]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R p where smul c x := ⟨c • x.1, smul_mem _ c x.2⟩

variable {p} in
@[to_additive (attr := norm_cast, simp)]
/-
**SubMulAction.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：val_smul (r : R) (x : p) : (↑(r • x) : M) = r • (x : M)
参数：r : R；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_smul (r : R) (x : p) : (↑(r • x) : M) = r • (x : M) :=
  rfl

/-- Embedding of a submodule `p` to the ambient space `M`. -/
@[to_additive /-- Embedding of a submodule `p` to the ambient space `M`. -/]
/-
**SubMulAction.subtype** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction`。
形式化陈述：{R : Type u} → {M : Type v} → [inst : SMul R M] → (p : SubMulAction R M) →
 ↥p →ₑ[id] M
参数：p : SubMulAction R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of a submodule `p` to the ambient space `M`.
-/
protected def subtype : p →[R] M where
  toFun := Subtype.val
  map_smul' := by simp

variable {p} in
@[to_additive (attr := simp)]
/-
**SubMulAction.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：subtype_apply (x : p) : p.subtype x = x
参数：x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply (x : p) : p.subtype x = x :=
  rfl
/-
**SubMulAction.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAction`。
形式化陈述：subtype_injective : Function.Injective p.subtype
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective p.subtype :=
  Subtype.coe_injective

@[to_additive]
/-
**SubMulAction.subtype_eq_val** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：subtype_eq_val : (SubMulAction.subtype p : p -> M) = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_eq_val : (SubMulAction.subtype p : p → M) = Subtype.val :=
  rfl

end SMul

namespace SMulMemClass

variable [Monoid R] [MulAction R M] {A : Type*} [SetLike A M]
variable [hA : SMulMemClass A R M] (S' : A)

-- Prefer subclasses of `MulAction` over `SMulMemClass`.
/-- A `SubMulAction` of a `MulAction` is a `MulAction`. -/
@[to_additive /-- A `SubAddAction` of an `AddAction` is an `AddAction`. -/]
/-
**SubMulAction.SMulMemClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction.SMulMemClas
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SubMulAction` of a `MulAction` is a `MulAction`.
-/
instance (priority := 75) toMulAction : MulAction R S' :=
  Subtype.coe_injective.mulAction Subtype.val (SetLike.val_smul S')

/-- The natural `MulActionHom` over `R` from a `SubMulAction` of `M` to `M`. -/
@[to_additive /-- The natural `AddActionHom` over `R` from a `SubAddAction` of `M` to `M`. -/]
/-
**SubMulAction.SMulMemClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction.SMul
MemClass`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Monoid R] →       [inst_1 : Mu
lAction R M] →         {A : Type u_1} → [inst_2 : SetLike A M] → [hA : SMulMemCl
ass A R M] → (S' : A) → ↥S' →ₑ[id] M
参数：S' : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `MulActionHom` over `R` from a `SubMulAction` of `M` to `M`.
-/
protected def subtype : S' →[R] M where
  toFun := Subtype.val; map_smul' _ _ := rfl

variable {S'} in
@[simp]
/-
**SubMulAction.SMulMemClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `SubMulActio
n.SMulMemClass`。
形式化陈述：subtype_apply (x : S') : SMulMemClass.subtype S' x = x
参数：x : S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (x : S') :
    SMulMemClass.subtype S' x = x := rfl
/-
**SubMulAction.SMulMemClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `SubMulA
ction.SMulMemClass`。
形式化陈述：subtype_injective : Function.Injective (SMulMemClass.subtype S')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective (SMulMemClass.subtype S') :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/-
**SubMulAction.SMulMemClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction.
SMulMemClass`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Monoid R] [inst_1 : MulAction R M] {A 
: Type u_1} [inst_2 : SetLike A M]   [hA : SMulMemClass A R M] (S' : A), ⇑(SubMu
lAction.SMulMemClass.subtype S') = Subtype.val
参数：S' : A；SubMulAction.SMulMemClass.subtype S'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_subtype : (SMulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl

end SMulMemClass

section MulActionMonoid

variable [Monoid R] [MulAction R M]

section

variable [SMul S R] [SMul S M] [IsScalarTower S R M]
variable (p : SubMulAction R M)

@[to_additive]
/-
**SubMulAction.smul_of_tower_mem** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：smul_of_tower_mem (s : S) {x : M} (h : x in p) : s • x in p
参数：s : S；h : x in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SubMulAction.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem smul_of_tower_mem (s : S) {x : M} (h : x ∈ p) : s • x ∈ p := by
  rw [← one_smul R x, ← smul_assoc]
  exact p.smul_mem _ h

@[to_additive]
/-
**SubMulAction.smul'** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
形式化陈述：smul' : SMul S p where smul c x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul' : SMul S p where smul c x := ⟨c • x.1, smul_of_tower_mem _ c x.2⟩

@[to_additive]
/-
**SubMulAction.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
形式化陈述：isScalarTower : IsScalarTower S R p where smul_assoc s r x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower : IsScalarTower S R p where
  smul_assoc s r x := Subtype.ext <| smul_assoc s r (x : M)

@[to_additive]
/-
**SubMulAction.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
形式化陈述：isScalarTower' {S' : Type*} [SMul S' R] [SMul S' S] [SMul S' M] [IsScalarT
ower S' R M] [IsScalarTower S' S M] : IsScalarTower S' S p where smul_assoc s r 
x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower' {S' : Type*} [SMul S' R] [SMul S' S] [SMul S' M] [IsScalarTower S' R M]
    [IsScalarTower S' S M] : IsScalarTower S' S p where
  smul_assoc s r x := Subtype.ext <| smul_assoc s r (x : M)

@[to_additive (attr := norm_cast, simp)]
/-
**SubMulAction.val_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：val_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • (x : M)
参数：s : S；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • (x : M) :=
  rfl

@[to_additive (attr := simp)]
/-
**SubMulAction.smul_mem_iff'** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：smul_mem_iff' {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R 
M] (g : G) {x : M} : g • x in p ↔ x in p
参数：g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_of_tower_mem`：smul_of_tower_mem (s : S) {x : M} (h : x
 in p) : s • x in p
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem smul_mem_iff' {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M] (g : G)
    {x : M} : g • x ∈ p ↔ x ∈ p :=
  ⟨fun h => inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩

@[to_additive]
/-
**SubMulAction.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
形式化陈述：isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCe
ntralScalar S M] : IsCentralScalar S p where op_smul_eq_smul r x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] :
    IsCentralScalar S p where
  op_smul_eq_smul r x := Subtype.ext <| op_smul_eq_smul r (x : M)

end

section

variable [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
variable (p : SubMulAction R M)

/-- If the scalar product forms a `MulAction`, then the subset inherits this action -/
@[to_additive]
/-
**SubMulAction.mulAction'** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
形式化陈述：mulAction' : MulAction S p where one_smul x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the scalar product forms a `MulAction`, then the subset inherits this action
-/
instance mulAction' : MulAction S p where
  one_smul x := Subtype.ext <| one_smul _ (x : M)
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul c₁ c₂ (x : M)

@[to_additive]
/-
**SubMulAction.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
形式化陈述：mulAction : MulAction R p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction : MulAction R p :=
  p.mulAction'

end

/-- Orbits in a `SubMulAction` coincide with orbits in the ambient space. -/
@[to_additive]
/-
**SubMulAction.val_image_orbit** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：val_image_orbit {p : SubMulAction R M} (m : p) : Subtype.val '' MulAction.
orbit R m = MulAction.orbit R (m : M)
参数：m : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f

--- 原说明 ---
Orbits in a `SubMulAction` coincide with orbits in the ambient space.
-/
theorem val_image_orbit {p : SubMulAction R M} (m : p) :
    Subtype.val '' MulAction.orbit R m = MulAction.orbit R (m : M) :=
  (Set.range_comp _ _).symm

@[to_additive]
/-
**SubMulAction.val_preimage_orbit** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：val_preimage_orbit {p : SubMulAction R M} (m : p) : Subtype.val ⁻¹' MulAct
ion.orbit R (m : M) = MulAction.orbit R m
参数：m : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.val_image_orbit`：val_image_orbit {p : SubMulAction R M} (m 
: p) : Subtype.val '' MulAction.orbit R m = MulAction.orbit R (m : M)
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem val_preimage_orbit {p : SubMulAction R M} (m : p) :
    Subtype.val ⁻¹' MulAction.orbit R (m : M) = MulAction.orbit R m := by
  rw [← val_image_orbit, Subtype.val_injective.preimage_image]

@[to_additive]
/-
**SubMulAction.mem_orbit_subMul_iff** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAction`。
形式化陈述：mem_orbit_subMul_iff {p : SubMulAction R M} {x m : p} : x in MulAction.orb
it R m ↔ (x : M) in MulAction.orbit R (m : M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.val_preimage_orbit`：val_preimage_orbit {p : SubMulAction R 
M} (m : p) : Subtype.val ⁻¹' MulAction.orbit R (m : M) = MulAction.orbit R m
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_orbit_subMul_iff {p : SubMulAction R M} {x m : p} :
    x ∈ MulAction.orbit R m ↔ (x : M) ∈ MulAction.orbit R (m : M) := by
  rw [← val_preimage_orbit, Set.mem_preimage]

/-- Stabilizers in monoid SubMulAction coincide with stabilizers in the ambient space -/
@[to_additive]
/-
**SubMulAction.stabilizer_of_subMul.submonoid** 是 Mathlib 中的一个定理，位于命名空间 `SubMulA
ction.stabilizer_of_subMul`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Monoid R] [inst_1 : MulAction R M] {p 
: SubMulAction R M} (m : ↥p),   MulAction.stabilizerSubmonoid R m = MulAction.st
abilizerSubmonoid R ↑m
参数：m : ↥p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Stabilizers in monoid SubMulAction coincide with stabilizers in the ambient spac
e
-/
theorem stabilizer_of_subMul.submonoid {p : SubMulAction R M} (m : p) :
    MulAction.stabilizerSubmonoid R m = MulAction.stabilizerSubmonoid R (m : M) := by
  ext
  simp only [MulAction.mem_stabilizerSubmonoid_iff, ← SubMulAction.val_smul, SetLike.coe_eq_coe]

end MulActionMonoid

section MulActionGroup

variable [Group R] [MulAction R M]

@[to_additive]
/-
**SubMulAction.orbitRel_of_subMul** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAction`。
形式化陈述：orbitRel_of_subMul (p : SubMulAction R M) : MulAction.orbitRel R p = (MulA
ction.orbitRel R M).comap Subtype.val
参数：p : SubMulAction R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Setoid.ext_iff`：∀ {α : Sort u_3} {s t : Setoid α}, s = t ↔ ∀ (a b : α), 
s a b ↔ t a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.comap_rel`：comap_rel (f : α -> β) (r : Setoid β) (x y : α) : coma
p f r x y ↔ r (f x) (f y)
· 使用引理 `SubMulAction.mem_orbit_subMul_iff`：mem_orbit_subMul_iff {p : SubMulActio
n R M} {x m : p} : x in MulAction.orbit R m ↔ (x : M) in MulAction.orbit R (m : 
M)
-/
lemma orbitRel_of_subMul (p : SubMulAction R M) :
    MulAction.orbitRel R p = (MulAction.orbitRel R M).comap Subtype.val := by
  refine Setoid.ext_iff.2 (fun x y ↦ ?_)
  rw [Setoid.comap_rel]
  exact mem_orbit_subMul_iff

/-- Stabilizers in group SubMulAction coincide with stabilizers in the ambient space -/
@[to_additive]
/-
**SubMulAction.stabilizer_of_subMul** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：stabilizer_of_subMul {p : SubMulAction R M} (m : p) : MulAction.stabilizer
 R m = MulAction.stabilizer R (m : M)
参数：m : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.toSubmonoid_inj`：toSubmonoid_inj {p q : Subgroup G} : p.toSubmo
noid = q.toSubmonoid ↔ p = q
· 使用定理 `SubMulAction.stabilizer_of_subMul.submonoid`：∀ {R : Type u} {M : Type v}
 [inst : Monoid R] [inst_1 : MulAction R M] {p : SubMulAction R M} (m : ↥p),   M
ulAction.stabilizerSubmonoid R m …

--- 原说明 ---
Stabilizers in group SubMulAction coincide with stabilizers in the ambient space
-/
theorem stabilizer_of_subMul {p : SubMulAction R M} (m : p) :
    MulAction.stabilizer R m = MulAction.stabilizer R (m : M) := by
  rw [← Subgroup.toSubmonoid_inj]
  exact stabilizer_of_subMul.submonoid m

/-- SubMulAction on the complement of an invariant subset -/
@[to_additive /-- SubAddAction on the complement of an invariant subset -/]
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
SubMulAction on the complement of an invariant subset
-/
instance : Compl (SubMulAction R M) where
  compl s := ⟨sᶜ, by simp⟩

@[to_additive]
/-
**SubMulAction.compl_def** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：compl_def (s : SubMulAction R M) : sᶜ.carrier = (s : Set M)ᶜ
参数：s : SubMulAction R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl_def (s : SubMulAction R M) : sᶜ.carrier = (s : Set M)ᶜ := rfl

end MulActionGroup

section Module

variable [Semiring R] [AddCommMonoid M]
variable [Module R M]
variable (p : SubMulAction R M)

/-
**SubMulAction.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：zero_mem (h : (p : Set M).Nonempty) : (0 : M) in p
参数：h : (p : Set M).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem zero_mem (h : (p : Set M).Nonempty) : (0 : M) ∈ p :=
  let ⟨x, hx⟩ := h
  zero_smul R (x : M) ▸ p.smul_mem 0 hx

/-- If the scalar product forms a `Module`, and the `SubMulAction` is not `⊥`, then the
subset inherits the zero. -/
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the scalar product forms a `Module`, and the `SubMulAction` is not `⊥`, then 
the
subset inherits the zero.
-/
instance [n_empty : Nonempty p] : Zero p where
  zero := ⟨0, n_empty.elim fun x => p.zero_mem ⟨x, x.prop⟩⟩

end Module

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable [Module R M]
variable (p p' : SubMulAction R M)
variable {r : R} {x y : M}

/-
**SubMulAction.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：neg_mem (hx : x in p) : -x in p
参数：hx : x in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `SubMulAction.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem neg_mem (hx : x ∈ p) : -x ∈ p := by
  rw [← neg_one_smul R]
  exact p.smul_mem _ hx

@[simp]
/-
**SubMulAction.neg_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：neg_mem_iff : -x in p ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `SubMulAction.neg_mem`：neg_mem (hx : x in p) : -x in p
-/
theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  ⟨fun h => by
    rw [← neg_neg x]
    exact neg_mem _ h, neg_mem _⟩
/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg p :=
  ⟨fun x => ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast]
/-
**SubMulAction.val_neg** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：val_neg (x : p) : ((-x : p) : M) = -x
参数：x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_neg (x : p) : ((-x : p) : M) = -x :=
  rfl

end AddCommGroup

end SubMulAction

namespace SubMulAction

variable [GroupWithZero S] [Monoid R] [MulAction R M]
variable [SMul S R] [MulAction S M] [IsScalarTower S R M]
variable (p : SubMulAction R M) {s : S} {x y : M}

/-
**SubMulAction.smul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
参数：s0 : s != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_mem_iff'`：smul_mem_iff' {G} [Group G] [SMul G R] [MulA
ction G M] [IsScalarTower G R M] (g : G) {x : M} : g • x in p ↔ x in p
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
-/
theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.smul_mem_iff' (Units.mk0 s s0)

end SubMulAction

namespace SubMulAction

/- The inclusion of a `SubMulAction`, as an equivariant map -/
variable {M α : Type*} [Monoid M] [MulAction M α]


/-- The inclusion of a SubMulAction into the ambient set, as an equivariant map -/
@[to_additive /-- The inclusion of a SubAddAction into the ambient set, as an equivariant map. -/]
/-
**SubMulAction.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction`。
形式化陈述：inclusion (s : SubMulAction M α) : s ->[M] α where -- The inclusion map of
 the inclusion of a SubMulAction toFun
参数：s : SubMulAction M α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a SubMulAction into the ambient set, as an equivariant map
-/
def inclusion (s : SubMulAction M α) : s →[M] α where
-- The inclusion map of the inclusion of a SubMulAction
  toFun := Subtype.val
-- The commutation property
  map_smul' _ _ := rfl

@[to_additive]
/-
**SubMulAction.inclusion.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction.in
clusion`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Monoid M] [inst_1 : MulAction M α]
 (s : SubMulAction M α),   s.inclusion.toFun = Subtype.val
参数：s : SubMulAction M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion.toFun_eq_coe (s : SubMulAction M α) :
    s.inclusion.toFun = Subtype.val := rfl

@[to_additive]
/-
**SubMulAction.inclusion.coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction.inclusio
n`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Monoid M] [inst_1 : MulAction M α]
 (s : SubMulAction M α),   ⇑s.inclusion = Subtype.val
参数：s : SubMulAction M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion.coe_eq (s : SubMulAction M α) :
    ⇑s.inclusion = Subtype.val := rfl

@[to_additive]
/-
**SubMulAction.image_inclusion** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAction`。
形式化陈述：image_inclusion (s : SubMulAction M α) : Set.range s.inclusion = s.carrier
参数：s : SubMulAction M α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubMulAction.inclusion.coe_eq`：∀ {M : Type u_1} {α : Type u_2} [inst : M
onoid M] [inst_1 : MulAction M α] (s : SubMulAction M α),   ⇑s.inclusion = Subty
pe.val
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
lemma image_inclusion (s : SubMulAction M α) :
    Set.range s.inclusion = s.carrier := by
  rw [inclusion.coe_eq]
  exact Subtype.range_coe

@[to_additive]
/-
**SubMulAction.inclusion_injective** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAction`。
形式化陈述：inclusion_injective (s : SubMulAction M α) : Function.Injective s.inclusio
n
参数：s : SubMulAction M α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma inclusion_injective (s : SubMulAction M α) :
    Function.Injective s.inclusion :=
  Subtype.val_injective

end SubMulAction

namespace Units

variable (R M : Type*) [Monoid R] [AddCommMonoid M] [DistribMulAction R M]

/-- The non-zero elements of `M` are invariant under the action by the units of `R`. -/
/-
**Units.nonZeroSubMul** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：nonZeroSubMul : SubMulAction Rˣ M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-zero elements of `M` are invariant under the action by the units of `R`.
-/
def nonZeroSubMul : SubMulAction Rˣ M where
  carrier := { x : M | x ≠ 0 }
  smul_mem' := by simp [Units.smul_def]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction Rˣ { x : M // x ≠ 0 } :=
  inferInstanceAs <| MulAction Rˣ (nonZeroSubMul R M)

@[simp]
/-
**Units.smul_coe** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：smul_coe (a : Rˣ) (x : { x : M // x != 0 }) : (a • x).val = a • x.val
参数：a : Rˣ；x : { x : M // x != 0 }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_coe (a : Rˣ) (x : { x : M // x ≠ 0 }) :
    (a • x).val = a • x.val :=
  rfl
/-
**Units.orbitRel_nonZero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：orbitRel_nonZero_iff (x y : { v : M // v != 0 }) : MulAction.orbitRel Rˣ {
 v // v != 0 } x y ↔ MulAction.orbitRel Rˣ M x y
参数：x y : { v : M // v != 0 }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma orbitRel_nonZero_iff (x y : { v : M // v ≠ 0 }) :
    MulAction.orbitRel Rˣ { v // v ≠ 0 } x y ↔ MulAction.orbitRel Rˣ M x y :=
  ⟨by rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩, by intro ⟨a, ha⟩; exact ⟨a, by ext; simpa⟩⟩

end Units

section FixedPoints

variable {G : Type*} [Group G] {α : Type*} [MulAction G α] {H : Subgroup G}

@[to_additive]
/-
**smul_mem_fixedPoints_of_normal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_mem_fixedPoints_of_normal [hH : H.Normal] (g : G) {a : α} (ha : a in 
MulAction.fixedPoints H α) : g • a in MulAction.fixedPoints H α
参数：g : G；ha : a in MulAction.fixedPoints H α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.smul_def`：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [ins
t_1 : MulAction G α] {S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Subgroup.Normal.conj_mem'`：conj_mem' (nH : H.Normal) (n : G) (hn : n in 
H) (g : G) : g⁻¹ * n * g in H
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma smul_mem_fixedPoints_of_normal [hH : H.Normal]
    (g : G) {a : α} (ha : a ∈ MulAction.fixedPoints H α) :
    g • a ∈ MulAction.fixedPoints H α := by
  intro h
  rw [Subgroup.smul_def, ← inv_smul_eq_iff, smul_smul, smul_smul]
  exact ha ⟨_, hH.conj_mem' _ h.2 _⟩

/-- The set of fixed points of a normal subgroup is stable under the group action. -/
@[to_additive /-- The set of fixed points of a normal subgroup is stable under the group action. -/]
/-
**fixedPointsSubMulOfNormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fixedPointsSubMulOfNormal [hH : H.Normal] : SubMulAction G α where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `smul_mem_fixedPoints_of_normal`：smul_mem_fixedPoints_of_normal [hH : H.N
ormal] (g : G) {a : α} (ha : a in MulAction.fixedPoints H α) : g • a in MulActio
n.fixedPoints H α

--- 原说明 ---
The set of fixed points of a normal subgroup is stable under the group action.
-/
def fixedPointsSubMulOfNormal [hH : H.Normal] : SubMulAction G α where
  carrier := MulAction.fixedPoints H α
  smul_mem' := smul_mem_fixedPoints_of_normal
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hH : H.Normal] : MulAction G (MulAction.fixedPoints H α) :=
  inferInstanceAs <| MulAction G fixedPointsSubMulOfNormal

@[simp]
/-
**coe_smul_fixedPoints_of_normal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_smul_fixedPoints_of_normal [hH : H.Normal] (g : G) (a : MulAction.fixe
dPoints H α) : (g • a : MulAction.fixedPoints H α) = g • (a : α)
参数：g : G；a : MulAction.fixedPoints H α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul_fixedPoints_of_normal [hH : H.Normal]
    (g : G) (a : MulAction.fixedPoints H α) :
    (g • a : MulAction.fixedPoints H α) = g • (a : α) :=
  rfl

end FixedPoints

