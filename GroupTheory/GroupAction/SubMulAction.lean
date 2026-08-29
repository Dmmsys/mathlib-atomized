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

/--
Definition of `SMulMemClass` / `SMulMemClass` 的定义

English:
class SMulMemClass
  parameters: (S : Type*) (R : outParam Type*) (M : Type*) [SMul R M] [SetLike S M]
  axioms and operations (1):
    - smul_mem : forall {s : S} (r : R) {m : M}, m in s -> r • m in s

中文:
类 SMulMemClass
  参数: (S : 类型) (R : outParam 类型) (M : 类型) [SMul R M] [SetLike S M]
  公理与运算 (1 个):
    - smul_mem : 对任意 {s : S} (r : R) {m : M}, m in s -> r • m in s
-/
class SMulMemClass (S : Type*) (R : outParam Type*) (M : Type*) [SMul R M] [SetLike S M] :
    Prop where
  /-- Multiplication by a scalar on an element of the set remains in the set. -/
  smul_mem : forall {s : S} (r : R) {m : M}, m in s -> r • m in s

/--
Definition of `VAddMemClass` / `VAddMemClass` 的定义

English:
class VAddMemClass
  parameters: (S : Type*) (R : outParam Type*) (M : Type*) [VAdd R M] [SetLike S M]
  axioms and operations (1):
    - vadd_mem : forall {s : S} (r : R) {m : M}, m in s -> r +ᵥ m in s

中文:
类 VAddMemClass
  参数: (S : 类型) (R : outParam 类型) (M : 类型) [VAdd R M] [SetLike S M]
  公理与运算 (1 个):
    - vadd_mem : 对任意 {s : S} (r : R) {m : M}, m in s -> r +ᵥ m in s

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, SetLike, VAddMemClass, VAddMemClass.vadd_mem, smul_mem, vadd_mem
-/
class VAddMemClass (S : Type*) (R : outParam Type*) (M : Type*) [VAdd R M] [SetLike S M] :
    Prop where
  /-- Addition by a scalar with an element of the set remains in the set. -/
  vadd_mem : forall {s : S} (r : R) {m : M}, m in s -> r +ᵥ m in s

attribute [to_additive] SMulMemClass

attribute [aesop 90% (rule_sets := [SetLike])] SMulMemClass.smul_mem VAddMemClass.vadd_mem

/--
lemma `AddSubmonoidClass.nsmulMemClass` / 引理 `AddSubmonoidClass.nsmulMemClass`

English:
lemma AddSubmonoidClass.nsmulMemClass
  statement: {S M : Type*} [AddMonoid M] [SetLike S M]
  proof: nsmul_mem hx n

中文:
引理 AddSubmonoidClass.nsmulMemClass
  结论: {S M : 类型} [AddMonoid M] [SetLike S M]
  证明: nsmul_mem hx n

Depends on / 依赖: nsmul_mem
-/
lemma AddSubmonoidClass.nsmulMemClass {S M : Type*} [AddMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] : SMulMemClass S Nat M where
  smul_mem n _x hx := nsmul_mem hx n

/--
lemma `AddSubgroupClass.zsmulMemClass` / 引理 `AddSubgroupClass.zsmulMemClass`

English:
lemma AddSubgroupClass.zsmulMemClass
  statement: {S M : Type*} [SubNegMonoid M] [SetLike S M]
  proof: zsmul_mem hx n

中文:
引理 AddSubgroupClass.zsmulMemClass
  结论: {S M : 类型} [SubNegMonoid M] [SetLike S M]
  证明: zsmul_mem hx n

Depends on / 依赖: zsmul_mem
-/
lemma AddSubgroupClass.zsmulMemClass {S M : Type*} [SubNegMonoid M] [SetLike S M]
    [AddSubgroupClass S M] : SMulMemClass S Int M where
  smul_mem n _x hx := zsmul_mem hx n

namespace SetLike

open SMulMemClass

section SMul

variable [SMul R M] [SetLike S M] [hS : SMulMemClass S R M] (s : S)

-- lower priority so other instances are found first
/-- A subset closed under the scalar action inherits that action. -/
@[to_additive /-- A subset closed under the additive action inherits that action. -/]
instance (priority := 50) smul : SMul R s :=
  ⟨fun r x => ⟨r • x.1, smul_mem r x.2⟩⟩

@[to_additive] instance (priority := 50) [SMul T M] [SMulMemClass S T M] [SMulCommClass T R M] :
    SMulCommClass T R s where
  smul_comm _ _ _ := Subtype.ext (smul_comm ..)

@[to_additive] instance (priority := 50) [IsLeftCancelSMul R M] : IsLeftCancelSMul R s where
left_cancel' x _ _ eq := Subtype.ext IsLeftCancelSMul.left_cancel x _ _ congr($eq)

@[to_additive] instance (priority := 50) [IsCancelSMul R M] : IsCancelSMul R s where
  right_cancel' _ _ x eq := IsCancelSMul.right_cancel _ _ x.1 congr($eq)

/--
theorem `_root_.SMulMemClass.ofIsScalarTower` / 定理 `_root_.SMulMemClass.ofIsScalarTower`

English:
theorem _root_.SMulMemClass.ofIsScalarTower
  statement: (S M N α : Type*) [SetLike S α]
  proof: { smul_mem := fun m a ha => smul_one_smul N m a ▸ SMulMemClass.smul_mem _ ha }

中文:
定理 _root_.SMulMemClass.ofIsScalarTower
  结论: (S M N α : 类型) [SetLike S α]
  证明: { smul_mem := fun m a ha => smul_one_smul N m a ▸ SMulMemClass.smul_mem _ ha }
-/
@[to_additive] theorem _root_.SMulMemClass.ofIsScalarTower (S M N α : Type*) [SetLike S α]
    [SMul M N] [SMul M α] [Monoid N] [MulAction N α] [SMulMemClass S N α] [IsScalarTower M N α] :
    SMulMemClass S M α :=
  { smul_mem := fun m a ha => smul_one_smul N m a ▸ SMulMemClass.smul_mem _ ha }

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [Mul M] [MulMemClass S M] [IsScalarTower R M M]
  body: Subtype.ext smul_assoc r (x : M) (y : M)

中文:
实例 instIsScalarTower
  签名: [Mul M] [MulMemClass S M] [IsScalarTower R M M]
  定义体: Subtype.ext smul_assoc r (x : M) (y : M)

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance instIsScalarTower [Mul M] [MulMemClass S M] [IsScalarTower R M M]
    (s : S) : IsScalarTower R s s where
smul_assoc r x y := Subtype.ext smul_assoc r (x : M) (y : M)

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [Mul M] [MulMemClass S M] [SMulCommClass R M M]
  body: Subtype.ext smul_comm r (x : M) (y : M)

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instSMulCommClass
  签名: [Mul M] [MulMemClass S M] [SMulCommClass R M M]
  定义体: Subtype.ext smul_comm r (x : M) (y : M)

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass [Mul M] [MulMemClass S M] [SMulCommClass R M M]
    (s : S) : SMulCommClass R s s where
smul_comm r x y := Subtype.ext smul_comm r (x : M) (y : M)

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_smul` / 定理 `val_smul`

English:
theorem val_smul
  given: (r : R) (x : s)
  statement: (↑(r • x) : M) = r • (x : M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 val_smul
  条件: (r : R) (x : s)
  结论: (↑(r • x) : M) = r • (x : M)
  证明: rfl

@[to_additive (attr := simp)]
-/
protected theorem val_smul (r : R) (x : s) : (↑(r • x) : M) = r • (x : M) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_smul_mk` / 定理 `mk_smul_mk`

English:
theorem mk_smul_mk
  given: (r : R) (x : M) (hx : x in s)
  statement: r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩
  proof: rfl

@[to_additive]

中文:
定理 mk_smul_mk
  条件: (r : R) (x : M) (hx : x in s)
  结论: r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩
  证明: rfl

@[to_additive]
-/
theorem mk_smul_mk (r : R) (x : M) (hx : x in s) : r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩ :=
  rfl

@[to_additive]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (r : R) (x : s)
  statement: r • x = ⟨r • x, smul_mem r x.2⟩
  proof: rfl

@[simp]

中文:
定理 smul_def
  条件: (r : R) (x : s)
  结论: r • x = ⟨r • x, smul_mem r x.2⟩
  证明: rfl

@[simp]
-/
theorem smul_def (r : R) (x : s) : r • x = ⟨r • x, smul_mem r x.2⟩ :=
  rfl

@[simp]
/--
theorem `forall_smul_mem_iff` / 定理 `forall_smul_mem_iff`

English:
theorem forall_smul_mem_iff
  statement: {R M S : Type*} [Monoid R] [MulAction R M] [SetLike S M]
  proof: ⟨fun h => by simpa using h 1, fun h a => SMulMemClass.smul_mem a h⟩

中文:
定理 forall_smul_mem_iff
  结论: {R M S : 类型} [Monoid R] [MulAction R M] [SetLike S M]
  证明: ⟨fun h => by simpa using h 1, fun h a => SMulMemClass.smul_mem a h⟩

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, smul_mem
-/
theorem forall_smul_mem_iff {R M S : Type*} [Monoid R] [MulAction R M] [SetLike S M]
    [SMulMemClass S R M] {N : S} {x : M} : (forall a : R, a • x in N) ↔ x in N :=
  ⟨fun h => by simpa using h 1, fun h a => SMulMemClass.smul_mem a h⟩

open scoped Pointwise in
@[to_additive]
/--
theorem `smul_subset_self` / 定理 `smul_subset_self`

English:
theorem smul_subset_self
  statement: {S R M : Type*} [SetLike S M] [SMul R M] [SMulMemClass S R M]
  proof: by
  rintro _ ⟨x, hx, rfl⟩
  simpa using SMulMemClass.smul_mem (r : R) hx

中文:
定理 smul_subset_self
  结论: {S R M : 类型} [SetLike S M] [SMul R M] [SMulMemClass S R M]
  证明: by
  rintro _ ⟨x, hx, rfl⟩
  simpa using SMulMemClass.smul_mem (r : R) hx

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, smul_mem
-/
theorem smul_subset_self {S R M : Type*} [SetLike S M] [SMul R M] [SMulMemClass S R M]
    (r : R) (s : S) : (r • s : Set M) subseteq s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa using SMulMemClass.smul_mem (r : R) hx

open scoped Pointwise in
@[to_additive (attr := simp)]
/--
theorem `units_smul` / 定理 `units_smul`

English:
theorem units_smul
  statement: {S R M : Type*} [SetLike S M] [Monoid R] [MulAction R M] [SMulMemClass S R M]
  proof: by
  apply subset_antisymm (smul_subset_self _ s)
  rintro x hx
  exact ⟨r⁻¹ • x, SMulMemClass.smul_mem (↑r⁻¹ : R) hx, by simp [← Units.smul_def]⟩

中文:
定理 units_smul
  结论: {S R M : 类型} [SetLike S M] [Monoid R] [MulAction R M] [SMulMemClass S R M]
  证明: by
  apply subset_antisymm (smul_subset_self _ s)
  rintro x hx
  exact ⟨r⁻¹ • x, SMulMemClass.smul_mem (↑r⁻¹ : R) hx, by simp [← Units.smul_def]⟩

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, Units.smul_def, smul_def, smul_mem, smul_subset_self, subset_antisymm
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
instance (priority := 50) smul' : SMul M s where
  smul r x := ⟨r • x.1, smul_one_smul N r x.1 ▸ smul_mem _ x.2⟩

instance (priority := 50) : IsScalarTower M N s where
  smul_assoc m n x := Subtype.ext (smul_assoc m n x.1)

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_smul_of_tower` / 定理 `val_smul_of_tower`

English:
theorem val_smul_of_tower
  given: (r : M) (x : s)
  statement: (↑(r • x) : α) = r • (x : α)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 val_smul_of_tower
  条件: (r : M) (x : s)
  结论: (↑(r • x) : α) = r • (x : α)
  证明: rfl

@[to_additive (attr := simp)]
-/
protected theorem val_smul_of_tower (r : M) (x : s) : (↑(r • x) : α) = r • (x : α) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_smul_of_tower_mk` / 定理 `mk_smul_of_tower_mk`

English:
theorem mk_smul_of_tower_mk
  given: (r : M) (x : α) (hx : x in s)
  proof: rfl

@[to_additive]

中文:
定理 mk_smul_of_tower_mk
  条件: (r : M) (x : α) (hx : x in s)
  证明: rfl

@[to_additive]
-/
theorem mk_smul_of_tower_mk (r : M) (x : α) (hx : x in s) :
    r • (⟨x, hx⟩ : s) = ⟨r • x, smul_one_smul N r x ▸ smul_mem _ hx⟩ :=
  rfl

@[to_additive]
/--
theorem `smul_of_tower_def` / 定理 `smul_of_tower_def`

English:
theorem smul_of_tower_def
  given: (r : M) (x : s)
  proof: rfl

中文:
定理 smul_of_tower_def
  条件: (r : M) (x : s)
  证明: rfl
-/
theorem smul_of_tower_def (r : M) (x : s) :
    r • x = ⟨r • x, smul_one_smul N r x.1 ▸ smul_mem _ x.2⟩ :=
  rfl

@[to_additive] instance (priority := 50) [SMulCommClass M N α] : SMulCommClass M N s where
  smul_comm _ _ _ := Subtype.ext (smul_comm ..)

@[to_additive] instance (priority := 50) [SMulCommClass N M α] : SMulCommClass N M s where
  smul_comm _ _ _ := Subtype.ext (smul_comm ..)

end OfTower

end SetLike

/--
Definition of `SubAddAction` / `SubAddAction` 的定义

English:
structure SubAddAction
  parameters: (R : Type u) (M : Type v) [VAdd R M]
  axioms and operations (2):
    - carrier : Set M
    - vadd_mem' : forall (c : R) {x : M}, x in carrier -> c +ᵥ x in carrier

中文:
结构 SubAddAction
  参数: (R : 类型u) (M : 类型v) [VAdd R M]
  公理与运算 (2 个):
    - carrier : Set M
    - vadd_mem' : 对任意 (c : R) {x : M}, x in carrier -> c +ᵥ x in carrier
-/
structure SubAddAction (R : Type u) (M : Type v) [VAdd R M] : Type v where
  /-- The underlying set of a `SubAddAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  vadd_mem' : forall (c : R) {x : M}, x in carrier -> c +ᵥ x in carrier

/-- A SubMulAction is a set which is closed under scalar multiplication. -/
@[to_additive]
/--
Definition of `SubMulAction` / `SubMulAction` 的定义

English:
structure SubMulAction
  parameters: (R : Type u) (M : Type v) [SMul R M]
  axioms and operations (2):
    - carrier : Set M
    - smul_mem' : forall (c : R) {x : M}, x in carrier -> c • x in carrier

中文:
结构 SubMulAction
  参数: (R : 类型u) (M : 类型v) [SMul R M]
  公理与运算 (2 个):
    - carrier : Set M
    - smul_mem' : 对任意 (c : R) {x : M}, x in carrier -> c • x in carrier
-/
structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : forall (c : R) {x : M}, x in carrier -> c • x in carrier

namespace SubMulAction

variable [SMul R M]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (SubMulAction R M) M
  body: ⟨SubMulAction.carrier, fun p q h => by cases p; cases q; congr⟩

中文:
实例 :
  签名: SetLike (SubMulAction R M) M
  定义体: ⟨SubMulAction.carrier, fun p q h => by cases p; cases q; congr⟩

Depends on / 依赖: SubMulAction, SubMulAction.carrier, carrier
-/
instance : SetLike (SubMulAction R M) M :=
  ⟨SubMulAction.carrier, fun p q h => by cases p; cases q; congr⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (SubMulAction R M)
  body: .ofSetLike (SubMulAction R M) M

@[to_additive]

中文:
实例 :
  签名: PartialOrder (SubMulAction R M)
  定义体: .ofSetLike (SubMulAction R M) M

@[to_additive]
-/
@[to_additive] instance : PartialOrder (SubMulAction R M) := .ofSetLike (SubMulAction R M) M

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulMemClass (SubMulAction R M) R M
  body: smul_mem' _

@[to_additive (attr := simp)]

中文:
实例 :
  签名: SMulMemClass (SubMulAction R M) R M
  定义体: smul_mem' _

@[to_additive (attr := simp)]

Depends on / 依赖: smul_mem
-/
instance : SMulMemClass (SubMulAction R M) R M where smul_mem := smul_mem' _

@[to_additive (attr := simp)]
/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {p : SubMulAction R M} {x : M}
  statement: x in p.carrier ↔ x in (p : Set M)
  proof: Iff.rfl

@[to_additive (attr := ext)]

中文:
定理 mem_carrier
  条件: {p : SubMulAction R M} {x : M}
  结论: x in p.carrier ↔ x in (p : Set M)
  证明: Iff.rfl

@[to_additive (attr := ext)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {p : SubMulAction R M} {x : M} : x in p.carrier ↔ x in (p : Set M) :=
  Iff.rfl

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : SubMulAction R M} (h : forall x, x in p ↔ x in q)
  statement: p = q
  proof: SetLike.ext h

中文:
定理 ext
  条件: {p q : SubMulAction R M} (h : 对任意 x, x in p ↔ x in q)
  结论: p = q
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {p q : SubMulAction R M} (h : forall x, x in p ↔ x in q) : p = q :=
  SetLike.ext h

/-- Copy of a sub_mul_action with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive /-- Copy of a sub_mul_action with a new `carrier` equal to the old one.
  Useful to fix definitional equalities. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (p : SubMulAction R M) (s : Set M) (hs : s = ↑p)
  body: s
  smul_mem' := hs.symm ▸ p.smul_mem'

@[to_additive (attr := simp)]

中文:
定义 copy
  签名: (p : SubMulAction R M) (s : Set M) (hs : s = ↑p)
  定义体: s
  smul_mem' := hs.symm ▸ p.smul_mem'

@[to_additive (attr := simp)]
-/
protected def copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : SubMulAction R M where
  carrier := s
  smul_mem' := hs.symm ▸ p.smul_mem'

@[to_additive (attr := simp)]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (p : SubMulAction R M) (s : Set M) (hs : s = ↑p)
  statement: (p.copy s hs : Set M) = s
  proof: rfl

@[to_additive]

中文:
定理 coe_copy
  条件: (p : SubMulAction R M) (s : Set M) (hs : s = ↑p)
  结论: (p.copy s hs : Set M) = s
  证明: rfl

@[to_additive]
-/
theorem coe_copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : (p.copy s hs : Set M) = s :=
  rfl

@[to_additive]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (p : SubMulAction R M) (s : Set M) (hs : s = ↑p)
  statement: p.copy s hs = p
  proof: SetLike.coe_injective hs

@[to_additive]

中文:
定理 copy_eq
  条件: (p : SubMulAction R M) (s : Set M) (hs : s = ↑p)
  结论: p.copy s hs = p
  证明: SetLike.coe_injective hs

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (SubMulAction R M)
  body: ⟨⟨∅, by simp⟩⟩

@[to_additive]

中文:
实例 :
  签名: Bot (SubMulAction R M)
  定义体: ⟨⟨∅, by simp⟩⟩

@[to_additive]
-/
instance : Bot (SubMulAction R M) :=
  ⟨⟨∅, by simp⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SubMulAction R M)
  body: ⟨⊥⟩

@[to_additive]

中文:
实例 :
  签名: Inhabited (SubMulAction R M)
  定义体: ⟨⊥⟩

@[to_additive]
-/
instance : Inhabited (SubMulAction R M) :=
  ⟨⊥⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (SubMulAction R M)
  body: ⟨⟨Set.univ, by simp⟩⟩

@[to_additive]

中文:
实例 :
  签名: Top (SubMulAction R M)
  定义体: ⟨⟨Set.univ, by simp⟩⟩

@[to_additive]

Depends on / 依赖: Set.univ
-/
instance : Top (SubMulAction R M) :=
  ⟨⟨Set.univ, by simp⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (SubMulAction R M)
  body: ⟨fun s t => ⟨s union t, by aesop⟩⟩

@[to_additive]

中文:
实例 :
  签名: Max (SubMulAction R M)
  定义体: ⟨fun s t => ⟨s union t, by aesop⟩⟩

@[to_additive]
-/
instance : Max (SubMulAction R M) :=
  ⟨fun s t => ⟨s union t, by aesop⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (SubMulAction R M)
  body: ⟨fun s t => ⟨s inter t, by aesop⟩⟩

@[to_additive]

中文:
实例 :
  签名: Min (SubMulAction R M)
  定义体: ⟨fun s t => ⟨s inter t, by aesop⟩⟩

@[to_additive]
-/
instance : Min (SubMulAction R M) :=
  ⟨fun s t => ⟨s inter t, by aesop⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (SubMulAction R M)
  body: ⟨fun S => ⟨⋃ s in S, s, by aesop⟩⟩

@[to_additive]

中文:
实例 :
  签名: SupSet (SubMulAction R M)
  定义体: ⟨fun S => ⟨⋃ s in S, s, by aesop⟩⟩

@[to_additive]
-/
instance : SupSet (SubMulAction R M) :=
  ⟨fun S => ⟨⋃ s in S, s, by aesop⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (SubMulAction R M)
  body: ⟨fun S => ⟨⋂ s in S, ↑s, by aesop⟩⟩

@[to_additive]

中文:
实例 :
  签名: InfSet (SubMulAction R M)
  定义体: ⟨fun S => ⟨⋂ s in S, ↑s, by aesop⟩⟩

@[to_additive]
-/
instance : InfSet (SubMulAction R M) :=
  ⟨fun S => ⟨⋂ s in S, ↑s, by aesop⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (SubMulAction R M)
  body: SetLike.coe_injective.completeLattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

@[to_additive (attr := simp)]

中文:
实例 :
  签名: CompleteLattice (SubMulAction R M)
  定义体: SetLike.coe_injective.completeLattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_injective.completeLattice, coe_injective, completeLattice
-/
instance : CompleteLattice (SubMulAction R M) :=
  SetLike.coe_injective.completeLattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

@[to_additive (attr := simp)]
/--
theorem `mem_iSup` / 定理 `mem_iSup`

English:
theorem mem_iSup
  given: {ι : Sort*} {p : ι -> SubMulAction R M} {x : M}
  proof: by
  change x in ⋃ s in Set.range p, s ↔ _
  simp

@[to_additive (attr := simp)]

中文:
定理 mem_iSup
  条件: {ι : Sort*} {p : ι -> SubMulAction R M} {x : M}
  证明: by
  change x in ⋃ s in Set.range p, s ↔ _
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Set.range
-/
theorem mem_iSup {ι : Sort*} {p : ι -> SubMulAction R M} {x : M} :
    x in ⨆ i, p i ↔ exists i, x in p i := by
  change x in ⋃ s in Set.range p, s ↔ _
  simp

@[to_additive (attr := simp)]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {p : ι -> SubMulAction R M} {x : M}
  proof: by
  change x in ⋂ s in Set.range p, s ↔ _
  simp

中文:
定理 mem_iInf
  条件: {ι : Sort*} {p : ι -> SubMulAction R M} {x : M}
  证明: by
  change x in ⋂ s in Set.range p, s ↔ _
  simp

Depends on / 依赖: Set.range
-/
theorem mem_iInf {ι : Sort*} {p : ι -> SubMulAction R M} {x : M} :
    x in ⨅ i, p i ↔ forall i, x in p i := by
  change x in ⋂ s in Set.range p, s ↔ _
  simp

end SubMulAction

namespace SubMulAction

section SMul

variable [SMul R M]
variable (p : SubMulAction R M)
variable {r : R} {x : M}

@[to_additive]
/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: (r : R) (h : x in p)
  statement: r • x in p
  proof: p.smul_mem' r h

@[to_additive]

中文:
定理 smul_mem
  条件: (r : R) (h : x in p)
  结论: r • x in p
  证明: p.smul_mem' r h

@[to_additive]

Depends on / 依赖: p.smul_mem, smul_mem
-/
theorem smul_mem (r : R) (h : x in p) : r • x in p :=
  p.smul_mem' r h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R p
  body: ⟨c • x.1, smul_mem _ c x.2⟩

中文:
实例 :
  签名: SMul R p
  定义体: ⟨c • x.1, smul_mem _ c x.2⟩

Depends on / 依赖: smul_mem
-/
instance : SMul R p where smul c x := ⟨c • x.1, smul_mem _ c x.2⟩

variable {p} in
@[to_additive (attr := norm_cast, simp)]
/--
theorem `val_smul` / 定理 `val_smul`

English:
theorem val_smul
  given: (r : R) (x : p)
  statement: (↑(r • x) : M) = r • (x : M)
  proof: rfl

中文:
定理 val_smul
  条件: (r : R) (x : p)
  结论: (↑(r • x) : M) = r • (x : M)
  证明: rfl
-/
theorem val_smul (r : R) (x : p) : (↑(r • x) : M) = r • (x : M) :=
  rfl

/-- Embedding of a submodule `p` to the ambient space `M`. -/
@[to_additive /-- Embedding of a submodule `p` to the ambient space `M`. -/]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : p ->[R] M where
  body: Subtype.val
  map_smul' := by simp

中文:
定义 subtype
  签名: : p ->[R] M where
  定义体: Subtype.val
  map_smul' := by simp
-/
protected def subtype : p ->[R] M where
  toFun := Subtype.val
  map_smul' := by simp

variable {p} in
@[to_additive (attr := simp)]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: (x : p)
  statement: p.subtype x = x
  proof: rfl

中文:
定理 subtype_apply
  条件: (x : p)
  结论: p.subtype x = x
  证明: rfl
-/
theorem subtype_apply (x : p) : p.subtype x = x :=
  rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[to_additive]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective p.subtype :=
  Subtype.coe_injective

@[to_additive]
/--
theorem `subtype_eq_val` / 定理 `subtype_eq_val`

English:
theorem subtype_eq_val
  statement: (SubMulAction.subtype p : p -> M) = Subtype.val
  proof: rfl

中文:
定理 subtype_eq_val
  结论: (SubMulAction.subtype p : p -> M) = Subtype.val
  证明: rfl
-/
theorem subtype_eq_val : (SubMulAction.subtype p : p -> M) = Subtype.val :=
  rfl

end SMul

namespace SMulMemClass

variable [Monoid R] [MulAction R M] {A : Type*} [SetLike A M]
variable [hA : SMulMemClass A R M] (S' : A)

-- Prefer subclasses of `MulAction` over `SMulMemClass`.
/-- A `SubMulAction` of a `MulAction` is a `MulAction`. -/
@[to_additive /-- A `SubAddAction` of an `AddAction` is an `AddAction`. -/]
instance (priority := 75) toMulAction : MulAction R S' :=
  Subtype.coe_injective.mulAction Subtype.val (SetLike.val_smul S')

/-- The natural `MulActionHom` over `R` from a `SubMulAction` of `M` to `M`. -/
@[to_additive /-- The natural `AddActionHom` over `R` from a `SubAddAction` of `M` to `M`. -/]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : S' ->[R] M where
  body: Subtype.val; map_smul' _ _ := rfl

中文:
定义 subtype
  签名: : S' ->[R] M where
  定义体: Subtype.val; map_smul' _ _ := rfl
-/
protected def subtype : S' ->[R] M where
  toFun := Subtype.val; map_smul' _ _ := rfl

variable {S'} in
@[simp]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (x : S')
  proof: rfl

中文:
引理 subtype_apply
  条件: (x : S')
  证明: rfl
-/
lemma subtype_apply (x : S') :
    SMulMemClass.subtype S' x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[to_additive (attr := simp)]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective (SMulMemClass.subtype S') :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (SMulMemClass.subtype S' : S' -> M) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (SMulMemClass.subtype S' : S' -> M) = Subtype.val
  证明: rfl
-/
protected theorem coe_subtype : (SMulMemClass.subtype S' : S' -> M) = Subtype.val :=
  rfl

end SMulMemClass

section MulActionMonoid

variable [Monoid R] [MulAction R M]

section

variable [SMul S R] [SMul S M] [IsScalarTower S R M]
variable (p : SubMulAction R M)

@[to_additive]
/--
theorem `smul_of_tower_mem` / 定理 `smul_of_tower_mem`

English:
theorem smul_of_tower_mem
  given: (s : S) {x : M} (h : x in p)
  statement: s • x in p
  proof: by
  rw [← one_smul R x]; rw [← smul_assoc]
  exact p.smul_mem _ h

@[to_additive]

中文:
定理 smul_of_tower_mem
  条件: (s : S) {x : M} (h : x in p)
  结论: s • x in p
  证明: by
  rw [← one_smul R x]; rw [← smul_assoc]
  exact p.smul_mem _ h

@[to_additive]

Depends on / 依赖: one_smul, p.smul_mem, smul_assoc, smul_mem
-/
theorem smul_of_tower_mem (s : S) {x : M} (h : x in p) : s • x in p := by
  rw [← one_smul R x]; rw [← smul_assoc]
  exact p.smul_mem _ h

@[to_additive]
/--
Instance `smul'` / 实例 `smul'`

English:
instance smul'
  signature: : SMul S p where smul c x
  body: ⟨c • x.1, smul_of_tower_mem _ c x.2⟩

@[to_additive]

中文:
实例 smul'
  签名: : SMul S p where smul c x
  定义体: ⟨c • x.1, smul_of_tower_mem _ c x.2⟩

@[to_additive]

Depends on / 依赖: smul_of_tower_mem
-/
instance smul' : SMul S p where smul c x := ⟨c • x.1, smul_of_tower_mem _ c x.2⟩

@[to_additive]
/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: : IsScalarTower S R p where
  body: Subtype.ext smul_assoc s r (x : M)

@[to_additive]

中文:
实例 isScalarTower
  签名: : IsScalarTower S R p where
  定义体: Subtype.ext smul_assoc s r (x : M)

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower : IsScalarTower S R p where
smul_assoc s r x := Subtype.ext smul_assoc s r (x : M)

@[to_additive]
/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: {S' : Type*} [SMul S' R] [SMul S' S] [SMul S' M] [IsScalarTower S' R M]
  body: Subtype.ext smul_assoc s r (x : M)

@[to_additive (attr := norm_cast, simp)]

中文:
实例 isScalarTower'
  签名: {S' : 类型} [SMul S' R] [SMul S' S] [SMul S' M] [IsScalarTower S' R M]
  定义体: Subtype.ext smul_assoc s r (x : M)

@[to_additive (attr := norm_cast, simp)]

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower' {S' : Type*} [SMul S' R] [SMul S' S] [SMul S' M] [IsScalarTower S' R M]
    [IsScalarTower S' S M] : IsScalarTower S' S p where
smul_assoc s r x := Subtype.ext smul_assoc s r (x : M)

@[to_additive (attr := norm_cast, simp)]
/--
theorem `val_smul_of_tower` / 定理 `val_smul_of_tower`

English:
theorem val_smul_of_tower
  given: (s : S) (x : p)
  statement: ((s • x : p) : M) = s • (x : M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 val_smul_of_tower
  条件: (s : S) (x : p)
  结论: ((s • x : p) : M) = s • (x : M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem val_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • (x : M) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_mem_iff'` / 定理 `smul_mem_iff'`

English:
theorem smul_mem_iff'
  statement: {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M] (g : G)
  proof: ⟨fun h => inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩

@[to_additive]

中文:
定理 smul_mem_iff'
  结论: {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M] (g : G)
  证明: ⟨fun h => inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩

@[to_additive]

Depends on / 依赖: inv_smul_smul, p.smul_of_tower_mem, smul_of_tower_mem
-/
theorem smul_mem_iff' {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M] (g : G)
    {x : M} : g • x in p ↔ x in p :=
  ⟨fun h => inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩

@[to_additive]
/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
  body: Subtype.ext op_smul_eq_smul r (x : M)

中文:
实例 isCentralScalar
  签名: [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
  定义体: Subtype.ext op_smul_eq_smul r (x : M)

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk_surjective, Subtype, Subtype.ext, mk_surjective, op_smul_eq_smul, small_of_surjective
-/
instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] :
    IsCentralScalar S p where
op_smul_eq_smul r x := Subtype.ext op_smul_eq_smul r (x : M)

end

section

variable [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
variable (p : SubMulAction R M)

/-- If the scalar product forms a `MulAction`, then the subset inherits this action -/
@[to_additive]
/--
Instance `mulAction'` / 实例 `mulAction'`

English:
instance mulAction'
  signature: : MulAction S p where
  body: Subtype.ext one_smul _ (x : M)
mul_smul c₁ c₂ x := Subtype.ext mul_smul c₁ c₂ (x : M)

@[to_additive]

中文:
实例 mulAction'
  签名: : MulAction S p where
  定义体: Subtype.ext one_smul _ (x : M)
mul_smul c₁ c₂ x := Subtype.ext mul_smul c₁ c₂ (x : M)

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext, one_smul
-/
instance mulAction' : MulAction S p where
one_smul x := Subtype.ext one_smul _ (x : M)
mul_smul c₁ c₂ x := Subtype.ext mul_smul c₁ c₂ (x : M)

@[to_additive]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: : MulAction R p
  body: p.mulAction'

中文:
实例 mulAction
  签名: : MulAction R p
  定义体: p.mulAction'

Depends on / 依赖: mulAction, p.mulAction
-/
instance mulAction : MulAction R p :=
  p.mulAction'

end

/-- Orbits in a `SubMulAction` coincide with orbits in the ambient space. -/
@[to_additive]
/--
theorem `val_image_orbit` / 定理 `val_image_orbit`

English:
theorem val_image_orbit
  given: {p : SubMulAction R M} (m : p)
  proof: (Set.range_comp _ _).symm

@[to_additive]

中文:
定理 val_image_orbit
  条件: {p : SubMulAction R M} (m : p)
  证明: (Set.range_comp _ _).symm

@[to_additive]

Depends on / 依赖: Set.range_comp, range_comp
-/
theorem val_image_orbit {p : SubMulAction R M} (m : p) :
    Subtype.val '' MulAction.orbit R m = MulAction.orbit R (m : M) :=
  (Set.range_comp _ _).symm

@[to_additive]
/--
theorem `val_preimage_orbit` / 定理 `val_preimage_orbit`

English:
theorem val_preimage_orbit
  given: {p : SubMulAction R M} (m : p)
  proof: by
  rw [← val_image_orbit]; rw [Subtype.val_injective.preimage_image]

@[to_additive]

中文:
定理 val_preimage_orbit
  条件: {p : SubMulAction R M} (m : p)
  证明: by
  rw [← val_image_orbit]; rw [Subtype.val_injective.preimage_image]

@[to_additive]

Depends on / 依赖: Subtype, Subtype.val_injective.preimage_image, preimage_image, val_image_orbit, val_injective
-/
theorem val_preimage_orbit {p : SubMulAction R M} (m : p) :
    Subtype.val ⁻¹' MulAction.orbit R (m : M) = MulAction.orbit R m := by
  rw [← val_image_orbit]; rw [Subtype.val_injective.preimage_image]

@[to_additive]
/--
lemma `mem_orbit_subMul_iff` / 引理 `mem_orbit_subMul_iff`

English:
lemma mem_orbit_subMul_iff
  given: {p : SubMulAction R M} {x m : p}
  proof: by
  rw [← val_preimage_orbit]; rw [Set.mem_preimage]

中文:
引理 mem_orbit_subMul_iff
  条件: {p : SubMulAction R M} {x m : p}
  证明: by
  rw [← val_preimage_orbit]; rw [Set.mem_preimage]

Depends on / 依赖: Set.mem_preimage, mem_preimage, val_preimage_orbit
-/
lemma mem_orbit_subMul_iff {p : SubMulAction R M} {x m : p} :
    x in MulAction.orbit R m ↔ (x : M) in MulAction.orbit R (m : M) := by
  rw [← val_preimage_orbit]; rw [Set.mem_preimage]

/-- Stabilizers in monoid SubMulAction coincide with stabilizers in the ambient space -/
@[to_additive]
/--
theorem `stabilizer_of_subMul.submonoid` / 定理 `stabilizer_of_subMul.submonoid`

English:
theorem stabilizer_of_subMul.submonoid
  given: {p : SubMulAction R M} (m : p)
  proof: by
  ext
  simp only [MulAction.mem_stabilizerSubmonoid_iff, ← SubMulAction.val_smul, SetLike.coe_eq_coe]

中文:
定理 stabilizer_of_subMul.submonoid
  条件: {p : SubMulAction R M} (m : p)
  证明: by
  ext
  simp only [MulAction.mem_stabilizerSubmonoid_iff, ← SubMulAction.val_smul, SetLike.coe_eq_coe]

Depends on / 依赖: MulAction, MulAction.mem_stabilizerSubmonoid_iff, SetLike, SetLike.coe_eq_coe, SubMulAction, SubMulAction.val_smul, coe_eq_coe, mem_stabilizerSubmonoid_iff, val_smul
-/
theorem stabilizer_of_subMul.submonoid {p : SubMulAction R M} (m : p) :
    MulAction.stabilizerSubmonoid R m = MulAction.stabilizerSubmonoid R (m : M) := by
  ext
  simp only [MulAction.mem_stabilizerSubmonoid_iff, ← SubMulAction.val_smul, SetLike.coe_eq_coe]

end MulActionMonoid

section MulActionGroup

variable [Group R] [MulAction R M]

@[to_additive]
/--
lemma `orbitRel_of_subMul` / 引理 `orbitRel_of_subMul`

English:
lemma orbitRel_of_subMul
  given: (p : SubMulAction R M)
  proof: by
  refine Setoid.ext_iff.2 (fun x y => ?_)
  rw [Setoid.comap_rel]
  exact mem_orbit_subMul_iff

中文:
引理 orbitRel_of_subMul
  条件: (p : SubMulAction R M)
  证明: by
  refine Setoid.ext_iff.2 (fun x y => ?_)
  rw [Setoid.comap_rel]
  exact mem_orbit_subMul_iff

Depends on / 依赖: Setoid, Setoid.comap_rel, Setoid.ext_iff, comap_rel, ext_iff, mem_orbit_subMul_iff
-/
lemma orbitRel_of_subMul (p : SubMulAction R M) :
    MulAction.orbitRel R p = (MulAction.orbitRel R M).comap Subtype.val := by
  refine Setoid.ext_iff.2 (fun x y => ?_)
  rw [Setoid.comap_rel]
  exact mem_orbit_subMul_iff

/-- Stabilizers in group SubMulAction coincide with stabilizers in the ambient space -/
@[to_additive]
/--
theorem `stabilizer_of_subMul` / 定理 `stabilizer_of_subMul`

English:
theorem stabilizer_of_subMul
  given: {p : SubMulAction R M} (m : p)
  proof: by
  rw [← Subgroup.toSubmonoid_inj]
  exact stabilizer_of_subMul.submonoid m

中文:
定理 stabilizer_of_subMul
  条件: {p : SubMulAction R M} (m : p)
  证明: by
  rw [← Subgroup.toSubmonoid_inj]
  exact stabilizer_of_subMul.submonoid m

Depends on / 依赖: Subgroup, Subgroup.toSubmonoid_inj, stabilizer_of_subMul, stabilizer_of_subMul.submonoid, submonoid, toSubmonoid_inj
-/
theorem stabilizer_of_subMul {p : SubMulAction R M} (m : p) :
    MulAction.stabilizer R m = MulAction.stabilizer R (m : M) := by
  rw [← Subgroup.toSubmonoid_inj]
  exact stabilizer_of_subMul.submonoid m

/-- SubMulAction on the complement of an invariant subset -/
@[to_additive /-- SubAddAction on the complement of an invariant subset -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl (SubMulAction R M)
  body: ⟨sᶜ, by simp⟩

@[to_additive]

中文:
实例 :
  签名: Compl (SubMulAction R M)
  定义体: ⟨sᶜ, by simp⟩

@[to_additive]
-/
instance : Compl (SubMulAction R M) where
  compl s := ⟨sᶜ, by simp⟩

@[to_additive]
/--
theorem `compl_def` / 定理 `compl_def`

English:
theorem compl_def
  given: (s : SubMulAction R M)
  statement: sᶜ.carrier = (s : Set M)ᶜ
  proof: rfl

中文:
定理 compl_def
  条件: (s : SubMulAction R M)
  结论: sᶜ.carrier = (s : Set M)ᶜ
  证明: rfl
-/
theorem compl_def (s : SubMulAction R M) : sᶜ.carrier = (s : Set M)ᶜ := rfl

end MulActionGroup

section Module

variable [Semiring R] [AddCommMonoid M]
variable [Module R M]
variable (p : SubMulAction R M)

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  given: (h : (p : Set M).Nonempty)
  statement: (0 : M) in p
  proof: let ⟨x, hx⟩ := h
  zero_smul R (x : M) ▸ p.smul_mem 0 hx

中文:
定理 zero_mem
  条件: (h : (p : Set M).Nonempty)
  结论: (0 : M) in p
  证明: let ⟨x, hx⟩ := h
  zero_smul R (x : M) ▸ p.smul_mem 0 hx

Depends on / 依赖: p.smul_mem, smul_mem, zero_smul
-/
theorem zero_mem (h : (p : Set M).Nonempty) : (0 : M) in p :=
  let ⟨x, hx⟩ := h
  zero_smul R (x : M) ▸ p.smul_mem 0 hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [n_empty
  signature: : Nonempty p] : Zero p where
  body: ⟨0, n_empty.elim fun x => p.zero_mem ⟨x, x.prop⟩⟩

中文:
实例 [n_empty
  签名: : Nonempty p] : Zero p where
  定义体: ⟨0, n_empty.elim fun x => p.zero_mem ⟨x, x.prop⟩⟩

Depends on / 依赖: n_empty, n_empty.elim, p.zero_mem, x.prop, zero_mem
-/
instance [n_empty : Nonempty p] : Zero p where
  zero := ⟨0, n_empty.elim fun x => p.zero_mem ⟨x, x.prop⟩⟩

end Module

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable [Module R M]
variable (p p' : SubMulAction R M)
variable {r : R} {x y : M}

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: (hx : x in p)
  statement: -x in p
  proof: by
  rw [← neg_one_smul R]
  exact p.smul_mem _ hx

@[simp]

中文:
定理 neg_mem
  条件: (hx : x in p)
  结论: -x in p
  证明: by
  rw [← neg_one_smul R]
  exact p.smul_mem _ hx

@[simp]

Depends on / 依赖: neg_one_smul, p.smul_mem, smul_mem
-/
theorem neg_mem (hx : x in p) : -x in p := by
  rw [← neg_one_smul R]
  exact p.smul_mem _ hx

@[simp]
/--
theorem `neg_mem_iff` / 定理 `neg_mem_iff`

English:
theorem neg_mem_iff
  statement: -x in p ↔ x in p
  proof: ⟨fun h => by
    rw [← neg_neg x]
    exact neg_mem _ h, neg_mem _⟩

中文:
定理 neg_mem_iff
  结论: -x in p ↔ x in p
  证明: ⟨fun h => by
    rw [← neg_neg x]
    exact neg_mem _ h, neg_mem _⟩

Depends on / 依赖: neg_mem, neg_neg
-/
theorem neg_mem_iff : -x in p ↔ x in p :=
  ⟨fun h => by
    rw [← neg_neg x]
    exact neg_mem _ h, neg_mem _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg p
  body: ⟨fun x => ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Neg p
  定义体: ⟨fun x => ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: neg_mem
-/
instance : Neg p :=
  ⟨fun x => ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast]
/--
theorem `val_neg` / 定理 `val_neg`

English:
theorem val_neg
  given: (x : p)
  statement: ((-x : p) : M) = -x
  proof: rfl

中文:
定理 val_neg
  条件: (x : p)
  结论: ((-x : p) : M) = -x
  证明: rfl
-/
theorem val_neg (x : p) : ((-x : p) : M) = -x :=
  rfl

end AddCommGroup

end SubMulAction

namespace SubMulAction

variable [GroupWithZero S] [Monoid R] [MulAction R M]
variable [SMul S R] [MulAction S M] [IsScalarTower S R M]
variable (p : SubMulAction R M) {s : S} {x y : M}

/--
theorem `smul_mem_iff` / 定理 `smul_mem_iff`

English:
theorem smul_mem_iff
  given: (s0 : s != 0)
  statement: s • x in p ↔ x in p
  proof: p.smul_mem_iff' (Units.mk0 s s0)

中文:
定理 smul_mem_iff
  条件: (s0 : s != 0)
  结论: s • x in p ↔ x in p
  证明: p.smul_mem_iff' (Units.mk0 s s0)

Depends on / 依赖: Units.mk0, p.smul_mem_iff, smul_mem_iff
-/
theorem smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p :=
  p.smul_mem_iff' (Units.mk0 s s0)

end SubMulAction

namespace SubMulAction

/- The inclusion of a `SubMulAction`, as an equivariant map -/
variable {M α : Type*} [Monoid M] [MulAction M α]


/-- The inclusion of a SubMulAction into the ambient set, as an equivariant map -/
@[to_additive /-- The inclusion of a SubAddAction into the ambient set, as an equivariant map. -/]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (s : SubMulAction M α)

中文:
定义 inclusion
  签名: (s : SubMulAction M α)

Depends on / 依赖: Subtype, Subtype.val
-/
def inclusion (s : SubMulAction M α) : s ->[M] α where
-- The inclusion map of the inclusion of a SubMulAction
  toFun := Subtype.val
-- The commutation property
  map_smul' _ _ := rfl

@[to_additive]
/--
theorem `inclusion.toFun_eq_coe` / 定理 `inclusion.toFun_eq_coe`

English:
theorem inclusion.toFun_eq_coe
  given: (s : SubMulAction M α)
  proof: rfl

@[to_additive]

中文:
定理 inclusion.toFun_eq_coe
  条件: (s : SubMulAction M α)
  证明: rfl

@[to_additive]
-/
theorem inclusion.toFun_eq_coe (s : SubMulAction M α) :
    s.inclusion.toFun = Subtype.val := rfl

@[to_additive]
/--
theorem `inclusion.coe_eq` / 定理 `inclusion.coe_eq`

English:
theorem inclusion.coe_eq
  given: (s : SubMulAction M α)
  proof: rfl

@[to_additive]

中文:
定理 inclusion.coe_eq
  条件: (s : SubMulAction M α)
  证明: rfl

@[to_additive]
-/
theorem inclusion.coe_eq (s : SubMulAction M α) :
    ⇑s.inclusion = Subtype.val := rfl

@[to_additive]
/--
lemma `image_inclusion` / 引理 `image_inclusion`

English:
lemma image_inclusion
  given: (s : SubMulAction M α)
  proof: by
  rw [inclusion.coe_eq]
  exact Subtype.range_coe

@[to_additive]

中文:
引理 image_inclusion
  条件: (s : SubMulAction M α)
  证明: by
  rw [inclusion.coe_eq]
  exact Subtype.range_coe

@[to_additive]

Depends on / 依赖: Subtype, Subtype.range_coe, coe_eq, inclusion, inclusion.coe_eq, range_coe
-/
lemma image_inclusion (s : SubMulAction M α) :
    Set.range s.inclusion = s.carrier := by
  rw [inclusion.coe_eq]
  exact Subtype.range_coe

@[to_additive]
/--
lemma `inclusion_injective` / 引理 `inclusion_injective`

English:
lemma inclusion_injective
  given: (s : SubMulAction M α)
  proof: Subtype.val_injective

中文:
引理 inclusion_injective
  条件: (s : SubMulAction M α)
  证明: Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
lemma inclusion_injective (s : SubMulAction M α) :
    Function.Injective s.inclusion :=
  Subtype.val_injective

end SubMulAction

namespace Units

variable (R M : Type*) [Monoid R] [AddCommMonoid M] [DistribMulAction R M]

/--
Definition of `nonZeroSubMul` / `nonZeroSubMul` 的定义

English:
definition nonZeroSubMul
  signature: : SubMulAction Rˣ M where
  body: { x : M | x != 0 }
  smul_mem' := by simp [Units.smul_def]

中文:
定义 nonZeroSubMul
  签名: : SubMulAction Rˣ M where
  定义体: { x : M | x != 0 }
  smul_mem' := by simp [Units.smul_def]
-/
def nonZeroSubMul : SubMulAction Rˣ M where
  carrier := { x : M | x != 0 }
  smul_mem' := by simp [Units.smul_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction Rˣ { x : M // x != 0 }
  body: inferInstanceAs MulAction Rˣ (nonZeroSubMul R M)

@[simp]

中文:
实例 :
  签名: MulAction Rˣ { x : M // x != 0 }
  定义体: inferInstanceAs MulAction Rˣ (nonZeroSubMul R M)

@[simp]

Depends on / 依赖: MulAction, nonZeroSubMul
-/
instance : MulAction Rˣ { x : M // x != 0 } :=
inferInstanceAs MulAction Rˣ (nonZeroSubMul R M)

@[simp]
/--
lemma `smul_coe` / 引理 `smul_coe`

English:
lemma smul_coe
  given: (a : Rˣ) (x : { x : M // x != 0 })
  proof: rfl

中文:
引理 smul_coe
  条件: (a : Rˣ) (x : { x : M // x != 0 })
  证明: rfl
-/
lemma smul_coe (a : Rˣ) (x : { x : M // x != 0 }) :
    (a • x).val = a • x.val :=
  rfl

/--
lemma `orbitRel_nonZero_iff` / 引理 `orbitRel_nonZero_iff`

English:
lemma orbitRel_nonZero_iff
  given: (x y : { v : M // v != 0 })
  proof: ⟨by rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩, by intro ⟨a, ha⟩; exact ⟨a, by ext; simpa⟩⟩

中文:
引理 orbitRel_nonZero_iff
  条件: (x y : { v : M // v != 0 })
  证明: ⟨by rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩, by intro ⟨a, ha⟩; exact ⟨a, by ext; simpa⟩⟩
-/
lemma orbitRel_nonZero_iff (x y : { v : M // v != 0 }) :
    MulAction.orbitRel Rˣ { v // v != 0 } x y ↔ MulAction.orbitRel Rˣ M x y :=
  ⟨by rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩, by intro ⟨a, ha⟩; exact ⟨a, by ext; simpa⟩⟩

end Units

section FixedPoints

variable {G : Type*} [Group G] {α : Type*} [MulAction G α] {H : Subgroup G}

@[to_additive]
/--
lemma `smul_mem_fixedPoints_of_normal` / 引理 `smul_mem_fixedPoints_of_normal`

English:
lemma smul_mem_fixedPoints_of_normal
  statement: [hH : H.Normal]
  proof: by
  intro h
  rw [Subgroup.smul_def]; rw [← inv_smul_eq_iff]; rw [smul_smul]; rw [smul_smul]
  exact ha ⟨_, hH.conj_mem' _ h.2 _⟩

中文:
引理 smul_mem_fixedPoints_of_normal
  结论: [hH : H.Normal]
  证明: by
  intro h
  rw [Subgroup.smul_def]; rw [← inv_smul_eq_iff]; rw [smul_smul]; rw [smul_smul]
  exact ha ⟨_, hH.conj_mem' _ h.2 _⟩

Depends on / 依赖: Subgroup, Subgroup.smul_def, conj_mem, hH.conj_mem, inv_smul_eq_iff, smul_def, smul_smul
-/
lemma smul_mem_fixedPoints_of_normal [hH : H.Normal]
    (g : G) {a : α} (ha : a in MulAction.fixedPoints H α) :
    g • a in MulAction.fixedPoints H α := by
  intro h
  rw [Subgroup.smul_def]; rw [← inv_smul_eq_iff]; rw [smul_smul]; rw [smul_smul]
  exact ha ⟨_, hH.conj_mem' _ h.2 _⟩

/-- The set of fixed points of a normal subgroup is stable under the group action. -/
@[to_additive /-- The set of fixed points of a normal subgroup is stable under the group action. -/]
/--
Definition of `fixedPointsSubMulOfNormal` / `fixedPointsSubMulOfNormal` 的定义

English:
definition fixedPointsSubMulOfNormal
  signature: [hH : H.Normal]
  body: MulAction.fixedPoints H α
  smul_mem' := smul_mem_fixedPoints_of_normal

中文:
定义 fixedPointsSubMulOfNormal
  签名: [hH : H.Normal]
  定义体: MulAction.fixedPoints H α
  smul_mem' := smul_mem_fixedPoints_of_normal

Depends on / 依赖: MulAction, MulAction.fixedPoints, fixedPoints
-/
def fixedPointsSubMulOfNormal [hH : H.Normal] : SubMulAction G α where
  carrier := MulAction.fixedPoints H α
  smul_mem' := smul_mem_fixedPoints_of_normal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hH
  signature: : H.Normal] : MulAction G (MulAction.fixedPoints H α)
  body: inferInstanceAs MulAction G fixedPointsSubMulOfNormal

@[simp]

中文:
实例 [hH
  签名: : H.Normal] : MulAction G (MulAction.fixedPoints H α)
  定义体: inferInstanceAs MulAction G fixedPointsSubMulOfNormal

@[simp]

Depends on / 依赖: MulAction, fixedPointsSubMulOfNormal
-/
instance [hH : H.Normal] : MulAction G (MulAction.fixedPoints H α) :=
inferInstanceAs MulAction G fixedPointsSubMulOfNormal

@[simp]
/--
lemma `coe_smul_fixedPoints_of_normal` / 引理 `coe_smul_fixedPoints_of_normal`

English:
lemma coe_smul_fixedPoints_of_normal
  statement: [hH : H.Normal]
  proof: rfl

中文:
引理 coe_smul_fixedPoints_of_normal
  结论: [hH : H.Normal]
  证明: rfl
-/
lemma coe_smul_fixedPoints_of_normal [hH : H.Normal]
    (g : G) (a : MulAction.fixedPoints H α) :
    (g • a : MulAction.fixedPoints H α) = g • (a : α) :=
  rfl

end FixedPoints
