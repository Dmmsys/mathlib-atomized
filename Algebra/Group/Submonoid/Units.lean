/-
Copyright (c) 2023 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Submonoid.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!

# Submonoid of units

Given a submonoid `S` of a monoid `M`, we define the subgroup `S.units` as the units of `S` as a
subgroup of `Mˣ`. That is to say, `S.units` contains all members of `S` which have a
two-sided inverse within `S`, as terms of type `Mˣ`.

We also define, for subgroups `S` of `Mˣ`, `S.ofUnits`, which is `S` considered as a submonoid
of `M`. `Submonoid.units` and `Subgroup.ofUnits` form a Galois coinsertion.

We also make the equivalent additive definitions.

## Implementation details
There are a number of other constructions which are multiplicatively equivalent to `S.units` but
which have a different type.

| Definition           | Type          |
|----------------------|---------------|
| `S.units`            | `Subgroup Mˣ` |
| `Sˣ`                 | `Type u`      |
| `IsUnit.submonoid S` | `Submonoid S` |
| `S.units.ofUnits`    | `Submonoid M` |

All of these are distinct from `S.leftInv`, which is the submonoid of `M` which contains
every member of `M` with a right inverse in `S`.
-/

@[expose] public section

variable {M : Type*} [Monoid M]

open Units

open scoped Pointwise in
/-- The units of `S`, packaged as a subgroup of `Mˣ`. -/
@[to_additive /-- The additive units of `S`, packaged as an additive subgroup of `AddUnits M`. -/]
/-
**Submonoid.units** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.units (S : Submonoid M) : Subgroup Mˣ where toSubmonoid
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The units of `S`, packaged as a subgroup of `Mˣ`.
-/
def Submonoid.units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

/-- A subgroup of units represented as a submonoid of `M`. -/
@[to_additive
/-- An additive subgroup of additive units represented as an additive submonoid of `M`. -/]
/-
**Subgroup.ofUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.ofUnits (S : Subgroup Mˣ) : Submonoid M
参数：S : Subgroup Mˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Subgroup.ofUnits (S : Subgroup Mˣ) : Submonoid M := S.toSubmonoid.map (coeHom M)

@[to_additive]
/-
**Submonoid.units_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.units_mono : Monotone (Submonoid.units (M
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Submonoid.units_mono : Monotone (Submonoid.units (M := M)) :=
  fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive (attr := simp)]
/-
**Submonoid.ofUnits_units_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.ofUnits_units_le (S : Submonoid M) : S.units.ofUnits <= S
参数：S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Submonoid.ofUnits_units_le (S : Submonoid M) : S.units.ofUnits ≤ S :=
  fun _ ⟨_, hm, he⟩ => he ▸ hm.1

@[to_additive]
/-
**Subgroup.ofUnits_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnits (M
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnits (M := M)) :=
  fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[to_additive (attr := simp)]
/-
**Subgroup.units_ofUnits_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.units_ofUnits_eq (S : Subgroup Mˣ) : S.ofUnits.units = S
参数：S : Subgroup Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
-/
lemma Subgroup.units_ofUnits_eq (S : Subgroup Mˣ) : S.ofUnits.units = S :=
  Subgroup.ext (fun _ =>
  ⟨fun ⟨⟨_, hm, he⟩, _⟩ => (Units.ext he) ▸ hm, fun hm => ⟨⟨_, hm, rfl⟩, _, S.inv_mem hm, rfl⟩⟩)

/-- A Galois coinsertion exists between the coercion from a subgroup of units to a submonoid and
the reduction from a submonoid to its unit group. -/
@[to_additive /-- A Galois coinsertion exists between the coercion from an additive subgroup of
additive units to an additive submonoid and the reduction from an additive submonoid to its unit
group. -/]
/-
**ofUnits_units_gci** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofUnits_units_gci : GaloisCoinsertion (Subgroup.ofUnits (M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Submonoid.units_mono`：Submonoid.units_mono : Monotone (Submonoid.units (
M
· 使用引理 `Subgroup.ofUnits_mono`：Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnit
s (M
· 使用引理 `Submonoid.ofUnits_units_le`：Submonoid.ofUnits_units_le (S : Submonoid M)
 : S.units.ofUnits <= S
· 使用引理 `Subgroup.units_ofUnits_eq`：Subgroup.units_ofUnits_eq (S : Subgroup Mˣ) :
 S.ofUnits.units = S
-/
def ofUnits_units_gci : GaloisCoinsertion (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
  GaloisCoinsertion.monotoneIntro Submonoid.units_mono Subgroup.ofUnits_mono
  Submonoid.ofUnits_units_le Subgroup.units_ofUnits_eq

@[to_additive]
/-
**ofUnits_units_gc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
lemma ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
ofUnits_units_gci.gc

@[to_additive]
/-
**ofUnits_le_iff_le_units** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofUnits_le_iff_le_units (S : Submonoid M) (H : Subgroup Mˣ) : H.ofUnits <=
 S ↔ H <= S.units
参数：S : Submonoid M；H : Subgroup Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma ofUnits_le_iff_le_units (S : Submonoid M) (H : Subgroup Mˣ) :
    H.ofUnits ≤ S ↔ H ≤ S.units := ofUnits_units_gc _ _

@[to_additive]
/-
**IsUnit.coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.coe {S : Type*} [SetLike S M] [SubmonoidClass S M] {N : S} {a : N} 
(ha : IsUnit a) : IsUnit (a : M)
参数：ha : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
theorem IsUnit.coe {S : Type*} [SetLike S M] [SubmonoidClass S M] {N : S} {a : N}
    (ha : IsUnit a) : IsUnit (a : M) := ha.map (SubmonoidClass.subtype N)

namespace Submonoid

section Units

@[to_additive]
/-
**Submonoid.mem_units_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mem_units_iff (S : Submonoid M) (x : Mˣ) : x in S.units ↔ ((x : M) in S ∧ 
((x⁻¹ : Mˣ) : M) in S)
参数：S : Submonoid M；x : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔
    ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := Iff.rfl

@[to_additive]
/-
**Submonoid.mem_units_of_val_mem_inv_val_mem** 是 Mathlib 中的一个引理，位于命名空间 `Submonoi
d`。
形式化陈述：mem_units_of_val_mem_inv_val_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) 
in S) (h₂ : ((x⁻¹ : Mˣ) : M) in S) : x in S.units
参数：S : Submonoid M；h₁ : (x : M) in S；h₂ : ((x⁻¹ : Mˣ) : M) in S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_units_of_val_mem_inv_val_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) ∈ S)
    (h₂ : ((x⁻¹ : Mˣ) : M) ∈ S) : x ∈ S.units := ⟨h₁, h₂⟩

@[to_additive]
/-
**Submonoid.val_mem_of_mem_units** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x in S.units) : (x : 
M) in S
参数：S : Submonoid M；h : x in S.units。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : (x : M) ∈ S := h.1

@[to_additive]
/-
**Submonoid.inv_val_mem_of_mem_units** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：inv_val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x in S.units) : (
(x⁻¹ : Mˣ) : M) in S
参数：S : Submonoid M；h : x in S.units。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma inv_val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    ((x⁻¹ : Mˣ) : M) ∈ S := h.2

@[to_additive]
/-
**Submonoid.coe_inv_val_mul_coe_val** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} : ((x⁻¹ : Sˣ) : M) * ((
x : Sˣ) : M) = 1
参数：S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
lemma coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.inv_mul

@[to_additive]
/-
**Submonoid.coe_val_mul_coe_inv_val** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} : ((x : Sˣ) : M) * ((x⁻
¹ : Sˣ) : M) = 1
参数：S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
lemma coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.mul_inv

@[to_additive]
/-
**Submonoid.mk_inv_mul_mk_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mk_inv_mul_mk_eq_one (S : Submonoid M) {x : Mˣ} (h : x in S.units) : (⟨_, 
h.2⟩ : S) * ⟨_, h.1⟩ = 1
参数：S : Submonoid M；h : x in S.units。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
lemma mk_inv_mul_mk_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.2⟩ : S) * ⟨_, h.1⟩ = 1 := Subtype.ext x.inv_mul

@[to_additive]
/-
**Submonoid.mk_mul_mk_inv_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mk_mul_mk_inv_eq_one (S : Submonoid M) {x : Mˣ} (h : x in S.units) : (⟨_, 
h.1⟩ : S) * ⟨_, h.2⟩ = 1
参数：S : Submonoid M；h : x in S.units。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
lemma mk_mul_mk_inv_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.1⟩ : S) * ⟨_, h.2⟩ = 1 := Subtype.ext x.mul_inv

@[to_additive]
/-
**Submonoid.mul_mem_units** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mul_mem_units (S : Submonoid M) {x y : Mˣ} (h₁ : x in S.units) (h₂ : y in 
S.units) : x * y in S.units
参数：S : Submonoid M；h₁ : x in S.units；h₂ : y in S.units。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma mul_mem_units (S : Submonoid M) {x y : Mˣ} (h₁ : x ∈ S.units) (h₂ : y ∈ S.units) :
    x * y ∈ S.units := mul_mem h₁ h₂

@[to_additive]
/-
**Submonoid.inv_mem_units** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：inv_mem_units (S : Submonoid M) {x : Mˣ} (h : x in S.units) : x⁻¹ in S.uni
ts
参数：S : Submonoid M；h : x in S.units。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma inv_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : x⁻¹ ∈ S.units := inv_mem h

@[to_additive]
/-
**Submonoid.inv_mem_units_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：inv_mem_units_iff (S : Submonoid M) {x : Mˣ} : x⁻¹ in S.units ↔ x in S.uni
ts
参数：S : Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma inv_mem_units_iff (S : Submonoid M) {x : Mˣ} : x⁻¹ ∈ S.units ↔ x ∈ S.units := inv_mem_iff

/-- The equivalence between the subgroup of units of `S` and the type of units of `S`. -/
@[to_additive (attr := simps)
/-- The equivalence between the additive subgroup of additive units of
`S` and the type of additive units of `S`. -/]
/-
**Submonoid.unitsEquivUnitsType** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：unitsEquivUnitsType (S : Submonoid M) : S.units ≃* Sˣ where toFun
参数：S : Submonoid M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Submonoid.mk_mul_mk_inv_eq_one`：mk_mul_mk_inv_eq_one (S : Submonoid M) {
x : Mˣ} (h : x in S.units) : (⟨_, h.1⟩ : S) * ⟨_, h.2⟩ = 1
· 使用引理 `Submonoid.mk_inv_mul_mk_eq_one`：mk_inv_mul_mk_eq_one (S : Submonoid M) {
x : Mˣ} (h : x in S.units) : (⟨_, h.2⟩ : S) * ⟨_, h.1⟩ = 1
· 使用引理 `Submonoid.coe_val_mul_coe_inv_val`：coe_val_mul_coe_inv_val (S : Submonoi
d M) {x : Sˣ} : ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1
· 使用引理 `Submonoid.coe_inv_val_mul_coe_val`：coe_inv_val_mul_coe_val (S : Submonoi
d M) {x : Sˣ} : ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1
-/
def unitsEquivUnitsType (S : Submonoid M) : S.units ≃* Sˣ where
  toFun := fun ⟨_, h⟩ => ⟨⟨_, h.1⟩, ⟨_, h.2⟩, S.mk_mul_mk_inv_eq_one h, S.mk_inv_mul_mk_eq_one h⟩
  invFun := fun x => ⟨⟨_, _, S.coe_val_mul_coe_inv_val, S.coe_inv_val_mul_coe_val⟩, ⟨x.1.2, x.2.2⟩⟩
  map_mul' := fun _ _ => rfl

@[to_additive (attr := simp)]
/-
**Submonoid.units_top** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_top : (⊤ : Submonoid M).units = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma units_top : (⊤ : Submonoid M).units = ⊤ := ofUnits_units_gc.u_top

@[to_additive]
/-
**Submonoid.units_inf** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_inf (S T : Submonoid M) : (S ⊓ T).units = S.units ⊓ T.units
参数：S T : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma units_inf (S T : Submonoid M) : (S ⊓ T).units = S.units ⊓ T.units :=
  ofUnits_units_gc.u_inf

@[to_additive]
/-
**Submonoid.units_sInf** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_sInf {s : Set (Submonoid M)} : (sInf s).units = ⨅ S in s, S.units
参数：Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma units_sInf {s : Set (Submonoid M)} : (sInf s).units = ⨅ S ∈ s, S.units :=
  ofUnits_units_gc.u_sInf

@[to_additive]
/-
**Submonoid.units_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_iInf {ι : Sort*} (f : ι -> Submonoid M) : (iInf f).units = ⨅ (i : ι)
, (f i).units
参数：f : ι -> Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma units_iInf {ι : Sort*} (f : ι → Submonoid M) : (iInf f).units = ⨅ (i : ι), (f i).units :=
  ofUnits_units_gc.u_iInf

@[to_additive]
/-
**Submonoid.units_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_iInf {ι : Sort*} (f : ι -> Submonoid M) : (iInf f).units = ⨅ (i : ι)
, (f i).units
参数：f : ι -> Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma units_iInf₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Submonoid M) :
    (⨅ (i : ι), ⨅ (j : κ i), f i j).units = ⨅ (i : ι), ⨅ (j : κ i), (f i j).units :=
  ofUnits_units_gc.u_iInf₂

@[to_additive (attr := simp)]
/-
**Submonoid.units_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_bot : (⊥ : Submonoid M).units = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_bot`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β 
→ α} [inst : Preorder α] [inst_1 : PartialOrder β] [inst_2 : OrderBot α]   [inst
_3 : OrderBot…
-/
lemma units_bot : (⊥ : Submonoid M).units = ⊥ := ofUnits_units_gci.u_bot

@[to_additive]
/-
**Submonoid.units_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_surjective : Function.Surjective (units (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_surjective`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsert
ion l u), Function.S…
-/
lemma units_surjective : Function.Surjective (units (M := M)) :=
  ofUnits_units_gci.u_surjective

@[to_additive]
/-
**Submonoid.units_left_inverse** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：units_left_inverse : Function.LeftInverse (units (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.leftInverse_u_l`：∀ {α : Type u} {β : Type v} {u : α → 
β} {l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoins
ertion l u), Function.L…
-/
lemma units_left_inverse :
    Function.LeftInverse (units (M := M)) (Subgroup.ofUnits (M := M)) :=
  ofUnits_units_gci.leftInverse_u_l

/-- The equivalence between the subgroup of units of `S` and the submonoid of unit
elements of `S`. -/
@[to_additive /-- The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`. -/]
/-
**Submonoid.unitsEquivIsUnitSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：unitsEquivIsUnitSubmonoid (S : Submonoid M) : S.units ≃* IsUnit.submonoid 
S
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def unitsEquivIsUnitSubmonoid (S : Submonoid M) : S.units ≃* IsUnit.submonoid S :=
S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid

end Units

/-
**Submonoid.instSubsingletonUnits** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：instSubsingletonUnits [Subsingleton Mˣ] {S : Submonoid M} : Subsingleton S
ˣ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.units_of_isUnit`：∀ {M : Type u_1} [inst : Monoid M], (∀ (a 
: M), IsUnit a → a = 1) → Subsingleton Mˣ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsUnit.eq_one`：∀ {M : Type u_1} [inst : Monoid M] {a : M} [Subsingleton 
Mˣ], IsUnit a → a = 1
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
instance instSubsingletonUnits [Subsingleton Mˣ] {S : Submonoid M} : Subsingleton Sˣ :=
  .units_of_isUnit fun _a ha ↦ Subtype.ext (ha.map S.subtype).eq_one

end Submonoid

namespace Subgroup

@[to_additive]
/-
**Subgroup.mem_ofUnits_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x in S.ofUnits ↔ exists y in S
, y = x
参数：S : Subgroup Mˣ；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x ∈ S.ofUnits ↔ ∃ y ∈ S, y = x := Iff.rfl

@[to_additive]
/-
**Subgroup.mem_ofUnits** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y in S) (h₂ : y = x) 
: x in S.ofUnits
参数：S : Subgroup Mˣ；h₁ : y in S；h₂ : y = x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y ∈ S) (h₂ : y = x) : x ∈ S.ofUnits :=
  ⟨_, h₁, h₂⟩

@[to_additive]
/-
**Subgroup.exists_mem_ofUnits_val_eq** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：exists_mem_ofUnits_val_eq (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits) :
 exists y in S, y = x
参数：S : Subgroup Mˣ；h : x in S.ofUnits。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_mem_ofUnits_val_eq (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    ∃ y ∈ S, y = x := h

@[to_additive]
/-
**Subgroup.mem_of_mem_val_ofUnits** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) in S.ofUni
ts) : y in S
参数：S : Subgroup Mˣ；hy : (y : M) in S.ofUnits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
lemma mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) ∈ S.ofUnits) : y ∈ S :=
  match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

@[to_additive]
/-
**Subgroup.isUnit_of_mem_ofUnits** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (hx : x in S.ofUnits) : Is
Unit x
参数：S : Subgroup Mˣ；hx : x in S.ofUnits。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (hx : x ∈ S.ofUnits) : IsUnit x :=
  match hx with
  | ⟨_, _, h⟩ => ⟨_, h⟩

/-- Given some `x : M` which is a member of the submonoid of unit elements corresponding to a
subgroup of units, produce a unit of `M` whose coercion is equal to `x`. -/
@[to_additive /-- Given some `x : M` which is a member of the additive submonoid of additive unit
elements corresponding to a subgroup of units, produce a unit of `M` whose coercion is equal to
`x`. -/]
/-
**Subgroup.unit_of_mem_ofUnits** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits) : Mˣ
参数：S : Subgroup Mˣ；h : x in S.ofUnits。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) : Mˣ :=
  (Classical.choose h).copy x (Classical.choose_spec h).2.symm _ rfl

@[to_additive]
/-
**Subgroup.unit_of_mem_ofUnits_spec_eq_of_val_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sub
group`。
形式化陈述：unit_of_mem_ofUnits_spec_eq_of_val_mem (S : Subgroup Mˣ) {x : Mˣ} (h : (x 
: M) in S.ofUnits) : S.unit_of_mem_ofUnits h = x
参数：S : Subgroup Mˣ；h : (x : M) in S.ofUnits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
lemma unit_of_mem_ofUnits_spec_eq_of_val_mem (S : Subgroup Mˣ) {x : Mˣ} (h : (x : M) ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := Units.ext rfl

@[to_additive]
/-
**Subgroup.unit_of_mem_ofUnits_spec_val_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sub
group`。
形式化陈述：unit_of_mem_ofUnits_spec_val_eq_of_mem (S : Subgroup Mˣ) {x : M} (h : x in
 S.ofUnits) : S.unit_of_mem_ofUnits h = x
参数：S : Subgroup Mˣ；h : x in S.ofUnits。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unit_of_mem_ofUnits_spec_val_eq_of_mem (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := rfl

@[to_additive]
/-
**Subgroup.unit_of_mem_ofUnits_spec_mem** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：unit_of_mem_ofUnits_spec_mem (S : Subgroup Mˣ) {x : M} {h : x in S.ofUnits
} : S.unit_of_mem_ofUnits h in S
参数：S : Subgroup Mˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.mem_of_mem_val_ofUnits`：mem_of_mem_val_ofUnits (S : Subgroup Mˣ
) {y : Mˣ} (hy : (y : M) in S.ofUnits) : y in S
-/
lemma unit_of_mem_ofUnits_spec_mem (S : Subgroup Mˣ) {x : M} {h : x ∈ S.ofUnits} :
    S.unit_of_mem_ofUnits h ∈ S := S.mem_of_mem_val_ofUnits h

@[to_additive]
/-
**Subgroup.unit_eq_unit_of_mem_ofUnits** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：unit_eq_unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x) (h₂ 
: x in S.ofUnits) : h₁.unit = S.unit_of_mem_ofUnits h₂
参数：S : Subgroup Mˣ；h₁ : IsUnit x；h₂ : x in S.ofUnits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
lemma unit_eq_unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : x ∈ S.ofUnits) : h₁.unit = S.unit_of_mem_ofUnits h₂ := Units.ext rfl

@[to_additive]
/-
**Subgroup.unit_mem_of_mem_ofUnits** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x} (h₂ : x 
in S.ofUnits) : h₁.unit in S
参数：S : Subgroup Mˣ；h₂ : x in S.ofUnits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.unit_of_mem_ofUnits_spec_mem`：unit_of_mem_ofUnits_spec_mem (S :
 Subgroup Mˣ) {x : M} {h : x in S.ofUnits} : S.unit_of_mem_ofUnits h in S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.unit_eq_unit_of_mem_ofUnits`：unit_eq_unit_of_mem_ofUnits (S : S
ubgroup Mˣ) {x : M} (h₁ : IsUnit x) (h₂ : x in S.ofUnits) : h₁.unit = S.unit_of_
mem_ofUnits h₂
-/
lemma unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
    (h₂ : x ∈ S.ofUnits) : h₁.unit ∈ S :=
  S.unit_eq_unit_of_mem_ofUnits h₁ h₂ ▸ (S.unit_of_mem_ofUnits_spec_mem)

@[to_additive]
/-
**Subgroup.mem_ofUnits_of_isUnit_of_unit_mem** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup
`。
形式化陈述：mem_ofUnits_of_isUnit_of_unit_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x
) (h₂ : h₁.unit in S) : x in S.ofUnits
参数：S : Subgroup Mˣ；h₁ : IsUnit x；h₂ : h₁.unit in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.mem_ofUnits`：mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁
 : y in S) (h₂ : y = x) : x in S.ofUnits
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
-/
lemma mem_ofUnits_of_isUnit_of_unit_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : h₁.unit ∈ S) : x ∈ S.ofUnits := S.mem_ofUnits h₂ h₁.unit_spec

@[to_additive]
/-
**Subgroup.mem_ofUnits_iff_exists_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) : x in S.ofUnits ↔
 exists h : IsUnit x, h.unit in S
参数：S : Subgroup Mˣ；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isUnit_of_mem_ofUnits`：isUnit_of_mem_ofUnits (S : Subgroup Mˣ) 
{x : M} (hx : x in S.ofUnits) : IsUnit x
· 使用引理 `Subgroup.unit_mem_of_mem_ofUnits`：unit_mem_of_mem_ofUnits (S : Subgroup 
Mˣ) {x : M} {h₁ : IsUnit x} (h₂ : x in S.ofUnits) : h₁.unit in S
· 使用引理 `Subgroup.mem_ofUnits_of_isUnit_of_unit_mem`：mem_ofUnits_of_isUnit_of_uni
t_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x) (h₂ : h₁.unit in S) : x in S.ofU
nits
-/
lemma mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x ∈ S.ofUnits ↔ ∃ h : IsUnit x, h.unit ∈ S :=
  ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
  fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

/-- The equivalence between the coercion of a subgroup `S` of `Mˣ` to a submonoid of `M` and
the subgroup itself as a type. -/
@[to_additive /-- The equivalence between the coercion of an additive subgroup `S` of
`Mˣ` to an additive submonoid of `M` and the additive subgroup itself as a type. -/]
/-
**Subgroup.ofUnitsEquivType** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：ofUnitsEquivType (S : Subgroup Mˣ) : S.ofUnits ≃* S where toFun
参数：S : Subgroup Mˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def ofUnitsEquivType (S : Subgroup Mˣ) : S.ofUnits ≃* S where
  toFun := fun x => ⟨S.unit_of_mem_ofUnits x.2, S.unit_of_mem_ofUnits_spec_mem⟩
  invFun := fun x => ⟨x.1, ⟨x.1, x.2, rfl⟩⟩
  map_mul' := fun _ _ => Subtype.ext (Units.ext rfl)

@[to_additive (attr := simp)]
/-
**Subgroup.ofUnits_bot** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_bot : (⊥ : Subgroup Mˣ).ofUnits = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma ofUnits_bot : (⊥ : Subgroup Mˣ).ofUnits = ⊥ := ofUnits_units_gc.l_bot

@[to_additive]
/-
**Subgroup.ofUnits_inf** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_inf (S T : Subgroup Mˣ) : (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits
参数：S T : Subgroup Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma ofUnits_inf (S T : Subgroup Mˣ) : (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits :=
ofUnits_units_gc.l_sup

@[to_additive]
/-
**Subgroup.ofUnits_sSup** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_sSup (s : Set (Subgroup Mˣ)) : (sSup s).ofUnits = ⨆ S in s, S.ofUn
its
参数：s : Set (Subgroup Mˣ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma ofUnits_sSup (s : Set (Subgroup Mˣ)) : (sSup s).ofUnits = ⨆ S ∈ s, S.ofUnits :=
ofUnits_units_gc.l_sSup

@[to_additive]
/-
**Subgroup.ofUnits_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_iSup {ι : Sort*} {f : ι -> Subgroup Mˣ} : (iSup f).ofUnits = ⨆ (i 
: ι), (f i).ofUnits
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma ofUnits_iSup {ι : Sort*} {f : ι → Subgroup Mˣ} :
    (iSup f).ofUnits = ⨆ (i : ι), (f i).ofUnits := ofUnits_units_gc.l_iSup

@[to_additive]
/-
**Subgroup.ofUnits_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_iSup {ι : Sort*} {f : ι -> Subgroup Mˣ} : (iSup f).ofUnits = ⨆ (i 
: ι), (f i).ofUnits
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用引理 `ofUnits_units_gc`：ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits 
(M
-/
lemma ofUnits_iSup₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Subgroup Mˣ) :
    (⨆ (i : ι), ⨆ (j : κ i), f i j).ofUnits = ⨆ (i : ι), ⨆ (j : κ i), (f i j).ofUnits :=
  ofUnits_units_gc.l_iSup₂

@[to_additive]
/-
**Subgroup.ofUnits_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_injective : Function.Injective (ofUnits (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_injective`：∀ {α : Type u} {β : Type v} {u : α → β} {
l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinserti
on l u), Function.I…
-/
lemma ofUnits_injective : Function.Injective (ofUnits (M := M)) :=
  ofUnits_units_gci.l_injective

@[to_additive (attr := simp)]
/-
**Subgroup.ofUnits_sup_units** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_sup_units (S T : Subgroup Mˣ) : (S.ofUnits ⊔ T.ofUnits).units = S 
⊔ T
参数：S T : Subgroup Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_sup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   (gi : GaloisCoins
ertion l u) (a …
-/
lemma ofUnits_sup_units (S T : Subgroup Mˣ) : (S.ofUnits ⊔ T.ofUnits).units = S ⊔ T :=
  ofUnits_units_gci.u_sup_l _ _

@[to_additive (attr := simp)]
/-
**Subgroup.ofUnits_inf_units** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_inf_units (S T : Subgroup Mˣ) : (S.ofUnits ⊓ T.ofUnits).units = S 
⊓ T
参数：S T : Subgroup Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_inf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   (gi : GaloisCoins
ertion l u) (a …
-/
lemma ofUnits_inf_units (S T : Subgroup Mˣ) : (S.ofUnits ⊓ T.ofUnits).units = S ⊓ T :=
  ofUnits_units_gci.u_inf_l _ _

@[to_additive]
/-
**Subgroup.ofUnits_right_inverse** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_right_inverse : Function.RightInverse (ofUnits (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.leftInverse_u_l`：∀ {α : Type u} {β : Type v} {u : α → 
β} {l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoins
ertion l u), Function.L…
-/
lemma ofUnits_right_inverse :
    Function.RightInverse (ofUnits (M := M)) (Submonoid.units (M := M)) :=
  ofUnits_units_gci.leftInverse_u_l

@[to_additive]
/-
**Subgroup.ofUnits_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_strictMono : StrictMono (ofUnits (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.strictMono_l`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion 
l u), StrictMono l
-/
lemma ofUnits_strictMono : StrictMono (ofUnits (M := M)) := ofUnits_units_gci.strictMono_l
/-
**Subgroup.ofUnits_le_ofUnits_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：ofUnits_le_ofUnits_iff {S T : Subgroup Mˣ} : S.ofUnits <= T.ofUnits ↔ S <=
 T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
-/
lemma ofUnits_le_ofUnits_iff {S T : Subgroup Mˣ} : S.ofUnits ≤ T.ofUnits ↔ S ≤ T :=
  ofUnits_units_gci.l_le_l_iff

/-- The equivalence between the top subgroup of `Mˣ` coerced to a submonoid `M` and the
units of `M`. -/
@[to_additive /-- The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`. -/]
/-
**Subgroup.ofUnitsTopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：ofUnitsTopEquiv : (⊤ : Subgroup Mˣ).ofUnits ≃* Mˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def ofUnitsTopEquiv : (⊤ : Subgroup Mˣ).ofUnits ≃* Mˣ :=
  (⊤ : Subgroup Mˣ).ofUnitsEquivType.trans topEquiv

variable {G : Type*} [Group G]

@[to_additive]
/-
**Subgroup.mem_units_iff_val_mem** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_units_iff_val_mem (H : Subgroup G) (x : Gˣ) : x in H.units ↔ (x : G) i
n H
参数：H : Subgroup G；x : Gˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_units_iff_val_mem (H : Subgroup G) (x : Gˣ) : x ∈ H.units ↔ (x : G) ∈ H := by
  simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, val_inv_eq_inv_val, inv_mem_iff, and_self]

@[to_additive]
/-
**Subgroup.mem_ofUnits_iff_toUnits_mem** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G) : x in H.ofUnits ↔ (
toUnits x) in H
参数：H : Subgroup Gˣ；x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `val_toUnits_apply`：∀ {G : Type u_5} [inst : Group G] (x : G), ↑(toUnits 
x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G) : x ∈ H.ofUnits ↔ (toUnits x) ∈ H := by
  simp_rw [mem_ofUnits_iff, toUnits.surjective.exists, val_toUnits_apply, exists_eq_right]

@[to_additive (attr := simp)]
/-
**Subgroup.mem_iff_toUnits_mem_units** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_iff_toUnits_mem_units (H : Subgroup G) (x : G) : toUnits x in H.units 
↔ x in H
参数：H : Subgroup G；x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `val_toUnits_apply`：∀ {G : Type u_5} [inst : Group G] (x : G), ↑(toUnits 
x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_iff_toUnits_mem_units (H : Subgroup G) (x : G) : toUnits x ∈ H.units ↔ x ∈ H := by
  simp_rw [mem_units_iff_val_mem, val_toUnits_apply]

@[to_additive (attr := simp)]
/-
**Subgroup.val_mem_ofUnits_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：val_mem_ofUnits_iff_mem (H : Subgroup Gˣ) (x : Gˣ) : (x : G) in H.ofUnits 
↔ x in H
参数：H : Subgroup Gˣ；x : Gˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `toUnits_val_apply`：toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : to
Units (x : G) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma val_mem_ofUnits_iff_mem (H : Subgroup Gˣ) (x : Gˣ) : (x : G) ∈ H.ofUnits ↔ x ∈ H := by
  simp_rw [mem_ofUnits_iff_toUnits_mem, toUnits_val_apply]

/-- The equivalence between the greatest subgroup of units contained within `T` and `T` itself. -/
@[to_additive /-- The equivalence between the greatest subgroup of additive units
contained within `T` and `T` itself. -/]
/-
**Subgroup.unitsEquivSelf** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：unitsEquivSelf (H : Subgroup G) : H.units ≃* H
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unitsEquivSelf (H : Subgroup G) : H.units ≃* H :=
  H.unitsEquivUnitsType.trans (toUnits (G := H)).symm

end Subgroup

@[to_additive]
/-
**MonoidHom.isUnit_eqLocusM_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isUnit_eqLocusM_mk_iff {N : Type*} [Monoid N] (f g : M ->* N) {r
 : M} (hr : f r = g r) : IsUnit (⟨r, hr⟩ : f.eqLocusM g) ↔ IsUnit r
参数：f g : M ->* N；hr : f r = g r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem MonoidHom.isUnit_eqLocusM_mk_iff {N : Type*} [Monoid N] (f g : M →* N) {r : M}
    (hr : f r = g r) : IsUnit (⟨r, hr⟩ : f.eqLocusM g) ↔ IsUnit r := by
  refine ⟨fun h ↦ h.map (SubmonoidClass.subtype _), fun h ↦ ?_⟩
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  suffices ∃ a, r * a = 1 ∧ f a = g a ∧ a * r = 1 by
    simpa [isUnit_iff_exists, ← Subtype.val_inj]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s), ← map_one g, ← hs.left, map_mul, ← mul_assoc, ← hr, ← map_mul,
    hs.right, map_one, one_mul]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {N : Type*} [Monoid N] (f g : M →* N) : IsLocalHom (f.eqLocusM g).subtype where
  map_nonunit r := f.isUnit_eqLocusM_mk_iff g r.prop |>.2
