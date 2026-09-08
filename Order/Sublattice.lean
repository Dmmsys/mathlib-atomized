/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.SupClosed

/-!
# Sublattices

This file defines sublattices.

## TODO

Subsemilattices, if people care about them.

## Tags

sublattice
-/

@[expose] public section

open Function Set

variable {ι : Sort*} (α β γ : Type*) [Lattice α] [Lattice β] [Lattice γ]

/-- A sublattice of a lattice is a set containing the suprema and infima of any of its elements. -/
/-
**Sublattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Lattice α] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sublattice of a lattice is a set containing the suprema and infima of any of i
ts elements.
-/
structure Sublattice where
  /-- The underlying set of a sublattice. **Do not use directly**. Instead, use the coercion
  `Sublattice α → Set α`, which Lean should automatically insert for you in most cases. -/
  carrier : Set α
  supClosed' : SupClosed carrier
  infClosed' : InfClosed carrier

variable {α β γ}

namespace Sublattice
variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a b : α}

/-
**Sublattice.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instSetLike : SetLike (Sublattice α) α where coe L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (Sublattice α) α where
  coe L := L.carrier
  coe_injective L M h := by cases L; congr
/-
**Sublattice.** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Sublattice α) := .ofSetLike (Sublattice α) α

/-- See Note [custom simps projection]. -/
/-
**Sublattice.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice.Simps`。
形式化陈述：{α : Type u_2} → [inst : Lattice α] → Sublattice α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (L : Sublattice α) : Set α := L

initialize_simps_projections Sublattice (carrier → coe, as_prefix coe)

/-- Turn a set closed under supremum and infimum into a sublattice. -/
/-
**Sublattice.ofIsSublattice** 是 Mathlib 中的一个缩写定义，位于命名空间 `Sublattice`。
形式化陈述：ofIsSublattice (s : Set α) (hs : IsSublattice s) : Sublattice α
参数：s : Set α；hs : IsSublattice s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s

--- 原说明 ---
Turn a set closed under supremum and infimum into a sublattice.
-/
abbrev ofIsSublattice (s : Set α) (hs : IsSublattice s) : Sublattice α := ⟨s, hs.1, hs.2⟩
/-
**Sublattice.coe_inj** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：coe_inj : (L : Set α) = M ↔ L = M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq
/-
**Sublattice.supClosed** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattice α), SupClosed ↑L
参数：L : Sublattice α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.supClosed'`：∀ {α : Type u_2} [inst : Lattice α] (self : Subla
ttice α), SupClosed self.carrier
-/
@[simp] lemma supClosed (L : Sublattice α) : SupClosed (L : Set α) := L.supClosed'
/-
**Sublattice.infClosed** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattice α), InfClosed ↑L
参数：L : Sublattice α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.infClosed'`：∀ {α : Type u_2} [inst : Lattice α] (self : Subla
ttice α), InfClosed self.carrier
-/
@[simp] lemma infClosed (L : Sublattice α) : InfClosed (L : Set α) := L.infClosed'
/-
**Sublattice.sup_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：sup_mem (ha : a in L) (hb : b in L) : a ⊔ b in L
参数：ha : a in L；hb : b in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.supClosed`：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattic
e α), SupClosed ↑L
-/
lemma sup_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊔ b ∈ L := L.supClosed ha hb
/-
**Sublattice.inf_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：inf_mem (ha : a in L) (hb : b in L) : a ⊓ b in L
参数：ha : a in L；hb : b in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.infClosed`：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattic
e α), InfClosed ↑L
-/
lemma inf_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊓ b ∈ L := L.infClosed ha hb
/-
**Sublattice.isSublattice** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattice α), IsSublattice ↑L
参数：L : Sublattice α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.supClosed`：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattic
e α), SupClosed ↑L
· 使用定理 `Sublattice.infClosed`：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattic
e α), InfClosed ↑L
-/
@[simp] lemma isSublattice (L : Sublattice α) : IsSublattice (L : Set α) :=
  ⟨L.supClosed, L.infClosed⟩
/-
**Sublattice.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α} {a : α}, a ∈ L.carr
ier ↔ a ∈ L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := Iff.rfl
/-
**Sublattice.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {s : Set α} {a : α} (h_sup : SupClosed
 s) (h_inf : InfClosed s),   a ∈ { carrier := s, supClosed' := h_sup, infClosed'
 := h_inf } ↔ a ∈ s
参数：h_sup : SupClosed s；h_inf : InfClosed s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk (h_sup h_inf) : a ∈ mk s h_sup h_inf ↔ a ∈ s := Iff.rfl
/-
**Sublattice.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {s : Set α} (h_sup : SupClosed s) (h_i
nf : InfClosed s),   ↑{ carrier := s, supClosed' := h_sup, infClosed' := h_inf }
 = s
参数：h_sup : SupClosed s；h_inf : InfClosed s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk (h_sup h_inf) : mk s h_sup h_inf = s := rfl
/-
**Sublattice.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {s t : Set α} (hs_sup : SupClosed s) (
hs_inf : InfClosed s) (ht_sup : SupClosed t)   (ht_inf : InfClosed t),   { carri
er := s, supClosed' := hs_sup, infClosed' := hs_inf } ≤       { carrier := t, su
pClosed' := ht_sup, infClosed' := ht_inf } ↔     s ⊆ t
参数：hs_sup : SupClosed s；hs_inf : InfClosed s；ht_sup : SupClosed t；ht_inf : InfCl
osed t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mk_le_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf ≤ mk t ht_sup ht_inf ↔ s ⊆ t := Iff.rfl
/-
**Sublattice.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {s t : Set α} (hs_sup : SupClosed s) (
hs_inf : InfClosed s) (ht_sup : SupClosed t)   (ht_inf : InfClosed t),   { carri
er := s, supClosed' := hs_sup, infClosed' := hs_inf } <       { carrier := t, su
pClosed' := ht_sup, infClosed' := ht_inf } ↔     s ⊂ t
参数：hs_sup : SupClosed s；hs_inf : InfClosed s；ht_sup : SupClosed t；ht_inf : InfCl
osed t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mk_lt_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf < mk t ht_sup ht_inf ↔ s ⊂ t := Iff.rfl

/-- Copy of a sublattice with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
/-
**Sublattice.copy** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：{α : Type u_2} → [inst : Lattice α] → (L : Sublattice α) → (s : Set α) → s
 = ↑L → Sublattice α
参数：L : Sublattice α；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a sublattice with a new `carrier` equal to the old one. Useful to fix de
finitional
equalities.
-/
protected def copy (L : Sublattice α) (s : Set α) (hs : s = L) : Sublattice α where
  carrier := s
  supClosed' := hs.symm ▸ L.supClosed'
  infClosed' := hs.symm ▸ L.infClosed'
/-
**Sublattice.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattice α) (s : Set α) (hs : s
 = ↑L), ↑(L.copy s hs) = s
参数：L : Sublattice α；s : Set α；hs : s = ↑L；L.copy s hs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_copy (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = s := rfl
/-
**Sublattice.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：copy_eq (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = L
参数：L : Sublattice α；s : Set α；hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
lemma copy_eq (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = L := SetLike.coe_injective hs

/-- Two sublattices are equal if they have the same elements. -/
/-
**Sublattice.ext** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：ext : (forall a, a in L ↔ a in M) -> L = M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two sublattices are equal if they have the same elements.
-/
lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext

/-- A sublattice of a lattice inherits a supremum. -/
/-
**Sublattice.instSupCoe** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instSupCoe : Max L where max a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sublattice of a lattice inherits a supremum.
-/
instance instSupCoe : Max L where
  max a b := ⟨a ⊔ b, L.supClosed a.2 b.2⟩

/-- A sublattice of a lattice inherits an infimum. -/
/-
**Sublattice.instInfCoe** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instInfCoe : Min L where min a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sublattice of a lattice inherits an infimum.
-/
instance instInfCoe : Min L where
  min a b := ⟨a ⊓ b, L.infClosed a.2 b.2⟩
/-
**Sublattice.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α} (a b : ↥L), ↑(a ⊔ b
) = ↑a ⊔ ↑b
参数：a b : ↥L；a ⊔ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
/-
**Sublattice.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α} (a b : ↥L), ↑(a ⊓ b
) = ↑a ⊓ ↑b
参数：a b : ↥L；a ⊓ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
/-
**Sublattice.mk_sup_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α} (a b : α) (ha : a ∈
 L) (hb : b ∈ L),   ⟨a, ha⟩ ⊔ ⟨b, hb⟩ = ⟨a ⊔ b, ⋯⟩
参数：a b : α；ha : a ∈ L；hb : b ∈ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_sup_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩ :=
  rfl
/-
**Sublattice.mk_inf_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α} (a b : α) (ha : a ∈
 L) (hb : b ∈ L),   ⟨a, ha⟩ ⊓ ⟨b, hb⟩ = ⟨a ⊓ b, ⋯⟩
参数：a b : α；ha : a ∈ L；hb : b ∈ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_inf_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩ :=
  rfl

/-- A sublattice of a lattice inherits a lattice structure. -/
/-
**Sublattice.instLatticeCoe** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instLatticeCoe (L : Sublattice α) : Lattice L
参数：L : Sublattice α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sublattice of a lattice inherits a lattice structure.
-/
instance instLatticeCoe (L : Sublattice α) : Lattice L :=
  Subtype.coe_injective.lattice _ .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- A sublattice of a distributive lattice inherits a distributive lattice structure. -/
/-
**Sublattice.instDistribLatticeCoe** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instDistribLatticeCoe {α : Type*} [DistribLattice α] (L : Sublattice α) : 
DistribLattice L
参数：L : Sublattice α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sublattice of a distributive lattice inherits a distributive lattice structure
.
-/
instance instDistribLatticeCoe {α : Type*} [DistribLattice α] (L : Sublattice α) :
    DistribLattice L :=
  Subtype.coe_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The natural lattice hom from a sublattice to the original lattice. -/
/-
**Sublattice.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：subtype (L : Sublattice α) : LatticeHom L α where toFun
参数：L : Sublattice α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural lattice hom from a sublattice to the original lattice.
-/
def subtype (L : Sublattice α) : LatticeHom L α where
  toFun := ((↑) : L → α)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
/-
**Sublattice.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattice α), ⇑L.subtype = Subty
pe.val
参数：L : Sublattice α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_subtype (L : Sublattice α) : L.subtype = ((↑) : L → α) := rfl
/-
**Sublattice.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a
参数：L : Sublattice α；a : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a := rfl
/-
**Sublattice.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：subtype_injective (L : Sublattice α) : Injective subtype L
参数：L : Sublattice α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective (L : Sublattice α) : Injective <| subtype L := Subtype.coe_injective

/-- The inclusion homomorphism from a sublattice `L` to a bigger sublattice `M`. -/
/-
**Sublattice.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：inclusion (h : L <= M) : LatticeHom L M where toFun
参数：h : L <= M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion homomorphism from a sublattice `L` to a bigger sublattice `M`.
-/
def inclusion (h : L ≤ M) : LatticeHom L M where
  toFun := Set.inclusion h
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
/-
**Sublattice.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L M : Sublattice α} (h : L ≤ M), ⇑(Su
blattice.inclusion h) = Set.inclusion h
参数：h : L ≤ M；Sublattice.inclusion h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_inclusion (h : L ≤ M) : inclusion h = Set.inclusion h := rfl
/-
**Sublattice.inclusion_apply** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：inclusion_apply (h : L <= M) (a : L) : inclusion h a = Set.inclusion h a
参数：h : L <= M；a : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclusion_apply (h : L ≤ M) (a : L) : inclusion h a = Set.inclusion h a := rfl
/-
**Sublattice.inclusion_injective** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：inclusion_injective (h : L <= M) : Injective inclusion h
参数：h : L <= M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
lemma inclusion_injective (h : L ≤ M) : Injective <| inclusion h := Set.inclusion_injective h
/-
**Sublattice.inclusion_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattice α), Sublattice.inclusi
on ⋯ = LatticeHom.id ↥L
参数：L : Sublattice α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[simp] lemma inclusion_rfl (L : Sublattice α) : inclusion le_rfl = LatticeHom.id L := rfl
/-
**Sublattice.subtype_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L M : Sublattice α} (h : L ≤ M),   M.
subtype.comp (Sublattice.inclusion h) = L.subtype
参数：h : L ≤ M；Sublattice.inclusion h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma subtype_comp_inclusion (h : L ≤ M) : M.subtype.comp (inclusion h) = L.subtype := rfl

/-- The maximum sublattice of a lattice. -/
/-
**Sublattice.instTop** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instTop : Top (Sublattice α) where top.carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximum sublattice of a lattice.
-/
instance instTop : Top (Sublattice α) where
  top.carrier := univ
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

/-- The empty sublattice of a lattice. -/
/-
**Sublattice.instBot** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instBot : Bot (Sublattice α) where bot.carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty sublattice of a lattice.
-/
instance instBot : Bot (Sublattice α) where
  bot.carrier := ∅
  bot.supClosed' := supClosed_empty
  bot.infClosed' := infClosed_empty

/-- The inf of two sublattices is their intersection. -/
/-
**Sublattice.instInf** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instInf : Min (Sublattice α) where min L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two sublattices is their intersection.
-/
instance instInf : Min (Sublattice α) where
  min L M := { carrier := L ∩ M
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

/-- The inf of sublattices is their intersection. -/
/-
**Sublattice.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instInfSet : InfSet (Sublattice α) where sInf S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of sublattices is their intersection.
-/
instance instInfSet : InfSet (Sublattice α) where
  sInf S := { carrier := ⨅ L ∈ S, L
              supClosed' := supClosed_sInter <| forall_mem_range.2 fun L ↦ supClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.supClosed
              infClosed' := infClosed_sInter <| forall_mem_range.2 fun L ↦ infClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.infClosed }
/-
**Sublattice.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instInhabited : Inhabited (Sublattice α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (Sublattice α) := ⟨⊥⟩

/-- The top sublattice is isomorphic to the original lattice.

This is the sublattice version of `Equiv.Set.univ α`. -/
/-
**Sublattice.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：topEquiv : (⊤ : Sublattice α) ≃o α where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top sublattice is isomorphic to the original lattice.

This is the sublattice version of `Equiv.Set.univ α`.
-/
def topEquiv : (⊤ : Sublattice α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := Iff.rfl
/-
**Sublattice.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α], ↑⊤ = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : (⊤ : Sublattice α) = (univ : Set α) := rfl
/-
**Sublattice.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α], ↑⊥ = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : Sublattice α) = (∅ : Set α) := rfl
/-
**Sublattice.coe_inf'** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L M : Sublattice α), ↑(L ⊓ M) = ↑L ∩ 
↑M
参数：L M : Sublattice α；L ⊓ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf' (L M : Sublattice α) : L ⊓ M = (L : Set α) ∩ M := rfl
/-
**Sublattice.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (S : Set (Sublattice α)), ↑(sInf S) = 
⋂ L ∈ S, ↑L
参数：S : Set (Sublattice α)；sInf S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sInf (S : Set (Sublattice α)) : sInf S = ⋂ L ∈ S, (L : Set α) := rfl
/-
**Sublattice.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : Lattice α] (f : ι → Sublattice α),
 ↑(⨅ i, f i) = ⋂ i, ↑(f i)
参数：f : ι → Sublattice α；⨅ i, f i；f i。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma coe_iInf (f : ι → Sublattice α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by
  simp [iInf]
/-
**Sublattice.coe_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α}, ↑L = Set.univ ↔ L 
= ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sublattice.coe_top`：∀ {α : Type u_2} [inst : Lattice α], ↑⊤ = Set.univ
· 使用引理 `Sublattice.coe_inj`：coe_inj : (L : Set α) = M ↔ L = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by rw [← coe_top, coe_inj]
/-
**Sublattice.coe_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α}, ↑L = ∅ ↔ L = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sublattice.coe_bot`：∀ {α : Type u_2} [inst : Lattice α], ↑⊥ = ∅
· 使用引理 `Sublattice.coe_inj`：coe_inj : (L : Set α) = M ↔ L = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_eq_empty : L = (∅ : Set α) ↔ L = ⊥ := by rw [← coe_bot, coe_inj]
/-
**Sublattice.notMem_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (a : α), a ∉ ⊥
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma notMem_bot (a : α) : a ∉ (⊥ : Sublattice α) := id
/-
**Sublattice.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (a : α), a ∈ ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
@[simp] lemma mem_top (a : α) : a ∈ (⊤ : Sublattice α) := mem_univ _
/-
**Sublattice.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L M : Sublattice α} {a : α}, a ∈ L ⊓ 
M ↔ a ∈ L ∧ a ∈ M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_inf : a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M := Iff.rfl
/-
**Sublattice.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {a : α} {S : Set (Sublattice α)}, a ∈ 
sInf S ↔ ∀ L ∈ S, a ∈ L
参数：Sublattice α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_sInf {S : Set (Sublattice α)} : a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L := by
  rw [← SetLike.mem_coe]; simp
/-
**Sublattice.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : Lattice α] {a : α} {f : ι → Sublat
tice α}, a ∈ ⨅ i, f i ↔ ∀ (i : ι), a ∈ f i
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sublattice.coe_iInf`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Lattice α] 
(f : ι → Sublattice α), ↑(⨅ i, f i) = ⋂ i, ↑(f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_iInf {f : ι → Sublattice α} : a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe]; simp

/-- Sublattices of a lattice form a complete lattice. -/
/-
**Sublattice.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
形式化陈述：instCompleteLattice : CompleteLattice (Sublattice α) where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.mem_top`：∀ {α : Type u_2} [inst : Lattice α] (a : α), a ∈ ⊤

--- 原说明 ---
Sublattices of a lattice form a complete lattice.
-/
instance instCompleteLattice : CompleteLattice (Sublattice α) where
  bot := ⊥
  bot_le := fun _S _a ↦ False.elim
  top := ⊤
  le_top := fun _S a _ha ↦ mem_top a
  inf := (· ⊓ ·)
  le_inf := fun _L _M _N hM hN _a ha ↦ ⟨hM ha, hN ha⟩
  inf_le_left := fun _L _M _a ↦ And.left
  inf_le_right := fun _L _M _a ↦ And.right
  __ := completeLatticeOfInf (Sublattice α)
      fun _s ↦ IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf
/-
**Sublattice.subsingleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：subsingleton_iff : Subsingleton (Sublattice α) ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty 
α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Sublattice.coe_inj`：coe_inj : (L : Set α) = M ↔ L = M
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma subsingleton_iff : Subsingleton (Sublattice α) ↔ IsEmpty α :=
  ⟨fun _ ↦ univ_eq_empty_iff.1 <| coe_inj.2 <| Subsingleton.elim ⊤ ⊥,
    fun _ ↦ SetLike.coe_injective.subsingleton⟩
/-
**Sublattice.** 是 Mathlib 中的一个实例，位于命名空间 `Sublattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (Sublattice α) where
  uniq _ := @Subsingleton.elim _ (subsingleton_iff.2 ‹_›) _ _

/-- The preimage of a sublattice along a lattice homomorphism. -/
/-
**Sublattice.comap** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：comap (f : LatticeHom α β) (L : Sublattice β) : Sublattice α where carrier
参数：f : LatticeHom α β；L : Sublattice β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a sublattice along a lattice homomorphism.
-/
def comap (f : LatticeHom α β) (L : Sublattice β) : Sublattice α where
  carrier := f ⁻¹' L
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _
/-
**Sublattice.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (L
 : Sublattice β) (f : LatticeHom α β),   ↑(Sublattice.comap f L) = ⇑f ⁻¹' ↑L
参数：L : Sublattice β；f : LatticeHom α β；Sublattice.comap f L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_comap (L : Sublattice β) (f : LatticeHom α β) : L.comap f = f ⁻¹' L :=
  rfl
/-
**Sublattice.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] {f
 : LatticeHom α β} {a : α} {L : Sublattice β},   a ∈ Sublattice.comap f L ↔ f a 
∈ L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_comap {L : Sublattice β} : a ∈ L.comap f ↔ f a ∈ L := Iff.rfl
/-
**Sublattice.comap_mono** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：comap_mono : Monotone (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
lemma comap_mono : Monotone (comap f) := fun _ _ ↦ preimage_mono
/-
**Sublattice.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattice α), Sublattice.comap (
LatticeHom.id α) L = L
参数：L : Sublattice α；LatticeHom.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_id (L : Sublattice α) : L.comap (LatticeHom.id _) = L := rfl
/-
**Sublattice.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : Lattice α] [inst_1 
: Lattice β] [inst_2 : Lattice γ]   (L : Sublattice γ) (g : LatticeHom β γ) (f :
 LatticeHom α β),   Sublattice.comap f (Sublattice.comap g L) = Sublattice.comap
 (g.comp f) L
参数：L : Sublattice γ；g : LatticeHom β γ；f : LatticeHom α β；Sublattice.comap g L；g
.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_comap (L : Sublattice γ) (g : LatticeHom β γ) (f : LatticeHom α β) :
    (L.comap g).comap f = L.comap (g.comp f) := rfl

/-- The image of a sublattice along a monoid homomorphism is a sublattice. -/
/-
**Sublattice.map** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：map (f : LatticeHom α β) (L : Sublattice α) : Sublattice β where carrier
参数：f : LatticeHom α β；L : Sublattice α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a sublattice along a monoid homomorphism is a sublattice.
-/
def map (f : LatticeHom α β) (L : Sublattice α) : Sublattice β where
  carrier := f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
/-
**Sublattice.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (f
 : LatticeHom α β) (L : Sublattice α),   ↑(Sublattice.map f L) = ⇑f '' ↑L
参数：f : LatticeHom α β；L : Sublattice α；Sublattice.map f L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_map (f : LatticeHom α β) (L : Sublattice α) : (L.map f : Set β) = f '' L := rfl
/-
**Sublattice.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] {L
 : Sublattice α} {f : LatticeHom α β} {b : β},   b ∈ Sublattice.map f L ↔ ∃ a ∈ 
L, f a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_map {b : β} : b ∈ L.map f ↔ ∃ a ∈ L, f a = b := Iff.rfl
/-
**Sublattice.mem_map_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：mem_map_of_mem (f : LatticeHom α β) {a : α} : a in L -> f a in L.map f
参数：f : LatticeHom α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma mem_map_of_mem (f : LatticeHom α β) {a : α} : a ∈ L → f a ∈ L.map f := mem_image_of_mem f
/-
**Sublattice.apply_coe_mem_map** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：apply_coe_mem_map (f : LatticeHom α β) (a : L) : f a in L.map f
参数：f : LatticeHom α β；a : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.mem_map_of_mem`：mem_map_of_mem (f : LatticeHom α β) {a : α} :
 a in L -> f a in L.map f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma apply_coe_mem_map (f : LatticeHom α β) (a : L) : f a ∈ L.map f := mem_map_of_mem f a.prop
/-
**Sublattice.map_mono** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_mono : Monotone (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma map_mono : Monotone (map f) := fun _ _ ↦ image_mono
/-
**Sublattice.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice α}, Sublattice.map (La
tticeHom.id α) L = L
参数：LatticeHom.id α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
@[simp] lemma map_id : L.map (LatticeHom.id α) = L := SetLike.coe_injective <| image_id _
/-
**Sublattice.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : Lattice α] [inst_1 
: Lattice β] [inst_2 : Lattice γ]   {L : Sublattice α} (g : LatticeHom β γ) (f :
 LatticeHom α β),   Sublattice.map g (Sublattice.map f L) = Sublattice.map (g.co
mp f) L
参数：g : LatticeHom β γ；f : LatticeHom α β；Sublattice.map f L；g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
@[simp] lemma map_map (g : LatticeHom β γ) (f : LatticeHom α β) :
    (L.map f).map g = L.map (g.comp f) := SetLike.coe_injective <| image_image _ _ _
/-
**Sublattice.mem_map_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：mem_map_equiv {f : α ≃o β} {a : β} : a in L.map f ↔ f.symm a in L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
lemma mem_map_equiv {f : α ≃o β} {a : β} : a ∈ L.map f ↔ f.symm a ∈ L := Set.mem_image_equiv
/-
**Sublattice.apply_mem_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：apply_mem_map_iff (hf : Injective f) : f a in L.map f ↔ a in L
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
lemma apply_mem_map_iff (hf : Injective f) : f a ∈ L.map f ↔ a ∈ L := hf.mem_set_image
/-
**Sublattice.map_equiv_eq_comap_symm** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_equiv_eq_comap_symm (f : α ≃o β) (L : Sublattice α) : L.map f = L.coma
p (f.symm : LatticeHom β α)
参数：f : α ≃o β；L : Sublattice α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `OrderIsoClass.toLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Ty
pe u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]   [Or
derIsoClass F α β], L…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
lemma map_equiv_eq_comap_symm (f : α ≃o β) (L : Sublattice α) :
    L.map f = L.comap (f.symm : LatticeHom β α) :=
  SetLike.coe_injective <| f.toEquiv.image_eq_preimage_symm L
/-
**Sublattice.comap_equiv_eq_map_symm** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：comap_equiv_eq_map_symm (f : β ≃o α) (L : Sublattice α) : L.comap f = L.ma
p (f.symm : LatticeHom α β)
参数：f : β ≃o α；L : Sublattice α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIsoClass.toLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Ty
pe u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]   [Or
derIsoClass F α β], L…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用引理 `Sublattice.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : α ≃o β)
 (L : Sublattice α) : L.map f = L.comap (f.symm : LatticeHom β α)
-/
lemma comap_equiv_eq_map_symm (f : β ≃o α) (L : Sublattice α) :
    L.comap f = L.map (f.symm : LatticeHom α β) := (map_equiv_eq_comap_symm f.symm L).symm
/-
**Sublattice.map_symm_eq_iff_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_symm_eq_iff_eq_map {M : Sublattice β} {e : β ≃o α} : L.map ↑e.symm = M
 ↔ L = M.map ↑e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIsoClass.toLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Ty
pe u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]   [Or
derIsoClass F α β], L…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_image_iff_symm_image_eq`：eq_image_iff_symm_image_eq {α β} (e : 
α ≃ β) (s : Set α) (t : Set β) : t = e '' s ↔ e.symm '' t = s
-/
lemma map_symm_eq_iff_eq_map {M : Sublattice β} {e : β ≃o α} :
    L.map ↑e.symm = M ↔ L = M.map ↑e := by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm
/-
**Sublattice.map_le_iff_le_comap** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_le_iff_le_comap {f : LatticeHom α β} {M : Sublattice β} : L.map f <= M
 ↔ L <= M.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
lemma map_le_iff_le_comap {f : LatticeHom α β} {M : Sublattice β} : L.map f ≤ M ↔ L ≤ M.comap f :=
  image_subset_iff
/-
**Sublattice.gc_map_comap** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：gc_map_comap (f : LatticeHom α β) : GaloisConnection (map f) (comap f)
参数：f : LatticeHom α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.map_le_iff_le_comap`：map_le_iff_le_comap {f : LatticeHom α β}
 {M : Sublattice β} : L.map f <= M ↔ L <= M.comap f
-/
lemma gc_map_comap (f : LatticeHom α β) : GaloisConnection (map f) (comap f) :=
  fun _ _ ↦ map_le_iff_le_comap
/-
**Sublattice.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (f
 : LatticeHom α β), Sublattice.map f ⊥ = ⊥
参数：f : LatticeHom α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `Sublattice.gc_map_comap`：gc_map_comap (f : LatticeHom α β) : GaloisConne
ction (map f) (comap f)
-/
@[simp] lemma map_bot (f : LatticeHom α β) : (⊥ : Sublattice α).map f = ⊥ := (gc_map_comap f).l_bot
/-
**Sublattice.map_sup** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_sup (f : LatticeHom α β) (L M : Sublattice α) : (L ⊔ M).map f = L.map 
f ⊔ M.map f
参数：f : LatticeHom α β；L M : Sublattice α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `Sublattice.gc_map_comap`：gc_map_comap (f : LatticeHom α β) : GaloisConne
ction (map f) (comap f)
-/
lemma map_sup (f : LatticeHom α β) (L M : Sublattice α) : (L ⊔ M).map f = L.map f ⊔ M.map f :=
  (gc_map_comap f).l_sup
/-
**Sublattice.map_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_iSup (f : LatticeHom α β) (L : ι -> Sublattice α) : (⨆ i, L i).map f =
 ⨆ i, (L i).map f
参数：f : LatticeHom α β；L : ι -> Sublattice α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用引理 `Sublattice.gc_map_comap`：gc_map_comap (f : LatticeHom α β) : GaloisConne
ction (map f) (comap f)
-/
lemma map_iSup (f : LatticeHom α β) (L : ι → Sublattice α) : (⨆ i, L i).map f = ⨆ i, (L i).map f :=
  (gc_map_comap f).l_iSup
/-
**Sublattice.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (f
 : LatticeHom α β), Sublattice.comap f ⊤ = ⊤
参数：f : LatticeHom α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用引理 `Sublattice.gc_map_comap`：gc_map_comap (f : LatticeHom α β) : GaloisConne
ction (map f) (comap f)
-/
@[simp] lemma comap_top (f : LatticeHom α β) : (⊤ : Sublattice β).comap f = ⊤ :=
  (gc_map_comap f).u_top
/-
**Sublattice.comap_inf** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：comap_inf (L M : Sublattice β) (f : LatticeHom α β) : (L ⊓ M).comap f = L.
comap f ⊓ M.comap f
参数：L M : Sublattice β；f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用引理 `Sublattice.gc_map_comap`：gc_map_comap (f : LatticeHom α β) : GaloisConne
ction (map f) (comap f)
-/
lemma comap_inf (L M : Sublattice β) (f : LatticeHom α β) :
    (L ⊓ M).comap f = L.comap f ⊓ M.comap f := (gc_map_comap f).u_inf
/-
**Sublattice.comap_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：comap_iInf (f : LatticeHom α β) (s : ι -> Sublattice β) : (iInf s).comap f
 = ⨅ i, (s i).comap f
参数：f : LatticeHom α β；s : ι -> Sublattice β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用引理 `Sublattice.gc_map_comap`：gc_map_comap (f : LatticeHom α β) : GaloisConne
ction (map f) (comap f)
-/
lemma comap_iInf (f : LatticeHom α β) (s : ι → Sublattice β) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (gc_map_comap f).u_iInf
/-
**Sublattice.map_inf_le** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_inf_le (L M : Sublattice α) (f : LatticeHom α β) : map f (L ⊓ M) <= ma
p f L ⊓ map f M
参数：L M : Sublattice α；f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用引理 `Sublattice.map_mono`：map_mono : Monotone (map f)
-/
lemma map_inf_le (L M : Sublattice α) (f : LatticeHom α β) : map f (L ⊓ M) ≤ map f L ⊓ map f M :=
  map_mono.map_inf_le _ _
/-
**Sublattice.le_comap_sup** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：le_comap_sup (L M : Sublattice β) (f : LatticeHom α β) : comap f L ⊔ comap
 f M <= comap f (L ⊔ M)
参数：L M : Sublattice β；f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用引理 `Sublattice.comap_mono`：comap_mono : Monotone (comap f)
-/
lemma le_comap_sup (L M : Sublattice β) (f : LatticeHom α β) :
    comap f L ⊔ comap f M ≤ comap f (L ⊔ M) := comap_mono.le_map_sup _ _
/-
**Sublattice.le_comap_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：le_comap_iSup (f : LatticeHom α β) (L : ι -> Sublattice β) : ⨆ i, (L i).co
map f <= (⨆ i, L i).comap f
参数：f : LatticeHom α β；L : ι -> Sublattice β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
· 使用引理 `Sublattice.comap_mono`：comap_mono : Monotone (comap f)
-/
lemma le_comap_iSup (f : LatticeHom α β) (L : ι → Sublattice β) :
    ⨆ i, (L i).comap f ≤ (⨆ i, L i).comap f := comap_mono.le_map_iSup
/-
**Sublattice.map_inf** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_inf (L M : Sublattice α) (f : LatticeHom α β) (hf : Injective f) : map
 f (L ⊓ M) = map f L ⊓ map f M
参数：L M : Sublattice α；f : LatticeHom α β；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_inf (L M : Sublattice α) (f : LatticeHom α β) (hf : Injective f) :
    map f (L ⊓ M) = map f L ⊓ map f M := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]
/-
**Sublattice.map_top** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：map_top (f : LatticeHom α β) (h : Surjective f) : Sublattice.map f ⊤ = ⊤
参数：f : LatticeHom α β；h : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_top (f : LatticeHom α β) (h : Surjective f) : Sublattice.map f ⊤ = ⊤ :=
  SetLike.coe_injective <| by simp [h.range_eq]

end Sublattice

namespace Sublattice
variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a : α}

/-- Binary product of sublattices as a sublattice. -/
@[simps]
/-
**Sublattice.prod** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：prod (L : Sublattice α) (M : Sublattice β) : Sublattice (α × β) where carr
ier
参数：L : Sublattice α；M : Sublattice β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Binary product of sublattices as a sublattice.
-/
def prod (L : Sublattice α) (M : Sublattice β) : Sublattice (α × β) where
  carrier := L ×ˢ M
  supClosed' := L.supClosed.prod M.supClosed
  infClosed' := L.infClosed.prod M.infClosed

attribute [norm_cast] coe_prod
/-
**Sublattice.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] {L
 : Sublattice α} {M : Sublattice β}   {p : α × β}, p ∈ L.prod M ↔ p.1 ∈ L ∧ p.2 
∈ M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_prod {M : Sublattice β} {p : α × β} : p ∈ L.prod M ↔ p.1 ∈ L ∧ p.2 ∈ M := Iff.rfl

@[gcongr]
/-
**Sublattice.prod_mono** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：prod_mono {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublattice β} (hL : L₁ <= L₂) (h
M : M₁ <= M₂) : L₁.prod M₁ <= L₂.prod M₂
参数：hL : L₁ <= L₂；hM : M₁ <= M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
lemma prod_mono {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublattice β} (hL : L₁ ≤ L₂) (hM : M₁ ≤ M₂) :
    L₁.prod M₁ ≤ L₂.prod M₂ := Set.prod_mono hL hM
/-
**Sublattice.prod_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：prod_mono_left {L₁ L₂ : Sublattice α} {M : Sublattice β} (hL : L₁ <= L₂) :
 L₁.prod M <= L₂.prod M
参数：hL : L₁ <= L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.prod_mono`：prod_mono {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublatti
ce β} (hL : L₁ <= L₂) (hM : M₁ <= M₂) : L₁.prod M₁ <= L₂.prod M₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma prod_mono_left {L₁ L₂ : Sublattice α} {M : Sublattice β} (hL : L₁ ≤ L₂) :
    L₁.prod M ≤ L₂.prod M := prod_mono hL le_rfl
/-
**Sublattice.prod_mono_right** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：prod_mono_right {M₁ M₂ : Sublattice β} (hM : M₁ <= M₂) : L.prod M₁ <= L.pr
od M₂
参数：hM : M₁ <= M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.prod_mono`：prod_mono {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublatti
ce β} (hL : L₁ <= L₂) (hM : M₁ <= M₂) : L₁.prod M₁ <= L₂.prod M₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma prod_mono_right {M₁ M₂ : Sublattice β} (hM : M₁ ≤ M₂) : L.prod M₁ ≤ L.prod M₂ :=
  prod_mono le_rfl hM
/-
**Sublattice.prod_left_mono** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：prod_left_mono : Monotone fun L : Sublattice α => L.prod M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.prod_mono_left`：prod_mono_left {L₁ L₂ : Sublattice α} {M : Su
blattice β} (hL : L₁ <= L₂) : L₁.prod M <= L₂.prod M
-/
lemma prod_left_mono : Monotone fun L : Sublattice α ↦ L.prod M := fun _ _ ↦ prod_mono_left
/-
**Sublattice.prod_right_mono** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：prod_right_mono : Monotone fun M : Sublattice β => L.prod M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.prod_mono_right`：prod_mono_right {M₁ M₂ : Sublattice β} (hM :
 M₁ <= M₂) : L.prod M₁ <= L.prod M₂
-/
lemma prod_right_mono : Monotone fun M : Sublattice β ↦ L.prod M := fun _ _ ↦ prod_mono_right
/-
**Sublattice.prod_top** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：prod_top (L : Sublattice α) : L.prod (⊤ : Sublattice β) = L.comap LatticeH
om.fst
参数：L : Sublattice α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.ext`：ext : (forall a, a in L ↔ a in M) -> L = M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma prod_top (L : Sublattice α) : L.prod (⊤ : Sublattice β) = L.comap LatticeHom.fst :=
  ext fun a ↦ by simp [mem_prod, LatticeHom.coe_fst]
/-
**Sublattice.top_prod** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：top_prod (L : Sublattice β) : (⊤ : Sublattice α).prod L = L.comap LatticeH
om.snd
参数：L : Sublattice β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.ext`：ext : (forall a, a in L ↔ a in M) -> L = M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma top_prod (L : Sublattice β) : (⊤ : Sublattice α).prod L = L.comap LatticeHom.snd :=
  ext fun a ↦ by simp [mem_prod, LatticeHom.coe_snd]
/-
**Sublattice.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β], ⊤
.prod ⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Sublattice.top_prod`：top_prod (L : Sublattice β) : (⊤ : Sublattice α).pr
od L = L.comap LatticeHom.snd
· 使用定理 `Sublattice.comap_top`：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α]
 [inst_1 : Lattice β] (f : LatticeHom α β), Sublattice.comap f ⊤ = ⊤
-/
@[simp] lemma top_prod_top : (⊤ : Sublattice α).prod (⊤ : Sublattice β) = ⊤ :=
  (top_prod _).trans <| comap_top _
/-
**Sublattice.prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (L
 : Sublattice α), L.prod ⊥ = ⊥
参数：L : Sublattice α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
-/
@[simp] lemma prod_bot (L : Sublattice α) : L.prod (⊥ : Sublattice β) = ⊥ :=
  SetLike.coe_injective prod_empty
/-
**Sublattice.bot_prod** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (M
 : Sublattice β), ⊥.prod M = ⊥
参数：M : Sublattice β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
-/
@[simp] lemma bot_prod (M : Sublattice β) : (⊥ : Sublattice α).prod M = ⊥ :=
  SetLike.coe_injective empty_prod
/-
**Sublattice.le_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：le_prod_iff {M : Sublattice β} {N : Sublattice (α × β)} : N <= L.prod M ↔ 
N <= comap LatticeHom.fst L ∧ N <= comap LatticeHom.snd M
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_prod_iff {M : Sublattice β} {N : Sublattice (α × β)} :
    N ≤ L.prod M ↔ N ≤ comap LatticeHom.fst L ∧ N ≤ comap LatticeHom.snd M := by
  simp [SetLike.le_def, forall_and]
/-
**Sublattice.prod_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] {L
 : Sublattice α} {M : Sublattice β},   L.prod M = ⊥ ↔ L = ⊥ ∨ M = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
-/
@[simp] lemma prod_eq_bot {M : Sublattice β} : L.prod M = ⊥ ↔ L = ⊥ ∨ M = ⊥ := by
  simpa only [← coe_inj] using! Set.prod_eq_empty_iff
/-
**Sublattice.prod_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] {L
 : Sublattice α} [Nonempty α] [Nonempty β]   {M : Sublattice β}, L.prod M = ⊤ ↔ 
L = ⊤ ∧ M = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_eq_univ`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} [Nonempty α] [Nonempty β],   s ×ˢ t = Set.univ ↔ s = Set.univ ∧ t = Set.univ
-/
@[simp] lemma prod_eq_top [Nonempty α] [Nonempty β] {M : Sublattice β} :
    L.prod M = ⊤ ↔ L = ⊤ ∧ M = ⊤ := by simpa only [← coe_inj] using! Set.prod_eq_univ

/-- The product of sublattices is isomorphic to their product as lattices. -/
@[simps! toEquiv apply symm_apply]
/-
**Sublattice.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：prodEquiv (L : Sublattice α) (M : Sublattice β) : L.prod M ≃o L × M where 
toEquiv
参数：L : Sublattice α；M : Sublattice β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of sublattices is isomorphic to their product as lattices.
-/
def prodEquiv (L : Sublattice α) (M : Sublattice β) : L.prod M ≃o L × M where
  toEquiv := Equiv.Set.prod _ _
  map_rel_iff' := Iff.rfl

section Pi
variable {κ : Type*} {π : κ → Type*} [∀ i, Lattice (π i)]

/-- Arbitrary product of sublattices. Given an index set `s` and a family of sublattices
`L : Π i, Sublattice (α i)`, `pi s L` is the sublattice of dependent functions `f : Π i, α i` such
that `f i` belongs to `L i` whenever `i ∈ s`. -/
@[simps]
/-
**Sublattice.pi** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice`。
形式化陈述：pi (s : Set κ) (L : forall i, Sublattice (π i)) : Sublattice (forall i, π 
i) where carrier
参数：s : Set κ；L : forall i, Sublattice (π i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Arbitrary product of sublattices. Given an index set `s` and a family of sublatt
ices
`L : Π i, Sublattice (α i)`, `pi s L` is the sublattice of dependent functions `
f : Π i, α i` such
that `f i` belongs to `L i` whenever `i ∈ s`.
-/
def pi (s : Set κ) (L : ∀ i, Sublattice (π i)) : Sublattice (∀ i, π i) where
  carrier := s.pi fun i ↦ L i
  supClosed' := supClosed_pi fun i _ ↦ (L i).supClosed
  infClosed' := infClosed_pi fun i _ ↦ (L i).infClosed

attribute [norm_cast] coe_pi
/-
**Sublattice.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {κ : Type u_5} {π : κ → Type u_6} [inst : (i : κ) → Lattice (π i)] {s : 
Set κ} {L : (i : κ) → Sublattice (π i)}   {x : (i : κ) → π i}, x ∈ Sublattice.pi
 s L ↔ ∀ i ∈ s, x i ∈ L i
参数：i : κ；π i；i : κ；π i；i : κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_pi {s : Set κ} {L : ∀ i, Sublattice (π i)} {x : ∀ i, π i} :
    x ∈ pi s L ↔ ∀ i, i ∈ s → x i ∈ L i := Iff.rfl
/-
**Sublattice.pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {κ : Type u_5} {π : κ → Type u_6} [inst : (i : κ) → Lattice (π i)] (L : 
(i : κ) → Sublattice (π i)),   Sublattice.pi ∅ L = ⊤
参数：i : κ；π i；L : (i : κ) → Sublattice (π i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.ext`：ext : (forall a, a in L ↔ a in M) -> L = M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma pi_empty (L : ∀ i, Sublattice (π i)) : pi ∅ L = ⊤ := ext fun a ↦ by simp [mem_pi]
/-
**Sublattice.pi_top** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {κ : Type u_5} {π : κ → Type u_6} [inst : (i : κ) → Lattice (π i)] (s : 
Set κ), (Sublattice.pi s fun x => ⊤) = ⊤
参数：i : κ；π i；s : Set κ；Sublattice.pi s fun x => ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.ext`：ext : (forall a, a in L ↔ a in M) -> L = M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma pi_top (s : Set κ) : (pi s fun _ ↦ ⊤ : Sublattice (∀ i, π i)) = ⊤ :=
  ext fun a ↦ by simp [mem_pi]
/-
**Sublattice.pi_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {κ : Type u_5} {π : κ → Type u_6} [inst : (i : κ) → Lattice (π i)] {s : 
Set κ},   s.Nonempty → (Sublattice.pi s fun x => ⊥) = ⊥
参数：i : κ；π i；Sublattice.pi s fun x => ⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.ext`：ext : (forall a, a in L ↔ a in M) -> L = M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[simp] lemma pi_bot {s : Set κ} (hs : s.Nonempty) : (pi s fun _ ↦ ⊥ : Sublattice (∀ i, π i)) = ⊥ :=
  ext fun a ↦ by simpa [mem_pi] using! hs
/-
**Sublattice.pi_univ_bot** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：pi_univ_bot [Nonempty κ] : (pi univ fun _ => ⊥ : Sublattice (forall i, π i
)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sublattice.pi_bot`：∀ {κ : Type u_5} {π : κ → Type u_6} [inst : (i : κ) →
 Lattice (π i)] {s : Set κ},   s.Nonempty → (Sublattice.pi s fun x => ⊥) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pi_univ_bot [Nonempty κ] : (pi univ fun _ ↦ ⊥ : Sublattice (∀ i, π i)) = ⊥ := by simp
/-
**Sublattice.le_pi** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：le_pi {s : Set κ} {L : forall i, Sublattice (π i)} {M : Sublattice (forall
 i, π i)} : M <= pi s L ↔ forall i in s, M <= comap (Pi.evalLatticeHom i) (L i)
参数：π i；forall i, π i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma le_pi {s : Set κ} {L : ∀ i, Sublattice (π i)} {M : Sublattice (∀ i, π i)} :
    M ≤ pi s L ↔ ∀ i ∈ s, M ≤ comap (Pi.evalLatticeHom i) (L i) := by simp [SetLike.le_def]; grind
/-
**Sublattice.pi_univ_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {κ : Type u_5} {π : κ → Type u_6} [inst : (i : κ) → Lattice (π i)] {L : 
(i : κ) → Sublattice (π i)},   Sublattice.pi Set.univ L = ⊥ ↔ ∃ i, L i = ⊥
参数：i : κ；π i；i : κ；π i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sublattice.coe_pi`：∀ {κ : Type u_5} {π : κ → Type u_6} [inst : (i : κ) →
 Lattice (π i)] (s : Set κ) (L : (i : κ) → Sublattice (π i)),   ↑(Sublattice.pi 
s L) = …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma pi_univ_eq_bot_iff {L : ∀ i, Sublattice (π i)} : pi univ L = ⊥ ↔ ∃ i, L i = ⊥ := by
  simp_rw [← coe_inj]; simp
/-
**Sublattice.pi_univ_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：pi_univ_eq_bot {L : forall i, Sublattice (π i)} {i : κ} (hL : L i = ⊥) : p
i univ L = ⊥
参数：π i；hL : L i = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sublattice.pi_univ_eq_bot_iff`：∀ {κ : Type u_5} {π : κ → Type u_6} [inst
 : (i : κ) → Lattice (π i)] {L : (i : κ) → Sublattice (π i)},   Sublattice.pi Se
t.univ L = ⊥ ↔ ∃ i,…
-/
lemma pi_univ_eq_bot {L : ∀ i, Sublattice (π i)} {i : κ} (hL : L i = ⊥) : pi univ L = ⊥ :=
  pi_univ_eq_bot_iff.2 ⟨i, hL⟩

end Pi

namespace LatticeHom

/--
The range of `LatticeHom` is a sublattice.
-/
/-
**Sublattice.LatticeHom.range** 是 Mathlib 中的一个定义，位于命名空间 `Sublattice.LatticeHom`。
形式化陈述：range (f : LatticeHom α β)
参数：f : LatticeHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of `LatticeHom` is a sublattice.
-/
def range (f : LatticeHom α β) := (Sublattice.map f ⊤).copy (Set.range f) image_univ.symm
/-
**Sublattice.LatticeHom.range_coe** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice.LatticeH
om`。
形式化陈述：range_coe : (LatticeHom.range f : Set β) = Set.range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_coe : (LatticeHom.range f : Set β) = Set.range f := rfl

end LatticeHom

end Sublattice

