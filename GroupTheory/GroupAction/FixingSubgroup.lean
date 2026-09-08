/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!

# Fixing submonoid, fixing subgroup of an action

In the presence of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixingSubmonoid M s` : in the presence of `MulAction M α` (with `Monoid M`)
  it is the `Submonoid M` consisting of elements which fix `s : Set α` pointwise.

* `fixingSubmonoid_fixedPoints_gc M α` is the `GaloisConnection`
  that relates `fixingSubmonoid` with `fixedPoints`.

* `fixingSubgroup M s` : in the presence of `MulAction M α` (with `Group M`)
  it is the `Subgroup M` consisting of elements which fix `s : Set α` pointwise.

* `fixingSubgroup_fixedPoints_gc M α` is the `GaloisConnection`
  that relates `fixingSubgroup` with `fixedPoints`.

TODO :

* Maybe other lemmas are useful

* Treat semigroups ?

-/

@[expose] public section


section Monoid

open MulAction

variable (M : Type*) {α : Type*} [Monoid M] [MulAction M α]

/-- The submonoid fixing a set under a `MulAction`. -/
@[to_additive /-- The additive submonoid fixing a set under an `AddAction`. -/]
/-
**fixingSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fixingSubmonoid (s : Set α) : Submonoid M where carrier
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid fixing a set under a `MulAction`.
-/
def fixingSubmonoid (s : Set α) : Submonoid M where
  carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' {x y} hx hy z := by rw [mul_smul, hy z, hx z]

@[to_additive]
/-
**mem_fixingSubmonoid_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_fixingSubmonoid_iff {s : Set α} {m : M} : m in fixingSubmonoid M s ↔ f
orall y in s, m • y = y
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_fixingSubmonoid_iff {s : Set α} {m : M} :
    m ∈ fixingSubmonoid M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
@[to_additive]
/-
**fixingSubmonoid_fixedPoints_gc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubmonoid_fixedPoints_gc : GaloisConnection (OrderDual.toDual ∘ fixi
ngSubmonoid M) ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The Galois connection between fixing submonoids and fixed points of a monoid act
ion
-/
theorem fixingSubmonoid_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive]
/-
**fixingSubmonoid_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubmonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `fixingSubmonoid_fixedPoints_gc`：fixingSubmonoid_fixedPoints_gc : GaloisC
onnection (OrderDual.toDual ∘ fixingSubmonoid M) ((fun P : Submonoid M => fixedP
oints P α) ∘ OrderDu…
-/
theorem fixingSubmonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_l

@[to_additive fixedPoints_antitone_addSubmonoid]
/-
**fixedPoints_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixedPoints_antitone : Antitone fun P : Submonoid M => fixedPoints P α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Monotone f → Antitone (f ∘ ⇑OrderDual.ofDual)
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `fixingSubmonoid_fixedPoints_gc`：fixingSubmonoid_fixedPoints_gc : GaloisC
onnection (OrderDual.toDual ∘ fixingSubmonoid M) ((fun P : Submonoid M => fixedP
oints P α) ∘ OrderDu…
-/
theorem fixedPoints_antitone : Antitone fun P : Submonoid M => fixedPoints P α :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left

/-- Fixing submonoid of union is intersection -/
@[to_additive]
/-
**fixingSubmonoid_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubmonoid_union {s t : Set α} : fixingSubmonoid M (s union t) = fixi
ngSubmonoid M s ⊓ fixingSubmonoid M t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `fixingSubmonoid_fixedPoints_gc`：fixingSubmonoid_fixedPoints_gc : GaloisC
onnection (OrderDual.toDual ∘ fixingSubmonoid M) ((fun P : Submonoid M => fixedP
oints P α) ∘ OrderDu…

--- 原说明 ---
Fixing submonoid of union is intersection
-/
theorem fixingSubmonoid_union {s t : Set α} :
    fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixingSubmonoid_fixedPoints_gc M α).l_sup

/-- Fixing submonoid of iUnion is intersection -/
@[to_additive]
/-
**fixingSubmonoid_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubmonoid_iUnion {ι : Sort*} {s : ι -> Set α} : fixingSubmonoid M (⋃
 i, s i) = ⨅ i, fixingSubmonoid M (s i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `fixingSubmonoid_fixedPoints_gc`：fixingSubmonoid_fixedPoints_gc : GaloisC
onnection (OrderDual.toDual ∘ fixingSubmonoid M) ((fun P : Submonoid M => fixedP
oints P α) ∘ OrderDu…

--- 原说明 ---
Fixing submonoid of iUnion is intersection
-/
theorem fixingSubmonoid_iUnion {ι : Sort*} {s : ι → Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixingSubmonoid_fixedPoints_gc M α).l_iSup

/-- Fixed points of sup of submonoids is intersection -/
@[to_additive]
/-
**fixedPoints_submonoid_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixedPoints_submonoid_sup {P Q : Submonoid M} : fixedPoints (↥(P ⊔ Q)) α =
 fixedPoints P α inter fixedPoints Q α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `fixingSubmonoid_fixedPoints_gc`：fixingSubmonoid_fixedPoints_gc : GaloisC
onnection (OrderDual.toDual ∘ fixingSubmonoid M) ((fun P : Submonoid M => fixedP
oints P α) ∘ OrderDu…

--- 原说明 ---
Fixed points of sup of submonoids is intersection
-/
theorem fixedPoints_submonoid_sup {P Q : Submonoid M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_inf

/-- Fixed points of iSup of submonoids is intersection -/
@[to_additive]
/-
**fixedPoints_submonoid_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixedPoints_submonoid_iSup {ι : Sort*} {P : ι -> Submonoid M} : fixedPoint
s (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `fixingSubmonoid_fixedPoints_gc`：fixingSubmonoid_fixedPoints_gc : GaloisC
onnection (OrderDual.toDual ∘ fixingSubmonoid M) ((fun P : Submonoid M => fixedP
oints P α) ∘ OrderDu…

--- 原说明 ---
Fixed points of iSup of submonoids is intersection
-/
theorem fixedPoints_submonoid_iSup {ι : Sort*} {P : ι → Submonoid M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_iInf

end Monoid

section Group

open MulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α]

/-- The subgroup fixing a set under a `MulAction`. -/
@[to_additive /-- The additive subgroup fixing a set under an `AddAction`. -/]
/-
**fixingSubgroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fixingSubgroup (s : Set α) : Subgroup M
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup fixing a set under a `MulAction`.
-/
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun hx z => by rw [inv_smul_eq_iff, hx z] }

@[to_additive]
/-
**mem_fixingSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_fixingSubgroup_iff {s : Set α} {m : M} : m in fixingSubgroup M s ↔ for
all y in s, m • y = y
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_fixingSubgroup_iff {s : Set α} {m : M} : m ∈ fixingSubgroup M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

@[to_additive]
/-
**mem_fixingSubgroup_iff_subset_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_fixingSubgroup_iff_subset_fixedBy {s : Set α} {m : M} : m in fixingSub
group M s ↔ s subseteq fixedBy α m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_fixingSubgroup_iff_subset_fixedBy {s : Set α} {m : M} :
    m ∈ fixingSubgroup M s ↔ s ⊆ fixedBy α m := by
  simp_rw [mem_fixingSubgroup_iff, Set.subset_def, mem_fixedBy]

@[to_additive]
/-
**mem_fixingSubgroup_compl_iff_movedBy_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_fixingSubgroup_compl_iff_movedBy_subset {s : Set α} {m : M} : m in fix
ingSubgroup M sᶜ ↔ (fixedBy α m)ᶜ subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_fixingSubgroup_iff_subset_fixedBy`：mem_fixingSubgroup_iff_subset_fix
edBy {s : Set α} {m : M} : m in fixingSubgroup M s ↔ s subseteq fixedBy α m
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fixingSubgroup_compl_iff_movedBy_subset {s : Set α} {m : M} :
    m ∈ fixingSubgroup M sᶜ ↔ (fixedBy α m)ᶜ ⊆ s := by
  rw [mem_fixingSubgroup_iff_subset_fixedBy, Set.compl_subset_comm]

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
@[to_additive]
/-
**fixingSubgroup_fixedPoints_gc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubgroup_fixedPoints_gc : GaloisConnection (OrderDual.toDual ∘ fixin
gSubgroup M) ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The Galois connection between fixing subgroups and fixed points of a group actio
n
-/
theorem fixingSubgroup_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive (attr := simp)]
/-
**fixingSubgroup_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fixingSubgroup_empty : fixingSubgroup M (∅ : Set α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `fixingSubgroup_fixedPoints_gc`：fixingSubgroup_fixedPoints_gc : GaloisCon
nection (OrderDual.toDual ∘ fixingSubgroup M) ((fun P : Subgroup M => fixedPoint
s P α) ∘ OrderDual.…
-/
lemma fixingSubgroup_empty : fixingSubgroup M (∅ : Set α) = ⊤ :=
  GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)

@[to_additive]
/-
**fixingSubgroup_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubgroup_antitone : Antitone (fixingSubgroup M : Set α -> Subgroup M
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `fixingSubgroup_fixedPoints_gc`：fixingSubgroup_fixedPoints_gc : GaloisCon
nection (OrderDual.toDual ∘ fixingSubgroup M) ((fun P : Subgroup M => fixedPoint
s P α) ∘ OrderDual.…
-/
theorem fixingSubgroup_antitone : Antitone (fixingSubgroup M : Set α → Subgroup M) :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_l

@[to_additive]
/-
**fixedPoints_subgroup_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixedPoints_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints
 P α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Monotone f → Antitone (f ∘ ⇑OrderDual.ofDual)
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `fixingSubgroup_fixedPoints_gc`：fixingSubgroup_fixedPoints_gc : GaloisCon
nection (OrderDual.toDual ∘ fixingSubgroup M) ((fun P : Subgroup M => fixedPoint
s P α) ∘ OrderDual.…
-/
theorem fixedPoints_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints P α :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left

/-- Fixing subgroup of union is intersection -/
@[to_additive]
/-
**fixingSubgroup_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubgroup_union {s t : Set α} : fixingSubgroup M (s union t) = fixing
Subgroup M s ⊓ fixingSubgroup M t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `fixingSubgroup_fixedPoints_gc`：fixingSubgroup_fixedPoints_gc : GaloisCon
nection (OrderDual.toDual ∘ fixingSubgroup M) ((fun P : Subgroup M => fixedPoint
s P α) ∘ OrderDual.…

--- 原说明 ---
Fixing subgroup of union is intersection
-/
theorem fixingSubgroup_union {s t : Set α} :
    fixingSubgroup M (s ∪ t) = fixingSubgroup M s ⊓ fixingSubgroup M t :=
  (fixingSubgroup_fixedPoints_gc M α).l_sup

/-- Fixing subgroup of iUnion is intersection -/
@[to_additive]
/-
**fixingSubgroup_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixingSubgroup_iUnion {ι : Sort*} {s : ι -> Set α} : fixingSubgroup M (⋃ i
, s i) = ⨅ i, fixingSubgroup M (s i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `fixingSubgroup_fixedPoints_gc`：fixingSubgroup_fixedPoints_gc : GaloisCon
nection (OrderDual.toDual ∘ fixingSubgroup M) ((fun P : Subgroup M => fixedPoint
s P α) ∘ OrderDual.…

--- 原说明 ---
Fixing subgroup of iUnion is intersection
-/
theorem fixingSubgroup_iUnion {ι : Sort*} {s : ι → Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixingSubgroup_fixedPoints_gc M α).l_iSup

/-- Fixed points of sup of subgroups is intersection -/
@[to_additive]
/-
**fixedPoints_subgroup_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixedPoints_subgroup_sup {P Q : Subgroup M} : fixedPoints (↥(P ⊔ Q)) α = f
ixedPoints P α inter fixedPoints Q α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `fixingSubgroup_fixedPoints_gc`：fixingSubgroup_fixedPoints_gc : GaloisCon
nection (OrderDual.toDual ∘ fixingSubgroup M) ((fun P : Subgroup M => fixedPoint
s P α) ∘ OrderDual.…

--- 原说明 ---
Fixed points of sup of subgroups is intersection
-/
theorem fixedPoints_subgroup_sup {P Q : Subgroup M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubgroup_fixedPoints_gc M α).u_inf

/-- Fixed points of iSup of subgroups is intersection -/
@[to_additive]
/-
**fixedPoints_subgroup_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fixedPoints_subgroup_iSup {ι : Sort*} {P : ι -> Subgroup M} : fixedPoints 
(↥(iSup P)) α = ⋂ i, fixedPoints (P i) α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `fixingSubgroup_fixedPoints_gc`：fixingSubgroup_fixedPoints_gc : GaloisCon
nection (OrderDual.toDual ∘ fixingSubgroup M) ((fun P : Subgroup M => fixedPoint
s P α) ∘ OrderDual.…

--- 原说明 ---
Fixed points of iSup of subgroups is intersection
-/
theorem fixedPoints_subgroup_iSup {ι : Sort*} {P : ι → Subgroup M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubgroup_fixedPoints_gc M α).u_iInf

/-- The orbit of the fixing subgroup of `sᶜ` (i.e. the moving subgroup of `s`) is a subset of `s` -/
@[to_additive]
/-
**orbit_fixingSubgroup_compl_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orbit_fixingSubgroup_compl_subset {s : Set α} {a : α} (a_in_s : a in s) : 
MulAction.orbit (fixingSubgroup M sᶜ) a subseteq s
参数：a_in_s : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_orbit_iff`：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ 
exists x : γ, x • a₁ = a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submonoid.mk_smul`：mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S
) • a = g • a
· 使用定理 `MulAction.smul_mem_of_set_mem_fixedBy`：smul_mem_of_set_mem_fixedBy {s : 
Set α} {g : G} (s_in_fixedBy : s in fixedBy (Set α) g) {x : α} : g • x in s ↔ x 
in s
· 使用定理 `MulAction.set_mem_fixedBy_of_movedBy_subset`：set_mem_fixedBy_of_movedBy_
subset {s : Set α} {g : G} (s_subset : (fixedBy α g)ᶜ subseteq s) : s in fixedBy
 (Set α) g
· 使用定理 `mem_fixingSubgroup_compl_iff_movedBy_subset`：mem_fixingSubgroup_compl_if
f_movedBy_subset {s : Set α} {m : M} : m in fixingSubgroup M sᶜ ↔ (fixedBy α m)ᶜ
 subseteq s

--- 原说明 ---
The orbit of the fixing subgroup of `sᶜ` (i.e. the moving subgroup of `s`) is a 
subset of `s`
-/
theorem orbit_fixingSubgroup_compl_subset {s : Set α} {a : α} (a_in_s : a ∈ s) :
    MulAction.orbit (fixingSubgroup M sᶜ) a ⊆ s := by
  intro b b_in_orbit
  let ⟨⟨g, g_fixing⟩, g_eq⟩ := MulAction.mem_orbit_iff.mp b_in_orbit
  rw [Submonoid.mk_smul] at g_eq
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_fixing
  rwa [← g_eq, smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]

end Group

