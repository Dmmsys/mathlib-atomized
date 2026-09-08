/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Sublattice

/-!
# Boolean subalgebras

This file defines Boolean subalgebras.
-/

@[expose] public section

open Function Set

variable {ι : Sort*} {α β γ : Type*}

variable (α) in
/-- A Boolean subalgebra of a Boolean algebra is a set containing the bottom and top elements, and
closed under suprema, infima and complements. -/
/-
**BooleanSubalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [BooleanAlgebra α] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean subalgebra of a Boolean algebra is a set containing the bottom and top
 elements, and
closed under suprema, infima and complements.
-/
structure BooleanSubalgebra [BooleanAlgebra α] extends Sublattice α where
  compl_mem' {a} : a ∈ carrier → aᶜ ∈ carrier
  bot_mem' : ⊥ ∈ carrier

namespace BooleanSubalgebra
section BooleanAlgebra
variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ] {L M : BooleanSubalgebra α}
  {f : BoundedLatticeHom α β} {s t : Set α} {a b : α}

initialize_simps_projections BooleanSubalgebra (carrier → coe, as_prefix coe)

/-
**BooleanSubalgebra.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instSetLike : SetLike (BooleanSubalgebra α) α where coe L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (BooleanSubalgebra α) α where
  coe L := L.carrier
  coe_injective L M h := by obtain ⟨⟨_, _⟩, _⟩ := L; congr
/-
**BooleanSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (BooleanSubalgebra α) := .ofSetLike (BooleanSubalgebra α) α
/-
**BooleanSubalgebra.coe_inj** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：coe_inj : (L : Set α) = M ↔ L = M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq
/-
**BooleanSubalgebra.supClosed** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (L : BooleanSubalgebra α), SupC
losed ↑L
参数：L : BooleanSubalgebra α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.supClosed'`：∀ {α : Type u_2} [inst : Lattice α] (self : Subla
ttice α), SupClosed self.carrier
-/
@[simp] lemma supClosed (L : BooleanSubalgebra α) : SupClosed (L : Set α) := L.supClosed'
/-
**BooleanSubalgebra.infClosed** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (L : BooleanSubalgebra α), InfC
losed ↑L
参数：L : BooleanSubalgebra α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublattice.infClosed'`：∀ {α : Type u_2} [inst : Lattice α] (self : Subla
ttice α), InfClosed self.carrier
-/
@[simp] lemma infClosed (L : BooleanSubalgebra α) : InfClosed (L : Set α) := L.infClosed'
/-
**BooleanSubalgebra.compl_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：compl_mem (ha : a in L) : aᶜ in L
参数：ha : a in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.compl_mem'`：∀ {α : Type u_2} [inst : BooleanAlgebra α]
 (self : BooleanSubalgebra α) {a : α}, a ∈ self.carrier → aᶜ ∈ self.carrier
-/
lemma compl_mem (ha : a ∈ L) : aᶜ ∈ L := L.compl_mem' ha
/-
**BooleanSubalgebra.compl_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} {a : 
α}, aᶜ ∈ L ↔ a ∈ L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `BooleanSubalgebra.compl_mem`：compl_mem (ha : a in L) : aᶜ in L
-/
@[simp] lemma compl_mem_iff : aᶜ ∈ L ↔ a ∈ L := ⟨fun ha ↦ by simpa using compl_mem ha, compl_mem⟩
/-
**BooleanSubalgebra.bot_mem** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α}, ⊥ ∈ 
L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.bot_mem'`：∀ {α : Type u_2} [inst : BooleanAlgebra α] (
self : BooleanSubalgebra α), ⊥ ∈ self.carrier
-/
@[simp] lemma bot_mem : ⊥ ∈ L := L.bot_mem'
/-
**BooleanSubalgebra.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α}, ⊤ ∈ 
L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
· 使用引理 `BooleanSubalgebra.compl_mem`：compl_mem (ha : a in L) : aᶜ in L
· 使用定理 `BooleanSubalgebra.bot_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊥ ∈ L
-/
@[simp] lemma top_mem : ⊤ ∈ L := by simpa using compl_mem L.bot_mem
/-
**BooleanSubalgebra.sup_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：sup_mem (ha : a in L) (hb : b in L) : a ⊔ b in L
参数：ha : a in L；hb : b in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.supClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), SupClosed ↑L
-/
lemma sup_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊔ b ∈ L := L.supClosed ha hb
/-
**BooleanSubalgebra.inf_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：inf_mem (ha : a in L) (hb : b in L) : a ⊓ b in L
参数：ha : a in L；hb : b in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.infClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), InfClosed ↑L
-/
lemma inf_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊓ b ∈ L := L.infClosed ha hb
/-
**BooleanSubalgebra.sdiff_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：sdiff_mem (ha : a in L) (hb : b in L) : a \ b in L
参数：ha : a in L；hb : b in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `BooleanSubalgebra.infClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), InfClosed ↑L
· 使用引理 `BooleanSubalgebra.compl_mem`：compl_mem (ha : a in L) : aᶜ in L
-/
lemma sdiff_mem (ha : a ∈ L) (hb : b ∈ L) : a \ b ∈ L := by
  rw [_root_.sdiff_eq]; exact L.infClosed ha (compl_mem hb)
/-
**BooleanSubalgebra.himp_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：himp_mem (ha : a in L) (hb : b in L) : a ⇨ b in L
参数：ha : a in L；hb : b in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `BooleanSubalgebra.supClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), SupClosed ↑L
· 使用引理 `BooleanSubalgebra.compl_mem`：compl_mem (ha : a in L) : aᶜ in L
-/
lemma himp_mem (ha : a ∈ L) (hb : b ∈ L) : a ⇨ b ∈ L := by
  rw [himp_eq]; exact L.supClosed hb (compl_mem ha)
/-
**BooleanSubalgebra.mem_carrier** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：mem_carrier : a in L.carrier ↔ a in L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := .rfl
/-
**BooleanSubalgebra.mem_toSublattice** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebr
a`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} {a : 
α}, a ∈ L.toSublattice ↔ a ∈ L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_toSublattice : a ∈ L.toSublattice ↔ a ∈ L := .rfl
/-
**BooleanSubalgebra.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a : α} {L : Sublattice α}   (h
_compl : ∀ {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier) (h_bot : ⊥ ∈ L.carrier),   a
 ∈ { toSublattice := L, compl_mem' := h_compl, bot_mem' := h_bot } ↔ a ∈ L
参数：h_compl : ∀ {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier；h_bot : ⊥ ∈ L.carrier。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk {L : Sublattice α} (h_compl h_bot) : a ∈ mk L h_compl h_bot ↔ a ∈ L := .rfl
/-
**BooleanSubalgebra.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (L : Sublattice α) (h_compl : ∀
 {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier)   (h_bot : ⊥ ∈ L.carrier), ↑{ toSublat
tice := L, compl_mem' := h_compl, bot_mem' := h_bot } = ↑L
参数：L : Sublattice α；h_compl : ∀ {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier；h_bot : 
⊥ ∈ L.carrier。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (L : Sublattice α) (h_compl h_bot) : (mk L h_compl h_bot : Set α) = L := rfl
/-
**BooleanSubalgebra.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L M : Sublattice α} (hL_compl 
: ∀ {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier)   (hL_bot : ⊥ ∈ L.carrier) (hM_comp
l : ∀ {a : α}, a ∈ M.carrier → aᶜ ∈ M.carrier) (hM_bot : ⊥ ∈ M.carrier),   { toS
ublattice := L, compl_mem' := hL_compl, bot_mem' := hL_bot } ≤       { toSublatt
ice := M, compl_mem' := hM_compl, bot_mem' := hM_bot } ↔     L ≤ M
参数：hL_compl : ∀ {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier；hL_bot : ⊥ ∈ L.carrier；h
M_compl : ∀ {a : α}, a ∈ M.carrier → aᶜ ∈ M.carrier；hM_bot : ⊥ ∈ M.carrier。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mk_le_mk {L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot) :
    mk L hL_compl hL_bot ≤ mk M hM_compl hM_bot ↔ L ≤ M := .rfl
/-
**BooleanSubalgebra.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L M : Sublattice α} (hL_compl 
: ∀ {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier)   (hL_bot : ⊥ ∈ L.carrier) (hM_comp
l : ∀ {a : α}, a ∈ M.carrier → aᶜ ∈ M.carrier) (hM_bot : ⊥ ∈ M.carrier),   { toS
ublattice := L, compl_mem' := hL_compl, bot_mem' := hL_bot } <       { toSublatt
ice := M, compl_mem' := hM_compl, bot_mem' := hM_bot } ↔     L < M
参数：hL_compl : ∀ {a : α}, a ∈ L.carrier → aᶜ ∈ L.carrier；hL_bot : ⊥ ∈ L.carrier；h
M_compl : ∀ {a : α}, a ∈ M.carrier → aᶜ ∈ M.carrier；hM_bot : ⊥ ∈ M.carrier。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mk_lt_mk {L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot) :
    mk L hL_compl hL_bot < mk M hM_compl hM_bot ↔ L < M := .rfl

/-- Copy of a Boolean subalgebra with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
/-
**BooleanSubalgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 `BooleanSubalgebra`。
形式化陈述：{α : Type u_2} → [inst : BooleanAlgebra α] → (L : BooleanSubalgebra α) → (
s : Set α) → s = ↑L → BooleanSubalgebra α
参数：L : BooleanSubalgebra α；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a Boolean subalgebra with a new `carrier` equal to the old one. Useful t
o fix
definitional equalities.
-/
protected def copy (L : BooleanSubalgebra α) (s : Set α) (hs : s = L) : BooleanSubalgebra α where
  toSublattice := L.toSublattice.copy s <| by subst hs; rfl
  compl_mem' := by subst hs; exact L.compl_mem'
  bot_mem' := by subst hs; exact L.bot_mem'

@[simp, norm_cast]
/-
**BooleanSubalgebra.coe_copy** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：coe_copy (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = s
参数：L : BooleanSubalgebra α；s : Set α；hs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_copy (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = s := rfl
/-
**BooleanSubalgebra.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：copy_eq (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = L
参数：L : BooleanSubalgebra α；s : Set α；hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
lemma copy_eq (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = L :=
  SetLike.coe_injective hs

/-- Two Boolean subalgebras are equal if they have the same elements. -/
/-
**BooleanSubalgebra.ext** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：ext : (forall a, a in L ↔ a in M) -> L = M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two Boolean subalgebras are equal if they have the same elements.
-/
lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext

/-- A Boolean subalgebra of a lattice inherits a bottom element. -/
/-
**BooleanSubalgebra.instBotCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instBotCoe : Bot L where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.bot_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊥ ∈ L

--- 原说明 ---
A Boolean subalgebra of a lattice inherits a bottom element.
-/
instance instBotCoe : Bot L where bot := ⟨⊥, bot_mem⟩

/-- A Boolean subalgebra of a lattice inherits a top element. -/
/-
**BooleanSubalgebra.instTopCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instTopCoe : Top L where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.top_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊤ ∈ L

--- 原说明 ---
A Boolean subalgebra of a lattice inherits a top element.
-/
instance instTopCoe : Top L where top := ⟨⊤, top_mem⟩

/-- A Boolean subalgebra of a lattice inherits a supremum. -/
/-
**BooleanSubalgebra.instSupCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instSupCoe : Max L where max a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean subalgebra of a lattice inherits a supremum.
-/
instance instSupCoe : Max L where max a b := ⟨a ⊔ b, L.supClosed a.2 b.2⟩

/-- A Boolean subalgebra of a lattice inherits an infimum. -/
/-
**BooleanSubalgebra.instInfCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instInfCoe : Min L where min a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean subalgebra of a lattice inherits an infimum.
-/
instance instInfCoe : Min L where min a b := ⟨a ⊓ b, L.infClosed a.2 b.2⟩

/-- A Boolean subalgebra of a lattice inherits a complement. -/
/-
**BooleanSubalgebra.instComplCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instComplCoe : Compl L where compl a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean subalgebra of a lattice inherits a complement.
-/
instance instComplCoe : Compl L where compl a := ⟨aᶜ, compl_mem a.2⟩

/-- A Boolean subalgebra of a lattice inherits a difference. -/
/-
**BooleanSubalgebra.instSDiffCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instSDiffCoe : SDiff L where sdiff a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean subalgebra of a lattice inherits a difference.
-/
instance instSDiffCoe : SDiff L where sdiff a b := ⟨a \ b, sdiff_mem a.2 b.2⟩

/-- A Boolean subalgebra of a lattice inherits a Heyting implication. -/
/-
**BooleanSubalgebra.instHImpCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instHImpCoe : HImp L where himp a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean subalgebra of a lattice inherits a Heyting implication.
-/
instance instHImpCoe : HImp L where himp a b := ⟨a ⇨ b, himp_mem a.2 b.2⟩
/-
**BooleanSubalgebra.val_bot** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α}, ↑⊥ =
 ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_bot : (⊥ : L) = (⊥ : α) := rfl
/-
**BooleanSubalgebra.val_top** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α}, ↑⊤ =
 ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_top : (⊤ : L) = (⊤ : α) := rfl
/-
**BooleanSubalgebra.val_sup** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: ↥L), ↑(a ⊔ b) = ↑a ⊔ ↑b
参数：a b : ↥L；a ⊔ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
/-
**BooleanSubalgebra.val_inf** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: ↥L), ↑(a ⊓ b) = ↑a ⊓ ↑b
参数：a b : ↥L；a ⊓ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
/-
**BooleanSubalgebra.val_compl** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a : 
↥L), ↑aᶜ = (↑a)ᶜ
参数：a : ↥L；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_compl (a : L) : aᶜ = (a : α)ᶜ := rfl
/-
**BooleanSubalgebra.val_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: ↥L), ↑(a \ b) = ↑a \ ↑b
参数：a b : ↥L；a \ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_sdiff (a b : L) : a \ b = (a : α) \ b := rfl
/-
**BooleanSubalgebra.val_himp** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: ↥L), ↑(a ⇨ b) = ↑a ⇨ ↑b
参数：a b : ↥L；a ⇨ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_himp (a b : L) : a ⇨ b = (a : α) ⇨ b := rfl
/-
**BooleanSubalgebra.mk_bot** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α}, ⟨⊥, 
⋯⟩ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.bot_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊥ ∈ L
-/
@[simp] lemma mk_bot : (⟨⊥, bot_mem⟩ : L) = ⊥ := rfl
/-
**BooleanSubalgebra.mk_top** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α}, ⟨⊤, 
⋯⟩ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.top_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊤ ∈ L
-/
@[simp] lemma mk_top : (⟨⊤, top_mem⟩ : L) = ⊤ := rfl
/-
**BooleanSubalgebra.mk_sup_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: α) (ha : a ∈ L) (hb : b ∈ L),   ⟨a, ha⟩ ⊔ ⟨b, hb⟩ = ⟨a ⊔ b, ⋯⟩
参数：a b : α；ha : a ∈ L；hb : b ∈ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_sup_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩ :=
  rfl
/-
**BooleanSubalgebra.mk_inf_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: α) (ha : a ∈ L) (hb : b ∈ L),   ⟨a, ha⟩ ⊓ ⟨b, hb⟩ = ⟨a ⊓ b, ⋯⟩
参数：a b : α；ha : a ∈ L；hb : b ∈ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_inf_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩ :=
  rfl
/-
**BooleanSubalgebra.compl_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a : 
α) (ha : a ∈ L), ⟨a, ha⟩ᶜ = ⟨aᶜ, ⋯⟩
参数：a : α；ha : a ∈ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compl_mk (a : α) (ha) : (⟨a, ha⟩ : L)ᶜ = ⟨aᶜ, compl_mem ha⟩ := rfl
/-
**BooleanSubalgebra.mk_sdiff_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: α) (ha : a ∈ L) (hb : b ∈ L),   ⟨a, ha⟩ \ ⟨b, hb⟩ = ⟨a \ b, ⋯⟩
参数：a b : α；ha : a ∈ L；hb : b ∈ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_sdiff_mk (a b : α) (ha hb) : (⟨a, ha⟩ \ ⟨b, hb⟩ : L) = ⟨a \ b, sdiff_mem ha hb⟩ :=
  rfl
/-
**BooleanSubalgebra.mk_himp_mk** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} (a b 
: α) (ha : a ∈ L) (hb : b ∈ L),   ⟨a, ha⟩ ⇨ ⟨b, hb⟩ = ⟨a ⇨ b, ⋯⟩
参数：a b : α；ha : a ∈ L；hb : b ∈ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_himp_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⇨ ⟨b, hb⟩ : L) = ⟨a ⇨ b, himp_mem ha hb⟩ :=
  rfl
/-
**BooleanSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : BooleanSubalgebra α) : PartialOrder L :=
  PartialOrder.lift _ Subtype.coe_injective

/-- A Boolean subalgebra of a lattice inherits a Boolean algebra structure. -/
/-
**BooleanSubalgebra.instBooleanAlgebraCoe** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSuba
lgebra`。
形式化陈述：instBooleanAlgebraCoe (L : BooleanSubalgebra α) : BooleanAlgebra L
参数：L : BooleanSubalgebra α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.val_sup`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α} (a b : ↥L), ↑(a ⊔ b) = ↑a ⊔ ↑b
· 使用定理 `BooleanSubalgebra.val_inf`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α} (a b : ↥L), ↑(a ⊓ b) = ↑a ⊓ ↑b
· 使用定理 `BooleanSubalgebra.val_top`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ↑⊤ = ⊤
· 使用定理 `BooleanSubalgebra.val_bot`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ↑⊥ = ⊥
· 使用定理 `BooleanSubalgebra.val_compl`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
{L : BooleanSubalgebra α} (a : ↥L), ↑aᶜ = (↑a)ᶜ
· 使用定理 `BooleanSubalgebra.val_sdiff`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
{L : BooleanSubalgebra α} (a b : ↥L), ↑(a \ b) = ↑a \ ↑b
· 使用定理 `BooleanSubalgebra.val_himp`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {
L : BooleanSubalgebra α} (a b : ↥L), ↑(a ⇨ b) = ↑a ⇨ ↑b

--- 原说明 ---
A Boolean subalgebra of a lattice inherits a Boolean algebra structure.
-/
instance instBooleanAlgebraCoe (L : BooleanSubalgebra α) : BooleanAlgebra L :=
  Subtype.coe_injective.booleanAlgebra _ .rfl .rfl val_sup val_inf val_top val_bot val_compl
    val_sdiff val_himp

/-- The natural lattice hom from a Boolean subalgebra to the original lattice. -/
/-
**BooleanSubalgebra.subtype** 是 Mathlib 中的一个定义，位于命名空间 `BooleanSubalgebra`。
形式化陈述：subtype (L : BooleanSubalgebra α) : BoundedLatticeHom L α where toFun
参数：L : BooleanSubalgebra α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.val_sup`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α} (a b : ↥L), ↑(a ⊔ b) = ↑a ⊔ ↑b
· 使用定理 `BooleanSubalgebra.val_inf`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α} (a b : ↥L), ↑(a ⊓ b) = ↑a ⊓ ↑b
· 使用定理 `BooleanSubalgebra.val_top`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ↑⊤ = ⊤
· 使用定理 `BooleanSubalgebra.val_bot`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ↑⊥ = ⊥

--- 原说明 ---
The natural lattice hom from a Boolean subalgebra to the original lattice.
-/
def subtype (L : BooleanSubalgebra α) : BoundedLatticeHom L α where
  toFun := ((↑) : L → α)
  map_bot' := L.val_bot
  map_top' := L.val_top
  map_sup' := val_sup
  map_inf' := val_inf
/-
**BooleanSubalgebra.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (L : BooleanSubalgebra α), ⇑L.s
ubtype = Subtype.val
参数：L : BooleanSubalgebra α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_subtype (L : BooleanSubalgebra α) : L.subtype = ((↑) : L → α) := rfl
/-
**BooleanSubalgebra.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：subtype_apply (L : BooleanSubalgebra α) (a : L) : L.subtype a = a
参数：L : BooleanSubalgebra α；a : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (L : BooleanSubalgebra α) (a : L) : L.subtype a = a := rfl
/-
**BooleanSubalgebra.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgeb
ra`。
形式化陈述：subtype_injective (L : BooleanSubalgebra α) : Injective subtype L
参数：L : BooleanSubalgebra α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective (L : BooleanSubalgebra α) : Injective <| subtype L := Subtype.coe_injective

/-- The inclusion homomorphism from a Boolean subalgebra `L` to a bigger Boolean subalgebra `M`. -/
/-
**BooleanSubalgebra.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `BooleanSubalgebra`。
形式化陈述：inclusion (h : L <= M) : BoundedLatticeHom L M where toFun
参数：h : L <= M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion homomorphism from a Boolean subalgebra `L` to a bigger Boolean sub
algebra `M`.
-/
def inclusion (h : L ≤ M) : BoundedLatticeHom L M where
  toFun := Set.inclusion h
  map_bot' := rfl
  map_top' := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
/-
**BooleanSubalgebra.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L M : BooleanSubalgebra α} (h 
: L ≤ M),   ⇑(BooleanSubalgebra.inclusion h) = Set.inclusion h
参数：h : L ≤ M；BooleanSubalgebra.inclusion h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_inclusion (h : L ≤ M) : inclusion h = Set.inclusion h := rfl
/-
**BooleanSubalgebra.inclusion_apply** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra
`。
形式化陈述：inclusion_apply (h : L <= M) (a : L) : inclusion h a = Set.inclusion h a
参数：h : L <= M；a : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclusion_apply (h : L ≤ M) (a : L) : inclusion h a = Set.inclusion h a := rfl
/-
**BooleanSubalgebra.inclusion_injective** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalg
ebra`。
形式化陈述：inclusion_injective (h : L <= M) : Injective inclusion h
参数：h : L <= M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
lemma inclusion_injective (h : L ≤ M) : Injective <| inclusion h := Set.inclusion_injective h
/-
**BooleanSubalgebra.inclusion_rfl** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (L : BooleanSubalgebra α),   Bo
oleanSubalgebra.inclusion ⋯ = BoundedLatticeHom.id ↥L
参数：L : BooleanSubalgebra α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[simp] lemma inclusion_rfl (L : BooleanSubalgebra α) : inclusion le_rfl = .id L := rfl
/-
**BooleanSubalgebra.subtype_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSub
algebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L M : BooleanSubalgebra α} (h 
: L ≤ M),   M.subtype.comp (BooleanSubalgebra.inclusion h) = L.subtype
参数：h : L ≤ M；BooleanSubalgebra.inclusion h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma subtype_comp_inclusion (h : L ≤ M) : M.subtype.comp (inclusion h) = L.subtype := rfl

/-- The maximum Boolean subalgebra of a lattice. -/
/-
**BooleanSubalgebra.instTop** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instTop : Top (BooleanSubalgebra α) where top.carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximum Boolean subalgebra of a lattice.
-/
instance instTop : Top (BooleanSubalgebra α) where
  top.carrier := univ
  top.bot_mem' := mem_univ _
  top.compl_mem' _ := mem_univ _
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

/-- The trivial Boolean subalgebra of a lattice. -/
/-
**BooleanSubalgebra.instBot** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instBot : Bot (BooleanSubalgebra α) where bot.carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial Boolean subalgebra of a lattice.
-/
instance instBot : Bot (BooleanSubalgebra α) where
  bot.carrier := {⊥, ⊤}
  bot.bot_mem' := by simp
  bot.compl_mem' := by simp
  bot.supClosed' _ := by simp
  bot.infClosed' _ := by simp

/-- The inf of two Boolean subalgebras is their intersection. -/
/-
**BooleanSubalgebra.instInf** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instInf : Min (BooleanSubalgebra α) where min L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two Boolean subalgebras is their intersection.
-/
instance instInf : Min (BooleanSubalgebra α) where
  min L M := { carrier := L ∩ M
               bot_mem' := ⟨bot_mem, bot_mem⟩
               compl_mem' := fun ha ↦ ⟨compl_mem ha.1, compl_mem ha.2⟩
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

/-- The inf of Boolean subalgebras is their intersection. -/
/-
**BooleanSubalgebra.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instInfSet : InfSet (BooleanSubalgebra α) where sInf S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of Boolean subalgebras is their intersection.
-/
instance instInfSet : InfSet (BooleanSubalgebra α) where
  sInf S := { carrier := ⋂ L ∈ S, L
              bot_mem' := mem_iInter₂.2 fun _ _ ↦ bot_mem
              compl_mem' := fun ha ↦ mem_iInter₂.2 fun L hL ↦ compl_mem <| mem_iInter₂.1 ha L hL
              supClosed' := supClosed_sInter <| forall_mem_range.2 fun L ↦ supClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.supClosed
              infClosed' := infClosed_sInter <| forall_mem_range.2 fun L ↦ infClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.infClosed }
/-
**BooleanSubalgebra.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
形式化陈述：instInhabited : Inhabited (BooleanSubalgebra α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (BooleanSubalgebra α) := ⟨⊥⟩

/-- The top Boolean subalgebra is isomorphic to the original Boolean algebra.

This is the Boolean subalgebra version of `Equiv.Set.univ α`. -/
/-
**BooleanSubalgebra.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BooleanSubalgebra`。
形式化陈述：topEquiv : (⊤ : BooleanSubalgebra α) ≃o α where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top Boolean subalgebra is isomorphic to the original Boolean algebra.

This is the Boolean subalgebra version of `Equiv.Set.univ α`.
-/
def topEquiv : (⊤ : BooleanSubalgebra α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := .rfl
/-
**BooleanSubalgebra.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α], ↑⊤ = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : (⊤ : BooleanSubalgebra α) = (univ : Set α) := rfl
/-
**BooleanSubalgebra.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α], ↑⊥ = {⊥, ⊤}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : BooleanSubalgebra α) = ({⊥, ⊤} : Set α) := rfl
/-
**BooleanSubalgebra.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (L M : BooleanSubalgebra α), ↑(
L ⊓ M) = ↑L ∩ ↑M
参数：L M : BooleanSubalgebra α；L ⊓ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (L M : BooleanSubalgebra α) : L ⊓ M = (L : Set α) ∩ M := rfl

@[simp, norm_cast]
/-
**BooleanSubalgebra.coe_sInf** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：coe_sInf (S : Set (BooleanSubalgebra α)) : sInf S = ⋂ L in S, (L : Set α)
参数：S : Set (BooleanSubalgebra α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sInf (S : Set (BooleanSubalgebra α)) : sInf S = ⋂ L ∈ S, (L : Set α) := rfl

@[simp, norm_cast]
/-
**BooleanSubalgebra.coe_iInf** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：coe_iInf (f : ι -> BooleanSubalgebra α) : ⨅ i, f i = ⋂ i, (f i : Set α)
参数：f : ι -> BooleanSubalgebra α。
该定理/引理给出了一组等式。
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
lemma coe_iInf (f : ι → BooleanSubalgebra α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by simp [iInf]
/-
**BooleanSubalgebra.coe_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α}, ↑L =
 Set.univ ↔ L = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BooleanSubalgebra.coe_top`：∀ {α : Type u_2} [inst : BooleanAlgebra α], ↑
⊤ = Set.univ
· 使用引理 `BooleanSubalgebra.coe_inj`：coe_inj : (L : Set α) = M ↔ L = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by rw [← coe_top, coe_inj]
/-
**BooleanSubalgebra.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a : α}, a ∈ ⊥ ↔ a = ⊥ ∨ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_bot : a ∈ (⊥ : BooleanSubalgebra α) ↔ a = ⊥ ∨ a = ⊤ := .rfl
/-
**BooleanSubalgebra.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a : α}, a ∈ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
@[simp] lemma mem_top : a ∈ (⊤ : BooleanSubalgebra α) := mem_univ _
/-
**BooleanSubalgebra.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L M : BooleanSubalgebra α} {a 
: α}, a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_inf : a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M := .rfl
/-
**BooleanSubalgebra.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a : α} {S : Set (BooleanSubalg
ebra α)}, a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L
参数：BooleanSubalgebra α。
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
@[simp] lemma mem_sInf {S : Set (BooleanSubalgebra α)} : a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L := by
  rw [← SetLike.mem_coe]; simp
/-
**BooleanSubalgebra.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : BooleanAlgebra α] {a : α} {f : ι →
 BooleanSubalgebra α},   a ∈ ⨅ i, f i ↔ ∀ (i : ι), a ∈ f i
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
· 使用引理 `BooleanSubalgebra.coe_iInf`：coe_iInf (f : ι -> BooleanSubalgebra α) : ⨅ 
i, f i = ⋂ i, (f i : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_iInf {f : ι → BooleanSubalgebra α} : a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe]; simp

/-- BooleanSubalgebras of a lattice form a complete lattice. -/
/-
**BooleanSubalgebra.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalg
ebra`。
形式化陈述：instCompleteLattice : CompleteLattice (BooleanSubalgebra α) where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.mem_top`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a
 : α}, a ∈ ⊤

--- 原说明 ---
BooleanSubalgebras of a lattice form a complete lattice.
-/
instance instCompleteLattice : CompleteLattice (BooleanSubalgebra α) where
  bot := ⊥
  bot_le _S _a := by aesop
  top := ⊤
  le_top _S a _ha := mem_top
  inf := (· ⊓ ·)
  le_inf _L _M _N hM hN _a ha := ⟨hM ha, hN ha⟩
  inf_le_left _L _M _a := And.left
  inf_le_right _L _M _a := And.right
  __ := completeLatticeOfInf (BooleanSubalgebra α)
      fun _s ↦ IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf
/-
**BooleanSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Subsingleton (BooleanSubalgebra α) := SetLike.coe_injective.subsingleton
/-
**BooleanSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `BooleanSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (BooleanSubalgebra α) := uniqueOfSubsingleton ⊤

/-- The preimage of a Boolean subalgebra along a bounded lattice homomorphism. -/
/-
**BooleanSubalgebra.comap** 是 Mathlib 中的一个定义，位于命名空间 `BooleanSubalgebra`。
形式化陈述：comap (f : BoundedLatticeHom α β) (L : BooleanSubalgebra β) : BooleanSubal
gebra α where carrier
参数：f : BoundedLatticeHom α β；L : BooleanSubalgebra β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a Boolean subalgebra along a bounded lattice homomorphism.
-/
def comap (f : BoundedLatticeHom α β) (L : BooleanSubalgebra β) : BooleanSubalgebra α where
  carrier := f ⁻¹' L
  bot_mem' := by simp
  compl_mem' := by simp [map_compl']
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

@[simp, norm_cast]
/-
**BooleanSubalgebra.coe_comap** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：coe_comap (L : BooleanSubalgebra β) (f : BoundedLatticeHom α β) : L.comap 
f = f ⁻¹' L
参数：L : BooleanSubalgebra β；f : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comap (L : BooleanSubalgebra β) (f : BoundedLatticeHom α β) : L.comap f = f ⁻¹' L := rfl
/-
**BooleanSubalgebra.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : BooleanAlgebra α] [inst_1 : Boolea
nAlgebra β] {f : BoundedLatticeHom α β}   {a : α} {L : BooleanSubalgebra β}, a ∈
 BooleanSubalgebra.comap f L ↔ f a ∈ L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_comap {L : BooleanSubalgebra β} : a ∈ L.comap f ↔ f a ∈ L := .rfl
/-
**BooleanSubalgebra.comap_mono** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：comap_mono : Monotone (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
lemma comap_mono : Monotone (comap f) := fun _ _ ↦ preimage_mono
/-
**BooleanSubalgebra.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (L : BooleanSubalgebra α),   Bo
oleanSubalgebra.comap (BoundedLatticeHom.id α) L = L
参数：L : BooleanSubalgebra α；BoundedLatticeHom.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_id (L : BooleanSubalgebra α) : L.comap (BoundedLatticeHom.id _) = L := rfl
/-
**BooleanSubalgebra.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : BooleanAlgebra α] [
inst_1 : BooleanAlgebra β]   [inst_2 : BooleanAlgebra γ] (L : BooleanSubalgebra 
γ) (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β),   BooleanSubalgebra.
comap f (BooleanSubalgebra.comap g L) = BooleanSubalgebra.comap (g.comp f) L
参数：L : BooleanSubalgebra γ；g : BoundedLatticeHom β γ；f : BoundedLatticeHom α β；B
ooleanSubalgebra.comap g L；g.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_comap (L : BooleanSubalgebra γ) (g : BoundedLatticeHom β γ)
    (f : BoundedLatticeHom α β) : (L.comap g).comap f = L.comap (g.comp f) := rfl

/-- The image of a Boolean subalgebra along a monoid homomorphism is a Boolean subalgebra. -/
/-
**BooleanSubalgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `BooleanSubalgebra`。
形式化陈述：map (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α) : BooleanSubalge
bra β where carrier
参数：f : BoundedLatticeHom α β；L : BooleanSubalgebra α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a Boolean subalgebra along a monoid homomorphism is a Boolean subal
gebra.
-/
def map (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α) : BooleanSubalgebra β where
  carrier := f '' L
  bot_mem' := ⟨⊥, by simp⟩
  compl_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨aᶜ, by simpa [map_compl']⟩
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
/-
**BooleanSubalgebra.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : BooleanAlgebra α] [inst_1 : Boolea
nAlgebra β] (f : BoundedLatticeHom α β)   (L : BooleanSubalgebra α), ↑(BooleanSu
balgebra.map f L) = ⇑f '' ↑L
参数：f : BoundedLatticeHom α β；L : BooleanSubalgebra α；BooleanSubalgebra.map f L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_map (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α) :
    (L.map f : Set β) = f '' L := rfl
/-
**BooleanSubalgebra.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : BooleanAlgebra α] [inst_1 : Boolea
nAlgebra β] {L : BooleanSubalgebra α}   {f : BoundedLatticeHom α β} {b : β}, b ∈
 BooleanSubalgebra.map f L ↔ ∃ a ∈ L, f a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_map {b : β} : b ∈ L.map f ↔ ∃ a ∈ L, f a = b := .rfl
/-
**BooleanSubalgebra.mem_map_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`
。
形式化陈述：mem_map_of_mem (f : BoundedLatticeHom α β) {a : α} : a in L -> f a in L.ma
p f
参数：f : BoundedLatticeHom α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma mem_map_of_mem (f : BoundedLatticeHom α β) {a : α} : a ∈ L → f a ∈ L.map f :=
  mem_image_of_mem f
/-
**BooleanSubalgebra.apply_coe_mem_map** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgeb
ra`。
形式化陈述：apply_coe_mem_map (f : BoundedLatticeHom α β) (a : L) : f a in L.map f
参数：f : BoundedLatticeHom α β；a : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BooleanSubalgebra.mem_map_of_mem`：mem_map_of_mem (f : BoundedLatticeHom 
α β) {a : α} : a in L -> f a in L.map f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma apply_coe_mem_map (f : BoundedLatticeHom α β) (a : L) : f a ∈ L.map f :=
  mem_map_of_mem f a.prop
/-
**BooleanSubalgebra.map_mono** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：map_mono : Monotone (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma map_mono : Monotone (map f) := fun _ _ ↦ image_mono
/-
**BooleanSubalgebra.map_id** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α},   Bo
oleanSubalgebra.map (BoundedLatticeHom.id α) L = L
参数：BoundedLatticeHom.id α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
@[simp] lemma map_id : L.map (.id α) = L := SetLike.coe_injective <| image_id _
/-
**BooleanSubalgebra.map_map** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : BooleanAlgebra α] [
inst_1 : BooleanAlgebra β]   [inst_2 : BooleanAlgebra γ] {L : BooleanSubalgebra 
α} (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β),   BooleanSubalgebra.
map g (BooleanSubalgebra.map f L) = BooleanSubalgebra.map (g.comp f) L
参数：g : BoundedLatticeHom β γ；f : BoundedLatticeHom α β；BooleanSubalgebra.map f L
；g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
@[simp] lemma map_map (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (L.map f).map g = L.map (g.comp f) := SetLike.coe_injective <| image_image _ _ _
/-
**BooleanSubalgebra.mem_map_equiv** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：mem_map_equiv {f : α ≃o β} {a : β} : a in L.map f ↔ f.symm a in L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
lemma mem_map_equiv {f : α ≃o β} {a : β} : a ∈ L.map f ↔ f.symm a ∈ L := Set.mem_image_equiv
/-
**BooleanSubalgebra.apply_mem_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgeb
ra`。
形式化陈述：apply_mem_map_iff (hf : Injective f) : f a in L.map f ↔ a in L
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
lemma apply_mem_map_iff (hf : Injective f) : f a ∈ L.map f ↔ a ∈ L := hf.mem_set_image
/-
**BooleanSubalgebra.map_equiv_eq_comap_symm** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSu
balgebra`。
形式化陈述：map_equiv_eq_comap_symm (f : α ≃o β) (L : BooleanSubalgebra α) : L.map f =
 L.comap (f.symm : BoundedLatticeHom β α)
参数：f : α ≃o β；L : BooleanSubalgebra α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `OrderIsoClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β
]   [inst_3 : BoundedOrder α…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `LatticeHom.map_inf'`：∀ {α : Type u_6} {β : Type u_7} [inst : Lattice α] 
[inst_1 : Lattice β] (self : LatticeHom α β) (a b : α),   self.toFun (a ⊓ b) = s
elf.toFun…
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
lemma map_equiv_eq_comap_symm (f : α ≃o β) (L : BooleanSubalgebra α) :
    L.map f = L.comap (f.symm : BoundedLatticeHom β α) :=
  SetLike.coe_injective <| f.toEquiv.image_eq_preimage_symm L
/-
**BooleanSubalgebra.comap_equiv_eq_map_symm** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSu
balgebra`。
形式化陈述：comap_equiv_eq_map_symm (f : β ≃o α) (L : BooleanSubalgebra α) : L.comap f
 = L.map (f.symm : BoundedLatticeHom α β)
参数：f : β ≃o α；L : BooleanSubalgebra α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIsoClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β
]   [inst_3 : BoundedOrder α…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `LatticeHom.map_inf'`：∀ {α : Type u_6} {β : Type u_7} [inst : Lattice α] 
[inst_1 : Lattice β] (self : LatticeHom α β) (a b : α),   self.toFun (a ⊓ b) = s
elf.toFun…
· 使用引理 `BooleanSubalgebra.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : 
α ≃o β) (L : BooleanSubalgebra α) : L.map f = L.comap (f.symm : BoundedLatticeHo
m β α)
-/
lemma comap_equiv_eq_map_symm (f : β ≃o α) (L : BooleanSubalgebra α) :
    L.comap f = L.map (f.symm : BoundedLatticeHom α β) := (map_equiv_eq_comap_symm f.symm L).symm
/-
**BooleanSubalgebra.map_symm_eq_iff_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSub
algebra`。
形式化陈述：map_symm_eq_iff_eq_map {M : BooleanSubalgebra β} {e : β ≃o α} : L.map ↑e.s
ymm = M ↔ L = M.map ↑e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIsoClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β
]   [inst_3 : BoundedOrder α…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `LatticeHom.map_inf'`：∀ {α : Type u_6} {β : Type u_7} [inst : Lattice α] 
[inst_1 : Lattice β] (self : LatticeHom α β) (a b : α),   self.toFun (a ⊓ b) = s
elf.toFun…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_image_iff_symm_image_eq`：eq_image_iff_symm_image_eq {α β} (e : 
α ≃ β) (s : Set α) (t : Set β) : t = e '' s ↔ e.symm '' t = s
-/
lemma map_symm_eq_iff_eq_map {M : BooleanSubalgebra β} {e : β ≃o α} :
    L.map ↑e.symm = M ↔ L = M.map ↑e := by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm
/-
**BooleanSubalgebra.map_le_iff_le_comap** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalg
ebra`。
形式化陈述：map_le_iff_le_comap {f : BoundedLatticeHom α β} {M : BooleanSubalgebra β} 
: L.map f <= M ↔ L <= M.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
lemma map_le_iff_le_comap {f : BoundedLatticeHom α β} {M : BooleanSubalgebra β} :
    L.map f ≤ M ↔ L ≤ M.comap f := image_subset_iff
/-
**BooleanSubalgebra.gc_map_comap** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：gc_map_comap (f : BoundedLatticeHom α β) : GaloisConnection (map f) (comap
 f)
参数：f : BoundedLatticeHom α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BooleanSubalgebra.map_le_iff_le_comap`：map_le_iff_le_comap {f : BoundedL
atticeHom α β} {M : BooleanSubalgebra β} : L.map f <= M ↔ L <= M.comap f
-/
lemma gc_map_comap (f : BoundedLatticeHom α β) : GaloisConnection (map f) (comap f) :=
  fun _ _ ↦ map_le_iff_le_comap
/-
**BooleanSubalgebra.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : BooleanAlgebra α] [inst_1 : Boolea
nAlgebra β] (f : BoundedLatticeHom α β),   BooleanSubalgebra.map f ⊥ = ⊥
参数：f : BoundedLatticeHom α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `BooleanSubalgebra.gc_map_comap`：gc_map_comap (f : BoundedLatticeHom α β)
 : GaloisConnection (map f) (comap f)
-/
@[simp] lemma map_bot (f : BoundedLatticeHom α β) : (⊥ : BooleanSubalgebra α).map f = ⊥ :=
  (gc_map_comap f).l_bot
/-
**BooleanSubalgebra.map_sup** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：map_sup (f : BoundedLatticeHom α β) (L M : BooleanSubalgebra α) : (L ⊔ M).
map f = L.map f ⊔ M.map f
参数：f : BoundedLatticeHom α β；L M : BooleanSubalgebra α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `BooleanSubalgebra.gc_map_comap`：gc_map_comap (f : BoundedLatticeHom α β)
 : GaloisConnection (map f) (comap f)
-/
lemma map_sup (f : BoundedLatticeHom α β) (L M : BooleanSubalgebra α) :
    (L ⊔ M).map f = L.map f ⊔ M.map f := (gc_map_comap f).l_sup
/-
**BooleanSubalgebra.map_iSup** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：map_iSup (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra α) : (⨆ i
, L i).map f = ⨆ i, (L i).map f
参数：f : BoundedLatticeHom α β；L : ι -> BooleanSubalgebra α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用引理 `BooleanSubalgebra.gc_map_comap`：gc_map_comap (f : BoundedLatticeHom α β)
 : GaloisConnection (map f) (comap f)
-/
lemma map_iSup (f : BoundedLatticeHom α β) (L : ι → BooleanSubalgebra α) :
    (⨆ i, L i).map f = ⨆ i, (L i).map f := (gc_map_comap f).l_iSup
/-
**BooleanSubalgebra.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : BooleanAlgebra α] [inst_1 : Boolea
nAlgebra β] (f : BoundedLatticeHom α β),   BooleanSubalgebra.comap f ⊤ = ⊤
参数：f : BoundedLatticeHom α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用引理 `BooleanSubalgebra.gc_map_comap`：gc_map_comap (f : BoundedLatticeHom α β)
 : GaloisConnection (map f) (comap f)
-/
@[simp] lemma comap_top (f : BoundedLatticeHom α β) : (⊤ : BooleanSubalgebra β).comap f = ⊤ :=
  (gc_map_comap f).u_top
/-
**BooleanSubalgebra.comap_inf** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：comap_inf (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) : (L ⊓ M
).comap f = L.comap f ⊓ M.comap f
参数：L M : BooleanSubalgebra β；f : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用引理 `BooleanSubalgebra.gc_map_comap`：gc_map_comap (f : BoundedLatticeHom α β)
 : GaloisConnection (map f) (comap f)
-/
lemma comap_inf (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) :
    (L ⊓ M).comap f = L.comap f ⊓ M.comap f := (gc_map_comap f).u_inf
/-
**BooleanSubalgebra.comap_iInf** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：comap_iInf (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra β) : (⨅
 i, L i).comap f = ⨅ i, (L i).comap f
参数：f : BoundedLatticeHom α β；L : ι -> BooleanSubalgebra β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用引理 `BooleanSubalgebra.gc_map_comap`：gc_map_comap (f : BoundedLatticeHom α β)
 : GaloisConnection (map f) (comap f)
-/
lemma comap_iInf (f : BoundedLatticeHom α β) (L : ι → BooleanSubalgebra β) :
    (⨅ i, L i).comap f = ⨅ i, (L i).comap f := (gc_map_comap f).u_iInf
/-
**BooleanSubalgebra.map_inf_le** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：map_inf_le (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) : map f
 (L ⊓ M) <= map f L ⊓ map f M
参数：L M : BooleanSubalgebra α；f : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用引理 `BooleanSubalgebra.map_mono`：map_mono : Monotone (map f)
-/
lemma map_inf_le (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) :
    map f (L ⊓ M) ≤ map f L ⊓ map f M := map_mono.map_inf_le _ _
/-
**BooleanSubalgebra.le_comap_sup** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：le_comap_sup (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) : com
ap f L ⊔ comap f M <= comap f (L ⊔ M)
参数：L M : BooleanSubalgebra β；f : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用引理 `BooleanSubalgebra.comap_mono`：comap_mono : Monotone (comap f)
-/
lemma le_comap_sup (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) :
    comap f L ⊔ comap f M ≤ comap f (L ⊔ M) := comap_mono.le_map_sup _ _
/-
**BooleanSubalgebra.le_comap_iSup** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：le_comap_iSup (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra β) :
 ⨆ i, (L i).comap f <= (⨆ i, L i).comap f
参数：f : BoundedLatticeHom α β；L : ι -> BooleanSubalgebra β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
· 使用引理 `BooleanSubalgebra.comap_mono`：comap_mono : Monotone (comap f)
-/
lemma le_comap_iSup (f : BoundedLatticeHom α β) (L : ι → BooleanSubalgebra β) :
    ⨆ i, (L i).comap f ≤ (⨆ i, L i).comap f := comap_mono.le_map_iSup
/-
**BooleanSubalgebra.map_inf** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：map_inf (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) (hf : Inje
ctive f) : map f (L ⊓ M) = map f L ⊓ map f M
参数：L M : BooleanSubalgebra α；f : BoundedLatticeHom α β；hf : Injective f。
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
lemma map_inf (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) (hf : Injective f) :
    map f (L ⊓ M) = map f L ⊓ map f M := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]
/-
**BooleanSubalgebra.map_top** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：map_top (f : BoundedLatticeHom α β) (h : Surjective f) : BooleanSubalgebra
.map f ⊤ = ⊤
参数：f : BoundedLatticeHom α β；h : Surjective f。
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
lemma map_top (f : BoundedLatticeHom α β) (h : Surjective f) : BooleanSubalgebra.map f ⊤ = ⊤ :=
  SetLike.coe_injective <| by simp [h.range_eq]

/-- The minimum Boolean subalgebra containing a given set. -/
/-
**BooleanSubalgebra.closure** 是 Mathlib 中的一个定义，位于命名空间 `BooleanSubalgebra`。
形式化陈述：closure (s : Set α) : BooleanSubalgebra α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimum Boolean subalgebra containing a given set.
-/
def closure (s : Set α) : BooleanSubalgebra α := sInf {L | s ⊆ L}

variable {s : Set α}
/-
**BooleanSubalgebra.mem_closure** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：mem_closure {x : α} : x in closure s ↔ forall ⦃L : BooleanSubalgebra α⦄, s
 subseteq L -> x in L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanSubalgebra.mem_sInf`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {
a : α} {S : Set (BooleanSubalgebra α)}, a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L
-/
lemma mem_closure {x : α} : x ∈ closure s ↔ ∀ ⦃L : BooleanSubalgebra α⦄, s ⊆ L → x ∈ L := mem_sInf

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**BooleanSubalgebra.subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`
。
形式化陈述：subset_closure : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `BooleanSubalgebra.mem_closure`：mem_closure {x : α} : x in closure s ↔ fo
rall ⦃L : BooleanSubalgebra α⦄, s subseteq L -> x in L
-/
lemma subset_closure : s ⊆ closure s := fun _ hx ↦ mem_closure.2 fun _ hK ↦ hK hx

@[aesop 80% (rule_sets := [SetLike])]
/-
**BooleanSubalgebra.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalge
bra`。
形式化陈述：mem_closure_of_mem {s : Set α} {x : α} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BooleanSubalgebra.subset_closure`：subset_closure : s subseteq closure s
-/
theorem mem_closure_of_mem {s : Set α} {x : α} (hx : x ∈ s) : x ∈ closure s := subset_closure hx
/-
**BooleanSubalgebra.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L : BooleanSubalgebra α} {s : 
Set α},   BooleanSubalgebra.closure s ≤ L ↔ s ⊆ ↑L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `BooleanSubalgebra.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
@[simp] lemma closure_le : closure s ≤ L ↔ s ⊆ L := ⟨subset_closure.trans, fun h ↦ sInf_le h⟩
/-
**BooleanSubalgebra.closure_mono** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：closure_mono (hst : s subseteq t) : closure s <= closure t
参数：hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma closure_mono (hst : s ⊆ t) : closure s ≤ closure t := sInf_le_sInf fun _L ↦ hst.trans
/-
**BooleanSubalgebra.latticeClosure_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Boo
leanSubalgebra`。
形式化陈述：latticeClosure_subset_closure : latticeClosure s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `latticeClosure_min`：latticeClosure_min : s subseteq t -> IsSublattice t 
-> latticeClosure s subseteq t
· 使用引理 `BooleanSubalgebra.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Sublattice.isSublattice`：∀ {α : Type u_2} [inst : Lattice α] (L : Sublat
tice α), IsSublattice ↑L
-/
lemma latticeClosure_subset_closure : latticeClosure s ⊆ closure s :=
  latticeClosure_min subset_closure (closure s).isSublattice
/-
**BooleanSubalgebra.closure_latticeClosure** 是 Mathlib 中的一个定理，位于命名空间 `BooleanSub
algebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] (s : Set α),   BooleanSubalgebr
a.closure (latticeClosure s) = BooleanSubalgebra.closure s
参数：s : Set α；latticeClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BooleanSubalgebra.closure_le`：∀ {α : Type u_2} [inst : BooleanAlgebra α]
 {L : BooleanSubalgebra α} {s : Set α},   BooleanSubalgebra.closure s ≤ L ↔ s ⊆ 
↑L
· 使用引理 `BooleanSubalgebra.latticeClosure_subset_closure`：latticeClosure_subset_c
losure : latticeClosure s subseteq closure s
· 使用引理 `BooleanSubalgebra.closure_mono`：closure_mono (hst : s subseteq t) : clos
ure s <= closure t
· 使用定理 `subset_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, 
s ⊆ latticeClosure s
-/
@[simp] lemma closure_latticeClosure (s : Set α) : closure (latticeClosure s) = closure s :=
  le_antisymm (closure_le.2 latticeClosure_subset_closure) (closure_mono subset_latticeClosure)

/-- An induction principle for closure membership. If `p` holds for `⊥` and all elements of `s`, and
is preserved under suprema and complement, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim]
/-
**BooleanSubalgebra.closure_bot_sup_induction** 是 Mathlib 中的一个引理，位于命名空间 `Boolean
Subalgebra`。
形式化陈述：closure_bot_sup_induction {p : forall g in closure s, Prop} (mem : forall 
x hx, p x (subset_closure hx)) (bot : p ⊥ bot_mem) (sup : forall x hx y hy, p x 
hx -> p y hy -> p (x ⊔ y) (supClosed _ hx hy)) (compl : forall x hx, p x hx -> p
 xᶜ (compl_mem hx)) {x} (hx : x in closure s) : p x hx
参数：mem : forall x hx, p x (subset_closure hx)；bot : p ⊥ bot_mem；sup : forall x h
x y hy, p x hx -> p y hy -> p (x ⊔ y) (supClosed _ hx hy)；compl : forall x hx, p
 x hx -> p xᶜ (compl_mem hx)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BooleanSubalgebra.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `BooleanSubalgebra.bot_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊥ ∈ L
· 使用定理 `BooleanSubalgebra.supClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), SupClosed ↑L
· 使用引理 `BooleanSubalgebra.compl_mem`：compl_mem (ha : a in L) : aᶜ in L
· 使用定理 `BooleanSubalgebra.infClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), InfClosed ↑L
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `compl_sup`：compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BooleanSubalgebra.closure_le`：∀ {α : Type u_2} [inst : BooleanAlgebra α]
 {L : BooleanSubalgebra α} {s : Set α},   BooleanSubalgebra.closure s ≤ L ↔ s ⊆ 
↑L

--- 原说明 ---
An induction principle for closure membership. If `p` holds for `⊥` and all elem
ents of `s`, and
is preserved under suprema and complement, then `p` holds for all elements of th
e closure of `s`.
-/
lemma closure_bot_sup_induction {p : ∀ g ∈ closure s, Prop} (mem : ∀ x hx, p x (subset_closure hx))
    (bot : p ⊥ bot_mem)
    (sup : ∀ x hx y hy, p x hx → p y hy → p (x ⊔ y) (supClosed _ hx hy))
    (compl : ∀ x hx, p x hx → p xᶜ (compl_mem hx)) {x} (hx : x ∈ closure s) : p x hx :=
  have inf ⦃x hx y hy⦄ (hx' : p x hx) (hy' : p y hy) : p (x ⊓ y) (infClosed _ hx hy) := by
    simpa using compl _ _ <| sup _ _ _ _ (compl _ _ hx') (compl _ _ hy')
  let L : BooleanSubalgebra α :=
    { carrier := { x | ∃ hx, p x hx }
      supClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ ↦ ⟨_, sup _ _ _ _ ha hb⟩
      infClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ ↦ ⟨_, inf ha hb⟩
      bot_mem' := ⟨_, bot⟩
      compl_mem' := fun ⟨_, hb⟩ ↦ ⟨_, compl _ _ hb⟩ }
  closure_le (L := L).mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

section sdiff_sup

variable (isSublattice : IsSublattice s) (bot_mem : ⊥ ∈ s) (top_mem : ⊤ ∈ s)
include isSublattice bot_mem top_mem

/-
**BooleanSubalgebra.mem_closure_iff_sup_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Boolean
Subalgebra`。
形式化陈述：mem_closure_iff_sup_sdiff {a : α} : a in closure s ↔ exists t : Finset (s 
× s), a = t.sup fun x => x.1.1 \ x.2.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BooleanSubalgebra.closure_bot_sup_induction`：closure_bot_sup_induction {
p : forall g in closure s, Prop} (mem : forall x hx, p x (subset_closure hx)) (b
ot : p ⊥ bot_mem) (sup : forall x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `compl_sup`：compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Finset.sup_mem`：sup_mem (s : Set α) (w₁ : ⊥ in s) (w₂ : forallᵉ (x in s)
 (y in s), x ⊔ y in s) {ι : Type*} (t : Finset ι) (p : ι -> α) (h : forall i in 
t, p…
· 使用引理 `BooleanSubalgebra.subset_closure`：subset_closure : s subseteq closure s
（共 32 条，此处仅展示前 30 条）
-/
theorem mem_closure_iff_sup_sdiff {a : α} :
    a ∈ closure s ↔ ∃ t : Finset (s × s), a = t.sup fun x ↦ x.1.1 \ x.2.1 := by
  classical
  refine ⟨closure_bot_sup_induction
    (fun x h ↦ ⟨{(⟨x, h⟩, ⟨⊥, bot_mem⟩)}, by simp⟩) ⟨∅, by simp⟩ ?_ ?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact t.sup_mem _ (subset_closure bot_mem) (fun _ h _ ↦ sup_mem h) _
      fun x hx ↦ sdiff_mem (subset_closure x.1.2) (subset_closure x.2.2)
  · rintro _ - _ - ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
    exact ⟨t₁ ∪ t₂, by rw [Finset.sup_union]⟩
  rintro x - ⟨t, rfl⟩
  refine t.induction ⟨{(⟨⊤, top_mem⟩, ⟨⊥, bot_mem⟩)}, by simp⟩ fun ⟨x, y⟩ t _ ⟨tc, eq⟩ ↦ ?_
  simp_rw [Finset.sup_insert, compl_sup, eq]
  refine tc.induction ⟨∅, by simp⟩ fun ⟨z, w⟩ tc _ ⟨t, eq⟩ ↦ ?_
  simp_rw [Finset.sup_insert, inf_sup_left, eq]
  use {(z, ⟨_, isSublattice.supClosed x.2 w.2⟩), (⟨_, isSublattice.infClosed y.2 z.2⟩, w)} ∪ t
  simp_rw [Finset.sup_union, Finset.sup_insert, Finset.sup_singleton, _root_.sdiff_eq,
    compl_sup, inf_left_comm z.1, compl_inf, compl_compl, inf_sup_right, inf_assoc]
/-
**BooleanSubalgebra.closure_sdiff_sup_induction** 是 Mathlib 中的一个定理，位于命名空间 `Boole
anSubalgebra`。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {s : Set α},   IsSublattice s →
     ⊥ ∈ s →       ⊤ ∈ s →         ∀ {p : (g : α) → g ∈ BooleanSubalgebra.closur
e s → Prop},           (∀ (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s), p (x \ y) ⋯
) →             (∀ (x : α) (hx : x ∈ BooleanSubalgebra.closure s) (y : α) (hy : 
y ∈ BooleanSubalgebra.closure s),                 p x hx → p y hy → p (x ⊔ y) ⋯)
 →               ∀ (x : α) (hx : x ∈ BooleanSubalgebra.closure s), p x hx
参数：g : α；∀ (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s), p (x \ y) ⋯；∀ (x : α) (hx 
: x ∈ BooleanSubalgebra.closure s) (y : α) (hy : y ∈ BooleanSubalgebra.closure s
),                 p x hx → p y hy → p (x ⊔ y) ⋯；x : α；hx : x ∈ BooleanSubalgebr
a.closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BooleanSubalgebra.sdiff_mem`：sdiff_mem (ha : a in L) (hb : b in L) : a \
 b in L
· 使用引理 `BooleanSubalgebra.subset_closure`：subset_closure : s subseteq closure s
· 使用引理 `BooleanSubalgebra.sup_mem`：sup_mem (ha : a in L) (hb : b in L) : a ⊔ b i
n L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BooleanSubalgebra.mem_closure_iff_sup_sdiff`：mem_closure_iff_sup_sdiff {
a : α} : a in closure s ↔ exists t : Finset (s × s), a = t.sup fun x => x.1.1 \ 
x.2.1
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[elab_as_elim] theorem closure_sdiff_sup_induction {p : ∀ g ∈ closure s, Prop}
    (sdiff : ∀ x hx y hy, p (x \ y) (sdiff_mem (subset_closure hx) (subset_closure hy)))
    (sup : ∀ x hx y hy, p x hx → p y hy → p (x ⊔ y) (sup_mem hx hy))
    (x) (hx : x ∈ closure s) : p x hx := by
  obtain ⟨t, rfl⟩ := (mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mp hx
  revert hx
  classical
  refine t.induction (by simpa using sdiff _ bot_mem _ bot_mem) fun x t _ ih hxt ↦ ?_
  simp only [Finset.sup_insert] at hxt ⊢
  exact sup _ _ _ ((mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mpr ⟨_, rfl⟩)
    (sdiff _ x.1.2 _ x.2.2) (ih _)

end sdiff_sup

end BooleanAlgebra

section CompleteBooleanAlgebra
variable [CompleteBooleanAlgebra α] {L : BooleanSubalgebra α} {f : ι → α} {s : Set α}

/-
**BooleanSubalgebra.iSup_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：iSup_mem [Finite ι] (hf : forall i, f i in L) : ⨆ i, f i in L
参数：hf : forall i, f i in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.iSup_mem`：SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hb
ot : ⊥ in s) (hf : forall i, f i in s) : ⨆ i, f i in s
· 使用定理 `BooleanSubalgebra.supClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), SupClosed ↑L
· 使用定理 `BooleanSubalgebra.bot_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊥ ∈ L
-/
lemma iSup_mem [Finite ι] (hf : ∀ i, f i ∈ L) : ⨆ i, f i ∈ L := L.supClosed.iSup_mem bot_mem hf
/-
**BooleanSubalgebra.iInf_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：iInf_mem [Finite ι] (hf : forall i, f i in L) : ⨅ i, f i in L
参数：hf : forall i, f i in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfClosed.iInf_mem`：∀ {ι : Sort u_1} {α : Type u_3} [inst : CompleteLatt
ice α] {f : ι → α} {s : Set α} [Finite ι],   InfClosed s → ⊤ ∈ s → (∀ (i : ι), f
 i ∈ s) …
· 使用定理 `BooleanSubalgebra.infClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), InfClosed ↑L
· 使用定理 `BooleanSubalgebra.top_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊤ ∈ L
-/
lemma iInf_mem [Finite ι] (hf : ∀ i, f i ∈ L) : ⨅ i, f i ∈ L := L.infClosed.iInf_mem top_mem hf
/-
**BooleanSubalgebra.sSup_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：sSup_mem (hs : s.Finite) (hsL : s subseteq L) : sSup s in L
参数：hs : s.Finite；hsL : s subseteq L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.sSup_mem`：SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite
) (hbot : ⊥ in s) (hts : t subseteq s) : sSup t in s
· 使用定理 `BooleanSubalgebra.supClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), SupClosed ↑L
· 使用定理 `BooleanSubalgebra.bot_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊥ ∈ L
-/
lemma sSup_mem (hs : s.Finite) (hsL : s ⊆ L) : sSup s ∈ L := L.supClosed.sSup_mem hs bot_mem hsL
/-
**BooleanSubalgebra.sInf_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：sInf_mem (hs : s.Finite) (hsL : s subseteq L) : sInf s in L
参数：hs : s.Finite；hsL : s subseteq L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfClosed.sInf_mem`：∀ {α : Type u_3} [inst : CompleteLattice α] {s t : S
et α}, InfClosed s → t.Finite → ⊤ ∈ s → t ⊆ s → sInf t ∈ s
· 使用定理 `BooleanSubalgebra.infClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), InfClosed ↑L
· 使用定理 `BooleanSubalgebra.top_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊤ ∈ L
-/
lemma sInf_mem (hs : s.Finite) (hsL : s ⊆ L) : sInf s ∈ L := L.infClosed.sInf_mem hs top_mem hsL
/-
**BooleanSubalgebra.biSup_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：biSup_mem {ι : Type*} {t : Set ι} {f : ι -> α} (ht : t.Finite) (hf : foral
l i in t, f i in L) : ⨆ i in t, f i in L
参数：ht : t.Finite；hf : forall i in t, f i in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.biSup_mem`：SupClosed.biSup_mem {ι : Type*} {t : Set ι} {f : ι 
-> α} (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ in s) (hf : forall i in t, f 
i in s) :…
· 使用定理 `BooleanSubalgebra.supClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), SupClosed ↑L
· 使用定理 `BooleanSubalgebra.bot_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊥ ∈ L
-/
lemma biSup_mem {ι : Type*} {t : Set ι} {f : ι → α} (ht : t.Finite) (hf : ∀ i ∈ t, f i ∈ L) :
    ⨆ i ∈ t, f i ∈ L := L.supClosed.biSup_mem ht bot_mem hf
/-
**BooleanSubalgebra.biInf_mem** 是 Mathlib 中的一个引理，位于命名空间 `BooleanSubalgebra`。
形式化陈述：biInf_mem {ι : Type*} {t : Set ι} {f : ι -> α} (ht : t.Finite) (hf : foral
l i in t, f i in L) : ⨅ i in t, f i in L
参数：ht : t.Finite；hf : forall i in t, f i in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfClosed.biInf_mem`：∀ {α : Type u_3} [inst : CompleteLattice α] {s : Se
t α} {ι : Type u_5} {t : Set ι} {f : ι → α},   InfClosed s → t.Finite → ⊤ ∈ s → 
(∀ i ∈ t,…
· 使用定理 `BooleanSubalgebra.infClosed`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
(L : BooleanSubalgebra α), InfClosed ↑L
· 使用定理 `BooleanSubalgebra.top_mem`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {L
 : BooleanSubalgebra α}, ⊤ ∈ L
-/
lemma biInf_mem {ι : Type*} {t : Set ι} {f : ι → α} (ht : t.Finite) (hf : ∀ i ∈ t, f i ∈ L) :
    ⨅ i ∈ t, f i ∈ L := L.infClosed.biInf_mem ht top_mem hf

end CompleteBooleanAlgebra
end BooleanSubalgebra

