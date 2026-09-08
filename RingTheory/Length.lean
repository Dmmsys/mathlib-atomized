/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.LinearAlgebra.Dimension.Free

/-!

# Length of modules

## Main results
- `Module.length`: `Module.length R M` is the length of `M` as an `R`-module.
- `Module.length_pos`: The length of a nontrivial module is positive
- `Module.length_ne_top`: The length of an Artinian and Noetherian module is finite.
- `Module.length_eq_add_of_exact`: Length is additive in exact sequences.

-/

@[expose] public section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The length of a module, defined as the krull dimension of its submodule lattice. -/
noncomputable
/-
**Module.length** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.length : Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Module.length : ℕ∞ :=
  (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])
/-
**Module.coe_length** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.coe_length : (Module.length R M : WithBot Nat∞) = Order.krullDim (S
ubmodule R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
-/
lemma Module.coe_length :
    (Module.length R M : WithBot ℕ∞) = Order.krullDim (Submodule R M) :=
  WithBot.coe_unbot _ _
/-
**Module.length_eq_height** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_height : Module.length R M = Order.height (⊤ : Submodule 
R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `Order.height_top_eq_krullDim`：height_top_eq_krullDim [OrderTop α] : heig
ht (⊤ : α) = krullDim α
-/
lemma Module.length_eq_height : Module.length R M = Order.height (⊤ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Order.height_top_eq_krullDim]
/-
**Module.length_eq_coheight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_coheight : Module.length R M = Order.coheight (⊥ : Submod
ule R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `Order.coheight_bot_eq_krullDim`：coheight_bot_eq_krullDim [OrderBot α] : 
coheight (⊥ : α) = krullDim α
-/
lemma Module.length_eq_coheight : Module.length R M = Order.coheight (⊥ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Order.coheight_bot_eq_krullDim]

variable {R M}
/-
**Module.length_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_zero_iff : Module.length R M = 0 ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用引理 `Order.krullDim_eq_zero_iff_of_orderTop`：krullDim_eq_zero_iff_of_orderTop
 [OrderTop α] : krullDim α = 0 ↔ Subsingleton α
· 使用定理 `Submodule.subsingleton_iff`：subsingleton_iff : Subsingleton (Submodule R
 M) ↔ Subsingleton M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.length_eq_zero_iff : Module.length R M = 0 ↔ Subsingleton M := by
  rw [← WithBot.coe_inj, Module.coe_length, WithBot.coe_zero,
    Order.krullDim_eq_zero_iff_of_orderTop, Submodule.subsingleton_iff]

@[simp, nontriviality]
/-
**Module.length_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_zero [Subsingleton M] : Module.length R M = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.length_eq_zero_iff`：Module.length_eq_zero_iff : Module.length R M
 = 0 ↔ Subsingleton M
-/
lemma Module.length_eq_zero [Subsingleton M] : Module.length R M = 0 :=
  Module.length_eq_zero_iff.mpr ‹_›

@[simp, nontriviality]
/-
**Module.length_eq_zero_of_subsingleton_ring** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_zero_of_subsingleton_ring [Subsingleton R] : Module.lengt
h R M = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
-/
lemma Module.length_eq_zero_of_subsingleton_ring [Subsingleton R] : Module.length R M = 0 :=
  have := Module.subsingleton R M
  Module.length_eq_zero
/-
**Module.length_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_pos_iff : 0 < Module.length R M ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Module.length_eq_zero_iff`：Module.length_eq_zero_iff : Module.length R M
 = 0 ↔ Subsingleton M
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.length_pos_iff : 0 < Module.length R M ↔ Nontrivial M := by
  rw [pos_iff_ne_zero, ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial]
/-
**Module.length_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_pos [Nontrivial M] : 0 < Module.length R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.length_pos_iff`：Module.length_pos_iff : 0 < Module.length R M ↔ N
ontrivial M
-/
lemma Module.length_pos [Nontrivial M] : 0 < Module.length R M :=
  Module.length_pos_iff.mpr ‹_›
/-
**Module.length_compositionSeries** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_compositionSeries (s : CompositionSeries (Submodule R M)) (h
₁ : s.head = ⊥) (h₂ : s.last = ⊤) : s.length = Module.length R M
参数：s : CompositionSeries (Submodule R M)；h₁ : s.head = ⊥；h₂ : s.last = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `isFiniteLength_of_exists_compositionSeries`：isFiniteLength_of_exists_com
positionSeries (h : exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s
.last = ⊤) : IsFiniteLength R M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.LTSeries.length_le_krullDim`：∀ {α : Type u_1} [inst : Preorder α] 
(p : LTSeries α), ↑p.length ≤ Order.krullDim α
· 使用定理 `Order.krullDim.eq_1`：∀ (α : Type u_1) [inst : Preorder α], Order.krullDi
m α = ⨆ p, ↑p.length
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot`：exists_
relSeries_covBy_and_head_eq_bot_and_last_eq_bot {α} [PartialOrder α] [BoundedOrd
er α] [WellFoundedLT α] [WellFoundedGT α] (s : LTSeri…
· 使用定理 `CompositionSeries.jordan_holder`：jordan_holder (s₁ s₂ : CompositionSerie
s X) (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) : Equivalent s₁ s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
（共 37 条，此处仅展示前 30 条）
-/
lemma Module.length_compositionSeries (s : CompositionSeries (Submodule R M)) (h₁ : s.head = ⊥)
    (h₂ : s.last = ⊤) : s.length = Module.length R M := by
  have H := isFiniteLength_of_exists_compositionSeries ⟨s, h₁, h₂⟩
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).2
  rw [← WithBot.coe_inj, Module.coe_length]
  apply le_antisymm
  · exact (Order.LTSeries.length_le_krullDim <| s.map ⟨id, fun h ↦ h.1⟩)
  · rw [Order.krullDim, iSup_le_iff]
    intro t
    refine WithBot.coe_le_coe.mpr ?_
    obtain ⟨t', i, hi, ht₁, ht₂⟩ := t.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
    have := (s.jordan_holder t' (h₁.trans ht₁.symm) (h₂.trans ht₂.symm)).choose
    have h : t.length ≤ t'.length := by simpa using Fintype.card_le_of_embedding i
    have h' : t'.length = s.length := by simpa using Fintype.card_congr this.symm
    simpa using h.trans h'.le
/-
**Module.length_eq_top_iff_infiniteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Module.length_eq_top_iff_infiniteDimensionalOrder : length R M = ⊤ ↔ Infin
iteDimensionalOrder (Submodule R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
· 使用引理 `WithBot.coe_top`：coe_top [Top α] : ((⊤ : α) : WithBot α) = ⊤
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `Order.krullDim_eq_top_iff`：krullDim_eq_top_iff : krullDim α = ⊤ ↔ Infini
teDimensionalOrder α
· 使用引理 `not_finiteDimensionalOrder_iff`：not_finiteDimensionalOrder_iff [Preorder
 α] [Nonempty α] : ¬ FiniteDimensionalOrder α ↔ InfiniteDimensionalOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.length_eq_top_iff_infiniteDimensionalOrder :
    length R M = ⊤ ↔ InfiniteDimensionalOrder (Submodule R M) := by
  rw [← WithBot.coe_inj, WithBot.coe_top, coe_length, Order.krullDim_eq_top_iff,
      ← not_finiteDimensionalOrder_iff]
/-
**Module.length_ne_top_iff_finiteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_ne_top_iff_finiteDimensionalOrder : length R M != ⊤ ↔ Finite
DimensionalOrder (Submodule R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Module.length_eq_top_iff_infiniteDimensionalOrder`：Module.length_eq_top_
iff_infiniteDimensionalOrder : length R M = ⊤ ↔ InfiniteDimensionalOrder (Submod
ule R M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_finiteDimensionalOrder_iff`：not_finiteDimensionalOrder_iff [Preorder
 α] [Nonempty α] : ¬ FiniteDimensionalOrder α ↔ InfiniteDimensionalOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.length_ne_top_iff_finiteDimensionalOrder :
    length R M ≠ ⊤ ↔ FiniteDimensionalOrder (Submodule R M) := by
  rw [Ne, length_eq_top_iff_infiniteDimensionalOrder, ← not_finiteDimensionalOrder_iff, not_not]
/-
**Module.length_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_ne_top_iff : Module.length R M != ⊤ ↔ IsFiniteLength R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用定理 `isNoetherian_iff`：isNoetherian_iff : IsNoetherian R M ↔ WellFounded ((· 
> ·) : Submodule R M -> Submodule R M -> Prop)
· 使用定理 `isArtinian_iff`：isArtinian_iff (R M) [Semiring R] [AddCommMonoid M] [Mod
ule R M] : IsArtinian R M ↔ WellFounded (· < · : Submodule R M -> Submodule R M 
-> P…
· 使用引理 `SetRel.IsWellFounded.of_finiteDimensional`：SetRel.IsWellFounded.of_finit
eDimensional [r.FiniteDimensional] : r.IsWellFounded
· 使用引理 `Module.length_ne_top_iff_finiteDimensionalOrder`：Module.length_ne_top_if
f_finiteDimensionalOrder : length R M != ⊤ ↔ FiniteDimensionalOrder (Submodule R
 M)
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFiniteLength_iff_exists_compositionSeries`：isFiniteLength_iff_exists_c
ompositionSeries : IsFiniteLength R M ↔ exists s : CompositionSeries (Submodule 
R M), s.head = ⊥ ∧ s.last = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.length_compositionSeries`：Module.length_compositionSeries (s : Co
mpositionSeries (Submodule R M)) (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) : s.length 
= Module.length R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma Module.length_ne_top_iff : Module.length R M ≠ ⊤ ↔ IsFiniteLength R M := by
  refine ⟨fun h ↦ ?_, fun H ↦ ?_⟩
  · rw [length_ne_top_iff_finiteDimensionalOrder] at h
    rw [isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff, isArtinian_iff]
    let R : SetRel (Submodule R M) (Submodule R M) :=
      {(N₁, N₂) : Submodule R M × Submodule R M | N₁ < N₂}
    change R.inv.IsWellFounded ∧ R.IsWellFounded
    exact ⟨.of_finiteDimensional R.inv, .of_finiteDimensional R⟩
  · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp H
    rw [← length_compositionSeries s hs₁ hs₂]
    simp
/-
**Module.length_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_ne_top [IsArtinian R M] [IsNoetherian R M] : Module.length R
 M != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_ne_top_iff`：Module.length_ne_top_iff : Module.length R M !
= ⊤ ↔ IsFiniteLength R M
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
-/
lemma Module.length_ne_top [IsArtinian R M] [IsNoetherian R M] : Module.length R M ≠ ⊤ := by
  rw [length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨‹_›, ‹_›⟩

@[simp]
/-
**Module.finiteDimensionalOrder_submodule_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finiteDimensionalOrder_submodule_iff : FiniteDimensionalOrder (Subm
odule R M) ↔ IsFiniteLength R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.length_ne_top_iff_finiteDimensionalOrder`：Module.length_ne_top_if
f_finiteDimensionalOrder : length R M != ⊤ ↔ FiniteDimensionalOrder (Submodule R
 M)
· 使用引理 `Module.length_ne_top_iff`：Module.length_ne_top_iff : Module.length R M !
= ⊤ ↔ IsFiniteLength R M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.finiteDimensionalOrder_submodule_iff :
    FiniteDimensionalOrder (Submodule R M) ↔ IsFiniteLength R M := by
  rw [← Module.length_ne_top_iff_finiteDimensionalOrder, Module.length_ne_top_iff]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsArtinian R M] [IsNoetherian R M] : FiniteDimensionalOrder (Submodule R M) := by
  rw [Module.finiteDimensionalOrder_submodule_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  tauto
/-
**Module.length_submodule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_submodule {N : Submodule R M} : Module.length R N = Order.he
ight N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_eq_krullDim_Iic`：height_eq_krullDim_Iic (x : α) : (height x
 : Nat∞) = krullDim (Set.Iic x)
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
-/
lemma Module.length_submodule {N : Submodule R M} :
    Module.length R N = Order.height N := by
  apply WithBot.coe_injective
  rw [Order.height_eq_krullDim_Iic, coe_length, Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]
/-
**Module.length_quotient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_quotient {N : Submodule R M} : Module.length R (M ⧸ N) = Ord
er.coheight N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.coheight_eq_krullDim_Ici`：coheight_eq_krullDim_Ici {α : Type*} [Pr
eorder α] (x : α) : (coheight x : Nat∞) = krullDim (Set.Ici x)
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
-/
lemma Module.length_quotient {N : Submodule R M} :
    Module.length R (M ⧸ N) = Order.coheight N := by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici, coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]
/-
**LinearEquiv.length_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.length_eq {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[
R] N) : Module.length R M = Module.length R N
参数：e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
-/
lemma LinearEquiv.length_eq {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.length R M = Module.length R N := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]
/-
**Module.length_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.length_eq_of_surjective {S : Type*} [CommRing S] [Algebra S R] [Mod
ule S M] [IsScalarTower S R M] (h : Function.Surjective (algebraMap S R)) : Modu
le.length S M = Module.length R M
参数：h : Function.Surjective (algebraMap S R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddHom.id_apply`：∀ (M : Type u_10) [inst : Add M] (x : M), (AddHom.id M)
 x = x
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Module.length.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Ring R] [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.length R M = (Order
.krullDi…
· 使用定理 `WithBot.unbot_inj`：unbot_inj {a b : WithBot α} (ha : a != ⊥) (hb : b != 
⊥) : a.unbot ha = b.unbot hb ↔ a = b
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
theorem Module.length_eq_of_surjective {S : Type*} [CommRing S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (h : Function.Surjective (algebraMap S R)) :
    Module.length S M = Module.length R M := by
  have : RingHomSurjective (algebraMap S R) := ⟨h⟩
  let f : M →ₛₗ[algebraMap S R] M := ⟨AddHom.id M, by simp⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]
/-
**Module.length_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_bot : Module.length R (⊥ : Submodule R M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma Module.length_bot :
    Module.length R (⊥ : Submodule R M) = 0 :=
  Module.length_eq_zero
/-
**Module.length_top** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M],   Module.length R ↥⊤ = Module.length R M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_submodule`：Module.length_submodule {N : Submodule R M} : M
odule.length R N = Order.height N
· 使用引理 `Module.length_eq_height`：Module.length_eq_height : Module.length R M = O
rder.height (⊤ : Submodule R M)
-/
@[simp] lemma Module.length_top :
    Module.length R (⊤ : Submodule R M) = Module.length R M := by
  rw [Module.length_submodule, Module.length_eq_height]
/-
**Submodule.height_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.height_lt_top [IsArtinian R M] [IsNoetherian R M] (N : Submodule
 R M) : Order.height N < ⊤
参数：N : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用引理 `Module.length_ne_top`：Module.length_ne_top [IsArtinian R M] [IsNoetheria
n R M] : Module.length R M != ⊤
-/
lemma Submodule.height_lt_top [IsArtinian R M] [IsNoetherian R M] (N : Submodule R M) :
    Order.height N < ⊤ := by
  simpa only [← Module.length_submodule] using Module.length_ne_top.lt_top
/-
**Submodule.height_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.height_strictMono [IsArtinian R M] [IsNoetherian R M] : StrictMo
no (Order.height : Submodule R M -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.height_strictMono`：∀ {α : Type u_1} [inst : Preorder α] {x y : α},
 x < y → Order.height x < ⊤ → Order.height x < Order.height y
· 使用引理 `Submodule.height_lt_top`：Submodule.height_lt_top [IsArtinian R M] [IsNoe
therian R M] (N : Submodule R M) : Order.height N < ⊤
-/
lemma Submodule.height_strictMono [IsArtinian R M] [IsNoetherian R M] :
    StrictMono (Order.height : Submodule R M → ℕ∞) :=
  fun N _ h ↦ Order.height_strictMono h N.height_lt_top
/-
**Submodule.length_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.length_lt [IsArtinian R M] [IsNoetherian R M] {N : Submodule R M
} (h : N != ⊤) : Module.length R N < Module.length R M
参数：h : N != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_submodule`：Module.length_submodule {N : Submodule R M} : M
odule.length R N = Order.height N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.length_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst
_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.length R ↥⊤ = Module
.length…
· 使用引理 `Submodule.height_strictMono`：Submodule.height_strictMono [IsArtinian R M
] [IsNoetherian R M] : StrictMono (Order.height : Submodule R M -> Nat∞)
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
lemma Submodule.length_lt [IsArtinian R M] [IsNoetherian R M] {N : Submodule R M} (h : N ≠ ⊤) :
    Module.length R N < Module.length R M := by
  simpa [← Module.length_top (M := M), Module.length_submodule] using height_strictMono h.lt_top

variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
variable (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
variable (H : Function.Exact f g)

set_option backward.isDefEq.respectTransparency false in
include hf hg H in
/-- Length is additive in exact sequences. -/
/-
**Module.length_eq_add_of_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_add_of_exact : Module.length R M = Module.length R N + Mo
dule.length R P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFiniteLength_iff_exists_compositionSeries`：isFiniteLength_iff_exists_c
ompositionSeries : IsFiniteLength R M ↔ exists s : CompositionSeries (Submodule 
R M), s.head = ⊥ ∧ s.last = ⊤
· 使用引理 `Submodule.comap_covBy_of_surjective`：comap_covBy_of_surjective {f : M ->
ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p q : Submodule R₂ M₂} (h : p ⋖ q) : p.comap f 
⋖ q.comap f
· 使用引理 `Submodule.map_covBy_of_injective`：map_covBy_of_injective {p q : Submodul
e R M} (h : p ⋖ q) : p.map f ⋖ q.map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.length_compositionSeries`：Module.length_compositionSeries (s : Co
mpositionSeries (Submodule R M)) (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) : s.length 
= Module.length R M
· 使用定理 `RelSeries.head_smash`：∀ {α : Type u_1} {r : SetRel α α} {p q : RelSeries
 r} (h : p.last = q.head), (p.smash q h).head = p.head
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `RelSeries.last_smash`：∀ {α : Type u_1} {r : SetRel α α} {p q : RelSeries
 r} (h : p.last = q.head), (p.smash q h).last = q.last
· 使用定理 `Submodule.comap_top`：comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤
· 使用定理 `RelSeries.smash_length`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSeri
es r) (connect : p.last = q.head),   (p.smash q connect).length = p.length + q.l
ength
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RelSeries.map_length`：∀ {α : Type u_1} {r : SetRel α α} {β : Type u_2} {
s : SetRel β β} (p : RelSeries r) (f : r.Hom s),   (p.map f).length = p.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `IsFiniteLength.of_injective`：IsFiniteLength.of_injective (H : IsFiniteLe
ngth R N) (hf : Function.Injective f) : IsFiniteLength R M
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Module.length_ne_top_iff`：Module.length_ne_top_iff : Module.length R M !
= ⊤ ↔ IsFiniteLength R M
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用引理 `IsFiniteLength.of_surjective`：IsFiniteLength.of_surjective (H : IsFinite
Length R M) (hf : Function.Surjective f) : IsFiniteLength R N
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Length is additive in exact sequences.
-/
lemma Module.length_eq_add_of_exact :
    Module.length R M = Module.length R N + Module.length R P := by
  by_cases hP : IsFiniteLength R P
  · by_cases hN : IsFiniteLength R N
    · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hP
      obtain ⟨t, ht₁, ht₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
      let s' : CompositionSeries (Submodule R M) :=
        s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩
      let t' : CompositionSeries (Submodule R M) :=
        t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩
      have hfg : Submodule.map f ⊤ = Submodule.comap g ⊥ := by
        rw [Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
      let r := t'.smash s' (by simpa [s', t', hs₁, ht₂] using hfg)
      rw [← Module.length_compositionSeries s hs₁ hs₂,
        ← Module.length_compositionSeries t ht₁ ht₂,
        ← Module.length_compositionSeries r
          (by simpa [r, t', ht₁, -Submodule.map_bot] using Submodule.map_bot f)
          (by simpa [r, s', hs₂, -Submodule.comap_top] using Submodule.comap_top g)]
      simp_rw [r, RelSeries.smash_length, Nat.cast_add, s', t', RelSeries.map_length]
    · have := mt (IsFiniteLength.of_injective · hf) hN
      rw [← Module.length_ne_top_iff, ne_eq, not_not] at hN this
      rw [hN, this, top_add]
  · have := mt (IsFiniteLength.of_surjective · hg) hP
    rw [← Module.length_ne_top_iff, ne_eq, not_not] at hP this
    rw [hP, this, add_top]

include hf in
/-
**Module.length_le_of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_le_of_injective : Module.length R N <= Module.length R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_eq_add_of_exact`：Module.length_eq_add_of_exact : Module.le
ngth R M = Module.length R N + Module.length R P
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用引理 `LinearMap.exact_map_mkQ_range`：exact_map_mkQ_range (f : M ->ₗ[R] N) : Ex
act f (Submodule.mkQ (range f))
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma Module.length_le_of_injective : Module.length R N ≤ Module.length R M := by
  rw [Module.length_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact le_self_add

include hg in
/-
**Module.length_le_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_le_of_surjective : Module.length R P <= Module.length R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_eq_add_of_exact`：Module.length_eq_add_of_exact : Module.le
ngth R M = Module.length R N + Module.length R P
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用引理 `LinearMap.exact_subtype_ker_map`：exact_subtype_ker_map (g : N ->ₗ[R] P) 
: Exact (Submodule.subtype (ker g)) g
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma Module.length_le_of_surjective : Module.length R P ≤ Module.length R M := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g (Submodule.subtype_injective _) hg
    (LinearMap.exact_subtype_ker_map g)]
  exact le_add_self

variable (R M N) in
@[simp]
/-
**Module.length_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_prod : Module.length R (M × N) = Module.length R M + Module.
length R N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.length_eq_add_of_exact`：Module.length_eq_add_of_exact : Module.le
ngth R M = Module.length R N + Module.length R P
· 使用定理 `LinearMap.inl_injective`：inl_injective : Function.Injective (inl R M M₂)
· 使用定理 `LinearMap.snd_surjective`：snd_surjective : Function.Surjective (snd R M 
M₂)
· 使用定理 `Function.Exact.inl_snd`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} [
inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst
_3 : _root_.…
-/
lemma Module.length_prod :
    Module.length R (M × N) = Module.length R M + Module.length R N :=
  Module.length_eq_add_of_exact _ _ LinearMap.inl_injective LinearMap.snd_surjective .inl_snd

variable (R) in
@[simp]
/-
**Module.length_pi_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_pi_of_fintype : forall {ι : Type*} [Fintype ι] (M : ι -> Typ
e*) [forall i, AddCommGroup (M i)] [forall i, Module R (M i)], Module.length R (
Π i, M i) = ∑ i, Module.length R (M i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.induction_empty_option`：induction_empty_option {P : forall (α : 
Type u) [Fintype α], Prop} (of_equiv : forall (α β) [Fintype β] (e : α ≃ β), @P 
α (@Fintype.ofEquiv …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearEquiv.length_eq`：LinearEquiv.length_eq {N : Type*} [AddCommGroup N
] [Module R N] (e : M ≃ₗ[R] N) : Module.length R M = Module.length R N
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Module.length_prod`：Module.length_prod : Module.length R (M × N) = Modul
e.length R M + Module.length R N
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Fintype.sum_option`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [
inst_1 : AddCommMonoid M] (f : Option α → M),   ∑ i, f i = f none + ∑ i, f (some
 i)
-/
lemma Module.length_pi_of_fintype : ∀ {ι : Type*} [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
    Module.length R (Π i, M i) = ∑ i, Module.length R (M i) := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← (LinearEquiv.piCongrLeft R M e).length_eq, IH, e.sum_comp (length R <| M ·)]
  · intro M _ _
    simp [Module.length_eq_zero]
  · intro ι _ IH M _ _
    rw [(LinearEquiv.piOptionEquivProd _).length_eq, Module.length_prod, IH, add_comm,
      Fintype.sum_option, add_comm]

@[simp]
/-
**Module.length_finsupp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_finsupp {ι : Type*} : Module.length R (ι ->₀ M) = ENat.card 
ι * Module.length R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearEquiv.length_eq`：LinearEquiv.length_eq {N : Type*} [AddCommGroup N
] [Module R N] (e : M ≃ₗ[R] N) : Module.length R M = Module.length R N
· 使用引理 `Module.length_pi_of_fintype`：Module.length_pi_of_fintype : forall {ι : T
ype*} [Fintype ι] (M : ι -> Type*) [forall i, AddCommGroup (M i)] [forall i, Mod
ule R (M i)], Mod…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENat.top_mul`：∀ {m : ℕ∞}, m ≠ 0 → ⊤ * m = ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Module.length_pos`：Module.length_pos [Nontrivial M] : 0 < Module.length 
R M
· 使用引理 `ENat.eq_top_iff_forall_ge`：eq_top_iff_forall_ge : n = ⊤ ↔ forall m : Nat
, m <= n
· 使用定理 `Infinite.exists_subset_card_eq`：exists_subset_card_eq (α : Type*) [Infin
ite α] (n : Nat) : exists s : Finset α, #s = n
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `ENat.self_le_mul_right`：self_le_mul_right (a : Nat∞) (hc : c != 0) : a <
= a * c
· 使用引理 `Module.length_le_of_injective`：Module.length_le_of_injective : Module.le
ngth R N <= Module.length R M
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma Module.length_finsupp {ι : Type*} :
    Module.length R (ι →₀ M) = ENat.card ι * Module.length R M := by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp [(Finsupp.linearEquivFunOnFinite R M ι).length_eq]
  nontriviality M
  rw [ENat.card_eq_top_of_infinite, ENat.top_mul length_pos.ne', ENat.eq_top_iff_forall_ge]
  intro m
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι m
  have : length R (s →₀ M) = ↑m * length R M := by
    simp [(Finsupp.linearEquivFunOnFinite R M _).length_eq, hs]
  refine le_trans ?_ (Module.length_le_of_injective (Finsupp.lmapDomain M R ((↑) : s → ι))
    (Finsupp.mapDomain_injective Subtype.val_injective))
  rw [this]
  exact ENat.self_le_mul_right _ length_pos.ne'

@[simp]
/-
**Module.length_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_pi {ι : Type*} : Module.length R (ι -> M) = ENat.card ι * Mo
dule.length R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_pi_of_fintype`：Module.length_pi_of_fintype : forall {ι : T
ype*} [Fintype ι] (M : ι -> Type*) [forall i, AddCommGroup (M i)] [forall i, Mod
ule R (M i)], Mod…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENat.top_mul`：∀ {m : ℕ∞}, m ≠ 0 → ⊤ * m = ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Module.length_pos`：Module.length_pos [Nontrivial M] : 0 < Module.length 
R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Module.length_finsupp`：Module.length_finsupp {ι : Type*} : Module.length
 R (ι ->₀ M) = ENat.card ι * Module.length R M
· 使用引理 `Module.length_le_of_injective`：Module.length_le_of_injective : Module.le
ngth R N <= Module.length R M
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma Module.length_pi {ι : Type*} :
    Module.length R (ι → M) = ENat.card ι * Module.length R M := by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp
  nontriviality M
  rw [ENat.card_eq_top_of_infinite, ENat.top_mul length_pos.ne', ← top_le_iff]
  refine le_trans ?_ (Module.length_le_of_injective Finsupp.lcoeFun DFunLike.coe_injective)
  simp [ENat.top_mul length_pos.ne']

attribute [nontriviality] rank_subsingleton'

variable (R M) in
/-
**Module.length_of_free** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_of_free [Module.Free R M] : Module.length R M = (Module.rank
 R M).toENat * Module.length R R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_eq_zero_of_subsingleton_ring`：Module.length_eq_zero_of_sub
singleton_ring [Subsingleton R] : Module.length R M = 0
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `LinearEquiv.length_eq`：LinearEquiv.length_eq {N : Type*} [AddCommGroup N
] [Module R N] (e : M ≃ₗ[R] N) : Module.length R M = Module.length R N
· 使用引理 `Module.length_finsupp`：Module.length_finsupp {ι : Type*} : Module.length
 R (ι ->₀ M) = ENat.card ι * Module.length R M
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.rank_pos_of_free`：rank_pos_of_free [Module.Free R M] [Nontrivial 
M] : 0 < Module.rank R M
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用引理 `Module.length_ne_top_iff`：Module.length_ne_top_iff : Module.length R M !
= ⊤ ↔ IsFiniteLength R M
（共 35 条，此处仅展示前 30 条）
-/
lemma Module.length_of_free [Module.Free R M] :
    Module.length R M = (Module.rank R M).toENat * Module.length R R := by
  let b := Module.Free.chooseBasis R M
  nontriviality R
  nontriviality M
  by_cases H : Module.length R R = ⊤
  · simp [b.repr.length_eq, H, rank_pos_of_free.ne']
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at H
  cases H
  let b := Module.Free.chooseBasis R M
  rw [b.repr.length_eq, Module.length_finsupp, Free.rank_eq_card_chooseBasisIndex, ENat.card]

variable (R M) in
/-
**Module.length_of_free_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_of_free_of_finite [StrongRankCondition R] [Module.Free R M] 
[Module.Finite R M] : Module.length R M = Module.finrank R M * Module.length R R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_of_free`：Module.length_of_free [Module.Free R M] : Module.
length R M = (Module.rank R M).toENat * Module.length R R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.toENat_eq_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c = ↑n ↔ c = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
-/
lemma Module.length_of_free_of_finite
    [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.length R M = Module.finrank R M * Module.length R R := by
  rw [length_of_free, Cardinal.toENat_eq_natCast.mpr (finrank_eq_rank _ _).symm]
/-
**Module.length_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_one_iff : Module.length R M = 1 ↔ IsSimpleModule R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用引理 `Order.krullDim_eq_one_iff_of_boundedOrder`：krullDim_eq_one_iff_of_bounde
dOrder {α : Type*} [PartialOrder α] [BoundedOrder α] : krullDim α = 1 ↔ IsSimple
Order α
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.length_eq_one_iff :
    Module.length R M = 1 ↔ IsSimpleModule R M := by
  rw [← WithBot.coe_inj, Module.coe_length, WithBot.coe_one,
    Order.krullDim_eq_one_iff_of_boundedOrder, isSimpleModule_iff]

variable (R M) in
@[simp]
/-
**Module.length_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_one [IsSimpleModule R M] : Module.length R M = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.length_eq_one_iff`：Module.length_eq_one_iff : Module.length R M =
 1 ↔ IsSimpleModule R M
-/
lemma Module.length_eq_one [IsSimpleModule R M] :
    Module.length R M = 1 :=
  Module.length_eq_one_iff.mpr ‹_›
/-
**Module.length_eq_rank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_rank (K M : Type*) [DivisionRing K] [AddCommGroup M] [Mod
ule K M] : Module.length K M = (Module.rank K M).toENat
参数：K M : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_of_free`：Module.length_of_free [Module.Free R M] : Module.
length R M = (Module.rank R M).toENat * Module.length R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `Module.length_eq_one`：Module.length_eq_one [IsSimpleModule R M] : Module
.length R M = 1
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Module.length_eq_rank
    (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M] :
    Module.length K M = (Module.rank K M).toENat := by
  simp [Module.length_of_free]
/-
**Module.length_eq_finrank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.length_eq_finrank (K M : Type*) [DivisionRing K] [AddCommGroup M] [
Module K M] [Module.Finite K M] : Module.length K M = Module.finrank K M
参数：K M : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_of_free`：Module.length_of_free [Module.Free R M] : Module.
length R M = (Module.rank R M).toENat * Module.length R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `Module.length_eq_one`：Module.length_eq_one [IsSimpleModule R M] : Module
.length R M = 1
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Module.length_eq_finrank
    (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M] [Module.Finite K M] :
    Module.length K M = Module.finrank K M := by
  simp [Module.length_of_free]
/-
**Submodule.length_le_length_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.length_le_length_restrictScalars (A : Type*) [Ring A] [SMul A R]
 [Module A M] [IsScalarTower A R M] (p : Submodule R M) : Module.length R p <= M
odule.length A (p.restrictScalars A)
参数：A : Type*；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用引理 `Module.coe_length`：Module.coe_length : (Module.length R M : WithBot Nat∞
) = Order.krullDim (Submodule R M)
· 使用引理 `Order.krullDim_le_of_orderEmbedding`：krullDim_le_of_orderEmbedding (e : 
α ↪o β) : Order.krullDim α <= Order.krullDim β
-/
theorem Submodule.length_le_length_restrictScalars (A : Type*) [Ring A] [SMul A R] [Module A M]
    [IsScalarTower A R M] (p : Submodule R M) :
    Module.length R p ≤ Module.length A (p.restrictScalars A) := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding (restrictScalarsEmbedding A R p)
/-
**Submodule.length_quotient_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.length_quotient_lt [IsArtinian R M] [IsNoetherian R M] (p : Subm
odule R M) (h : p != ⊥) : Module.length R (M ⧸ p) < Module.length R M
参数：p : Submodule R M；h : p != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_quotient`：Module.length_quotient {N : Submodule R M} : Mod
ule.length R (M ⧸ N) = Order.coheight N
· 使用定理 `Module.length.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Ring R] [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.length R M = (Order
.krullDi…
· 使用引理 `WithBot.lt_unbot_iff`：lt_unbot_iff (hx : x != ⊥) : a < unbot x hx ↔ a < 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.coheight_bot_eq_krullDim`：coheight_bot_eq_krullDim [OrderBot α] : 
coheight (⊥ : α) = krullDim α
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Order.coheight_strictAnti`：∀ {α : Type u_1} [inst : Preorder α] {x y : α
}, y < x → Order.coheight x < ⊤ → Order.coheight x < Order.coheight y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用引理 `Order.coheight_lt_top`：coheight_lt_top [FiniteDimensionalOrder α] (x : α
) : coheight x < ⊤
· 使用定理 `instFiniteDimensionalOrderSubmoduleOfIsArtinianOfIsNoetherian`：∀ {R : Ty
pe u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root
_.Module R M] [IsArtinian R M]   [IsNoetherian R M]…
-/
theorem Submodule.length_quotient_lt [IsArtinian R M] [IsNoetherian R M] (p : Submodule R M)
    (h : p ≠ ⊥) : Module.length R (M ⧸ p) < Module.length R M := by
  rw [Module.length_quotient, Module.length, WithBot.lt_unbot_iff, ← Order.coheight_bot_eq_krullDim,
    WithBot.coe_lt_coe]
  exact Order.coheight_strictAnti (bot_lt_iff_ne_bot.mpr h) (Order.coheight_lt_top p)
