/-
Copyright (c) 2021 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
module

public import Mathlib.Order.Ideal
public import Mathlib.Order.PFilter

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `Order.Ideal.PrimePair`: A pair of an `Order.Ideal` and an `Order.PFilter` which form a partition
  of `P`.  This is useful as giving the data of a prime ideal is the same as giving the data of a
  prime filter.
- `Order.Ideal.IsPrime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `Order.PFilter.IsPrime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/

@[expose] public section


open Order.PFilter

namespace Order

variable {P : Type*}

namespace Ideal

/-- A pair of an `Order.Ideal` and an `Order.PFilter` which form a partition of `P`.
-/
/-
**Order.Ideal.PrimePair** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order.Ideal`。
形式化陈述：(P : Type u_2) → [Preorder P] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of an `Order.Ideal` and an `Order.PFilter` which form a partition of `P`.
-/
structure PrimePair (P : Type*) [Preorder P] where
  I : Ideal P
  F : PFilter P
  isCompl_I_F : IsCompl (I : Set P) F

namespace PrimePair

variable [Preorder P] (IF : PrimePair P)

/-
**Order.Ideal.PrimePair.compl_I_eq_F** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.Prim
ePair`。
形式化陈述：compl_I_eq_F : (IF.I : Set P)ᶜ = IF.F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `Order.Ideal.PrimePair.isCompl_I_F`：∀ {P : Type u_2} [inst : Preorder P] 
(self : Order.Ideal.PrimePair P), IsCompl ↑self.I ↑self.F
-/
theorem compl_I_eq_F : (IF.I : Set P)ᶜ = IF.F :=
  IF.isCompl_I_F.compl_eq
/-
**Order.Ideal.PrimePair.compl_F_eq_I** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.Prim
ePair`。
形式化陈述：compl_F_eq_I : (IF.F : Set P)ᶜ = IF.I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.eq_compl`：IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ
· 使用定理 `Order.Ideal.PrimePair.isCompl_I_F`：∀ {P : Type u_2} [inst : Preorder P] 
(self : Order.Ideal.PrimePair P), IsCompl ↑self.I ↑self.F
-/
theorem compl_F_eq_I : (IF.F : Set P)ᶜ = IF.I :=
  IF.isCompl_I_F.eq_compl.symm
/-
**Order.Ideal.PrimePair.I_isProper** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.PrimeP
air`。
形式化陈述：I_isProper : IsProper IF.I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.PFilter.nonempty`：∀ {P : Type u_1} [inst : Preorder P] (F : Order.
PFilter P), (↑F).Nonempty
· 使用定理 `Order.Ideal.isProper_of_notMem`：isProper_of_notMem {I : Ideal P} {p : P}
 (notMem : p ∉ I) : IsProper I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.Ideal.PrimePair.compl_I_eq_F`：compl_I_eq_F : (IF.I : Set P)ᶜ = IF.
F
-/
theorem I_isProper : IsProper IF.I := by
  obtain ⟨w, h⟩ := IF.F.nonempty
  apply isProper_of_notMem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h
/-
**Order.Ideal.PrimePair.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.PrimePai
r`。
形式化陈述：∀ {P : Type u_1} [inst : Preorder P] (IF : Order.Ideal.PrimePair P), Disjo
int ↑IF.I ↑IF.F
参数：IF : Order.Ideal.PrimePair P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Order.Ideal.PrimePair.isCompl_I_F`：∀ {P : Type u_2} [inst : Preorder P] 
(self : Order.Ideal.PrimePair P), IsCompl ↑self.I ↑self.F
-/
protected theorem disjoint : Disjoint (IF.I : Set P) IF.F :=
  IF.isCompl_I_F.disjoint
/-
**Order.Ideal.PrimePair.I_union_F** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.PrimePa
ir`。
形式化陈述：I_union_F : (IF.I : Set P) union IF.F = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Order.Ideal.PrimePair.isCompl_I_F`：∀ {P : Type u_2} [inst : Preorder P] 
(self : Order.Ideal.PrimePair P), IsCompl ↑self.I ↑self.F
-/
theorem I_union_F : (IF.I : Set P) ∪ IF.F = Set.univ :=
  IF.isCompl_I_F.sup_eq_top
/-
**Order.Ideal.PrimePair.F_union_I** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.PrimePa
ir`。
形式化陈述：F_union_I : (IF.F : Set P) union IF.I = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Order.Ideal.PrimePair.isCompl_I_F`：∀ {P : Type u_2} [inst : Preorder P] 
(self : Order.Ideal.PrimePair P), IsCompl ↑self.I ↑self.F
-/
theorem F_union_I : (IF.F : Set P) ∪ IF.I = Set.univ :=
  IF.isCompl_I_F.symm.sup_eq_top

end PrimePair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff]
/-
**Order.Ideal.IsPrime** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order.Ideal`。
形式化陈述：{P : Type u_1} → [inst : Preorder P] → Order.Ideal P → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal `I` is prime if its complement is a filter.
-/
class IsPrime [Preorder P] (I : Ideal P) : Prop extends IsProper I where
  compl_filter : IsPFilter (I : Set P)ᶜ

section Preorder

variable [Preorder P]

/-- Create an element of type `Order.Ideal.PrimePair` from an ideal satisfying the predicate
`Order.Ideal.IsPrime`. -/
/-
**Order.Ideal.IsPrime.toPrimePair** 是 Mathlib 中的一个定义，位于命名空间 `Order.Ideal.IsPrime
`。
形式化陈述：{P : Type u_1} → [inst : Preorder P] → {I : Order.Ideal P} → I.IsPrime → O
rder.Ideal.PrimePair P
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.IsPrime.compl_filter`：∀ {P : Type u_1} {inst : Preorder P} {
I : Order.Ideal P} [self : I.IsPrime], Order.IsPFilter (↑I)ᶜ

--- 原说明 ---
Create an element of type `Order.Ideal.PrimePair` from an ideal satisfying the p
redicate
`Order.Ideal.IsPrime`.
-/
def IsPrime.toPrimePair {I : Ideal P} (h : IsPrime I) : PrimePair P :=
  { I
    F := h.compl_filter.toPFilter
    isCompl_I_F := isCompl_compl }
/-
**Order.Ideal.PrimePair.I_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.PrimePa
ir`。
形式化陈述：∀ {P : Type u_1} [inst : Preorder P] (IF : Order.Ideal.PrimePair P), IF.I.
IsPrime
参数：IF : Order.Ideal.PrimePair P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.PrimePair.I_isProper`：I_isProper : IsProper IF.I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Ideal.PrimePair.compl_I_eq_F`：compl_I_eq_F : (IF.I : Set P)ᶜ = IF.
F
· 使用定理 `Order.PFilter.isPFilter`：isPFilter : IsPFilter (F : Set P)
-/
theorem PrimePair.I_isPrime (IF : PrimePair P) : IsPrime IF.I :=
  { IF.I_isProper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.isPFilter }

end Preorder

section SemilatticeInf

variable [SemilatticeInf P] {I : Ideal P}

/-
**Order.Ideal.IsPrime.mem_or_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.IsPrime`
。
形式化陈述：∀ {P : Type u_1} [inst : SemilatticeInf P] {I : Order.Ideal P}, I.IsPrime 
→ ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.Ideal.IsPrime.compl_filter`：∀ {P : Type u_1} {inst : Preorder P} {
I : Order.Ideal P} [self : I.IsPrime], Order.IsPFilter (↑I)ᶜ
· 使用定理 `Order.PFilter.inf_mem`：inf_mem (hx : x in F) (hy : y in F) : x ⊓ y in F
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsPrime.mem_or_mem (hI : IsPrime I) {x y : P} : x ⊓ y ∈ I → x ∈ I ∨ y ∈ I := by
  contrapose!
  let F := hI.compl_filter.toPFilter
  change x ∈ F ∧ y ∈ F → x ⊓ y ∈ F
  exact fun h => inf_mem h.1 h.2
/-
**Order.Ideal.IsPrime.of_mem_or_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.IsPri
me`。
形式化陈述：∀ {P : Type u_1} [inst : SemilatticeInf P] {I : Order.Ideal P} [I.IsProper
],   (∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I) → I.IsPrime
参数：∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Ideal.isPrime_iff`：∀ {P : Type u_1} [inst : Preorder P] (I : Order
.Ideal P), I.IsPrime ↔ I.IsProper ∧ Order.IsPFilter (↑I)ᶜ
· 使用定理 `Order.IsPFilter.of_def`：∀ {P : Type u_1} [inst : Preorder P] {F : Set P}
,   F.Nonempty → DirectedOn (fun x1 x2 => x1 ≥ x2) F → (∀ {x y : P}, x ≤ y → x ∈
 F → y ∈ F) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.Ideal.isProper_iff`：∀ {P : Type u_1} [inst : LE P] (I : Order.Idea
l P), I.IsProper ↔ ↑I ≠ Set.univ
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Order.Ideal.mem_compl_of_ge`：mem_compl_of_ge {x y : P} : x <= y -> x in 
(I : Set P)ᶜ -> y in (I : Set P)ᶜ
-/
theorem IsPrime.of_mem_or_mem [IsProper I] (hI : ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I) :
    IsPrime I := by
  rw [isPrime_iff]
  use ‹_›
  refine .of_def ?_ ?_ ?_
  · exact Set.nonempty_compl.2 (I.isProper_iff.1 ‹_›)
  · intro x hx y hy
    exact ⟨x ⊓ y, fun h => (hI h).elim hx hy, inf_le_left, inf_le_right⟩
  · exact @mem_compl_of_ge _ _ _
/-
**Order.Ideal.isPrime_iff_mem_or_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal`。
形式化陈述：isPrime_iff_mem_or_mem [IsProper I] : IsPrime I ↔ forall {x y : P}, x ⊓ y 
in I -> x in I ∨ y in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.IsPrime.mem_or_mem`：∀ {P : Type u_1} [inst : SemilatticeInf 
P] {I : Order.Ideal P}, I.IsPrime → ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Order.Ideal.IsPrime.of_mem_or_mem`：∀ {P : Type u_1} [inst : SemilatticeI
nf P] {I : Order.Ideal P} [I.IsProper],   (∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ 
I) → I.IsPrime
-/
theorem isPrime_iff_mem_or_mem [IsProper I] : IsPrime I ↔ ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩

end SemilatticeInf

section DistribLattice

variable [DistribLattice P] {I : Ideal P}

/-
**Order.Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Order.Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsMaximal.isPrime [IsMaximal I] : IsPrime I := by
  rw [isPrime_iff_mem_or_mem]
  intro x y
  contrapose!
  rintro ⟨hx, hynI⟩ hxy
  apply hynI
  let J := I ⊔ principal x
  have hJuniv : (J : Set P) = Set.univ :=
    IsMaximal.maximal_proper (lt_sup_principal_of_notMem ‹_›)
  have hyJ : y ∈ (J : Set P) := Set.eq_univ_iff_forall.mp hJuniv y
  rw [coe_sup_eq] at hyJ
  rcases hyJ with ⟨a, ha, b, hb, hy⟩
  rw [hy]
  refine sup_mem ha (I.lower (le_inf hb ?_) hxy)
  rw [hy]
  exact le_sup_right

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {x : P} {I : Ideal P}

/-
**Order.Ideal.IsPrime.mem_or_compl_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal.Is
Prime`。
形式化陈述：∀ {P : Type u_1} [inst : BooleanAlgebra P] {x : P} {I : Order.Ideal P}, I.
IsPrime → x ∈ I ∨ xᶜ ∈ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.IsPrime.mem_or_mem`：∀ {P : Type u_1} [inst : SemilatticeInf 
P] {I : Order.Ideal P}, I.IsPrime → ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_compl_eq_bot`：inf_compl_eq_bot : a ⊓ aᶜ = ⊥
· 使用定理 `Order.Ideal.bot_mem`：bot_mem (s : Ideal P) : ⊥ in s
-/
theorem IsPrime.mem_or_compl_mem (hI : IsPrime I) : x ∈ I ∨ xᶜ ∈ I := by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem
/-
**Order.Ideal.IsPrime.compl_mem_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal
.IsPrime`。
形式化陈述：∀ {P : Type u_1} [inst : BooleanAlgebra P] {x : P} {I : Order.Ideal P}, I.
IsPrime → x ∉ I → xᶜ ∈ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Order.Ideal.IsPrime.mem_or_compl_mem`：∀ {P : Type u_1} [inst : BooleanAl
gebra P] {x : P} {I : Order.Ideal P}, I.IsPrime → x ∈ I ∨ xᶜ ∈ I
-/
theorem IsPrime.compl_mem_of_notMem (hI : IsPrime I) (hxnI : x ∉ I) : xᶜ ∈ I :=
  hI.mem_or_compl_mem.resolve_left hxnI
/-
**Order.Ideal.isPrime_of_mem_or_compl_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.Ideal
`。
形式化陈述：isPrime_of_mem_or_compl_mem [IsProper I] (h : forall {x : P}, x in I ∨ xᶜ 
in I) : IsPrime I
参数：h : forall {x : P}, x in I ∨ xᶜ in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Order.Ideal.sup_mem`：sup_mem (hx : x in s) (hy : y in s) : x ⊔ y in s
· 使用定理 `Order.Ideal.lower`：∀ {P : Type u_1} [inst : LE P] (s : Order.Ideal P), I
sLowerSet ↑s
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_inf_compl`：sup_inf_inf_compl : x ⊓ y ⊔ x ⊓ yᶜ = x
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem isPrime_of_mem_or_compl_mem [IsProper I] (h : ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I) : IsPrime I := by
  simp only [isPrime_iff_mem_or_mem, or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ ∈ I := h.resolve_left hxI
  have ass : x ⊓ y ⊔ y ⊓ xᶜ ∈ I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass
/-
**Order.Ideal.isPrime_iff_mem_or_compl_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.Idea
l`。
形式化陈述：isPrime_iff_mem_or_compl_mem [IsProper I] : IsPrime I ↔ forall {x : P}, x 
in I ∨ xᶜ in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.IsPrime.mem_or_compl_mem`：∀ {P : Type u_1} [inst : BooleanAl
gebra P] {x : P} {I : Order.Ideal P}, I.IsPrime → x ∈ I ∨ xᶜ ∈ I
· 使用定理 `Order.Ideal.isPrime_of_mem_or_compl_mem`：isPrime_of_mem_or_compl_mem [Is
Proper I] (h : forall {x : P}, x in I ∨ xᶜ in I) : IsPrime I
-/
theorem isPrime_iff_mem_or_compl_mem [IsProper I] : IsPrime I ↔ ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I :=
  ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩
/-
**Order.Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Order.Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsPrime.isMaximal [IsPrime I] : IsMaximal I := by
  simp only [isMaximal_iff, Set.eq_univ_iff_forall, IsPrime.toIsProper, true_and]
  intro J hIJ x
  rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
  suffices ass : x ⊓ y ⊔ x ⊓ yᶜ ∈ J by rwa [sup_inf_inf_compl] at ass
  exact
    sup_mem (J.lower inf_le_right hyJ)
      (hIJ.le <| I.lower inf_le_right <| IsPrime.compl_mem_of_notMem ‹_› hyI)

end BooleanAlgebra

end Ideal

namespace PFilter

variable [Preorder P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mk_iff]
/-
**Order.PFilter.IsPrime** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order.PFilter`。
形式化陈述：{P : Type u_1} → [inst : Preorder P] → Order.PFilter P → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter `F` is prime if its complement is an ideal.
-/
class IsPrime (F : PFilter P) : Prop where
  compl_ideal : IsIdeal (F : Set P)ᶜ

/-- Create an element of type `Order.Ideal.PrimePair` from a filter satisfying the predicate
`Order.PFilter.IsPrime`. -/
/-
**Order.PFilter.IsPrime.toPrimePair** 是 Mathlib 中的一个定义，位于命名空间 `Order.PFilter.IsP
rime`。
形式化陈述：{P : Type u_1} → [inst : Preorder P] → {F : Order.PFilter P} → F.IsPrime →
 Order.Ideal.PrimePair P
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.PFilter.IsPrime.compl_ideal`：∀ {P : Type u_1} {inst : Preorder P} 
{F : Order.PFilter P} [self : F.IsPrime], Order.IsIdeal (↑F)ᶜ

--- 原说明 ---
Create an element of type `Order.Ideal.PrimePair` from a filter satisfying the p
redicate
`Order.PFilter.IsPrime`.
-/
def IsPrime.toPrimePair {F : PFilter P} (h : IsPrime F) : Ideal.PrimePair P :=
  { I := h.compl_ideal.toIdeal
    F
    isCompl_I_F := isCompl_compl.symm }
/-
**Order.PFilter._root_.Order.Ideal.PrimePair.F_isPrime** 是 Mathlib 中的一个定理，位于命名空间
 `Order.PFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Order.Ideal.PrimePair.F_isPrime (IF : Ideal.PrimePair P) : IsPrime IF.F :=
  {
    compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.isIdeal }

end PFilter

end Order

