/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Markus Himmel, Lorenzo Luccioli, Alessio Rondelli, Etienne Marion
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Covering numbers

We define covering numbers of sets in a pseudo-metric space, which are minimal cardinalities of
`ε`-covers of sets by closed balls.
We also define the packing number, which is the maximal cardinality of an `ε`-separated set.

We prove inequalities between these covering and packing numbers.

## Main definitions

* `externalCoveringNumber`: the external covering number of a set `A` for radius `ε` is the minimal
  cardinality (in `ℕ∞`) of an `ε`-cover.
* `coveringNumber`: the covering number (or internal covering number) of a set `A` for radius `ε` is
  the minimal cardinality (in `ℕ∞`) of an `ε`-cover contained in `A`.
* `packingNumber`: the packing number of a set `A` for radius `ε` is the maximal cardinality of
  an `ε`-separated set in `A`.

We define sets achieving these minimal/maximal cardinalities when they exist:
* `minimalCover`: a finite internal `ε`-cover of a set `A` by closed balls with minimal cardinality.
* `maximalSeparatedSet`: a finite `ε`-separated subset of a set `A` with maximal cardinality.

## Main statements

We have the following inequalities between covering and packing numbers:
* `externalCoveringNumber_le_coveringNumber`: external covering number ≤ covering number.
* `packingNumber_two_mul_le_externalCoveringNumber`: packing number for `2 * ε` ≤ external covering
  number for `ε`.
* `coveringNumber_le_packingNumber`: covering number ≤ packing number.
* `coveringNumber_two_mul_le_externalCoveringNumber`: covering number for `2 * ε` ≤ external
  covering number for `ε`.

The covering number is not monotone for set inclusion (because the cover must be contained
in the set), but we have the following inequality:
* `coveringNumber_subset_le`: if `A ⊆ B`, then `coveringNumber ε A ≤ coveringNumber (ε / 2) B`.

## References

* [R. Vershynin, *High-dimensional probability*][vershynin2018high]

-/

@[expose] public section

open EMetric Set
open scoped ENNReal NNReal

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  {A B C : Set X} {ε δ : ℝ≥0} {x : X}

section Definitions

/-- The external covering number of a set `A` in `X` for radius `ε` is the minimal cardinality
(in `ℕ∞`) of an `ε`-cover by points in `X` (not necessarily in `A`). -/
noncomputable
/-
**Metric.externalCoveringNumber** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber (ε : Real>=0) (A : Set X) : Nat∞
参数：ε : Real>=0；A : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def externalCoveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Set X) (_ : IsCover ε A C), C.encard

/-- The covering number (or internal covering number) of a set `A` for radius `ε` is
the minimal cardinality (in `ℕ∞`) of an `ε`-cover contained in `A`. -/
noncomputable
/-
**Metric.coveringNumber** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：coveringNumber (ε : Real>=0) (A : Set X) : Nat∞
参数：ε : Real>=0；A : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Set X) (_ : C ⊆ A) (_ : IsCover ε A C), C.encard

/-- The packing number of a set `A` for radius `ε` is the maximal cardinality (in `ℕ∞`)
of an `ε`-separated set in `A`. -/
noncomputable
/-
**Metric.packingNumber** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：packingNumber (ε : Real>=0) (A : Set X) : Nat∞
参数：ε : Real>=0；A : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def packingNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsSeparated ε C), C.encard

end Definitions

@[simp]
/-
**Metric.externalCoveringNumber_empty** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber_empty (ε : Real>=0) : externalCoveringNumber ε (∅ :
 Set X) = 0
参数：ε : Real>=0。
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
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
-/
lemma externalCoveringNumber_empty (ε : ℝ≥0) : externalCoveringNumber ε (∅ : Set X) = 0 := by
  simp [externalCoveringNumber]

@[simp]
/-
**Metric.coveringNumber_empty** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_empty (ε : Real>=0) : coveringNumber ε (∅ : Set X) = 0
参数：ε : Real>=0。
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
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `iInf_iInf_eq_left`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] {b : β} {f : (x : β) → x = b → α},   ⨅ x, ⨅ (h : x = b), f x h = f b ⋯
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coveringNumber_empty (ε : ℝ≥0) : coveringNumber ε (∅ : Set X) = 0 := by simp [coveringNumber]

@[simp]
/-
**Metric.packingNumber_empty** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：packingNumber_empty (ε : Real>=0) : packingNumber ε (∅ : Set X) = 0
参数：ε : Real>=0。
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
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma packingNumber_empty (ε : ℝ≥0) : packingNumber ε (∅ : Set X) = 0 := by simp [packingNumber]

@[simp]
/-
**Metric.externalCoveringNumber_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber_eq_zero : externalCoveringNumber ε A = 0 ↔ A = ∅
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma externalCoveringNumber_eq_zero :
    externalCoveringNumber ε A = 0 ↔ A = ∅ := by simp [externalCoveringNumber]

@[simp]
/-
**Metric.externalCoveringNumber_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber_pos_iff : 0 < externalCoveringNumber ε A ↔ A.Nonemp
ty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma externalCoveringNumber_pos_iff : 0 < externalCoveringNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]
/-
**Metric.coveringNumber_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_eq_zero : coveringNumber ε A = 0 ↔ A = ∅
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coveringNumber_eq_zero : coveringNumber ε A = 0 ↔ A = ∅ := by simp [coveringNumber]

@[simp]
/-
**Metric.coveringNumber_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_pos_iff : 0 < coveringNumber ε A ↔ A.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coveringNumber_pos_iff : 0 < coveringNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]
/-
**Metric.packingNumber_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：packingNumber_eq_zero : packingNumber ε A = 0 ↔ A = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma packingNumber_eq_zero : packingNumber ε A = 0 ↔ A = ∅ := by
  simp only [packingNumber, ENat.iSup_eq_zero, encard_eq_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra!
  obtain ⟨x, hx⟩ := this
  simpa using h {x} (by simp [hx]) (by simp)

@[simp]
/-
**Metric.packingNumber_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：packingNumber_pos_iff : 0 < packingNumber ε A ↔ A.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma packingNumber_pos_iff : 0 < packingNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]
/-
**Metric.externalCoveringNumber_le_coveringNumber** 是 Mathlib 中的一个引理，位于命名空间 `Met
ric`。
形式化陈述：externalCoveringNumber_le_coveringNumber (ε : Real>=0) (A : Set X) : exter
nalCoveringNumber ε A <= coveringNumber ε A
参数：ε : Real>=0；A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
lemma externalCoveringNumber_le_coveringNumber (ε : ℝ≥0) (A : Set X) :
    externalCoveringNumber ε A ≤ coveringNumber ε A := by
  simp only [externalCoveringNumber, coveringNumber, le_iInf_iff]
  exact fun C _ hC_cover ↦ iInf₂_le C hC_cover
/-
**Metric.IsCover.externalCoveringNumber_le_encard** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric.IsCover`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {A C : Set X} {ε : NNReal},
   Metric.IsCover ε A C → Metric.externalCoveringNumber ε A ≤ C.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
lemma IsCover.externalCoveringNumber_le_encard (hC : IsCover ε A C) :
    externalCoveringNumber ε A ≤ C.encard := iInf₂_le C hC
/-
**Metric.IsCover.coveringNumber_le_encard** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCo
ver`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {A C : Set X} {ε : NNReal},
   C ⊆ A → Metric.IsCover ε A C → Metric.coveringNumber ε A ≤ C.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma IsCover.coveringNumber_le_encard (h_subset : C ⊆ A) (hC : IsCover ε A C) :
    coveringNumber ε A ≤ C.encard := (iInf₂_le C h_subset).trans (iInf_le _ hC)
/-
**Metric.IsSeparated.encard_le_packingNumber** 是 Mathlib 中的一个定理，位于命名空间 `Metric.I
sSeparated`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {A C : Set X} {ε : NNReal},
   C ⊆ A → Metric.IsSeparated (↑ε) C → C.encard ≤ Metric.packingNumber ε A
参数：↑ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma IsSeparated.encard_le_packingNumber (h_subset : C ⊆ A) (hC : IsSeparated ε C) :
    C.encard ≤ packingNumber ε A := le_iSup₂_of_le C h_subset (le_iSup_of_le hC le_rfl)
/-
**Metric.externalCoveringNumber_le_encard_self** 是 Mathlib 中的一个引理，位于命名空间 `Metric
`。
形式化陈述：externalCoveringNumber_le_encard_self (A : Set X) : externalCoveringNumber
 ε A <= A.encard
参数：A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.IsCover.externalCoveringNumber_le_encard`：∀ {X : Type u_1} [inst 
: PseudoEMetricSpace X] {A C : Set X} {ε : NNReal},   Metric.IsCover ε A C → Met
ric.externalCoveringNumber ε A ≤ C.en…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma externalCoveringNumber_le_encard_self (A : Set X) : externalCoveringNumber ε A ≤ A.encard :=
  IsCover.externalCoveringNumber_le_encard (by simp)
/-
**Metric.coveringNumber_le_encard_self** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_le_encard_self (A : Set X) : coveringNumber ε A <= A.encard
参数：A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.IsCover.coveringNumber_le_encard`：∀ {X : Type u_1} [inst : Pseudo
EMetricSpace X] {A C : Set X} {ε : NNReal},   C ⊆ A → Metric.IsCover ε A C → Met
ric.coveringNumber ε A ≤ C.en…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma coveringNumber_le_encard_self (A : Set X) : coveringNumber ε A ≤ A.encard :=
  IsCover.coveringNumber_le_encard (by simp) (by simp)
/-
**Metric.packingNumber_le_encard_self** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：packingNumber_le_encard_self (A : Set X) : packingNumber ε A <= A.encard
参数：A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
-/
lemma packingNumber_le_encard_self (A : Set X) : packingNumber ε A ≤ A.encard := by
  simp only [packingNumber, iSup_le_iff]
  exact fun _ hC _ ↦ encard_le_encard hC
/-
**Metric.externalCoveringNumber_anti** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber_anti (h : ε <= δ) : externalCoveringNumber δ A <= e
xternalCoveringNumber ε A
参数：h : ε <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `iInf_const_mono`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst :
 CompleteLattice α] {a : α} (h : ι → ι'), ⨅ x, a ≤ ⨅ x, a
· 使用定理 `Metric.IsCover.mono_radius`：∀ {X : Type u_1} [inst : PseudoEMetricSpace 
X] {ε δ : NNReal} {s N : Set X},   ε ≤ δ → Metric.IsCover ε s N → Metric.IsCover
 δ s N
-/
lemma externalCoveringNumber_anti (h : ε ≤ δ) :
    externalCoveringNumber δ A ≤ externalCoveringNumber ε A := by
  simp_rw [externalCoveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover ↦ h_cover.mono_radius h)
/-
**Metric.coveringNumber_anti** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_anti (h : ε <= δ) : coveringNumber δ A <= coveringNumber ε 
A
参数：h : ε <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `iInf_const_mono`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst :
 CompleteLattice α] {a : α} (h : ι → ι'), ⨅ x, a ≤ ⨅ x, a
· 使用定理 `Metric.IsCover.mono_radius`：∀ {X : Type u_1} [inst : PseudoEMetricSpace 
X] {ε δ : NNReal} {s N : Set X},   ε ≤ δ → Metric.IsCover ε s N → Metric.IsCover
 δ s N
-/
lemma coveringNumber_anti (h : ε ≤ δ) : coveringNumber δ A ≤ coveringNumber ε A := by
  simp_rw [coveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover ↦ h_cover.mono_radius h)
/-
**Metric.externalCoveringNumber_mono_set** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber_mono_set (h : A subseteq B) : externalCoveringNumbe
r ε A <= externalCoveringNumber ε B
参数：h : A subseteq B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Metric.IsCover.anti`：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {ε :
 NNReal} {s t N : Set X},   s ⊆ t → Metric.IsCover ε t N → Metric.IsCover ε s N
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma externalCoveringNumber_mono_set (h : A ⊆ B) :
    externalCoveringNumber ε A ≤ externalCoveringNumber ε B := by
  simp only [externalCoveringNumber, le_iInf_iff]
  exact fun C hC ↦ iInf_le_of_le C <| iInf_le_of_le (hC.anti h) le_rfl

@[simp]
/-
**Metric.externalCoveringNumber_zero** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) : ext
ernalCoveringNumber 0 A = A.encard
参数：A : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Metric.externalCoveringNumber_le_encard_self`：externalCoveringNumber_le_
encard_self (A : Set X) : externalCoveringNumber ε A <= A.encard
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.isCover_zero`：∀ {X : Type u_1} [inst : EMetricSpace X] {s N : Set
 X}, Metric.IsCover 0 s N ↔ s ⊆ N
-/
lemma externalCoveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    externalCoveringNumber 0 A = A.encard := by
  refine le_antisymm (externalCoveringNumber_le_encard_self A) ?_
  refine le_iInf fun C ↦ le_iInf fun hC₁ ↦ ?_
  rw [isCover_zero] at hC₁
  exact encard_le_encard hC₁

@[simp]
/-
**Metric.coveringNumber_zero** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) : coveringNum
ber 0 A = A.encard
参数：A : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Metric.coveringNumber_le_encard_self`：coveringNumber_le_encard_self (A :
 Set X) : coveringNumber ε A <= A.encard
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.externalCoveringNumber_zero`：externalCoveringNumber_zero {E : Typ
e*} [EMetricSpace E] (A : Set E) : externalCoveringNumber 0 A = A.encard
· 使用引理 `Metric.externalCoveringNumber_le_coveringNumber`：externalCoveringNumber_
le_coveringNumber (ε : Real>=0) (A : Set X) : externalCoveringNumber ε A <= cove
ringNumber ε A
-/
lemma coveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    coveringNumber 0 A = A.encard := by
  refine le_antisymm (coveringNumber_le_encard_self A) ?_
  rw [← externalCoveringNumber_zero]
  exact externalCoveringNumber_le_coveringNumber 0 A

@[simp]
/-
**Metric.packingNumber_zero** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：packingNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) : packingNumbe
r 0 A = A.encard
参数：A : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Metric.packingNumber_le_encard_self`：packingNumber_le_encard_self (A : S
et X) : packingNumber ε A <= A.encard
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
-/
lemma packingNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    packingNumber 0 A = A.encard :=
  le_antisymm (packingNumber_le_encard_self A) (le_iSup_of_le A (by simp))
/-
**Metric.coveringNumber_eq_one_of_ediam_le** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : ediam A 
<= ε) : coveringNumber ε A = 1
参数：h_nonempty : A.Nonempty；hA : ediam A <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.IsCover.coveringNumber_le_encard`：∀ {X : Type u_1} [inst : Pseudo
EMetricSpace X] {A C : Set X} {ε : NNReal},   C ⊆ A → Metric.IsCover ε A C → Met
ric.coveringNumber ε A ≤ C.en…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Metric.IsCover.singleton_of_ediam_le`：∀ {X : Type u_1} [inst : PseudoEMe
tricSpace X] {ε : NNReal} {s : Set X} {x : X},   Metric.ediam s ≤ ↑ε → x ∈ s → M
etric.IsCover ε s {x}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
-/
lemma coveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : ediam A ≤ ε) :
    coveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ ≤ ({a} : Set X).encard :=
        (IsCover.singleton_of_ediam_le hA ha).coveringNumber_le_encard (by simp [ha])
      _ ≤ 1 := by simp
  · simpa [Order.one_le_iff_pos]
/-
**Metric.externalCoveringNumber_eq_one_of_ediam_le** 是 Mathlib 中的一个引理，位于命名空间 `Me
tric`。
形式化陈述：externalCoveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : 
ediam A <= ε) : externalCoveringNumber ε A = 1
参数：h_nonempty : A.Nonempty；hA : ediam A <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Metric.externalCoveringNumber_le_coveringNumber`：externalCoveringNumber_
le_coveringNumber (ε : Real>=0) (A : Set X) : externalCoveringNumber ε A <= cove
ringNumber ε A
· 使用引理 `Metric.coveringNumber_eq_one_of_ediam_le`：coveringNumber_eq_one_of_ediam
_le (h_nonempty : A.Nonempty) (hA : ediam A <= ε) : coveringNumber ε A = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
-/
lemma externalCoveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty)
    (hA : ediam A ≤ ε) :
    externalCoveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · exact (externalCoveringNumber_le_coveringNumber ε A).trans_eq
      (coveringNumber_eq_one_of_ediam_le h_nonempty hA)
  · simpa [Order.one_le_iff_pos]
/-
**Metric.externalCoveringNumber_le_one_of_ediam_le** 是 Mathlib 中的一个引理，位于命名空间 `Me
tric`。
形式化陈述：externalCoveringNumber_le_one_of_ediam_le (hA : ediam A <= ε) : externalCo
veringNumber ε A <= 1
参数：hA : ediam A <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.externalCoveringNumber_eq_zero`：externalCoveringNumber_eq_zero : 
externalCoveringNumber ε A = 0 ↔ A = ∅
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Metric.externalCoveringNumber_eq_one_of_ediam_le`：externalCoveringNumber
_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : ediam A <= ε) : externalCove
ringNumber ε A = 1
-/
lemma externalCoveringNumber_le_one_of_ediam_le (hA : ediam A ≤ ε) :
    externalCoveringNumber ε A ≤ 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← externalCoveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (externalCoveringNumber_eq_one_of_ediam_le h_nonempty hA).le
/-
**Metric.coveringNumber_le_one_of_ediam_le** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_le_one_of_ediam_le (hA : ediam A <= ε) : coveringNumber ε A
 <= 1
参数：hA : ediam A <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.coveringNumber_eq_zero`：coveringNumber_eq_zero : coveringNumber ε
 A = 0 ↔ A = ∅
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Metric.coveringNumber_eq_one_of_ediam_le`：coveringNumber_eq_one_of_ediam
_le (h_nonempty : A.Nonempty) (hA : ediam A <= ε) : coveringNumber ε A = 1
-/
lemma coveringNumber_le_one_of_ediam_le (hA : ediam A ≤ ε) : coveringNumber ε A ≤ 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← coveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (coveringNumber_eq_one_of_ediam_le h_nonempty hA).le

@[simp]
/-
**Metric.coveringNumber_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_singleton (ε : Real>=0) (x : X) : coveringNumber ε {x} = 1
参数：ε : Real>=0；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.coveringNumber_eq_one_of_ediam_le`：coveringNumber_eq_one_of_ediam
_le (h_nonempty : A.Nonempty) (hA : ediam A <= ε) : coveringNumber ε A = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_singleton`：ediam_singleton : ediam ({x} : Set X) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma coveringNumber_singleton (ε : ℝ≥0) (x : X) : coveringNumber ε {x} = 1 :=
  coveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]
/-
**Metric.externalCoveringNumber_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：externalCoveringNumber_singleton (ε : Real>=0) (x : X) : externalCoveringN
umber ε {x} = 1
参数：ε : Real>=0；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.externalCoveringNumber_eq_one_of_ediam_le`：externalCoveringNumber
_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : ediam A <= ε) : externalCove
ringNumber ε A = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_singleton`：ediam_singleton : ediam ({x} : Set X) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma externalCoveringNumber_singleton (ε : ℝ≥0) (x : X) : externalCoveringNumber ε {x} = 1 :=
  externalCoveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]
/-
**Metric.packingNumber_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：packingNumber_singleton (ε : Real>=0) (x : X) : packingNumber ε {x} = 1
参数：ε : Real>=0；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Metric.packingNumber_le_encard_self`：packingNumber_le_encard_self (A : S
et X) : packingNumber ε A <= A.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
-/
lemma packingNumber_singleton (ε : ℝ≥0) (x : X) : packingNumber ε {x} = 1 :=
  le_antisymm ((packingNumber_le_encard_self {x}).trans_eq (by simp)) <|
    le_iSup_of_le {x} <| le_iSup_of_le (by simp) <| le_iSup_of_le (by simp) (by simp)

section MinimalCover

/-
**Metric.exists_set_encard_eq_coveringNumber** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：exists_set_encard_eq_coveringNumber (h : coveringNumber ε A != ⊤) : exists
 C, C subseteq A ∧ C.Finite ∧ IsCover ε A C ∧ C.encard = coveringNumber ε A
参数：h : coveringNumber ε A != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ENat.exists_eq_iInf`：exists_eq_iInf [Nonempty ι] (f : ι -> Nat∞) : exist
s a, f a = ⨅ x, f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.encard_lt_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard < ⊤ ↔ s.Fi
nite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
-/
lemma exists_set_encard_eq_coveringNumber (h : coveringNumber ε A ≠ ⊤) :
    ∃ C, C ⊆ A ∧ C.Finite ∧ IsCover ε A C ∧ C.encard = coveringNumber ε A := by
  simp only [coveringNumber, ne_eq, iInf_eq_top, encard_eq_top_iff, not_forall, not_infinite] at h
  obtain ⟨C', hC'_subset, hC'_cover, hC'_fin⟩ := h
  have : Nonempty { s : Set X // s ⊆ A ∧ IsCover ε A s } := ⟨C', hC'_subset, hC'_cover⟩
  let h := ENat.exists_eq_iInf (fun C : {s : Set X // s ⊆ A ∧ IsCover ε A s} ↦ (C : Set X).encard)
  obtain ⟨C, hC⟩ := h
  refine ⟨C, C.2.1, ?_, C.2.2, ?_⟩
  · refine Set.encard_lt_top_iff.mp ?_
    simp only [hC, iInf_lt_top, encard_lt_top_iff, Subtype.exists, exists_prop]
    exact ⟨C', ⟨hC'_subset, hC'_cover⟩, hC'_fin⟩
  · rw [hC]
    simp_rw [iInf_subtype, iInf_and]
    rfl

/-- A finite internal `ε`-cover of a set `A` by closed balls with minimal cardinality.
It is defined as the empty set if no such finite cover exists. -/
noncomputable
/-
**Metric.minimalCover** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：minimalCover (ε : Real>=0) (A : Set X) : Set X
参数：ε : Real>=0；A : Set X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.exists_set_encard_eq_coveringNumber`：exists_set_encard_eq_coverin
gNumber (h : coveringNumber ε A != ⊤) : exists C, C subseteq A ∧ C.Finite ∧ IsCo
ver ε A C ∧ C.encard = coveringN…
-/
def minimalCover (ε : ℝ≥0) (A : Set X) : Set X :=
  if h : coveringNumber ε A ≠ ⊤ then (exists_set_encard_eq_coveringNumber h).choose else ∅
/-
**Metric.minimalCover_subset** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：minimalCover_subset : minimalCover ε A subseteq A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma minimalCover_subset : minimalCover ε A ⊆ A := by grind [minimalCover]
/-
**Metric.finite_minimalCover** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：finite_minimalCover : (minimalCover ε A).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finite_minimalCover :
    (minimalCover ε A).Finite := by grind [minimalCover]
/-
**Metric.isCover_minimalCover** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isCover_minimalCover (h : coveringNumber ε A != ⊤) : IsCover ε A (minimalC
over ε A)
参数：h : coveringNumber ε A != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isCover_minimalCover (h : coveringNumber ε A ≠ ⊤) :
    IsCover ε A (minimalCover ε A) := by grind [minimalCover]
/-
**Metric.encard_minimalCover** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：encard_minimalCover (h : coveringNumber ε A != ⊤) : (minimalCover ε A).enc
ard = coveringNumber ε A
参数：h : coveringNumber ε A != ⊤。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma encard_minimalCover (h : coveringNumber ε A ≠ ⊤) :
    (minimalCover ε A).encard = coveringNumber ε A := by grind [minimalCover]

end MinimalCover

section MaximalSeparatedSet

/-
**Metric.exists_set_encard_eq_packingNumber** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：exists_set_encard_eq_packingNumber (h : packingNumber ε A != ⊤) : exists C
, C subseteq A ∧ C.Finite ∧ IsSeparated ε C ∧ C.encard = packingNumber ε A
参数：h : packingNumber ε A != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ENat.exists_eq_iSup_of_lt_top`：exists_eq_iSup_of_lt_top [Nonempty ι] (h 
: ⨆ i, f i < ⊤) : exists i, f i = ⨆ i, f i
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.encard_ne_top_iff`：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma exists_set_encard_eq_packingNumber (h : packingNumber ε A ≠ ⊤) :
    ∃ C, C ⊆ A ∧ C.Finite ∧ IsSeparated ε C ∧ C.encard = packingNumber ε A := by
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · simp [hA, packingNumber]
  have : Nonempty { s : Set X // s ⊆ A ∧ IsSeparated ε s } := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨{a}, by simp [ha], by simp⟩⟩
  let h_exists := ENat.exists_eq_iSup_of_lt_top
    (f := fun C : { s : Set X // s ⊆ A ∧ IsSeparated ε s } ↦ (C : Set X).encard)
  simp_rw [packingNumber] at h ⊢
  simp_rw [iSup_subtype, iSup_and] at h_exists
  specialize h_exists h.lt_top
  obtain ⟨C, hC⟩ := h_exists
  refine ⟨C, C.2.1, ?_, C.2.2, ?_⟩
  · refine Set.encard_ne_top_iff.mp ?_
    rwa [hC]
  · rw [hC]

/-- A finite `ε`-separated subset of a set `A` with maximal cardinality.
It is defined as the empty set if no such finite subset exists. -/
noncomputable
/-
**Metric.maximalSeparatedSet** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：maximalSeparatedSet (ε : Real>=0) (A : Set X) : Set X
参数：ε : Real>=0；A : Set X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.exists_set_encard_eq_packingNumber`：exists_set_encard_eq_packingN
umber (h : packingNumber ε A != ⊤) : exists C, C subseteq A ∧ C.Finite ∧ IsSepar
ated ε C ∧ C.encard = packingNu…
-/
def maximalSeparatedSet (ε : ℝ≥0) (A : Set X) : Set X :=
  if h : packingNumber ε A ≠ ⊤ then (exists_set_encard_eq_packingNumber h).choose else ∅
/-
**Metric.maximalSeparatedSet_subset** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：maximalSeparatedSet_subset : maximalSeparatedSet ε A subseteq A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma maximalSeparatedSet_subset : maximalSeparatedSet ε A ⊆ A := by grind [maximalSeparatedSet]
/-
**Metric.isSeparated_maximalSeparatedSet** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isSeparated_maximalSeparatedSet : IsSeparated ε (maximalSeparatedSet ε A :
 Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isSeparated_maximalSeparatedSet :
    IsSeparated ε (maximalSeparatedSet ε A : Set X) := by grind [maximalSeparatedSet]
/-
**Metric.encard_maximalSeparatedSet** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：encard_maximalSeparatedSet (h : packingNumber ε A != ⊤) : (maximalSeparate
dSet ε A).encard = packingNumber ε A
参数：h : packingNumber ε A != ⊤。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma encard_maximalSeparatedSet (h : packingNumber ε A ≠ ⊤) :
    (maximalSeparatedSet ε A).encard = packingNumber ε A := by grind [maximalSeparatedSet]
/-
**Metric.encard_le_of_isSeparated** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：encard_le_of_isSeparated (h_subset : C subseteq A) (h_sep : IsSeparated ε 
C) (h : packingNumber ε A != ⊤) : C.encard <= (maximalSeparatedSet ε A).encard
参数：h_subset : C subseteq A；h_sep : IsSeparated ε C；h : packingNumber ε A != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.encard_maximalSeparatedSet`：encard_maximalSeparatedSet (h : packi
ngNumber ε A != ⊤) : (maximalSeparatedSet ε A).encard = packingNumber ε A
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma encard_le_of_isSeparated (h_subset : C ⊆ A)
    (h_sep : IsSeparated ε C) (h : packingNumber ε A ≠ ⊤) :
    C.encard ≤ (maximalSeparatedSet ε A).encard := by
  rw [encard_maximalSeparatedSet h]
  exact le_iSup_of_le C <| le_iSup_of_le h_subset <| le_iSup_of_le h_sep (by simp)

/-- The maximal separated set is a cover. -/
/-
**Metric.isCover_maximalSeparatedSet** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isCover_maximalSeparatedSet (h : packingNumber ε A != ⊤) : IsCover ε A (ma
ximalSeparatedSet ε A)
参数：h : packingNumber ε A != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Metric.isSeparated_insert_of_notMem`：isSeparated_insert_of_notMem (hx : 
x ∉ s) : IsSeparated ε (insert x s) ↔ IsSeparated ε s ∧ forall y in s, ε < edist
 x y
· 使用引理 `Metric.isSeparated_maximalSeparatedSet`：isSeparated_maximalSeparatedSet 
: IsSeparated ε (maximalSeparatedSet ε A : Set X)
· 使用引理 `Metric.encard_le_of_isSeparated`：encard_le_of_isSeparated (h_subset : C 
subseteq A) (h_sep : IsSeparated ε C) (h : packingNumber ε A != ⊤) : C.encard <=
 (maximalSeparatedSet…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `ENat.lt_add_one_iff`：lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.encard_maximalSeparatedSet`：encard_maximalSeparatedSet (h : packi
ngNumber ε A != ⊤) : (maximalSeparatedSet ε A).encard = packingNumber ε A

--- 原说明 ---
The maximal separated set is a cover.
-/
lemma isCover_maximalSeparatedSet (h : packingNumber ε A ≠ ⊤) :
    IsCover ε A (maximalSeparatedSet ε A) := by
  intro x hxA
  by_contra! h_dist
  let C := {x} ∪ maximalSeparatedSet ε A
  have hx_not_mem : x ∉ maximalSeparatedSet ε A := by simpa using h_dist x
  suffices C ⊆ A ∧ IsSeparated ε C by
    refine absurd (encard_le_of_isSeparated this.1 this.2 h) ?_
    simp [C, encard_insert_of_notMem hx_not_mem,
      ENat.lt_add_one_iff (encard_maximalSeparatedSet h ▸ h)]
  constructor
  · simp [C, hxA, maximalSeparatedSet_subset, Set.insert_subset]
  · exact isSeparated_insert_of_notMem hx_not_mem |>.mpr
      ⟨isSeparated_maximalSeparatedSet, by simpa using h_dist⟩

end MaximalSeparatedSet

section Comparisons

/-- The packing number of a set `A` for radius `2 * ε` is at most the external covering number
of `A` for radius `ε`. -/
/-
**Metric.packingNumber_two_mul_le_externalCoveringNumber** 是 Mathlib 中的一个定理，位于命名
空间 `Metric`。
形式化陈述：packingNumber_two_mul_le_externalCoveringNumber (ε : Real>=0) (A : Set X) 
: packingNumber (2 * ε) A <= externalCoveringNumber ε A
参数：ε : Real>=0；A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x

--- 原说明 ---
The packing number of a set `A` for radius `2 * ε` is at most the external cover
ing number
of `A` for radius `ε`.
-/
theorem packingNumber_two_mul_le_externalCoveringNumber (ε : ℝ≥0) (A : Set X) :
    packingNumber (2 * ε) A ≤ externalCoveringNumber ε A := by
  simp only [packingNumber, ENNReal.coe_mul, ENNReal.coe_ofNat, externalCoveringNumber, le_iInf_iff,
    iSup_le_iff]
  intro C hC_cover D hD_subset hD_separated
  -- For each point in D, choose a point in C which is ε-close to it
  let f : D → C := fun x ↦
    ⟨(hC_cover (hD_subset x.2)).choose, (hC_cover (hD_subset x.2)).choose_spec.1⟩
  have hf' (x : D) : edist x.1 (f x) ≤ ε := (hC_cover (hD_subset x.2)).choose_spec.2
  -- `⊢ D.encard ≤ C.encard`
  -- It suffices to prove that `f` is injective
  simp only [← Set.toENat_cardinalMk]
  gcongr
  refine Cardinal.mk_le_of_injective (f := f) fun x y hxy ↦ Subtype.ext ?_
  apply Set.Pairwise.eq hD_separated x.2 y.2
  simp only [not_lt]
  calc
    edist (x : X) y ≤ edist (x : X) (f x) + edist (f x : X) y := edist_triangle ..
    _ ≤ 2 * ε := by
      rw [two_mul]
      gcongr
      · exact hf' x
      · simpa [edist_comm, hxy] using hf' y
/-
**Metric.coveringNumber_le_packingNumber** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_le_packingNumber (ε : Real>=0) (A : Set X) : coveringNumber
 ε A <= packingNumber ε A
参数：ε : Real>=0；A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.encard_maximalSeparatedSet`：encard_maximalSeparatedSet (h : packi
ngNumber ε A != ⊤) : (maximalSeparatedSet ε A).encard = packingNumber ε A
· 使用定理 `Metric.IsCover.coveringNumber_le_encard`：∀ {X : Type u_1} [inst : Pseudo
EMetricSpace X] {A C : Set X} {ε : NNReal},   C ⊆ A → Metric.IsCover ε A C → Met
ric.coveringNumber ε A ≤ C.en…
· 使用引理 `Metric.maximalSeparatedSet_subset`：maximalSeparatedSet_subset : maximalS
eparatedSet ε A subseteq A
· 使用引理 `Metric.isCover_maximalSeparatedSet`：isCover_maximalSeparatedSet (h : pac
kingNumber ε A != ⊤) : IsCover ε A (maximalSeparatedSet ε A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem coveringNumber_le_packingNumber (ε : ℝ≥0) (A : Set X) :
    coveringNumber ε A ≤ packingNumber ε A := by
  by_cases! h_top : packingNumber ε A ≠ ⊤
  · rw [← encard_maximalSeparatedSet h_top]
    exact isCover_maximalSeparatedSet h_top |>.coveringNumber_le_encard maximalSeparatedSet_subset
  · simp [h_top]
/-
**Metric.coveringNumber_two_mul_le_externalCoveringNumber** 是 Mathlib 中的一个定理，位于命
名空间 `Metric`。
形式化陈述：coveringNumber_two_mul_le_externalCoveringNumber (ε : Real>=0) (A : Set X)
 : coveringNumber (2 * ε) A <= externalCoveringNumber ε A
参数：ε : Real>=0；A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.coveringNumber_empty`：coveringNumber_empty (ε : Real>=0) : coveri
ngNumber ε (∅ : Set X) = 0
· 使用引理 `Metric.externalCoveringNumber_empty`：externalCoveringNumber_empty (ε : R
eal>=0) : externalCoveringNumber ε (∅ : Set X) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.coveringNumber_le_packingNumber`：coveringNumber_le_packingNumber 
(ε : Real>=0) (A : Set X) : coveringNumber ε A <= packingNumber ε A
· 使用定理 `Metric.packingNumber_two_mul_le_externalCoveringNumber`：packingNumber_tw
o_mul_le_externalCoveringNumber (ε : Real>=0) (A : Set X) : packingNumber (2 * ε
) A <= externalCoveringNumber ε A
-/
theorem coveringNumber_two_mul_le_externalCoveringNumber (ε : ℝ≥0) (A : Set X) :
    coveringNumber (2 * ε) A ≤ externalCoveringNumber ε A := by
  rcases Set.eq_empty_or_nonempty A with rfl | h_nonempty
  · simp
  refine (coveringNumber_le_packingNumber _ A).trans ?_
  exact packingNumber_two_mul_le_externalCoveringNumber ε A
/-
**Metric.coveringNumber_subset_le** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：coveringNumber_subset_le (h : A subseteq B) : coveringNumber ε A <= coveri
ngNumber (ε / 2) B
参数：h : A subseteq B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.coveringNumber_le_packingNumber`：coveringNumber_le_packingNumber 
(ε : Real>=0) (A : Set X) : coveringNumber ε A <= packingNumber ε A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 42 条，此处仅展示前 30 条）
-/
lemma coveringNumber_subset_le (h : A ⊆ B) :
    coveringNumber ε A ≤ coveringNumber (ε / 2) B := calc
  coveringNumber ε A
  _ ≤ packingNumber ε A := coveringNumber_le_packingNumber ε A
  _ = packingNumber (2 * (ε / 2)) A := by ring_nf
  _ ≤ externalCoveringNumber (ε / 2) A :=
    packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
  _ ≤ externalCoveringNumber (ε / 2) B := externalCoveringNumber_mono_set h
  _ ≤ coveringNumber (ε / 2) B :=
    externalCoveringNumber_le_coveringNumber (ε / 2) B

end Comparisons

/-- The covering number of the image of a set under an injective isometry is equal to
the covering number of the set.
See `Isometry.coveringNumber_image` for the version in an `EMetricSpace`, in which injectivity is
a consequence of being an isometry. -/
/-
**Metric._root_.Isometry.coveringNumber_image'** 是 Mathlib 中的一个引理，位于命名空间 `Metric
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covering number of the image of a set under an injective isometry is equal t
o
the covering number of the set.
See `Isometry.coveringNumber_image` for the version in an `EMetricSpace`, in whi
ch injectivity is
a consequence of being an isometry.
-/
lemma _root_.Isometry.coveringNumber_image' {f : X → Y} (hf : Isometry f) (hf_inj : Set.InjOn f A) :
    coveringNumber ε (f '' A) = coveringNumber ε A := by
  refine le_antisymm ?_ ?_
  · simp only [coveringNumber, le_iInf_iff]
    intro C hC_subset hC_cover
    refine (iInf_le _ (C.image f)).trans ?_
    simp only [Set.image_subset_iff]
    have : ↑C ⊆ f ⁻¹' f '' A := hC_subset.trans (Set.subset_preimage_image f A)
    refine (iInf_le _ this).trans ?_
    rw [hf.isCover_image_iff]
    refine (iInf_le _ hC_cover).trans ?_
    exact encard_image_le f C
  · simp only [coveringNumber, le_iInf_iff]
    intro C hC_subset hC_cover
    obtain ⟨C', hC'_subset, rfl⟩ : ∃ C', C' ⊆ A ∧ C = C'.image f := by
      have (x : C) : ∃ y ∈ A, f y = x := by simpa using hC_subset x.2
      choose g hg_mem hg using this
      refine ⟨Set.range g, ?_, ?_⟩
      · rwa [Set.range_subset_iff]
      · ext
        simp
        grind
    refine (iInf_le _ C').trans <| (iInf_le _ hC'_subset).trans ?_
    simp only [hf.isCover_image_iff] at hC_cover
    refine (iInf_le _ hC_cover).trans ?_
    rw [InjOn.encard_image]
    exact hf_inj.mono hC'_subset

/-- The covering number of the image of a set under an injective isometry is equal to
the covering number of the set.
See `Isometry.coveringNumber_image'` for the version in a `PseudoEMetricSpace` and not
an `EMetricSpace`, for which an additional injectivity assumption is needed. -/
/-
**Metric._root_.Isometry.coveringNumber_image** 是 Mathlib 中的一个引理，位于命名空间 `Metric`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covering number of the image of a set under an injective isometry is equal t
o
the covering number of the set.
See `Isometry.coveringNumber_image'` for the version in a `PseudoEMetricSpace` a
nd not
an `EMetricSpace`, for which an additional injectivity assumption is needed.
-/
lemma _root_.Isometry.coveringNumber_image {X : Type*} [EMetricSpace X]
    {f : X → Y} (hf : Isometry f) {A : Set X} :
    coveringNumber ε (f '' A) = coveringNumber ε A :=
  hf.coveringNumber_image' hf.injective.injOn

end Metric

