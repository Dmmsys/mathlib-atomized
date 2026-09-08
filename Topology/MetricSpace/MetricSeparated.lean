/-
Copyright (c) 2021 Yury Kudryashov, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Data.Rel.Separated
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Metric separation

This file defines a few notions of separations of sets in a metric space.


The first notion (`Metric.IsSeparated`) is quantitative and describes a single set: a set `s` is
`ε`-separated if the distance between any two distinct elements is strictly greater than `ε`

The second notion (`Metric.AreSeparated`) is qualitative and about two sets: Two sets `s` and `t`
are separated if the distance between `x ∈ s` and `y ∈ t` is bounded from below by a positive
constant.
-/

@[expose] public section

open EMetric Set
open scoped NNReal ENNReal

noncomputable section

namespace Metric
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
variable {s t : Set X} {ε δ : ℝ≥0∞} {x : X} {y : Y}

/-!
### Metric-separated sets

In this section we define the predicate `Metric.IsSeparated` for `ε`-separated sets.
-/

/-- A set `s` is `ε`-separated if the extended distance between any two distinct
elements is strictly greater than `ε`. -/
/-
**Metric.IsSeparated** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：IsSeparated (ε : Real>=0∞) (s : Set X) : Prop
参数：ε : Real>=0∞；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is `ε`-separated if the extended distance between any two distinct
elements is strictly greater than `ε`.
-/
def IsSeparated (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε < edist · ·)
/-
**Metric.isSeparated_iff_setRelIsSeparated** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isSeparated_iff_setRelIsSeparated : IsSeparated ε s ↔ SetRel.IsSeparated {
(x, y) | edist x y <= ε} s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSeparated_iff_setRelIsSeparated :
    IsSeparated ε s ↔ SetRel.IsSeparated {(x, y) | edist x y ≤ ε} s := by
  simp [IsSeparated, SetRel.IsSeparated]

@[grind .]
/-
**Metric.IsSeparated.empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsSeparated`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {ε : ENNReal}, Metric.IsSep
arated ε ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_empty`：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pa
irwise r
-/
protected lemma IsSeparated.empty : IsSeparated ε (∅ : Set X) := pairwise_empty _
/-
**Metric.IsSeparated.singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsSeparated`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {ε : ENNReal} {x : X}, Metr
ic.IsSeparated ε {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_singleton`：pairwise_singleton (a : α) (r : α -> α -> Prop) 
: Set.Pairwise {a} r
-/
protected lemma IsSeparated.singleton : IsSeparated ε {x} := pairwise_singleton ..
/-
**Metric.IsSeparated.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsSeparat
ed`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {s : Set X} {ε : ENNReal}, 
s.Subsingleton → Metric.IsSeparated ε s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
@[simp] lemma IsSeparated.of_subsingleton (hs : s.Subsingleton) : IsSeparated ε s := hs.pairwise _

alias _root_.Set.Subsingleton.isSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.anti (hεδ : ε ≤ δ) (hs : IsSeparated δ s) : IsSeparated ε s :=
  hs.mono' fun _ _ ↦ hεδ.trans_lt
/-
**Metric.IsSeparated.subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsSeparated`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {s t : Set X} {ε : ENNReal}
,   s ⊆ t → Metric.IsSeparated ε t → Metric.IsSeparated ε s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
lemma IsSeparated.subset (hst : s ⊆ t) (hs : IsSeparated ε t) : IsSeparated ε s := hs.mono hst
/-
**Metric.isSeparated_insert** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isSeparated_insert : IsSeparated ε (insert x s) ↔ IsSeparated ε s ∧ forall
 y in s, x != y -> ε < edist x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.pairwise_insert_of_symm`：pairwise_insert_of_symm [Std.Symm r] : (ins
ert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b
-/
lemma isSeparated_insert :
    IsSeparated ε (insert x s) ↔ IsSeparated ε s ∧ ∀ y ∈ s, x ≠ y → ε < edist x y :=
  have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm
/-
**Metric.isSeparated_insert_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isSeparated_insert_of_notMem (hx : x ∉ s) : IsSeparated ε (insert x s) ↔ I
sSeparated ε s ∧ forall y in s, ε < edist x y
参数：hx : x ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.pairwise_insert_of_symm_of_notMem`：pairwise_insert_of_symm_of_notMem
 [Std.Symm r] (ha : a ∉ s) : (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b i
n s, r a b
-/
lemma isSeparated_insert_of_notMem (hx : x ∉ s) :
    IsSeparated ε (insert x s) ↔ IsSeparated ε s ∧ ∀ y ∈ s, ε < edist x y :=
  have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm_of_notMem hx
/-
**Metric.IsSeparated.insert** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsSeparated`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {s : Set X} {ε : ENNReal} {
x : X},   Metric.IsSeparated ε s → (∀ y ∈ s, x ≠ y → ε < edist x y) → Metric.IsS
eparated ε (insert x s)
参数：∀ y ∈ s, x ≠ y → ε < edist x y；insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Metric.isSeparated_insert`：isSeparated_insert : IsSeparated ε (insert x 
s) ↔ IsSeparated ε s ∧ forall y in s, x != y -> ε < edist x y
-/
protected lemma IsSeparated.insert (hs : IsSeparated ε s) (h : ∀ y ∈ s, x ≠ y → ε < edist x y) :
    IsSeparated ε (insert x s) := isSeparated_insert.2 ⟨hs, h⟩

@[simp]
/-
**Metric.isSeparated_zero** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isSeparated_zero {X : Type*} [EMetricSpace X] (s : Set X) : IsSeparated 0 
s
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isSeparated_zero {X : Type*} [EMetricSpace X] (s : Set X) : IsSeparated 0 s := by
  simp [IsSeparated, Set.Pairwise]
/-
**Metric.IsSeparated.image_antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsSep
arated`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {s : Set X}   {ε K₁ : NNReal} {f : X → Y},   Metric.IsSepara
ted (↑ε) s → AntilipschitzWith K₁ f → 0 < K₁ → Metric.IsSeparated (↑(ε / K₁)) (f
 '' s)
参数：↑ε；↑(ε / K₁)；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.div_lt_of_lt_mul`：div_lt_of_lt_mul (h : a < b * c) : a / c < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma IsSeparated.image_antilipschitz {ε K₁ : ℝ≥0} {f : X → Y}
    (hs : IsSeparated ε s) (hf : AntilipschitzWith K₁ f) (hK₁ : 0 < K₁) :
    IsSeparated ↑(ε / K₁) (f '' s) := by
  rintro x' ⟨x, hx, rfl⟩ y' ⟨y, hy, rfl⟩ hne
  have hmul : (↑ε : ℝ≥0∞) < edist (f x) (f y) * ↑K₁ :=
    lt_of_lt_of_le (hs hx hy (by grind)) (by rw [mul_comm]; exact hf x y)
  exact ENNReal.coe_div hK₁.ne' ▸ ENNReal.div_lt_of_lt_mul hmul

/-!
### Metric separated pairs of sets

In this section we define the predicate `Metric.AreSeparated`. We say that two sets in an
(extended) metric space are *metric separated* if the (extended) distance between `x ∈ s` and
`y ∈ t` is bounded from below by a positive constant.

This notion is useful, e.g., to define metric outer measures.
-/

/-- Two sets in an (extended) metric space are called *metric separated* if the (extended) distance
between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant. -/
/-
**Metric.AreSeparated** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：AreSeparated (s t : Set X)
参数：s t : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets in an (extended) metric space are called *metric separated* if the (ext
ended) distance
between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant.
-/
def AreSeparated (s t : Set X) := ∃ r, r ≠ 0 ∧ ∀ x ∈ s, ∀ y ∈ t, r ≤ edist x y

namespace AreSeparated

@[symm]
/-
**Metric.AreSeparated.symm** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`。
形式化陈述：symm (h : AreSeparated s t) : AreSeparated t s
参数：h : AreSeparated s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
-/
theorem symm (h : AreSeparated s t) : AreSeparated t s :=
  let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩
/-
**Metric.AreSeparated.comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`。
形式化陈述：comm : AreSeparated s t ↔ AreSeparated t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.symm`：symm (h : AreSeparated s t) : AreSeparated t s
-/
theorem comm : AreSeparated s t ↔ AreSeparated t s := ⟨symm, symm⟩

@[simp]
/-
**Metric.AreSeparated.empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`
。
形式化陈述：empty_left (s : Set X) : AreSeparated ∅ s
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem empty_left (s : Set X) : AreSeparated ∅ s :=
  ⟨1, one_ne_zero, fun _x => False.elim⟩

@[simp]
/-
**Metric.AreSeparated.empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated
`。
形式化陈述：empty_right (s : Set X) : AreSeparated s ∅
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.symm`：symm (h : AreSeparated s t) : AreSeparated t s
· 使用定理 `Metric.AreSeparated.empty_left`：empty_left (s : Set X) : AreSeparated ∅ 
s
-/
theorem empty_right (s : Set X) : AreSeparated s ∅ :=
  (empty_left s).symm
/-
**Metric.AreSeparated.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {s t : Set X}, Metric.AreSe
parated s t → Disjoint s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
protected theorem disjoint (h : AreSeparated s t) : Disjoint s t :=
  let ⟨r, r0, hr⟩ := h
  Set.disjoint_left.mpr fun x hx1 hx2 => r0 <| by simpa using hr x hx1 x hx2
/-
**Metric.AreSeparated.subset_compl_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSe
parated`。
形式化陈述：subset_compl_right (h : AreSeparated s t) : s subseteq tᶜ
参数：h : AreSeparated s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Metric.AreSeparated.disjoint`：∀ {X : Type u_1} [inst : PseudoEMetricSpac
e X] {s t : Set X}, Metric.AreSeparated s t → Disjoint s t
-/
theorem subset_compl_right (h : AreSeparated s t) : s ⊆ tᶜ := fun _ hs ht =>
  h.disjoint.le_bot ⟨hs, ht⟩

@[gcongr, mono]
/-
**Metric.AreSeparated.mono** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`。
形式化陈述：mono {s' t'} (hs : s subseteq s') (ht : t subseteq t') : AreSeparated s' t
' -> AreSeparated s t
参数：hs : s subseteq s'；ht : t subseteq t'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono {s' t'} (hs : s ⊆ s') (ht : t ⊆ t') :
    AreSeparated s' t' → AreSeparated s t := fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩
/-
**Metric.AreSeparated.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`。
形式化陈述：mono_left {s'} (h' : AreSeparated s' t) (hs : s subseteq s') : AreSeparate
d s t
参数：h' : AreSeparated s' t；hs : s subseteq s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.mono`：mono {s' t'} (hs : s subseteq s') (ht : t subs
eteq t') : AreSeparated s' t' -> AreSeparated s t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem mono_left {s'} (h' : AreSeparated s' t) (hs : s ⊆ s') : AreSeparated s t :=
  h'.mono hs Subset.rfl
/-
**Metric.AreSeparated.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`
。
形式化陈述：mono_right {t'} (h' : AreSeparated s t') (ht : t subseteq t') : AreSeparat
ed s t
参数：h' : AreSeparated s t'；ht : t subseteq t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.mono`：mono {s' t'} (hs : s subseteq s') (ht : t subs
eteq t') : AreSeparated s' t' -> AreSeparated s t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem mono_right {t'} (h' : AreSeparated s t') (ht : t ⊆ t') : AreSeparated s t :=
  h'.mono Subset.rfl ht
/-
**Metric.AreSeparated.union_left** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated`
。
形式化陈述：union_left {s'} (h : AreSeparated s t) (h' : AreSeparated s' t) : AreSepar
ated (s union s') t
参数：h : AreSeparated s t；h' : AreSeparated s' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
theorem union_left {s'} (h : AreSeparated s t) (h' : AreSeparated s' t) :
    AreSeparated (s ∪ s') t := by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine ⟨min r r', ?_, fun x hx y hy => hx.elim ?_ ?_⟩
  · rw [← pos_iff_ne_zero] at r0 r0' ⊢
    exact lt_min r0 r0'
  · exact fun hx => (min_le_left _ _).trans (hr _ hx _ hy)
  · exact fun hx => (min_le_right _ _).trans (hr' _ hx _ hy)

@[simp]
/-
**Metric.AreSeparated.union_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSepara
ted`。
形式化陈述：union_left_iff {s'} : AreSeparated (s union s') t ↔ AreSeparated s t ∧ Are
Separated s' t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.mono_left`：mono_left {s'} (h' : AreSeparated s' t) (
hs : s subseteq s') : AreSeparated s t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Metric.AreSeparated.union_left`：union_left {s'} (h : AreSeparated s t) (
h' : AreSeparated s' t) : AreSeparated (s union s') t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem union_left_iff {s'} :
    AreSeparated (s ∪ s') t ↔ AreSeparated s t ∧ AreSeparated s' t :=
  ⟨fun h => ⟨h.mono_left subset_union_left, h.mono_left subset_union_right⟩, fun h =>
    h.1.union_left h.2⟩
/-
**Metric.AreSeparated.union_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSeparated
`。
形式化陈述：union_right {t'} (h : AreSeparated s t) (h' : AreSeparated s t') : AreSepa
rated s (t union t')
参数：h : AreSeparated s t；h' : AreSeparated s t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.symm`：symm (h : AreSeparated s t) : AreSeparated t s
· 使用定理 `Metric.AreSeparated.union_left`：union_left {s'} (h : AreSeparated s t) (
h' : AreSeparated s' t) : AreSeparated (s union s') t
-/
theorem union_right {t'} (h : AreSeparated s t) (h' : AreSeparated s t') :
    AreSeparated s (t ∪ t') :=
  (h.symm.union_left h'.symm).symm

@[simp]
/-
**Metric.AreSeparated.union_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric.AreSepar
ated`。
形式化陈述：union_right_iff {t'} : AreSeparated s (t union t') ↔ AreSeparated s t ∧ Ar
eSeparated s t'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.AreSeparated.comm`：comm : AreSeparated s t ↔ AreSeparated t s
· 使用定理 `Metric.AreSeparated.union_left_iff`：union_left_iff {s'} : AreSeparated (
s union s') t ↔ AreSeparated s t ∧ AreSeparated s' t
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
-/
theorem union_right_iff {t'} :
    AreSeparated s (t ∪ t') ↔ AreSeparated s t ∧ AreSeparated s t' :=
  comm.trans <| union_left_iff.trans <| and_congr comm comm
/-
**Metric.AreSeparated.finite_iUnion_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric.A
reSeparated`。
形式化陈述：finite_iUnion_left_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> S
et X} {t : Set X} : AreSeparated (⋃ i in I, s i) t ↔ forall i in I, AreSeparated
 (s i) t
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `Set.forall_mem_insert`：forall_mem_insert {P : α -> Prop} {a : α} {s : Se
t α} : (forall x in insert a s, P x) ↔ P a ∧ forall x in s, P x
· 使用定理 `Metric.AreSeparated.union_left_iff`：union_left_iff {s'} : AreSeparated (
s union s') t ↔ AreSeparated s t ∧ AreSeparated s' t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem finite_iUnion_left_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set X}
    {t : Set X} : AreSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, AreSeparated (s i) t := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hI => rw [biUnion_insert, forall_mem_insert, union_left_iff, hI]

alias ⟨_, finite_iUnion_left⟩ := finite_iUnion_left_iff
/-
**Metric.AreSeparated.finite_iUnion_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric.
AreSeparated`。
形式化陈述：finite_iUnion_right_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : Set X
} {t : ι -> Set X} : AreSeparated s (⋃ i in I, t i) ↔ forall i in I, AreSeparate
d s (t i)
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.AreSeparated.comm`：comm : AreSeparated s t ↔ AreSeparated t s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Metric.AreSeparated.finite_iUnion_left_iff`：finite_iUnion_left_iff {ι : 
Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set X} {t : Set X} : AreSeparated (
⋃ i in I, s i) t ↔ forall i in I…
-/
theorem finite_iUnion_right_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : Set X}
    {t : ι → Set X} : AreSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, AreSeparated s (t i) := by
  simpa only [@comm _ _ s] using finite_iUnion_left_iff hI

@[simp]
/-
**Metric.AreSeparated.finset_iUnion_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric.A
reSeparated`。
形式化陈述：finset_iUnion_left_iff {ι : Type*} {I : Finset ι} {s : ι -> Set X} {t : Se
t X} : AreSeparated (⋃ i in I, s i) t ↔ forall i in I, AreSeparated (s i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.finite_iUnion_left_iff`：finite_iUnion_left_iff {ι : 
Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set X} {t : Set X} : AreSeparated (
⋃ i in I, s i) t ↔ forall i in I…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem finset_iUnion_left_iff {ι : Type*} {I : Finset ι} {s : ι → Set X} {t : Set X} :
    AreSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, AreSeparated (s i) t :=
  finite_iUnion_left_iff I.finite_toSet

alias ⟨_, finset_iUnion_left⟩ := finset_iUnion_left_iff

@[simp]
/-
**Metric.AreSeparated.finset_iUnion_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric.
AreSeparated`。
形式化陈述：finset_iUnion_right_iff {ι : Type*} {I : Finset ι} {s : Set X} {t : ι -> S
et X} : AreSeparated s (⋃ i in I, t i) ↔ forall i in I, AreSeparated s (t i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.AreSeparated.finite_iUnion_right_iff`：finite_iUnion_right_iff {ι 
: Type*} {I : Set ι} (hI : I.Finite) {s : Set X} {t : ι -> Set X} : AreSeparated
 s (⋃ i in I, t i) ↔ forall i in …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem finset_iUnion_right_iff {ι : Type*} {I : Finset ι} {s : Set X} {t : ι → Set X} :
    AreSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, AreSeparated s (t i) :=
  finite_iUnion_right_iff I.finite_toSet

alias ⟨_, finset_iUnion_right⟩ := finset_iUnion_right_iff

end Metric.AreSeparated

