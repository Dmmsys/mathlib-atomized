/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.EMetricSpace.Pi

/-!
# Diameters of sets in extended metric spaces

In this file we define the diameter of a set in the extended metric space
as an extended nonnegative real number.
-/

@[expose] public section

open Set Filter

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

variable {α X : Type*} {s t : Set X} {x y z : X}

namespace Metric

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

/-- The diameter of a set in a pseudoemetric space as an extended nonnegative real number. -/
/-
**Metric.ediam** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：ediam (s : Set X)
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diameter of a set in a pseudoemetric space as an extended nonnegative real n
umber.
-/
noncomputable def ediam (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y
/-
**Metric.ediam_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_eq_sSup (s : Set X) : ediam s = sSup (image2 edist s s)
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image2`：sSup_image2 {f : β -> γ -> α} {s : Set β} {t : Set γ} : sSu
p (image2 f s t) = ⨆ (a in s) (b in t), f a b
-/
theorem ediam_eq_sSup (s : Set X) : ediam s = sSup (image2 edist s s) := sSup_image2.symm
/-
**Metric.ediam_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_le_iff {d : Real>=0∞} : ediam s <= d ↔ forall x in s, forall y in s,
 edist x y <= d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ediam_le_iff {d : ℝ≥0∞} : ediam s ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d := by
  simp only [ediam, iSup_le_iff]
/-
**Metric.ediam_image_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_image_le_iff {d : Real>=0∞} {f : α -> X} {s : Set α} : ediam (f '' s
) <= d ↔ forall x in s, forall y in s, edist (f x) (f y) <= d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ediam_image_le_iff {d : ℝ≥0∞} {f : α → X} {s : Set α} :
    ediam (f '' s) ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ d := by
  simp only [ediam_le_iff, forall_mem_image]
/-
**Metric.edist_le_of_ediam_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：edist_le_of_ediam_le {d} (hx : x in s) (hy : y in s) (hd : ediam s <= d) :
 edist x y <= d
参数：hx : x in s；hy : y in s；hd : ediam s <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.ediam_le_iff`：ediam_le_iff {d : Real>=0∞} : ediam s <= d ↔ forall
 x in s, forall y in s, edist x y <= d
-/
theorem edist_le_of_ediam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : ediam s ≤ d) : edist x y ≤ d :=
  ediam_le_iff.1 hd x hx y hy

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
/-
**Metric.edist_le_ediam_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：edist_le_ediam_of_mem (hx : x in s) (hy : y in s) : edist x y <= ediam s
参数：hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.edist_le_of_ediam_le`：edist_le_of_ediam_le {d} (hx : x in s) (hy 
: y in s) (hd : ediam s <= d) : edist x y <= d
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If two points belong to some set, their edistance is bounded by the diameter of 
the set
-/
theorem edist_le_ediam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ ediam s :=
  edist_le_of_ediam_le hx hy le_rfl

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
/-
**Metric.ediam_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in s, edist x y <= d)
 : ediam s <= d
参数：h : forall x in s, forall y in s, edist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ediam_le_iff`：ediam_le_iff {d : Real>=0∞} : ediam s <= d ↔ forall
 x in s, forall y in s, edist x y <= d

--- 原说明 ---
If the distance between any two points in a set is bounded by some constant, thi
s constant
bounds the diameter.
-/
theorem ediam_le {d : ℝ≥0∞} (h : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d) : ediam s ≤ d :=
  ediam_le_iff.2 h

/-- The diameter of a subsingleton vanishes. -/
/-
**Metric.ediam_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_subsingleton (hs : s.Subsingleton) : ediam s = 0
参数：hs : s.Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The diameter of a subsingleton vanishes.
-/
theorem ediam_subsingleton (hs : s.Subsingleton) : ediam s = 0 :=
  nonpos_iff_eq_zero.1 <| ediam_le fun _x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

alias _root_.Set.Subsingleton.ediam_eq := ediam_subsingleton

/-- The diameter of the empty set vanishes -/
@[simp]
/-
**Metric.ediam_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_empty : ediam (∅ : Set X) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_subsingleton`：ediam_subsingleton (hs : s.Subsingleton) : ed
iam s = 0
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton

--- 原说明 ---
The diameter of the empty set vanishes
-/
theorem ediam_empty : ediam (∅ : Set X) = 0 :=
  ediam_subsingleton subsingleton_empty

/-- The extended diameter of a singleton vanishes -/
@[simp]
/-
**Metric.ediam_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_singleton : ediam ({x} : Set X) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_subsingleton`：ediam_subsingleton (hs : s.Subsingleton) : ed
iam s = 0
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton

--- 原说明 ---
The extended diameter of a singleton vanishes
-/
theorem ediam_singleton : ediam ({x} : Set X) = 0 :=
  ediam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]
/-
**Metric.ediam_one** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_one [One X] : ediam (1 : Set X) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_singleton`：ediam_singleton : ediam ({x} : Set X) = 0
-/
theorem ediam_one [One X] : ediam (1 : Set X) = 0 :=
  ediam_singleton
/-
**Metric.ediam_iUnion_mem_option** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι -> Set X) : edia
m (⋃ i in o, s i) = ⨆ i in o, ediam (s i)
参数：o : Option ι；s : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Metric.ediam_empty`：ediam_empty : ediam (∅ : Set X) = 0
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `iSup_iSup_eq_right`：iSup_iSup_eq_right {b : β} {f : forall x : β, b = x 
-> α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl
-/
theorem ediam_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι → Set X) :
    ediam (⋃ i ∈ o, s i) = ⨆ i ∈ o, ediam (s i) := by cases o <;> simp
/-
**Metric.ediam_insert** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_insert : ediam (insert x s) = max (⨆ y in s, edist x y) (ediam s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ediam_insert : ediam (insert x s) = max (⨆ y ∈ s, edist x y) (ediam s) :=
  eq_of_forall_ge_iff fun d => by simp +contextual [ediam_le_iff, edist_comm]
/-
**Metric.ediam_pair** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_pair : ediam {x, y} = edist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_insert`：ediam_insert : ediam (insert x s) = max (⨆ y in s, 
edist x y) (ediam s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `Metric.ediam_singleton`：ediam_singleton : ediam ({x} : Set X) = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ediam_pair : ediam {x, y} = edist x y := by simp [ediam_insert]
/-
**Metric.ediam_triple** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_triple : ediam {x, y, z} = max (max (edist x y) (edist x z)) (edist 
y z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_insert`：ediam_insert : ediam (insert x s) = max (⨆ y in s, 
edist x y) (ediam s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
· 使用定理 `iSup_singleton`：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton 
b : Set β), f x = f b
· 使用定理 `Metric.ediam_singleton`：ediam_singleton : ediam ({x} : Set X) = 0
· 使用定理 `max_zero`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Zero α] [IsB
otZeroClass α] (a : α), max a 0 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ediam_triple : ediam {x, y, z} = max (max (edist x y) (edist x z)) (edist y z) := by
  simp only [ediam_insert, iSup_insert, iSup_singleton, ediam_singleton, max_zero]

/-- The extended diameter is monotonous with respect to inclusion -/
@[gcongr]
/-
**Metric.ediam_mono** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_mono (h : s subseteq t) : ediam s <= ediam t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s

--- 原说明 ---
The extended diameter is monotonous with respect to inclusion
-/
theorem ediam_mono (h : s ⊆ t) : ediam s ≤ ediam t :=
  ediam_le fun _x hx _y hy => edist_le_ediam_of_mem (h hx) (h hy)

/-- The extended diameter of a union is controlled by the diameter of the sets,
and the edistance between two points in the sets. -/
/-
**Metric.ediam_union_le_add_edist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_union_le_add_edist (xs : x in s) (yt : y in t) : ediam (s union t) <
= ediam s + edist x y + ediam t
参数：xs : x in s；yt : y in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_triangle4`：edist_triangle4 (x y z t : α) : edist x t <= edist x y 
+ edist y z + edist z t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a

--- 原说明 ---
The extended diameter of a union is controlled by the diameter of the sets,
and the edistance between two points in the sets.
-/
theorem ediam_union_le_add_edist (xs : x ∈ s) (yt : y ∈ t) :
    ediam (s ∪ t) ≤ ediam s + edist x y + ediam t := by
  have A : ∀ a ∈ s, ∀ b ∈ t, edist a b ≤ ediam s + edist x y + ediam t := fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ ≤ ediam s + edist x y + ediam t := by
        gcongr
        exacts [edist_le_ediam_of_mem ha xs, edist_le_ediam_of_mem yt hb]
  refine ediam_le fun a ha b hb => ?_
  rw [mem_union] at ha hb
  rcases ha with h'a | h'a <;> rcases hb with h'b | h'b
  · calc
      edist a b ≤ ediam s := edist_le_ediam_of_mem h'a h'b
      _ ≤ ediam s + (edist x y + ediam t) := le_self_add
      _ = ediam s + edist x y + ediam t := (add_assoc _ _ _).symm
  · exact A a h'a b h'b
  · have Z := A b h'b a h'a
    rwa [edist_comm] at Z
  · calc
      edist a b ≤ ediam t := edist_le_ediam_of_mem h'a h'b
      _ ≤ ediam s + edist x y + ediam t := le_add_self

/-- If two sets have nonempty intersection, then the extended diameter of their union
is estimated from above by the sum of their union. -/
/-
**Metric.ediam_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_union_le (h : (s inter t).Nonempty) : ediam (s union t) <= ediam s +
 ediam t
参数：h : (s inter t).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Metric.ediam_union_le_add_edist`：ediam_union_le_add_edist (xs : x in s) 
(yt : y in t) : ediam (s union t) <= ediam s + edist x y + ediam t

--- 原说明 ---
If two sets have nonempty intersection, then the extended diameter of their unio
n
is estimated from above by the sum of their union.
-/
theorem ediam_union_le (h : (s ∩ t).Nonempty) : ediam (s ∪ t) ≤ ediam s + ediam t := by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using ediam_union_le_add_edist xs xt
/-
**Metric.ediam_closedEBall_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_closedEBall_le {r : Real>=0∞} : ediam (closedEBall x r) <= 2 * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `edist_triangle_right`：edist_triangle_right (x y z : α) : edist x y <= ed
ist x z + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem ediam_closedEBall_le {r : ℝ≥0∞} : ediam (closedEBall x r) ≤ 2 * r :=
  ediam_le fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist b x := edist_triangle_right _ _ _
      _ ≤ r + r := add_le_add ha hb
      _ = 2 * r := (two_mul r).symm
/-
**Metric.ediam_eball_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_eball_le {r : Real>=0∞} : ediam (eball x r) <= 2 * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Metric.eball_subset_closedEBall`：eball_subset_closedEBall : eball x ε su
bseteq closedEBall x ε
· 使用定理 `Metric.ediam_closedEBall_le`：ediam_closedEBall_le {r : Real>=0∞} : ediam
 (closedEBall x r) <= 2 * r
-/
theorem ediam_eball_le {r : ℝ≥0∞} : ediam (eball x r) ≤ 2 * r :=
  le_trans (ediam_mono eball_subset_closedEBall) ediam_closedEBall_le
/-
**Metric.ediam_pi_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_pi_le_of_le {ι : Type*} {X : ι -> Type*} [Fintype ι] [forall i, Pseu
doEMetricSpace (X i)] {s : forall i : ι, Set (X i)} {c : Real>=0∞} (h : forall b
, ediam (s b) <= c) : ediam (Set.pi univ s) <= c
参数：X i；X i；h : forall b, ediam (s b) <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `edist_pi_le_iff`：edist_pi_le_iff [forall b, EDist (X b)] {f g : forall b
, X b} {d : Real>=0∞} : edist f g <= d ↔ forall b, edist (f b) (g b) <= d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.ediam_le_iff`：ediam_le_iff {d : Real>=0∞} : ediam s <= d ↔ forall
 x in s, forall y in s, edist x y <= d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
-/
theorem ediam_pi_le_of_le {ι : Type*} {X : ι → Type*} [Fintype ι] [∀ i, PseudoEMetricSpace (X i)]
    {s : ∀ i : ι, Set (X i)} {c : ℝ≥0∞} (h : ∀ b, ediam (s b) ≤ c) : ediam (Set.pi univ s) ≤ c := by
  refine ediam_le fun x hx y hy => edist_pi_le_iff.mpr ?_
  rw [mem_univ_pi] at hx hy
  exact fun b => ediam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

end PseudoEMetricSpace

section EMetricSpace

variable [EMetricSpace X]

/-
**Metric.ediam_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_eq_zero_iff : ediam s = 0 ↔ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `edist_le_zero`：edist_le_zero {x y : γ} : edist x y <= 0 ↔ x = y
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `Metric.ediam_subsingleton`：ediam_subsingleton (hs : s.Subsingleton) : ed
iam s = 0
-/
theorem ediam_eq_zero_iff : ediam s = 0 ↔ s.Subsingleton :=
  ⟨fun h _x hx _y hy => edist_le_zero.1 <| h ▸ edist_le_ediam_of_mem hx hy, ediam_subsingleton⟩
/-
**Metric.ediam_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_pos_iff : 0 < ediam s ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ediam_pos_iff : 0 < ediam s ↔ s.Nontrivial := by
  simp only [pos_iff_ne_zero, Ne, ediam_eq_zero_iff, Set.not_subsingleton_iff]
/-
**Metric.ediam_pos_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_pos_iff' : 0 < ediam s ↔ exists x in s, exists y in s, x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ediam_pos_iff' : 0 < ediam s ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  simp only [ediam_pos_iff, Set.Nontrivial]

end EMetricSpace

end Metric

namespace EMetric

open Metric

@[deprecated (since := "2026-01-04")] alias diam := Metric.ediam
@[deprecated (since := "2026-01-04")] alias diam_eq_sSup := ediam_eq_sSup
@[deprecated (since := "2026-01-04")] alias diam_le_iff := ediam_le_iff
@[deprecated (since := "2026-01-04")] alias diam_image_le_iff := ediam_image_le_iff
@[deprecated (since := "2026-01-04")] alias edist_le_of_diam_le := edist_le_of_ediam_le
@[deprecated (since := "2026-01-04")] alias edist_le_diam_of_mem := edist_le_ediam_of_mem
@[deprecated (since := "2026-01-04")] alias diam_le := ediam_le
@[deprecated (since := "2026-01-04")] alias diam_subsingleton := ediam_subsingleton
@[deprecated (since := "2026-01-04")] alias diam_empty := ediam_empty
@[deprecated (since := "2026-01-04")] alias diam_singleton := ediam_singleton
@[deprecated (since := "2026-01-04")] alias diam_zero := ediam_zero
@[to_additive existing, deprecated (since := "2026-01-04")] alias diam_one := ediam_one
@[deprecated (since := "2026-01-04")] alias diam_iUnion_mem_option := ediam_iUnion_mem_option
@[deprecated (since := "2026-01-04")] alias diam_insert := ediam_insert
@[deprecated (since := "2026-01-04")] alias diam_pair := ediam_pair
@[deprecated (since := "2026-01-04")] alias diam_triple := ediam_triple
@[deprecated (since := "2026-01-04")] alias diam_mono := ediam_mono
@[deprecated (since := "2026-01-04")] alias diam_union := ediam_union_le_add_edist
@[deprecated (since := "2026-01-04")] alias diam_union' := ediam_union_le
@[deprecated (since := "2026-01-04")] alias diam_closedBall := ediam_closedEBall_le
@[deprecated (since := "2026-01-04")] alias diam_ball := ediam_eball_le
@[deprecated (since := "2026-01-04")] alias diam_pi_le_of_le := ediam_pi_le_of_le
@[deprecated (since := "2026-01-04")] alias diam_eq_zero_iff := ediam_eq_zero_iff
@[deprecated (since := "2026-01-04")] alias diam_pos_iff := ediam_pos_iff
@[deprecated (since := "2026-01-04")] alias diam_pos_iff' := ediam_pos_iff'

end EMetric

