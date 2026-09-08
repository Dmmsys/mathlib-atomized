/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.ENNReal.Action
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.OuterMeasure.Caratheodory

/-!
# Induced Outer Measure

We can extend a function defined on a subset of `Set α` to an outer measure.
The underlying function is called `extend`, and the measure it induces is called
`inducedOuterMeasure`.

Some lemmas below are proven twice, once in the general case, and once where the function `m`
is only defined on measurable sets (i.e. when `P = MeasurableSet`). In the latter cases, we can
remove some hypotheses in the statement. The general version has the same name, but with a prime
at the end.

## Tags

outer measure

-/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory

open OuterMeasure


section Extend

variable {R α : Type*} {P : α → Prop}
variable (m : ∀ s : α, P s → ℝ≥0∞)

/-- We can trivially extend a function defined on a subclass of objects (with codomain `ℝ≥0∞`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
/-
**MeasureTheory.extend** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：extend (s : α) : Real>=0∞
参数：s : α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can trivially extend a function defined on a subclass of objects (with codoma
in `ℝ≥0∞`)
  to all objects by defining it to be `∞` on the objects not in the class.
-/
def extend (s : α) : ℝ≥0∞ :=
  ⨅ h : P s, m s h
/-
**MeasureTheory.extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_eq {s : α} (h : P s) : extend m s = m s h
参数：h : P s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_eq {s : α} (h : P s) : extend m s = m s h := by simp [extend, h]
/-
**MeasureTheory.extend_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞
参数：h : ¬P s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞ := by simp [extend, h]
/-
**MeasureTheory.smul_extend** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：smul_extend [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R
 Real>=0∞ Real>=0∞] [Module.IsTorsionFree R Real>=0∞] {c : R} (hc : c != 0) : c 
• extend m = extend fun s h => c • m s h
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.smul_top`：smul_top {R : Type*} [Semiring R] [IsDomain R] [Module
 R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] [Module.IsTorsionFree R Real>=0
∞] [De…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem smul_extend [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [Module.IsTorsionFree R ℝ≥0∞] {c : R} (hc : c ≠ 0) :
    c • extend m = extend fun s h => c • m s h := by
  classical
  ext s; by_cases h : P s <;> simp [extend, ENNReal.smul_top, *]
/-
**MeasureTheory.ennreal_smul_extend** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ennreal_smul_extend {c : Real>=0∞} (hc : c != 0) : c • extend m = extend f
un s h => c • m s h
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
-/
lemma ennreal_smul_extend {c : ℝ≥0∞} (hc : c ≠ 0) : c • extend m = extend fun s h => c • m s h := by
  ext s; by_cases h : P s <;> simp [extend, *]
/-
**MeasureTheory.le_extend** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_extend {s : α} (h : P s) : m s h <= extend m s
参数：h : P s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem le_extend {s : α} (h : P s) : m s h ≤ extend m s := by
  simp only [extend, le_iInf_iff]
  intro
  rfl

-- TODO: why this is a bad `congr` lemma?
/-
**MeasureTheory.extend_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_congr {β : Type*} {Pb : β -> Prop} {mb : forall s : β, Pb s -> Real
>=0∞} {sa : α} {sb : β} (hP : P sa ↔ Pb sb) (hm : forall (ha : P sa) (hb : Pb sb
), m sa ha = mb sb hb) : extend m sa = extend mb sb
参数：hP : P sa ↔ Pb sb；hm : forall (ha : P sa) (hb : Pb sb), m sa ha = mb sb hb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem extend_congr {β : Type*} {Pb : β → Prop} {mb : ∀ s : β, Pb s → ℝ≥0∞} {sa : α} {sb : β}
    (hP : P sa ↔ Pb sb) (hm : ∀ (ha : P sa) (hb : Pb sb), m sa ha = mb sb hb) :
    extend m sa = extend mb sb :=
  iInf_congr_Prop hP fun _h => hm _ _

@[simp]
/-
**MeasureTheory.extend_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_top {α : Type*} {P : α -> Prop} : extend (fun _ _ => ∞ : forall s :
 α, P s -> Real>=0∞) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_eq_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{s : ι → α}, iInf s = ⊤ ↔ ∀ (i : ι), s i = ⊤
-/
theorem extend_top {α : Type*} {P : α → Prop} : extend (fun _ _ => ∞ : ∀ s : α, P s → ℝ≥0∞) = ⊤ :=
  funext fun _ => iInf_eq_top.mpr fun _ => rfl

end Extend

section ExtendSet

variable {α : Type*} {P : Set α → Prop}
variable {m : ∀ s : Set α, P s → ℝ≥0∞}
variable (P0 : P ∅) (m0 : m ∅ P0 = 0)
variable (PU : ∀ ⦃f : ℕ → Set α⦄ (_hm : ∀ i, P (f i)), P (⋃ i, f i))
variable
  (mU :
    ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, P (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i))

variable (msU : ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, P (f i)), m (⋃ i, f i) (PU hm) ≤ ∑' i, m (f i) (hm i))
variable (m_mono : ∀ ⦃s₁ s₂ : Set α⦄ (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)

/-
**MeasureTheory.extend_iUnion_nat** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_iUnion_nat {f : Nat -> Set α} (hm : forall i, P (f i)) (mU : m (⋃ i
, f i) (PU hm) = ∑' i, m (f i) (hm i)) : extend m (⋃ i, f i) = ∑' i, extend m (f
 i)
参数：hm : forall i, P (f i)；mU : m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem extend_iUnion_nat {f : ℕ → Set α} (hm : ∀ i, P (f i))
    (mU : m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i)) :
    extend m (⋃ i, f i) = ∑' i, extend m (f i) :=
  (extend_eq _ _).trans <|
    mU.trans <| by
      congr with i
      rw [extend_eq]

include P0 m0 in
/-
**MeasureTheory.extend_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_empty : extend m ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
-/
theorem extend_empty : extend m ∅ = 0 :=
  (extend_eq _ P0).trans m0

section Subadditive

include PU msU in
/-
**MeasureTheory.extend_iUnion_le_tsum_nat'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：extend_iUnion_le_tsum_nat' (s : Nat -> Set α) : extend m (⋃ i, s i) <= ∑' 
i, extend m (s i)
参数：s : Nat -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `ENNReal.le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (a : α), f a ≤ ∑' (a
 : α), f a
-/
theorem extend_iUnion_le_tsum_nat' (s : ℕ → Set α) :
    extend m (⋃ i, s i) ≤ ∑' i, extend m (s i) := by
  by_cases! h : ∀ i, P (s i)
  · rw [extend_eq _ (PU h), congr_arg tsum _]
    · apply msU h
    funext i
    apply extend_eq _ (h i)
  · obtain ⟨i, hi⟩ := h
    exact le_trans (le_iInf fun h => hi.elim h) (ENNReal.le_tsum i)

end Subadditive

section Mono

include m_mono in
/-
**MeasureTheory.extend_mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_mono' ⦃s₁ s₂ : Set α⦄ (h₁ : P s₁) (hs : s₁ subseteq s₂) : extend m 
s₁ <= extend m s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
-/
theorem extend_mono' ⦃s₁ s₂ : Set α⦄ (h₁ : P s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ := by
  refine le_iInf ?_
  intro h₂
  rw [extend_eq m h₁]
  exact m_mono h₁ h₂ hs

end Mono

section Unions

include P0 m0 PU mU in
/-
**MeasureTheory.extend_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_iUnion {β} [Countable β] {f : β -> Set α} (hd : Pairwise (Disjoint 
on f)) (hm : forall i, P (f i)) : extend m (⋃ i, f i) = ∑' i, extend m (f i)
参数：hd : Pairwise (Disjoint on f)；hm : forall i, P (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_encodable`：nonempty_encodable (α : Type*) [Countable α] : Nonem
pty (Encodable α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Encodable.iUnion_decode₂`：iUnion_decode₂ (f : β -> Set α) : ⋃ (i : Nat) 
(b in decode₂ β i), f b = ⋃ b, f b
· 使用定理 `tsum_iUnion_decode₂`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 :
 TopologicalSpace M] {α : Type u_3} {β : Type u_4}   [inst_2 : Encodable β] (m :
 Set α → …
· 使用定理 `MeasureTheory.extend_empty`：extend_empty : extend m ∅ = 0
· 使用定理 `MeasureTheory.extend_iUnion_nat`：extend_iUnion_nat {f : Nat -> Set α} (h
m : forall i, P (f i)) (mU : m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i)) : exte
nd m (⋃ i, f i) = ∑' …
· 使用定理 `Encodable.iUnion_decode₂_cases`：iUnion_decode₂_cases {f : β -> Set α} {C
 : Set α -> Prop} (H0 : C ∅) (H1 : forall b, C (f b)) {n} : C (⋃ b in decode₂ β 
n, f b)
· 使用定理 `Encodable.iUnion_decode₂_disjoint_on`：iUnion_decode₂_disjoint_on {f : β 
-> Set α} (hd : Pairwise (Disjoint on f)) : Pairwise (Disjoint on fun i => ⋃ b i
n decode₂ β i, f b)
-/
theorem extend_iUnion {β} [Countable β] {f : β → Set α} (hd : Pairwise (Disjoint on f))
    (hm : ∀ i, P (f i)) : extend m (⋃ i, f i) = ∑' i, extend m (f i) := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂, ← tsum_iUnion_decode₂]
  · exact
      extend_iUnion_nat PU (fun n => Encodable.iUnion_decode₂_cases P0 hm)
        (mU _ (Encodable.iUnion_decode₂_disjoint_on hd))
  · exact extend_empty P0 m0

include P0 m0 PU mU in
/-
**MeasureTheory.extend_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_union {s₁ s₂ : Set α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂)
 : extend m (s₁ union s₂) = extend m s₁ + extend m s₂
参数：hd : Disjoint s₁ s₂；h₁ : P s₁；h₂ : P s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `MeasureTheory.extend_iUnion`：extend_iUnion {β} [Countable β] {f : β -> S
et α} (hd : Pairwise (Disjoint on f)) (hm : forall i, P (f i)) : extend m (⋃ i, 
f i) = ∑' i, exte…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pairwise_disjoint_on_bool`：pairwise_disjoint_on_bool [PartialOrder α] [O
rderBot α] {a b : α} : Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b
· 使用定理 `Bool.forall_bool`：∀ {p : Bool → Prop}, (∀ (b : Bool), p b) ↔ p false ∧ p
 true
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_union {s₁ s₂ : Set α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
    extend m (s₁ ∪ s₂) = extend m s₁ + extend m s₂ := by
  rw [union_eq_iUnion,
    extend_iUnion P0 m0 PU mU (pairwise_disjoint_on_bool.2 hd) (Bool.forall_bool.2 ⟨h₂, h₁⟩),
    tsum_fintype]
  simp

end Unions

variable (m)

/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
/-
**MeasureTheory.inducedOuterMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：inducedOuterMeasure : OuterMeasure α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.extend_empty`：extend_empty : extend m ∅ = 0

--- 原说明 ---
Given an arbitrary function on a subset of sets, we can define the outer measure
 corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the dom
ain of `m`).
-/
def inducedOuterMeasure : OuterMeasure α :=
  OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)

variable {m P0 m0}
/-
**MeasureTheory.le_inducedOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：le_inducedOuterMeasure {μ : OuterMeasure α} : μ <= inducedOuterMeasure m P
0 m0 ↔ forall (s) (hs : P s), μ s <= m s hs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.extend_empty`：extend_empty : extend m ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.le_ofFunction`：le_ofFunction {μ : OuterMeasur
e α} : μ <= OuterMeasure.ofFunction m m_empty ↔ forall s, μ s <= m s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
-/
theorem le_inducedOuterMeasure {μ : OuterMeasure α} :
    μ ≤ inducedOuterMeasure m P0 m0 ↔ ∀ (s) (hs : P s), μ s ≤ m s hs :=
  le_ofFunction.trans <| forall_congr' fun _s => le_iInf_iff

/-- If `P u` is `False` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = inducedOuterMeasure m P0 m0`.

E.g., if `α` is an (e)metric space and `P u = diam u < r`, then this lemma implies that
`μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s` and `y ∈ t`. -/
/-
**MeasureTheory.inducedOuterMeasure_union_of_false_of_nonempty_inter** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：inducedOuterMeasure_union_of_false_of_nonempty_inter {s t : Set α} (h : fo
rall u, (s inter u).Nonempty -> (t inter u).Nonempty -> ¬P u) : inducedOuterMeas
ure m P0 m0 (s union t) = inducedOuterMeasure m P0 m0 s + inducedOuterMeasure m 
P0 m0 t
参数：h : forall u, (s inter u).Nonempty -> (t inter u).Nonempty -> ¬P u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_union_of_top_of_nonempty_inter`：of
Function_union_of_top_of_nonempty_inter {s t : Set α} (h : forall u, (s inter u)
.Nonempty -> (t inter u).Nonempty -> m u = ∞) : OuterMeasu…
· 使用定理 `MeasureTheory.extend_empty`：extend_empty : extend m ∅ = 0
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤

--- 原说明 ---
If `P u` is `False` for any set `u` that has nonempty intersection both with `s`
 and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = inducedOuterMeasure m P0 m0`.

E.g., if `α` is an (e)metric space and `P u = diam u < r`, then this lemma impli
es that
`μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s
` and `y ∈ t`.
-/
theorem inducedOuterMeasure_union_of_false_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → ¬P u) :
    inducedOuterMeasure m P0 m0 (s ∪ t) =
      inducedOuterMeasure m P0 m0 s + inducedOuterMeasure m P0 m0 t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hsu htu => @iInf_of_empty _ _ _ ⟨h u hsu htu⟩ _

include PU msU m_mono
/-
**MeasureTheory.inducedOuterMeasure_eq_extend'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：inducedOuterMeasure_eq_extend' {s : Set α} (hs : P s) : inducedOuterMeasur
e m P0 m0 s = extend m s
参数：hs : P s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_eq`：ofFunction_eq (s : Set α) (m_m
ono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t) (m_subadd : forall s : Nat
 -> Set α, m (⋃ i, s i) <= ∑' …
· 使用定理 `MeasureTheory.extend_empty`：extend_empty : extend m ∅ = 0
· 使用定理 `MeasureTheory.extend_mono'`：extend_mono' ⦃s₁ s₂ : Set α⦄ (h₁ : P s₁) (hs
 : s₁ subseteq s₂) : extend m s₁ <= extend m s₂
· 使用定理 `MeasureTheory.extend_iUnion_le_tsum_nat'`：extend_iUnion_le_tsum_nat' (s 
: Nat -> Set α) : extend m (⋃ i, s i) <= ∑' i, extend m (s i)
-/
theorem inducedOuterMeasure_eq_extend' {s : Set α} (hs : P s) :
    inducedOuterMeasure m P0 m0 s = extend m s :=
  ofFunction_eq s (fun _t => extend_mono' m_mono hs) (extend_iUnion_le_tsum_nat' PU msU)
/-
**MeasureTheory.inducedOuterMeasure_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：inducedOuterMeasure_eq' {s : Set α} (hs : P s) : inducedOuterMeasure m P0 
m0 s = m s hs
参数：hs : P s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_extend'`：inducedOuterMeasure_eq_ext
end' {s : Set α} (hs : P s) : inducedOuterMeasure m P0 m0 s = extend m s
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
-/
theorem inducedOuterMeasure_eq' {s : Set α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs :=
  (inducedOuterMeasure_eq_extend' PU msU m_mono hs).trans <| extend_eq _ _
/-
**MeasureTheory.inducedOuterMeasure_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：inducedOuterMeasure_eq_iInf (s : Set α) : inducedOuterMeasure m P0 m0 s = 
⨅ (t : Set α) (ht : P t) (_ : s subseteq t), m t ht
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq'`：inducedOuterMeasure_eq' {s : Set 
α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `MeasureTheory.extend_iUnion_le_tsum_nat'`：extend_iUnion_le_tsum_nat' (s 
: Nat -> Set α) : extend m (⋃ i, s i) <= ∑' i, extend m (s i)
-/
theorem inducedOuterMeasure_eq_iInf (s : Set α) :
    inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s ⊆ t), m t ht := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro t ht hs
    grw [hs]
    exact le_of_eq (inducedOuterMeasure_eq' _ msU m_mono _)
  · refine le_iInf ?_
    intro f
    refine le_iInf ?_
    intro hf
    refine le_trans ?_ (extend_iUnion_le_tsum_nat' _ msU _)
    refine le_iInf ?_
    intro h2f
    exact iInf_le_of_le _ (iInf_le_of_le h2f <| iInf_le _ hf)

omit msU m_mono in
/-
**MeasureTheory.inducedOuterMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：inducedOuterMeasure_zero (Pu : P univ) : inducedOuterMeasure (fun _ _ => 0
) P0 (by simp) = 0
参数：Pu : P univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_iInf`：inducedOuterMeasure_eq_iInf (
s : Set α) : inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s sub
seteq t), m t ht
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsZeroApplySetENNReal`：∀ {α : Type u_1}, 
IsZeroApply (MeasureTheory.OuterMeasure α) (Set α) ENNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem inducedOuterMeasure_zero (Pu : P univ) :
    inducedOuterMeasure (fun _ _ => 0) P0 (by simp) = 0 := by
  ext s
  rw [inducedOuterMeasure_eq_iInf PU (fun _ _ => by simp) (fun _ _ => by simp)]
  exact le_antisymm (iInf₂_le_of_le univ Pu (by simp)) zero_le
/-
**MeasureTheory.inducedOuterMeasure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：inducedOuterMeasure_preimage (f : α ≃ α) (Pm : forall s : Set α, P (f ⁻¹' 
s) ↔ P s) (mm : forall (s : Set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s
 hs) {A : Set α} : inducedOuterMeasure m P0 m0 (f ⁻¹' A) = inducedOuterMeasure m
 P0 m0 A
参数：f : α ≃ α；Pm : forall s : Set α, P (f ⁻¹' s) ↔ P s；mm : forall (s : Set α) (h
s : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_iInf`：inducedOuterMeasure_eq_iInf (
s : Set α) : inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s sub
seteq t), m t ht
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : InfSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Function.Injective.preimage_surjective`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β}, Function.Injective f → Function.Surjective (Set.preimage f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Function.Surjective.preimage_subset_preimage_iff`：∀ {α : Type u_1} {β : 
Type u_2} {f : α → β} {s t : Set β}, Function.Surjective f → (f ⁻¹' s ⊆ f ⁻¹' t 
↔ s ⊆ t)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem inducedOuterMeasure_preimage (f : α ≃ α) (Pm : ∀ s : Set α, P (f ⁻¹' s) ↔ P s)
    (mm : ∀ (s : Set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs) {A : Set α} :
    inducedOuterMeasure m P0 m0 (f ⁻¹' A) = inducedOuterMeasure m P0 m0 A := by
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono, inducedOuterMeasure_eq_iInf _ msU m_mono]; symm
    refine f.injective.preimage_surjective.iInf_congr (preimage f) fun s => ?_
    refine iInf_congr_Prop (Pm s) ?_; intro hs
    refine iInf_congr_Prop f.surjective.preimage_subset_preimage_iff ?_
    intro _; exact mm s hs
/-
**MeasureTheory.inducedOuterMeasure_exists_set** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：inducedOuterMeasure_exists_set {s : Set α} (hs : inducedOuterMeasure m P0 
m0 s != ∞) {ε : Real>=0∞} (hε : ε != 0) : exists t : Set α, P t ∧ s subseteq t ∧
 inducedOuterMeasure m P0 m0 t <= inducedOuterMeasure m P0 m0 s + ε
参数：hs : inducedOuterMeasure m P0 m0 s != ∞；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_iInf`：inducedOuterMeasure_eq_iInf (
s : Set α) : inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s sub
seteq t), m t ht
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq'`：inducedOuterMeasure_eq' {s : Set 
α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem inducedOuterMeasure_exists_set {s : Set α} (hs : inducedOuterMeasure m P0 m0 s ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t : Set α,
      P t ∧ s ⊆ t ∧ inducedOuterMeasure m P0 m0 t ≤ inducedOuterMeasure m P0 m0 s + ε := by
  have h := ENNReal.lt_add_right hs hε
  conv at h =>
    lhs
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
  simp only [iInf_lt_iff] at h
  rcases h with ⟨t, h1t, h2t, h3t⟩
  exact
    ⟨t, h1t, h2t, le_trans (le_of_eq <| inducedOuterMeasure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩

/-- To test whether `s` is Carathéodory-measurable we only need to check the sets `t` for which
  `P t` holds. See `ofFunction_caratheodory` for another way to show the Carathéodory-measurability
  of `s`.
-/
/-
**MeasureTheory.inducedOuterMeasure_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：inducedOuterMeasure_caratheodory (s : Set α) : MeasurableSet[(inducedOuter
Measure m P0 m0).caratheodory] s ↔ forall t : Set α, P t -> inducedOuterMeasure 
m P0 m0 (t inter s) + inducedOuterMeasure m P0 m0 (t \ s) <= inducedOuterMeasure
 m P0 m0 t
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iff_le`：isCaratheodory_iff_le 
{s : Set α} : MeasurableSet[OuterMeasure.caratheodory m] s ↔ forall t, m (t inte
r s) + m (t \ s) <= m t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_iInf`：inducedOuterMeasure_eq_iInf (
s : Set α) : inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s sub
seteq t), m t ht
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq'`：inducedOuterMeasure_eq' {s : Set 
α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs

--- 原说明 ---
To test whether `s` is Carathéodory-measurable we only need to check the sets `t
` for which
  `P t` holds. See `ofFunction_caratheodory` for another way to show the Carathé
odory-measurability
  of `s`.
-/
theorem inducedOuterMeasure_caratheodory (s : Set α) :
    MeasurableSet[(inducedOuterMeasure m P0 m0).caratheodory] s ↔
      ∀ t : Set α,
        P t →
          inducedOuterMeasure m P0 m0 (t ∩ s) + inducedOuterMeasure m P0 m0 (t \ s) ≤
            inducedOuterMeasure m P0 m0 t := by
  rw [isCaratheodory_iff_le]
  constructor
  · intro h t _ht
    exact h t
  · intro h u
    conv_rhs => rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
    refine le_iInf ?_
    intro t
    refine le_iInf ?_
    intro ht
    refine le_iInf ?_
    intro h2t
    refine le_trans ?_ ((h t ht).trans_eq <| inducedOuterMeasure_eq' _ msU m_mono ht)
    gcongr

end ExtendSet

/-! If `P` is `MeasurableSet` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/


section MeasurableSpace

variable {α : Type*} [MeasurableSpace α]
variable {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}
variable (m0 : m ∅ MeasurableSet.empty = 0)
variable
  (mU :
    ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion hm) = ∑' i, m (f i) (hm i))
include m0 mU

/-
**MeasureTheory.extend_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：extend_mono {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (hs : s₁ subseteq s₂) 
: extend m s₁ <= extend m s₂
参数：h₁ : MeasurableSet s₁；hs : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `MeasureTheory.extend_union`：extend_union {s₁ s₂ : Set α} (hd : Disjoint 
s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) : extend m (s₁ union s₂) = extend m s₁ + extend m
 s₂
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
-/
theorem extend_mono {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (hs : s₁ ⊆ s₂) :
    extend m s₁ ≤ extend m s₂ := by
  refine le_iInf ?_; intro h₂
  have :=
    extend_union MeasurableSet.empty m0 MeasurableSet.iUnion mU disjoint_sdiff_self_right h₁
      (h₂.diff h₁)
  rw [union_sdiff_cancel hs] at this
  rw [← extend_eq m]
  exact le_iff_exists_add.2 ⟨_, this⟩
/-
**MeasureTheory.extend_iUnion_le_tsum_nat** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：extend_iUnion_le_tsum_nat : forall s : Nat -> Set α, extend m (⋃ i, s i) <
= ∑' i, extend m (s i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.extend_iUnion_le_tsum_nat'`：extend_iUnion_le_tsum_nat' (s 
: Nat -> Set α) : extend m (⋃ i, s i) <= ∑' i, extend m (s i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
· 使用定理 `MeasureTheory.extend_mono`：extend_mono {s₁ s₂ : Set α} (h₁ : MeasurableS
et s₁) (hs : s₁ subseteq s₂) : extend m s₁ <= extend m s₂
· 使用定理 `disjointed_le`：disjointed_le (f : ι -> α) : disjointed f <= f
-/
theorem extend_iUnion_le_tsum_nat : ∀ s : ℕ → Set α,
    extend m (⋃ i, s i) ≤ ∑' i, extend m (s i) := by
  refine extend_iUnion_le_tsum_nat' MeasurableSet.iUnion ?_; intro f h
  simp +singlePass only [iUnion_disjointed.symm]
  rw [mU (MeasurableSet.disjointed h) (disjoint_disjointed _)]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← extend_eq m, ← extend_eq m]
  exact extend_mono m0 mU (MeasurableSet.disjointed h _) (disjointed_le f _)
/-
**MeasureTheory.inducedOuterMeasure_eq_extend** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：inducedOuterMeasure_eq_extend {s : Set α} (hs : MeasurableSet s) : induced
OuterMeasure m MeasurableSet.empty m0 s = extend m s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_eq`：ofFunction_eq (s : Set α) (m_m
ono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t) (m_subadd : forall s : Nat
 -> Set α, m (⋃ i, s i) <= ∑' …
· 使用定理 `MeasureTheory.extend_empty`：extend_empty : extend m ∅ = 0
· 使用定理 `MeasureTheory.extend_mono`：extend_mono {s₁ s₂ : Set α} (h₁ : MeasurableS
et s₁) (hs : s₁ subseteq s₂) : extend m s₁ <= extend m s₂
· 使用定理 `MeasureTheory.extend_iUnion_le_tsum_nat`：extend_iUnion_le_tsum_nat : for
all s : Nat -> Set α, extend m (⋃ i, s i) <= ∑' i, extend m (s i)
-/
theorem inducedOuterMeasure_eq_extend {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = extend m s :=
  ofFunction_eq s (fun _t => extend_mono m0 mU hs) (extend_iUnion_le_tsum_nat m0 mU)
/-
**MeasureTheory.inducedOuterMeasure_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：inducedOuterMeasure_eq {s : Set α} (hs : MeasurableSet s) : inducedOuterMe
asure m MeasurableSet.empty m0 s = m s hs
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_extend`：inducedOuterMeasure_eq_exte
nd {s : Set α} (hs : MeasurableSet s) : inducedOuterMeasure m MeasurableSet.empt
y m0 s = extend m s
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
-/
theorem inducedOuterMeasure_eq {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = m s hs :=
  (inducedOuterMeasure_eq_extend m0 mU hs).trans <| extend_eq _ _

end MeasurableSpace

namespace OuterMeasure

variable {α : Type*} [MeasurableSpace α] (m : OuterMeasure α)

/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
/-
**MeasureTheory.OuterMeasure.trim** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Outer
Measure`。
形式化陈述：trim : OuterMeasure α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0

--- 原说明 ---
Given an outer measure `m` we can forget its value on non-measurable sets, and t
hen consider
  `m.trim`, the unique maximal outer measure less than that function.
-/
def trim : OuterMeasure α :=
  inducedOuterMeasure (P := MeasurableSet) (fun s _ => m s) .empty m.empty
/-
**MeasureTheory.OuterMeasure.le_trim_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：le_trim_iff {m₁ m₂ : OuterMeasure α} : m₁ <= m₂.trim ↔ forall s, Measurabl
eSet s -> m₁ s <= m₂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_inducedOuterMeasure`：le_inducedOuterMeasure {μ : OuterM
easure α} : μ <= inducedOuterMeasure m P0 m0 ↔ forall (s) (hs : P s), μ s <= m s
 hs
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0
-/
theorem le_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁ ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_inducedOuterMeasure
/-
**MeasureTheory.OuterMeasure.le_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：le_trim : m <= m.trim
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.le_trim_iff`：le_trim_iff {m₁ m₂ : OuterMeasur
e α} : m₁ <= m₂.trim ↔ forall s, MeasurableSet s -> m₁ s <= m₂ s
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_trim : m ≤ m.trim := le_trim_iff.2 fun _ _ ↦ le_rfl
/-
**MeasureTheory.OuterMeasure.null_of_trim_null** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.OuterMeasure`。
形式化陈述：null_of_trim_null {s : Set α} (h : m.trim s = 0) : m s = 0
参数：h : m.trim s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.le_trim`：le_trim : m <= m.trim
-/
lemma null_of_trim_null {s : Set α} (h : m.trim s = 0) : m s = 0 :=
  nonpos_iff_eq_zero.1 <| (le_trim m s).trans_eq h

@[simp]
/-
**MeasureTheory.OuterMeasure.trim_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：trim_eq {s : Set α} (hs : MeasurableSet s) : m.trim s = m s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq'`：inducedOuterMeasure_eq' {s : Set 
α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
-/
theorem trim_eq {s : Set α} (hs : MeasurableSet s) : m.trim s = m s :=
  inducedOuterMeasure_eq' MeasurableSet.iUnion (fun f _hf => measure_iUnion_le f)
    (fun _ _ _ _ h => measure_mono h) hs
/-
**MeasureTheory.OuterMeasure.trim_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：trim_congr {m₁ m₂ : OuterMeasure α} (H : forall {s : Set α}, MeasurableSet
 s -> m₁ s = m₂ s) : m₁.trim = m₂.trim
参数：H : forall {s : Set α}, MeasurableSet s -> m₁ s = m₂ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.inducedOuterMeasure.congr_simp`：∀ {α : Type u_1} {P : Set 
α → Prop} (m m_1 : (s : Set α) → P s → ENNReal) (e_m : m = m_1) (P0 : P ∅) (m0 :
 m ∅ P0 = 0),   MeasureTheory.indu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trim_congr {m₁ m₂ : OuterMeasure α} (H : ∀ {s : Set α}, MeasurableSet s → m₁ s = m₂ s) :
    m₁.trim = m₂.trim := by
  simp +contextual only [trim, H]

@[gcongr, mono]
/-
**MeasureTheory.OuterMeasure.trim_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：trim_mono : Monotone (trim : OuterMeasure α -> OuterMeasure α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
-/
theorem trim_mono : Monotone (trim : OuterMeasure α → OuterMeasure α) := fun _m₁ _m₂ H _s =>
  iInf₂_mono fun _f _hs => ENNReal.tsum_le_tsum fun _b => iInf_mono fun _hf => H _

/-- `OuterMeasure.trim` is antitone in the σ-algebra. -/
/-
**MeasureTheory.OuterMeasure.trim_anti_measurableSpace** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.OuterMeasure`。
形式化陈述：trim_anti_measurableSpace {α} (m : OuterMeasure α) {m0 m1 : MeasurableSpac
e α} (h : m0 <= m1) : @trim _ m1 m <= @trim _ m0 m
参数：m : OuterMeasure α；h : m0 <= m1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
`OuterMeasure.trim` is antitone in the σ-algebra.
-/
theorem trim_anti_measurableSpace {α} (m : OuterMeasure α) {m0 m1 : MeasurableSpace α}
    (h : m0 ≤ m1) : @trim _ m1 m ≤ @trim _ m0 m := by
  simp only [le_trim_iff]
  intro s hs
  rw [trim_eq _ (h s hs)]
/-
**MeasureTheory.OuterMeasure.trim_le_trim_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：trim_le_trim_iff {m₁ m₂ : OuterMeasure α} : m₁.trim <= m₂.trim ↔ forall s,
 MeasurableSet s -> m₁ s <= m₂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.OuterMeasure.le_trim_iff`：le_trim_iff {m₁ m₂ : OuterMeasur
e α} : m₁ <= m₂.trim ↔ forall s, MeasurableSet s -> m₁ s <= m₂ s
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trim_le_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_trim_iff.trans <| forall₂_congr fun s hs => by rw [trim_eq _ hs]
/-
**MeasureTheory.OuterMeasure.trim_eq_trim_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：trim_eq_trim_iff {m₁ m₂ : OuterMeasure α} : m₁.trim = m₂.trim ↔ forall s, 
MeasurableSet s -> m₁ s = m₂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem trim_eq_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim = m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s = m₂ s := by
  simp only [le_antisymm_iff, trim_le_trim_iff, forall_and]
/-
**MeasureTheory.OuterMeasure.trim_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：trim_eq_iInf (s : Set α) : m.trim s = ⨅ (t) (_ : s subseteq t) (_ : Measur
ableSet t), m t
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_comm`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Compl
eteLattice α] {f : ι → ι' → α},   ⨅ i, ⨅ j, f i j = ⨅ j, ⨅ i, f i j
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_iInf`：inducedOuterMeasure_eq_iInf (
s : Set α) : inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s sub
seteq t), m t ht
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
-/
theorem trim_eq_iInf (s : Set α) : m.trim s = ⨅ (t) (_ : s ⊆ t) (_ : MeasurableSet t), m t := by
  simp +singlePass only [iInf_comm]
  exact
    inducedOuterMeasure_eq_iInf MeasurableSet.iUnion (fun f _ => measure_iUnion_le f)
      (fun _ _ _ _ h => measure_mono h) s
/-
**MeasureTheory.OuterMeasure.trim_eq_iInf'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：trim_eq_iInf' (s : Set α) : m.trim s = ⨅ t : { t // s subseteq t ∧ Measura
bleSet t }, m t
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq_iInf`：trim_eq_iInf (s : Set α) : m.tr
im s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), m t
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trim_eq_iInf' (s : Set α) : m.trim s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, m t := by
  simp [iInf_subtype, iInf_and, trim_eq_iInf]
/-
**MeasureTheory.OuterMeasure.trim_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：trim_trim (m : OuterMeasure α) : m.trim.trim = m.trim
参数：m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq_trim_iff`：trim_eq_trim_iff {m₁ m₂ : O
uterMeasure α} : m₁.trim = m₂.trim ↔ forall s, MeasurableSet s -> m₁ s = m₂ s
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
-/
theorem trim_trim (m : OuterMeasure α) : m.trim.trim = m.trim :=
  trim_eq_trim_iff.2 fun _s => m.trim_eq

@[simp]
/-
**MeasureTheory.OuterMeasure.trim_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：trim_top : (⊤ : OuterMeasure α).trim = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `MeasureTheory.OuterMeasure.le_trim`：le_trim : m <= m.trim
-/
theorem trim_top : (⊤ : OuterMeasure α).trim = ⊤ :=
  top_unique <| le_trim _

@[simp]
/-
**MeasureTheory.OuterMeasure.trim_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：trim_zero : (0 : OuterMeasure α).trim = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem trim_zero : (0 : OuterMeasure α).trim = 0 := by
  ext s
  exact nonpos_iff_eq_zero.1 <| (measure_mono (subset_univ s)).trans_eq <| trim_eq _ .univ
/-
**MeasureTheory.OuterMeasure.trim_sum_ge** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：trim_sum_ge {ι} (m : ι -> OuterMeasure α) : (sum fun i => (m i).trim) <= (
sum m).trim
参数：m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq_iInf`：trim_eq_iInf (s : Set α) : m.tr
im s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), m t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem trim_sum_ge {ι} (m : ι → OuterMeasure α) : (sum fun i => (m i).trim) ≤ (sum m).trim :=
  fun s => by
  simp only [sum_apply, trim_eq_iInf, le_iInf_iff]
  exact fun t st ht =>
    ENNReal.tsum_le_tsum fun i => iInf_le_of_le t <| iInf_le_of_le st <| iInf_le _ ht
/-
**MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：exists_measurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) : exis
ts t, s subseteq t ∧ MeasurableSet t ∧ m t = m.trim s
参数：m : OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq_iInf`：trim_eq_iInf (s : Set α) : m.tr
im s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), m t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `ENNReal.tendsto_inv_nat_nhds_zero`：Filter.Tendsto (fun n => (↑n)⁻¹) Filt
er.atTop (nhds 0)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
（共 40 条，此处仅展示前 30 条）
-/
theorem exists_measurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t = m.trim s := by
  simp only [trim_eq_iInf]; set ms := ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), m t
  by_cases hs : ms = ∞
  · simp only [hs]
    simp only [iInf_eq_top, ms] at hs
    exact ⟨univ, subset_univ s, MeasurableSet.univ, hs _ (subset_univ s) MeasurableSet.univ⟩
  · have : ∀ r > ms, ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t < r := by
      intro r hs
      have : ∃ t, MeasurableSet t ∧ s ⊆ t ∧ m t < r := by simpa [ms, iInf_lt_iff] using hs
      rcases this with ⟨t, hmt, hin, hlt⟩
      exists t
    have : ∀ n : ℕ, ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t < ms + (n : ℝ≥0∞)⁻¹ := by
      intro n
      refine this _ (ENNReal.lt_add_right hs ?_)
      simp
    choose t hsub hm hm' using this
    refine ⟨⋂ n, t n, subset_iInter hsub, MeasurableSet.iInter hm, ?_⟩
    have : Tendsto (fun n : ℕ => ms + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (ms + 0)) :=
      tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
    rw [add_zero] at this
    refine le_antisymm (ge_of_tendsto' this fun n => ?_) ?_
    · exact le_trans (measure_mono <| iInter_subset t n) (hm' n).le
    · refine iInf_le_of_le (⋂ n, t n) ?_
      refine iInf_le_of_le (subset_iInter hsub) ?_
      exact iInf_le _ (MeasurableSet.iInter hm)
/-
**MeasureTheory.OuterMeasure.exists_measurable_superset_of_trim_eq_zero** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：exists_measurable_superset_of_trim_eq_zero {m : OuterMeasure α} {s : Set α
} (h : m.trim s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ m t = 0
参数：h : m.trim s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim`：exists_me
asurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) : exists t, s subsete
q t ∧ MeasurableSet t ∧ m t = m.trim s
-/
theorem exists_measurable_superset_of_trim_eq_zero {m : OuterMeasure α} {s : Set α}
    (h : m.trim s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t = 0 := by
  rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩
  exact ⟨t, hst, ht, h ▸ hm⟩

/-- If `μ i` is a countable family of outer measures, then for every set `s` there exists
a measurable set `t ⊇ s` such that `μ i t = (μ i).trim s` for all `i`. -/
/-
**MeasureTheory.OuterMeasure.exists_measurable_superset_forall_eq_trim** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：exists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι -> Oute
rMeasure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ forall i, μ
 i t = (μ i).trim s
参数：μ : ι -> OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim`：exists_me
asurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) : exists t, s subsete
q t ∧ MeasurableSet t ∧ m t = m.trim s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `μ i` is a countable family of outer measures, then for every set `s` there e
xists
a measurable set `t ⊇ s` such that `μ i t = (μ i).trim s` for all `i`.
-/
theorem exists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι → OuterMeasure α)
    (s : Set α) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = (μ i).trim s := by
  choose t hst ht hμt using fun i => (μ i).exists_measurable_superset_eq_trim s
  replace hst := subset_iInter hst
  replace ht := MeasurableSet.iInter ht
  refine ⟨⋂ i, t i, hst, ht, fun i => le_antisymm ?_ ?_⟩
  exacts [hμt i ▸ (μ i).mono (iInter_subset _ _), (measure_mono hst).trans_eq ((μ i).trim_eq ht)]

/-- If `m₁ s = op (m₂ s) (m₃ s)` for all `s`, then the same is true for `m₁.trim`, `m₂.trim`,
and `m₃ s`. -/
/-
**MeasureTheory.OuterMeasure.trim_binop** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：trim_binop {m₁ m₂ m₃ : OuterMeasure α} {op : Real>=0∞ -> Real>=0∞ -> Real>
=0∞} (h : forall s, m₁ s = op (m₂ s) (m₃ s)) (s : Set α) : m₁.trim s = op (m₂.tr
im s) (m₃.trim s)
参数：h : forall s, m₁ s = op (m₂ s) (m₃ s)；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_forall_eq_trim`：ex
ists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι -> OuterMeasure
 α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t…
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `m₁ s = op (m₂ s) (m₃ s)` for all `s`, then the same is true for `m₁.trim`, `
m₂.trim`,
and `m₃ s`.
-/
theorem trim_binop {m₁ m₂ m₃ : OuterMeasure α} {op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    (h : ∀ s, m₁ s = op (m₂ s) (m₃ s)) (s : Set α) : m₁.trim s = op (m₂.trim s) (m₃.trim s) := by
  rcases exists_measurable_superset_forall_eq_trim ![m₁, m₂, m₃] s with ⟨t, _hst, _ht, htm⟩
  simp only [Fin.forall_iff_succ, Matrix.cons_val_zero, Matrix.cons_val_succ] at htm
  rw [← htm.1, ← htm.2.1, ← htm.2.2.1, h]

/-- If `m₁ s = op (m₂ s)` for all `s`, then the same is true for `m₁.trim` and `m₂.trim`. -/
/-
**MeasureTheory.OuterMeasure.trim_op** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：trim_op {m₁ m₂ : OuterMeasure α} {op : Real>=0∞ -> Real>=0∞} (h : forall s
, m₁ s = op (m₂ s)) (s : Set α) : m₁.trim s = op (m₂.trim s)
参数：h : forall s, m₁ s = op (m₂ s)；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.trim_binop`：trim_binop {m₁ m₂ m₃ : OuterMeasu
re α} {op : Real>=0∞ -> Real>=0∞ -> Real>=0∞} (h : forall s, m₁ s = op (m₂ s) (m
₃ s)) (s : Set α) : m₁.trim…

--- 原说明 ---
If `m₁ s = op (m₂ s)` for all `s`, then the same is true for `m₁.trim` and `m₂.t
rim`.
-/
theorem trim_op {m₁ m₂ : OuterMeasure α} {op : ℝ≥0∞ → ℝ≥0∞} (h : ∀ s, m₁ s = op (m₂ s))
    (s : Set α) : m₁.trim s = op (m₂.trim s) :=
  @trim_binop α _ m₁ m₂ 0 (fun a _b => op a) h s

/-- `trim` is additive. -/
/-
**MeasureTheory.OuterMeasure.trim_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：trim_add (m₁ m₂ : OuterMeasure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim
参数：m₁ m₂ : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.OuterMeasure.trim_binop`：trim_binop {m₁ m₂ m₃ : OuterMeasu
re α} {op : Real>=0∞ -> Real>=0∞ -> Real>=0∞} (h : forall s, m₁ s = op (m₂ s) (m
₃ s)) (s : Set α) : m₁.trim…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.OuterMeasure.instIsAddApplySetENNReal`：∀ {α : Type u_1}, I
sAddApply (MeasureTheory.OuterMeasure α) (Set α) ENNReal

--- 原说明 ---
`trim` is additive.
-/
theorem trim_add (m₁ m₂ : OuterMeasure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim :=
  ext <| trim_binop (add_apply m₁ m₂)

/-- `trim` respects scalar multiplication. -/
/-
**MeasureTheory.OuterMeasure.trim_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：trim_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞
] (c : R) (m : OuterMeasure α) : (c • m).trim = c • m.trim
参数：c : R；m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.OuterMeasure.trim_op`：trim_op {m₁ m₂ : OuterMeasure α} {op
 : Real>=0∞ -> Real>=0∞} (h : forall s, m₁ s = op (m₂ s)) (s : Set α) : m₁.trim 
s = op (m₂.trim s)
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…

--- 原说明 ---
`trim` respects scalar multiplication.
-/
theorem trim_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    (m : OuterMeasure α) : (c • m).trim = c • m.trim :=
  ext <| trim_op (smul_apply m c)

/-- `trim` sends the supremum of two outer measures to the supremum of the trimmed measures. -/
/-
**MeasureTheory.OuterMeasure.trim_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：trim_sup (m₁ m₂ : OuterMeasure α) : (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim
参数：m₁ m₂ : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.OuterMeasure.trim_binop`：trim_binop {m₁ m₂ m₃ : OuterMeasu
re α} {op : Real>=0∞ -> Real>=0∞ -> Real>=0∞} (h : forall s, m₁ s = op (m₂ s) (m
₃ s)) (s : Set α) : m₁.trim…
· 使用定理 `MeasureTheory.OuterMeasure.sup_apply`：sup_apply (m₁ m₂ : OuterMeasure α)
 (s : Set α) : (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`trim` sends the supremum of two outer measures to the supremum of the trimmed m
easures.
-/
theorem trim_sup (m₁ m₂ : OuterMeasure α) : (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim :=
  ext fun s => (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm

/-- `trim` sends the supremum of a countable family of outer measures to the supremum
of the trimmed measures. -/
/-
**MeasureTheory.OuterMeasure.trim_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：trim_iSup {ι} [Countable ι] (μ : ι -> OuterMeasure α) : trim (⨆ i, μ i) = 
⨆ i, trim (μ i)
参数：μ : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_plift_down`：iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = 
⨆ i, f i
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_forall_eq_trim`：ex
ists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι -> OuterMeasure
 α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t…
· 使用定理 `instCountablePLift`：∀ {α : Sort u} [Countable α], Countable (PLift α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.OuterMeasure.iSup_apply`：iSup_apply {ι} (f : ι -> OuterMea
sure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
`trim` sends the supremum of a countable family of outer measures to the supremu
m
of the trimmed measures.
-/
theorem trim_iSup {ι} [Countable ι] (μ : ι → OuterMeasure α) :
    trim (⨆ i, μ i) = ⨆ i, trim (μ i) := by
  simp_rw [← @iSup_plift_down _ ι]
  ext1 s
  obtain ⟨t, _, _, hμt⟩ :=
    exists_measurable_superset_forall_eq_trim
      (Option.elim' (⨆ i, μ (PLift.down i)) (μ ∘ PLift.down)) s
  simp only [Option.forall, Option.elim'] at hμt
  simp only [iSup_apply, ← hμt.1]
  exact iSup_congr hμt.2

/-- The trimmed property of a measure μ states that `μ.toOuterMeasure.trim = μ.toOuterMeasure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
/-
**MeasureTheory.OuterMeasure.restrict_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：restrict_trim {μ : OuterMeasure α} {s : Set α} (hs : MeasurableSet s) : (r
estrict s μ).trim = restrict s μ.trim
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim`：exists_me
asurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) : exists t, s subsete
q t ∧ MeasurableSet t ∧ m t = m.trim s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.inter_subset`：inter_subset (a b c : Set α) : a inter b subseteq c ↔ 
a subseteq bᶜ union c
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.le_trim_iff`：le_trim_iff {m₁ m₂ : OuterMeasur
e α} : m₁ <= m₂.trim ↔ forall s, MeasurableSet s -> m₁ s <= m₂ s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The trimmed property of a measure μ states that `μ.toOuterMeasure.trim = μ.toOut
erMeasure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer me
asure.
-/
theorem restrict_trim {μ : OuterMeasure α} {s : Set α} (hs : MeasurableSet s) :
    (restrict s μ).trim = restrict s μ.trim := by
  refine le_antisymm (fun t => ?_) (le_trim_iff.2 fun t ht => ?_)
  · rw [restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (t ∩ s) with ⟨t', htt', ht', hμt'⟩
    rw [← hμt']
    rw [inter_subset] at htt'
    refine (measure_mono htt').trans ?_
    rw [trim_eq _ (hs.compl.union ht'), restrict_apply, union_inter_distrib_right, compl_inter_self,
      Set.empty_union]
    exact measure_mono inter_subset_left
  · rw [restrict_apply, trim_eq _ (ht.inter hs), restrict_apply]

end OuterMeasure

end MeasureTheory

