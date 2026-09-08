/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.HasLaw

import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Product of bernoulli distributions on a set

This file defines the product of bernoulli distributions on a set as a measure on sets.
For a set `u : Set ι` and `p` between `0` and `1`, this is the measure on `Set ι` such that each
`i ∈ u` belongs to the random set with probability `p`, and each `i ∉ u` doesn't belong to it.

## Notation

`setBer(u, p)` is the product of `p`-Bernoulli distributions on `u`.

## TODO

It is painful to convert from `unitInterval` to `ENNReal`. Should we introduce a coercion or
explicit operation (like `unitInterval.toNNReal`, note the lack of dot notation!)?
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal Finset

namespace ProbabilityTheory
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → Set ι} {s u : Set ι} {i j : ι} {p q : I}
  {P : Measure Ω}

variable (u p) in
/-- The product of bernoulli distributions with parameter `p` on the set `u : Set V` is the measure
on `Set V` such that each element of `u` is taken with probability `p`, and the elements outside of
`u` are never taken. -/
@[expose]
/-
**ProbabilityTheory.setBernoulli** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：setBernoulli : Measure (Set ι)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of bernoulli distributions with parameter `p` on the set `u : Set V`
 is the measure
on `Set V` such that each element of `u` is taken with probability `p`, and the 
elements outside of
`u` are never taken.
-/
noncomputable def setBernoulli : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i : ι ↦
    toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure setBer(u, p) :=
  MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap <|
    .of_forall fun P ↦ ⟨{i | P i}, rfl⟩

variable (u p) in
/-
**ProbabilityTheory.setBernoulli_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：setBernoulli_eq_map : setBer(u, p) = .map (fun p : ι -> Prop => {i | p i})
 (infinitePi fun i : ι => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac F
alse)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasurableEquiv.comap_symm`：comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.
comap e.symm = μ.map e
-/
lemma setBernoulli_eq_map :
    setBer(u, p) = .map (fun p : ι → Prop ↦ {i | p i})
      (infinitePi fun i : ι ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False) :=
  MeasurableEquiv.setOfPred.comap_symm
/-
**ProbabilityTheory.setBernoulli_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：setBernoulli_apply (S : Set (Set ι)) : setBer(u, p) S = (infinitePi fun i 
=> toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False) ((fun t i => i in
 t) '' S)
参数：S : Set (Set ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
lemma setBernoulli_apply (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
      ((fun t i ↦ i ∈ t) '' S) := MeasurableEquiv.setOfPred.symm.measurableEmbedding.comap_apply ..
/-
**ProbabilityTheory.setBernoulli_apply'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：setBernoulli_apply' (S : Set (Set ι)) : setBer(u, p) S = (infinitePi fun i
 => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False) ((fun p => {i | 
p i}) ⁻¹' S)
参数：S : Set (Set ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.comap_apply`：∀ {α : Type u_2} {β : Type u_3} {m0 : Measu
rableSpace α} {m1 : MeasurableSpace β} (e : α ≃ᵐ β)   (μ : MeasureTheory.Measure
 β) (s : Set α), …
-/
lemma setBernoulli_apply' (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
      ((fun p ↦ {i | p i}) ⁻¹' S) := MeasurableEquiv.setOfPred.symm.comap_apply ..

variable (u) in
/-
**ProbabilityTheory.setBernoulli_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：∀ {ι : Type u_1} (u : Set ι), ProbabilityTheory.setBernoulli u 0 = Measure
Theory.Measure.dirac ∅
参数：u : Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `ProbabilityTheory.setBernoulli_eq_map`：setBernoulli_eq_map : setBer(u, p
) = .map (fun p : ι -> Prop => {i | p i}) (infinitePi fun i : ι => toNNReal p • 
dirac (i in u) + toNNReal (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `unitInterval.symm_zero`：symm_zero : σ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.Measure.infinitePi_dirac`：∀ {ι : Type u_1} {X : ι → Type u
_2} {mX : (i : ι) → MeasurableSpace (X i)} (f : (i : ι) → X i),   (MeasureTheory
.Measure.infinitePi fun i =>…
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma setBernoulli_zero : setBer(u, 0) = dirac ∅ := by simp [setBernoulli_eq_map]

variable (u) in
/-
**ProbabilityTheory.setBernoulli_one** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：∀ {ι : Type u_1} (u : Set ι), ProbabilityTheory.setBernoulli u 1 = Measure
Theory.Measure.dirac u
参数：u : Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `ProbabilityTheory.setBernoulli_eq_map`：setBernoulli_eq_map : setBer(u, p
) = .map (fun p : ι -> Prop => {i | p i}) (infinitePi fun i : ι => toNNReal p • 
dirac (i in u) + toNNReal (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `unitInterval.symm_one`：symm_one : σ 1 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.Measure.infinitePi_dirac`：∀ {ι : Type u_1} {X : ι → Type u
_2} {mX : (i : ι) → MeasurableSpace (X i)} (f : (i : ι) → X i),   (MeasureTheory
.Measure.infinitePi fun i =>…
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma setBernoulli_one : setBer(u, 1) = dirac u := by simp [setBernoulli_eq_map]

section Countable
variable [Countable ι]

/-
**ProbabilityTheory.setBernoulli_ae_subset** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：setBernoulli_ae_subset : forallᵐ s ∂setBer(u, p), s subseteq u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用引理 `ProbabilityTheory.setBernoulli_apply'`：setBernoulli_apply' (S : Set (Set
 ι)) : setBer(u, p) S = (infinitePi fun i => toNNReal p • dirac (i in u) + toNNR
eal (σ p) • dirac False) ((…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `MeasureTheory.Measure.infinitePi_cylinder`：infinitePi_cylinder {s : Fins
et ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S) : infinitePi μ (cylinder s
 S) = Measure.pi (fun i : s => …
· 使用定理 `MeasureTheory.instIsProbabilityMeasureHAddMeasureHSMulNNRealToNNRealSymm
`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [Mea
sureTheory.IsProbabilityMeasure μ]   [MeasureTheory.IsProbabil…
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `MeasureTheory.Measure.pi_singleton`：∀ {ι : Type u_1} {α : ι → Type u_3} 
[inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → M
easureTheory.Measure (α …
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
（共 44 条，此处仅展示前 30 条）
-/
lemma setBernoulli_ae_subset : ∀ᵐ s ∂setBer(u, p), s ⊆ u := by
  simp only [Filter.Eventually, mem_ae_iff, Set.compl_ofPred, Set.not_subset_iff_exists_mem_notMem,
    Set.ofPred_exists, Set.ofPred_and, measure_iUnion_null_iff]
  rintro i
  by_cases hi : i ∈ u
  · simp [*]
  calc
    setBer(u, p) ({s | i ∈ s} ∩ {s | i ∉ u})
    _ = setBer(u, p) {s | i ∈ s} := by simp [hi]
    _ = infinitePi (fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
          (cylinder {i} {fun _ ↦ True}) := by
      rw [setBernoulli_apply']; congr!; ext; simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder, hi]

@[simp]
/-
**ProbabilityTheory.setBernoulli_singleton_of_not_subset** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：setBernoulli_singleton_of_not_subset {s : Set ι} (p : I) (hs : ¬ s subsete
q u) : setBer(u, p) {s} = 0
参数：p : I；hs : ¬ s subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.mono_null`：mono_null ⦃s t : Set α⦄ (h : s subseteq
 t) (ht : μ t = 0) : μ s = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.setBernoulli_ae_subset`：setBernoulli_ae_subset : foral
lᵐ s ∂setBer(u, p), s subseteq u
-/
lemma setBernoulli_singleton_of_not_subset {s : Set ι} (p : I) (hs : ¬ s ⊆ u) :
    setBer(u, p) {s} = 0 :=
  Measure.mono_null (by simpa) setBernoulli_ae_subset

/-- `setBer(u, p)` only gives mass to families of sets contained in `u`. -/
/-
**ProbabilityTheory.setBernoulli_apply_eq_apply_subsets** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：setBernoulli_apply_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) 
: setBer(u, p) S = setBer(u, p) { s in S | s subseteq u}
参数：u : Set ι；p : I；S : Set (Set ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_eq_measure_of_null_sdiff`：measure_eq_measure_of_nu
ll_sdiff {s t : Set α} (hst : s subseteq t) (h_nullsdiff : μ (t \ s) = 0) : μ s 
= μ t
· 使用引理 `MeasureTheory.Measure.mono_null`：mono_null ⦃s t : Set α⦄ (h : s subseteq
 t) (ht : μ t = 0) : μ s = 0
· 使用引理 `ProbabilityTheory.setBernoulli_ae_subset`：setBernoulli_ae_subset : foral
lᵐ s ∂setBer(u, p), s subseteq u

--- 原说明 ---
`setBer(u, p)` only gives mass to families of sets contained in `u`.
-/
lemma setBernoulli_apply_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) :
    setBer(u, p) S = setBer(u, p) { s ∈ S | s ⊆ u} := by
  apply (measure_eq_measure_of_null_sdiff (by grind) ?_).symm
  exact Measure.mono_null (by grind) setBernoulli_ae_subset
/-
**ProbabilityTheory.map_ncard_setBernoulli_apply** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：map_ncard_setBernoulli_apply (u : Set ι) (p : I) (s : Set Nat) : (setBer(u
, p).map Set.ncard) s = setBer(u, p) {t subseteq u | t.ncard in s}
参数：u : Set ι；p : I；s : Set Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_ncard`：measurable_ncard : Measurable (Set.ncard : Set α -> Na
t)
· 使用定理 `MeasurableSet.of_discrete`：∀ {α : Type u_1} [inst : MeasurableSpace α] [
DiscreteMeasurableSpace α] {s : Set α}, MeasurableSet s
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用引理 `ProbabilityTheory.setBernoulli_apply_eq_apply_subsets`：setBernoulli_appl
y_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) : setBer(u, p) S = setB
er(u, p) { s in S | s subseteq u}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_ncard_setBernoulli_apply (u : Set ι) (p : I) (s : Set ℕ) :
    (setBer(u, p).map Set.ncard) s = setBer(u, p) {t ⊆ u | t.ncard ∈ s} := by
  rw [map_apply (by fun_prop) .of_discrete, setBernoulli_apply_eq_apply_subsets]
  simp [And.comm]

variable (p) in
/-
**ProbabilityTheory.setBernoulli_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：∀ {ι : Type u_1} {s u : Set ι} (p : ↑unitInterval) [Countable ι],   s ⊆ u 
→     u.Finite →       (ProbabilityTheory.setBernoulli u p) {s} =         ↑(unit
Interval.toNNReal p) ^ s.ncard * ↑(unitInterval.toNNReal (unitInterval.symm p)) 
^ (u \ s).ncard
参数：p : ↑unitInterval；ProbabilityTheory.setBernoulli u p；unitInterval.toNNReal p；
unitInterval.toNNReal (unitInterval.symm p)；u \ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `ProbabilityTheory.setBernoulli_apply`：setBernoulli_apply (S : Set (Set ι
)) : setBer(u, p) S = (infinitePi fun i => toNNReal p • dirac (i in u) + toNNRea
l (σ p) • dirac False) ((f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用引理 `MeasureTheory.Measure.infinitePi_singleton`：infinitePi_singleton [Counta
ble ι] [forall i, MeasurableSingletonClass (X i)] (f : forall i, X i) : infinite
Pi μ {f} = ∏' i, μ i {f i}
· 使用定理 `MeasureTheory.instIsProbabilityMeasureHAddMeasureHSMulNNRealToNNRealSymm
`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [Mea
sureTheory.IsProbabilityMeasure μ]   [MeasureTheory.IsProbabil…
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ENNReal.smul_one`：smul_one (c : Real>=0) : c • (1 : Real>=0∞) = (c : Rea
l>=0∞)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tprod_eq_prod`：tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : forall b ∉
 s, f b = 1) : ∏'[L] b, f b = ∏ b in s, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 47 条，此处仅展示前 30 条）
-/
@[simp] lemma setBernoulli_singleton (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i ∈ u ↔ i ∈ s then (toNNReal p : ℝ≥0∞) else 0) +
          if i ∈ s then 0 else (toNNReal (σ p) : ℝ≥0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator]
    _ = ∏ i ∈ u, (if i ∈ s then (toNNReal p : ℝ≥0∞) else (toNNReal (σ p) : ℝ≥0∞)) := by
      rw [tprod_eq_prod, Finset.prod_congr rfl] <;>
        simp +contextual [ite_add_ite, mt (@hsu _), ← ENNReal.coe_add]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.ofPred_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_ofPred, Set.sdiff_eq_compl_inter, Set.inter_comm]

@[simp]
/-
**ProbabilityTheory.setBernoulli_real_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：setBernoulli_real_singleton (p : I) (hsu : s subseteq u) (hu : u.Finite) :
 setBer(u, p).real {s} = p ^ s.ncard * (1 - p : Real) ^ (u \ s).ncard
参数：p : I；hsu : s subseteq u；hu : u.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.setBernoulli_singleton`：∀ {ι : Type u_1} {s u : Set ι}
 (p : ↑unitInterval) [Countable ι],   s ⊆ u →     u.Finite →       (ProbabilityT
heory.setBernoulli u p) {s} = …
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_pow`：toReal_pow (a : Real>=0∞) (n : Nat) : (a ^ n).toReal
 = a.toReal ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setBernoulli_real_singleton (p : I) (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p).real {s} = p ^ s.ncard * (1 - p : ℝ) ^ (u \ s).ncard := by
  simp [measureReal_def, setBernoulli_singleton p hsu hu]
/-
**ProbabilityTheory.map_ncard_setBernoulli_real_singleton** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：map_ncard_setBernoulli_real_singleton {u : Set ι} (hu : u.Finite) (p : I) 
(k : Nat) : (setBer(u, p).map Set.ncard).real {k} = (u.ncard.choose k) * p ^ k *
 (1 - p) ^ (u.ncard - k)
参数：hu : u.Finite；p : I；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.finite_subsets`：∀ {α : Type u} {a : Set α}, a.Finite → {b | b
 ⊆ a}.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用引理 `ProbabilityTheory.map_ncard_setBernoulli_apply`：map_ncard_setBernoulli_a
pply (u : Set ι) (p : I) (s : Set Nat) : (setBer(u, p).map Set.ncard) s = setBer
(u, p) {t subseteq u | t.ncard in s}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `MeasureTheory.measureReal_biUnion_finset`：measureReal_biUnion_finset {s 
: Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall b in s,
 MeasurableSet (f b)) (h : for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.instIsProbabilityMeasureSetSetBernoulli`：∀ {ι : Type u
_1} {u : Set ι} {p : ↑unitInterval},   MeasureTheory.IsProbabilityMeasure (Proba
bilityTheory.setBernoulli u p)
· 使用引理 `ProbabilityTheory.setBernoulli_real_singleton`：setBernoulli_real_singlet
on (p : I) (hsu : s subseteq u) (hu : u.Finite) : setBer(u, p).real {s} = p ^ s.
ncard * (1 - p : Real) ^ (u \ s).nc…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.ncard_sdiff'`：ncard_sdiff' (hst : s subseteq t) (ht : t.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
（共 35 条，此处仅展示前 30 条）
-/
lemma map_ncard_setBernoulli_real_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard).real {k} =
      (u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k) := by
  have : {s ⊆ u | s.ncard ∈ ({k} : Set ℕ)}.Finite := hu.finite_subsets.subset (by grind)
  rw [measureReal_def, map_ncard_setBernoulli_apply, ← measureReal_def,
    ← Set.biUnion_of_singleton (Set.ofPred _)]
  simp_rw [← this.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s ∈ this.toFinset) :
      setBer(u, p).real {s} = p ^ k * (1 - p) ^ (u.ncard - k) := by
    simp only [Set.mem_singleton_iff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    rw [setBernoulli_real_singleton _ hs.1 hu, Set.ncard_sdiff' hs.1 hu, hs.2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_assoc,
    ← Set.ncard_eq_toFinset_card _ _]
  simp [Set.ncard_powerset_ncard, hu]
/-
**ProbabilityTheory.map_ncard_setBernoulli_singleton** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：map_ncard_setBernoulli_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : 
Nat) : (setBer(u, p).map Set.ncard) {k} = ENNReal.ofReal ((u.ncard.choose k) * p
 ^ k * (1 - p) ^ (u.ncard - k))
参数：hu : u.Finite；p : I；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.instIsProbabilityMeasureSetSetBernoulli`：∀ {ι : Type u
_1} {u : Set ι} {p : ↑unitInterval},   MeasureTheory.IsProbabilityMeasure (Proba
bilityTheory.setBernoulli u p)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用引理 `ProbabilityTheory.map_ncard_setBernoulli_real_singleton`：map_ncard_setBe
rnoulli_real_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : Nat) : (setBer(u
, p).map Set.ncard).real {k} = (u.ncard.choos…
-/
lemma map_ncard_setBernoulli_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard) {k} =
      ENNReal.ofReal ((u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k)) := by
  rw [← ENNReal.ofReal_toReal (a := (Measure.map _ _) _) (by simp), ← measureReal_def,
    map_ncard_setBernoulli_real_singleton hu]

@[simp]
/-
**ProbabilityTheory.setBernoulli_empty** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：setBernoulli_empty : setBer((∅ : Set ι), p) = dirac ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.setBernoulli_apply_eq_apply_subsets`：setBernoulli_appl
y_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) : setBer(u, p) S = setB
er(u, p) { s in S | s subseteq u}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.setBernoulli_singleton`：∀ {ι : Type u_1} {s u : Set ι}
 (p : ↑unitInterval) [Countable ι],   s ⊆ u →     u.Finite →       (ProbabilityT
heory.setBernoulli u p) {s} = …
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma setBernoulli_empty : setBer((∅ : Set ι), p) = dirac ∅ := by
  ext s hs
  rw [setBernoulli_apply_eq_apply_subsets]
  by_cases h : ∅ ∈ s
  · have : {t | t ∈ s ∧ t ⊆ ∅} = {∅} := by grind
    simp_all
  · have : {t | t ∈ s ∧ t ⊆ ∅} = ∅ := by grind
    rw [this]
    simp_all

end Countable

/-! ### Bernoulli random variables -/

variable (X u p P) in
/-- A random variable `X : Ω → Set ι` is `p`-bernoulli on a set `u : Set ι` if its distribution is
the product over `u` of `p`-bernoulli distributions. -/
/-
**ProbabilityTheory.IsSetBernoulli** 是 Mathlib 中的一个缩写定义，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：IsSetBernoulli : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random variable `X : Ω → Set ι` is `p`-bernoulli on a set `u : Set ι` if its d
istribution is
the product over `u` of `p`-bernoulli distributions.
-/
abbrev IsSetBernoulli : Prop := HasLaw X setBer(u, p) P
/-
**ProbabilityTheory.isSetBernoulli_congr** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：isSetBernoulli_congr (hXY : X =ᵐ[P] Y) : IsSetBernoulli X u p P ↔ IsSetBer
noulli Y u p P
参数：hXY : X =ᵐ[P] Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.hasLaw_congr`：hasLaw_congr (hXY : X =ᵐ[P] Y) : HasLaw 
X μ P ↔ HasLaw Y μ P where mp h
-/
lemma isSetBernoulli_congr (hXY : X =ᵐ[P] Y) : IsSetBernoulli X u p P ↔ IsSetBernoulli Y u p P :=
  hasLaw_congr hXY

variable [Countable ι]
/-
**ProbabilityTheory.IsSetBernoulli.ae_subset** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IsSetBernoulli`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {m : MeasurableSpace Ω} {X : Ω → Set ι} {u
 : Set ι} {p : ↑unitInterval}   {P : MeasureTheory.Measure Ω} [Countable ι], Pro
babilityTheory.IsSetBernoulli X u p P → ∀ᵐ (ω : Ω) ∂P, X ω ⊆ u
参数：ω : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.HasLaw.ae_iff`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : MeasureTh…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.subset`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpa
ce β] [Countable α] {s t : β → Set α},   Measurable s → Measurable t → Measurabl
e fun a…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用引理 `ProbabilityTheory.setBernoulli_ae_subset`：setBernoulli_ae_subset : foral
lᵐ s ∂setBer(u, p), s subseteq u
-/
lemma IsSetBernoulli.ae_subset (hX : IsSetBernoulli X u p P) : ∀ᵐ ω ∂P, X ω ⊆ u :=
  (hX.ae_iff <| by fun_prop).2 setBernoulli_ae_subset

end ProbabilityTheory

