/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite product of probability measures

This file provides a definition for the product measure of an arbitrary family of probability
measures. Given `μ : (i : ι) → Measure (X i)` such that each `μ i` is a probability measure,
`Measure.infinitePi μ` is the only probability measure `ν` over `Π i, X i` such that
`ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)`, with `s : Finset ι` and
such that `∀ i ∈ s, MeasurableSet (t i)` (see `eq_infinitePi` and `infinitePi_pi`).
We also provide a few results regarding integration against this measure.

## Main definition

* `Measure.infinitePi μ`: The product measure of the family of probability measures `μ`.

## Main statements

* `eq_infinitePi`: Any measure which gives to a finite product of sets the mass which is the
  product of their measures is the product measure.
* `infinitePi_pi`: the product measure gives to finite products of sets a mass which is
  the product of their masses.
* `infinitePi_cylinder`: `infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S`

## Implementation notes

To construct the product measure we first use the kernel `traj` obtained via the Ionescu-Tulcea
theorem to construct the measure over a product indexed by `ℕ`, which is `infinitePiNat`. This
is an implementation detail and should not be used directly. Then we construct the product measure
over an arbitrary type by extending `piContent μ` thanks to Carathéodory's theorem. The key lemma
to do so is `piContent_tendsto_zero`, which states that `piContent μ (A n)` tends to zero if
`A` is a nonincreasing sequence of sets satisfying `⋂ n, A n = ∅`.
We prove this lemma by reducing to the case of an at most countable product,
in which case `piContent μ` is known to be a true measure (see `piContent_eq_measure_pi` and
`piContent_eq_infinitePiNat`).

## Tags

infinite product measure
-/

@[expose] public section

open ProbabilityTheory Finset Filter Preorder MeasurableEquiv

open scoped ENNReal Topology

namespace MeasureTheory

section Preliminaries

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-- Consider a family of probability measures. You can take their products for any finite
subfamily. This gives a projective family of measures. -/
/-
**MeasureTheory.isProjectiveMeasureFamily_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：isProjectiveMeasureFamily_pi : IsProjectiveMeasureFamily (fun I : Finset ι
 => (Measure.pi (fun i : I => μ i)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Finset.restrict₂_preimage`：restrict₂_preimage [DecidablePred (· in s)] (
hst : s subseteq t) (u : (i : s) -> Set (π i)) : (restrict₂ hst) ⁻¹' (Set.univ.p
i u) = (@Set.un…
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_eq_prod_extend`：prod_eq_prod_extend (f : s -> M) : ∏ x, f x 
= ∏ x in s, Subtype.val.extend f 1 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset_one_on_sdiff`：prod_subset_one_on_sdiff [DecidableEq ι
] (h : s₁ subseteq s₂) (hg : forall x in s₂ \ s₁, g x = 1) (hfg : forall x in s₁
, f x = g x) : ∏ i in…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Function.extend_val_apply`：∀ {β : Sort u_2} {γ : Sort u_3} {p : β → Prop
} {g : { x // p x } → γ} {j : β → γ} {b : β} (hb : p b),   Function.extend Subty
pe.val g j b = …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc

--- 原说明 ---
Consider a family of probability measures. You can take their products for any f
inite
subfamily. This gives a projective family of measures.
-/
lemma isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  refine fun I J hJI ↦ Measure.pi_eq (fun s ms ↦ ?_)
  classical
  simp_rw [Measure.map_apply (measurable_restrict₂ hJI) (.univ_pi ms), restrict₂_preimage hJI,
    Measure.pi_pi, prod_eq_prod_extend]
  refine (prod_subset_one_on_sdiff hJI (fun x hx ↦ ?_) (fun x hx ↦ ?_)).symm
  · rw [Function.extend_val_apply (mem_sdiff.1 hx).1, dif_neg (mem_sdiff.1 hx).2, measure_univ]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (hJI hx), dif_pos hx]

/-- Consider a family of probability measures. You can take their products for any finite
subfamily. This gives an additive content on the measurable cylinders. -/
/-
**MeasureTheory.piContent** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：piContent : AddContent Real>=0∞ (measurableCylinders X)
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isProjectiveMeasureFamily_pi`：isProjectiveMeasureFamily_pi
 : IsProjectiveMeasureFamily (fun I : Finset ι => (Measure.pi (fun i : I => μ i)
))

--- 原说明 ---
Consider a family of probability measures. You can take their products for any f
inite
subfamily. This gives an additive content on the measurable cylinders.
-/
noncomputable def piContent : AddContent ℝ≥0∞ (measurableCylinders X) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_pi μ)
/-
**MeasureTheory.piContent_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：piContent_cylinder {I : Finset ι} {S : Set (Π i : I, X i)} (hS : Measurabl
eSet S) : piContent μ (cylinder I S) = Measure.pi (fun i : I => μ i) S
参数：Π i : I, X i；hS : MeasurableSet S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.projectiveFamilyContent_cylinder`：projectiveFamilyContent_
cylinder (hP : IsProjectiveMeasureFamily P) (hS : MeasurableSet S) : projectiveF
amilyContent hP (cylinder I S) = P I…
· 使用引理 `MeasureTheory.isProjectiveMeasureFamily_pi`：isProjectiveMeasureFamily_pi
 : IsProjectiveMeasureFamily (fun I : Finset ι => (Measure.pi (fun i : I => μ i)
))
-/
lemma piContent_cylinder {I : Finset ι} {S : Set (Π i : I, X i)} (hS : MeasurableSet S) :
    piContent μ (cylinder I S) = Measure.pi (fun i : I ↦ μ i) S :=
  projectiveFamilyContent_cylinder _ hS

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.piContent_eq_measure_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：piContent_eq_measure_pi [Fintype ι] {s : Set (Π i, X i)} (hs : MeasurableS
et s) : piContent μ s = Measure.pi μ s
参数：Π i, X i；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.piContent_cylinder`：piContent_cylinder {I : Finset ι} {S :
 Set (Π i : I, X i)} (hS : MeasurableSet S) : piContent μ (cylinder I S) = Measu
re.pi (fun i : I => μ …
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_map_piCongrLeft`：∀ {ι : Type u_1} {ι' : Type u_
2} [inst : Fintype ι] [inst_1 : Fintype ι'] (e : ι ≃ ι') {β : ι' → Type u_4}   [
inst_2 : (i : ι') → Measurable…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
-/
theorem piContent_eq_measure_pi [Fintype ι] {s : Set (Π i, X i)} (hs : MeasurableSet s) :
    piContent μ s = Measure.pi μ s := by
  let e : @Finset.univ ι _ ≃ ι :=
    { toFun i := i
      invFun i := ⟨i, mem_univ i⟩ }
  have : s = cylinder univ (MeasurableEquiv.piCongrLeft X e ⁻¹' s) := rfl
  nth_rw 1 [this]
  dsimp [e]
  rw [piContent_cylinder _ (hs.preimage (by fun_prop)), ← Measure.pi_map_piCongrLeft e,
    ← Measure.map_apply (by fun_prop) hs]; rfl

end Preliminaries

section Nat

open Kernel

/-! ### Product of measures indexed by `ℕ` -/

variable {X : ℕ → Type*}

variable {mX : ∀ n, MeasurableSpace (X n)}
  (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

namespace Measure

/-- Infinite product measure indexed by `ℕ`. This is an auxiliary construction, you should use
the generic product measure `Measure.infinitePi`. -/
/-
**MeasureTheory.Measure.infinitePiNat** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：infinitePiNat : Measure (Π n, X n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Infinite product measure indexed by `ℕ`. This is an auxiliary construction, you 
should use
the generic product measure `Measure.infinitePi`.
-/
noncomputable def infinitePiNat : Measure (Π n, X n) :=
  (traj (fun n ↦ const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 ↦ μ i))
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure (Measure.infinitePiNat μ) := by
  rw [Measure.infinitePiNat]; infer_instance

/-- Let `μ : (i : Ioc a c) → Measure (X i)` be a family of measures. Up to an equivalence,
`(⨂ i : Ioc a b, μ i) ⊗ (⨂ i : Ioc b c, μ i) = ⨂ i : Ioc a c, μ i`, where `⊗` denotes the
product of measures. -/
/-
**MeasureTheory.Measure.pi_prod_map_IocProdIoc** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：pi_prod_map_IocProdIoc {a b c : Nat} (hab : a <= b) (hbc : b <= c) : ((Mea
sure.pi (fun i : Ioc a b => μ i)).prod (Measure.pi (fun i : Ioc b c => μ i))).ma
p (IocProdIoc a b c) = Measure.pi (fun i : Ioc a c => μ i)
参数：hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用引理 `measurable_IocProdIoc`：measurable_IocProdIoc [forall i, MeasurableSpace 
(X i)] {a b c : ι} : Measurable (IocProdIoc (X
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Finset.Ioc_subset_Ioc_right`：Ioc_subset_Ioc_right (h : b₁ <= b₂) : Ioc a
 b₁ subseteq Ioc a b₂
· 使用定理 `Finset.Ioc_subset_Ioc_left`：Ioc_subset_Ioc_left (h : a₁ <= a₂) : Ioc a₂ 
b subseteq Ioc a₁ b
· 使用定理 `IocProdIoc_preimage`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 : L
ocallyFiniteOrder ι] [inst_2 : DecidableLE ι] {X : ι → Type u_2}   {a b c : ι} (
hab : a ≤…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `Finset.prod_eq_prod_extend`：prod_eq_prod_extend (f : s -> M) : ∏ x, f x 
= ∏ x in s, Subtype.val.extend f 1 x
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.Ioc_union_Ioc_eq_Ioc`：Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a <=
 b) (h₂ : b <= c) : Ioc a b union Ioc b c = Ioc a c
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.Ioc_disjoint_Ioc_of_le`：Ioc_disjoint_Ioc_of_le {d : α} (hbc : b <
= c) : Disjoint (Ioc a b) (Ioc c d)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Function.extend_val_apply`：∀ {β : Sort u_2} {γ : Sort u_3} {p : β → Prop
} {g : { x // p x } → γ} {j : β → γ} {b : β} (hb : p b),   Function.extend Subty
pe.val g j b = …
· 使用定理 `Finset.restrict₂.eq_1`：∀ {ι : Type u_2} {π : ι → Type u_3} {s t : Finset
 ι} (hst : s ⊆ t) (f : (i : ↥t) → π ↑i) (i : ↥s),   Finset.restrict₂ hst f i = f
 ⟨↑i, ⋯⟩

--- 原说明 ---
Let `μ : (i : Ioc a c) → Measure (X i)` be a family of measures. Up to an equiva
lence,
`(⨂ i : Ioc a b, μ i) ⊗ (⨂ i : Ioc b c, μ i) = ⨂ i : Ioc a c, μ i`, where `⊗` de
notes the
product of measures.
-/
lemma pi_prod_map_IocProdIoc {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Measure.pi (fun i : Ioc a b ↦ μ i)).prod (Measure.pi (fun i : Ioc b c ↦ μ i))).map
      (IocProdIoc a b c) = Measure.pi (fun i : Ioc a c ↦ μ i) := by
  refine (Measure.pi_eq fun s ms ↦ ?_).symm
  simp_rw [Measure.map_apply measurable_IocProdIoc (.univ_pi ms), IocProdIoc_preimage hab hbc,
    Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
  nth_rw 1 [Eq.comm, ← Ioc_union_Ioc_eq_Ioc hab hbc, prod_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1 <;> refine prod_congr rfl fun x hx ↦ ?_
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_right hbc hx),
      restrict₂]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_left hab hx),
      restrict₂]

/-- Let `μ : (i : Iic b) → Measure (X i)` be a family of measures. Up to an equivalence,
`(⨂ i : Iic a, μ i) ⊗ (⨂ i : Ioc a b, μ i) = ⨂ i : Iic b, μ i`, where `⊗` denotes the
product of measures. -/
/-
**MeasureTheory.Measure.pi_prod_map_IicProdIoc** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：pi_prod_map_IicProdIoc {a b : Nat} : ((Measure.pi (fun i : Iic a => μ i)).
prod (Measure.pi (fun i : Ioc a b => μ i))).map (IicProdIoc a b) = Measure.pi (f
un i : Iic b => μ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用引理 `measurable_IicProdIoc`：measurable_IicProdIoc {m n : ι} : Measurable (Iic
ProdIoc (X
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
· 使用定理 `IicProdIoc_preimage`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 : L
ocallyFiniteOrder ι] [inst_2 : DecidableLE ι] {X : ι → Type u_2}   [inst_3 : Loc
allyFinit…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `Finset.prod_eq_prod_extend`：prod_eq_prod_extend (f : s -> M) : ∏ x, f x 
= ∏ x in s, Subtype.val.extend f 1 x
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.Iic_union_Ioc_eq_Iic`：Iic_union_Ioc_eq_Iic (h : a <= b) : Iic a u
nion Ioc a b = Iic b
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.Iic_disjoint_Ioc`：Iic_disjoint_Ioc (h : a <= b) : Disjoint (Iic a
) (Ioc b c)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Function.extend_val_apply`：∀ {β : Sort u_2} {γ : Sort u_3} {p : β → Prop
} {g : { x // p x } → γ} {j : β → γ} {b : β} (hb : p b),   Function.extend Subty
pe.val g j b = …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Let `μ : (i : Iic b) → Measure (X i)` be a family of measures. Up to an equivale
nce,
`(⨂ i : Iic a, μ i) ⊗ (⨂ i : Ioc a b, μ i) = ⨂ i : Iic b, μ i`, where `⊗` denote
s the
product of measures.
-/
lemma pi_prod_map_IicProdIoc {a b : ℕ} :
    ((Measure.pi (fun i : Iic a ↦ μ i)).prod (Measure.pi (fun i : Ioc a b ↦ μ i))).map
      (IicProdIoc a b) = Measure.pi (fun i : Iic b ↦ μ i) := by
  obtain hab | hba := le_total a b
  · refine (Measure.pi_eq fun s ms ↦ ?_).symm
    simp_rw [Measure.map_apply measurable_IicProdIoc (.univ_pi ms), IicProdIoc_preimage hab,
      Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
    nth_rw 1 [Eq.comm, ← Iic_union_Ioc_eq_Iic hab, prod_union (Iic_disjoint_Ioc le_rfl)]
    congr 1 <;> refine prod_congr rfl fun x hx ↦ ?_
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Iic_subset_Iic.2 hab hx),
        frestrictLe₂, restrict₂]
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Iic_self hx),
        restrict₂]
  · rw [IicProdIoc_le hba, ← Measure.map_map, ← Measure.fst, Measure.fst_prod]
    · exact isProjectiveMeasureFamily_pi μ (Iic a) (Iic b) (Iic_subset_Iic.2 hba) |>.symm
    all_goals fun_prop

/-- Let `μ (i + 1) : Measure (X (i + 1))` be a measure. Up to an equivalence,
`μ i = ⨂ j : Ioc i (i + 1), μ i`, where `⊗` denotes the product of measures. -/
/-
**MeasureTheory.Measure.map_piSingleton** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：map_piSingleton (μ : (n : Nat) -> Measure (X n)) [forall n, SigmaFinite (μ
 n)] (n : Nat) : (μ (n + 1)).map (piSingleton n) = Measure.pi (fun i : Ioc n (n 
+ 1) => μ i)
参数：μ : (n : Nat) -> Measure (X n)；μ n；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Ioc_succ_singleton`：Ioc_succ_singleton : Ioc b (b + 1) = {b + 1}
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Fintype.prod_subsingleton`：prod_subsingleton [Subsingleton ι] (f : ι -> 
M) (a : ι) : ∏ x : ι, f x = f a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a

--- 原说明 ---
Let `μ (i + 1) : Measure (X (i + 1))` be a measure. Up to an equivalence,
`μ i = ⨂ j : Ioc i (i + 1), μ i`, where `⊗` denotes the product of measures.
-/
lemma map_piSingleton (μ : (n : ℕ) → Measure (X n)) [∀ n, SigmaFinite (μ n)] (n : ℕ) :
    (μ (n + 1)).map (piSingleton n) = Measure.pi (fun i : Ioc n (n + 1) ↦ μ i) := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have : Subsingleton (Ioc n (n + 1)) := by rw [Nat.Ioc_succ_singleton]; infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1, mem_Ioc.2 (by lia)⟩,
    Measure.map_apply (by fun_prop) (.univ_pi hs)]
  congr 1 with x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
    Nat.Ioc_succ_singleton, mem_singleton]
  exact ⟨fun h ↦ h (n + 1) rfl, fun h a b ↦ b.symm ▸ h⟩

end Measure

/-- `partialTraj κ a b` is a kernel which up to an equivalence is equal to
`Kernel.id ×ₖ (κ a ⊗ₖ ... ⊗ₖ κ (b - 1))`. This lemma therefore states that if the kernels `κ`
are constant then their composition-product is the product measure. -/
/-
**MeasureTheory.partialTraj_const_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`partialTraj κ a b` is a kernel which up to an equivalence is equal to
`Kernel.id ×ₖ (κ a ⊗ₖ ... ⊗ₖ κ (b - 1))`. This lemma therefore states that if th
e kernels `κ`
are constant then their composition-product is the product measure.
-/
theorem partialTraj_const_restrict₂ {a b : ℕ} :
    (partialTraj (fun n ↦ const _ (μ (n + 1))) a b).map (restrict₂ Ioc_subset_Iic_self) =
    const _ (Measure.pi (fun i : Ioc a b ↦ μ i)) := by
  obtain hab | hba := lt_or_ge a b
  · refine Nat.le_induction ?_ (fun n hn hind ↦ ?_) b (Nat.succ_le_of_lt hab) <;> ext1 x₀
    · rw [partialTraj_succ_self, ← map_comp_right, map_apply, prod_apply, map_apply, const_apply,
        const_apply, Measure.map_piSingleton, restrict₂_comp_IicProdIoc, Measure.map_snd_prod,
        measure_univ, one_smul]
      all_goals fun_prop
    · have : (restrict₂ (Ioc_subset_Iic_self (a := a))) ∘ (IicProdIoc (X := X) n (n + 1)) =
          (IocProdIoc a n (n + 1)) ∘ (Prod.map (restrict₂ Ioc_subset_Iic_self) id) := rfl
      rw [const_apply, partialTraj_succ_of_le (by lia), map_const, prod_const_comp, id_comp,
        ← map_comp_right, this, map_comp_right, ← map_prod_map, hind, Kernel.map_id, map_apply,
        prod_apply, const_apply, const_apply, Measure.map_piSingleton,
        Measure.pi_prod_map_IocProdIoc]
      any_goals fun_prop
      all_goals lia
  · have : IsEmpty (Ioc a b) := by simpa [hba] using Subtype.isEmpty_false
    ext x s ms
    by_cases hs : s.Nonempty
    · rw [Subsingleton.eq_univ_of_nonempty hs, @measure_univ .., measure_univ]
      exact (IsMarkovKernel.map _ (measurable_restrict₂ _)) |>.isProbabilityMeasure x
    · rw [Set.not_nonempty_iff_eq_empty.1 hs]
      simp

/-- `partialTraj κ a b` is a kernel which up to an equivalence is equal to
`Kernel.id ×ₖ (κ a ⊗ₖ ... ⊗ₖ κ (b - 1))`. This lemma therefore states that if the kernel `κ i`
is constant equal to `μ i` for all `i`, then up to an equivalence
`partialTraj κ a b = Kernel.id ×ₖ Kernel.const (⨂ μ i)`. -/
/-
**MeasureTheory.partialTraj_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：partialTraj_const {a b : Nat} : partialTraj (fun n => const _ (μ (n + 1)))
 a b = (Kernel.id ×ₖ (const _ (Measure.pi (fun i : Ioc a b => μ i)))).map (IicPr
odIoc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_eq_prod`：partialTraj_eq_prod [foral
l n, IsSFiniteKernel (κ n)] (a b : Nat) : partialTraj κ a b = (Kernel.id ×ₖ (par
tialTraj κ a b).map (restrict₂ Ioc…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.partialTraj_const_restrict₂`：partialTraj_const_restrict₂ {
a b : Nat} : (partialTraj (fun n => const _ (μ (n + 1))) a b).map (restrict₂ Ioc
_subset_Iic_self) = const _ (Me…

--- 原说明 ---
`partialTraj κ a b` is a kernel which up to an equivalence is equal to
`Kernel.id ×ₖ (κ a ⊗ₖ ... ⊗ₖ κ (b - 1))`. This lemma therefore states that if th
e kernel `κ i`
is constant equal to `μ i` for all `i`, then up to an equivalence
`partialTraj κ a b = Kernel.id ×ₖ Kernel.const (⨂ μ i)`.
-/
theorem partialTraj_const {a b : ℕ} :
    partialTraj (fun n ↦ const _ (μ (n + 1))) a b =
      (Kernel.id ×ₖ (const _ (Measure.pi (fun i : Ioc a b ↦ μ i)))).map (IicProdIoc a b) := by
  rw [partialTraj_eq_prod, partialTraj_const_restrict₂]

namespace Measure

/-
**MeasureTheory.Measure.isProjectiveLimit_infinitePiNat** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：isProjectiveLimit_infinitePiNat : IsProjectiveLimit (infinitePiNat μ) (fun
 I : Finset Nat => (Measure.pi (fun i : I => μ i)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.subset_Iic_sup_id`：subset_Iic_sup_id [OrderBot α] (s : Finset α) 
: s subseteq Iic (s.sup id)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.isProjectiveMeasureFamily_pi`：isProjectiveMeasureFamily_pi
 : IsProjectiveMeasureFamily (fun I : Finset ι => (Measure.pi (fun i : I => μ i)
))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.restrict₂_comp_restrict`：restrict₂_comp_restrict (hst : s subsete
q t) : (restrict₂ (π
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `Preorder.frestrictLe.eq_1`：∀ {α : Type u_1} [inst : Preorder α] {π : α →
 Type u_2} [inst_1 : LocallyFiniteOrderBot α] (a : α),   Preorder.frestrictLe a 
= (Finset.Iic a…
· 使用定理 `MeasureTheory.Measure.infinitePiNat.eq_1`：∀ {X : ℕ → Type u_1} {mX : (n 
: ℕ) → MeasurableSpace (X n)} (μ : (n : ℕ) → MeasureTheory.Measure (X n))   [hμ 
: ∀ (n : ℕ), MeasureTheory.IsP…
· 使用引理 `MeasureTheory.Measure.map_comp`：map_comp (μ : Measure α) (κ : Kernel α β
) {f : β -> γ} (hf : Measurable f) : (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用定理 `MeasureTheory.partialTraj_const`：partialTraj_const {a b : Nat} : partial
Traj (fun n => const _ (μ (n + 1))) a b = (Kernel.id ×ₖ (const _ (Measure.pi (fu
n i : Ioc a b => μ i)…
· 使用引理 `measurable_IicProdIoc`：measurable_IicProdIoc {m n : ι} : Measurable (Iic
ProdIoc (X
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用引理 `MeasureTheory.Measure.compProd_const`：compProd_const {ν : Measure β} [SF
inite μ] [SFinite ν] : μ otimesₘ (Kernel.const α ν) = μ.prod ν
· 使用引理 `MeasureTheory.Measure.pi_prod_map_IicProdIoc`：pi_prod_map_IicProdIoc {a 
b : Nat} : ((Measure.pi (fun i : Iic a => μ i)).prod (Measure.pi (fun i : Ioc a 
b => μ i))).map (IicProdIoc a b) =…
-/
theorem isProjectiveLimit_infinitePiNat :
    IsProjectiveLimit (infinitePiNat μ) (fun I : Finset ℕ ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  rw [isProjectiveMeasureFamily_pi μ _ _ I.subset_Iic_sup_id,
    ← restrict₂_comp_restrict I.subset_Iic_sup_id, ← map_map, ← frestrictLe, infinitePiNat,
    map_comp, traj_map_frestrictLe, partialTraj_const, ← map_comp, ← compProd_eq_comp_prod,
    compProd_const, pi_prod_map_IicProdIoc]
  all_goals fun_prop

/-- Restricting the product measure to a product indexed by a finset yields the usual
product measure. -/
/-
**MeasureTheory.Measure.infinitePiNat_map_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：infinitePiNat_map_restrict (I : Finset Nat) : (infinitePiNat μ).map I.rest
rict = Measure.pi fun i : I => μ i
参数：I : Finset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProjectiveLimit_infinitePiNat`：isProjectiveLimit
_infinitePiNat : IsProjectiveLimit (infinitePiNat μ) (fun I : Finset Nat => (Mea
sure.pi (fun i : I => μ i)))

--- 原说明 ---
Restricting the product measure to a product indexed by a finset yields the usua
l
product measure.
-/
lemma infinitePiNat_map_restrict (I : Finset ℕ) :
    (infinitePiNat μ).map I.restrict = Measure.pi fun i : I ↦ μ i :=
  isProjectiveLimit_infinitePiNat μ I
/-
**MeasureTheory.Measure.piContent_eq_infinitePiNat** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：piContent_eq_infinitePiNat {A : Set (Π n, X n)} (hA : A in measurableCylin
ders X) : piContent μ A = infinitePiNat μ A
参数：Π n, X n；hA : A in measurableCylinders X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.piContent_cylinder`：piContent_cylinder {I : Finset ι} {S :
 Set (Π i : I, X i)} (hS : MeasurableSet S) : piContent μ (cylinder I S) = Measu
re.pi (fun i : I => μ …
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用引理 `MeasureTheory.Measure.infinitePiNat_map_restrict`：infinitePiNat_map_rest
rict (I : Finset Nat) : (infinitePiNat μ).map I.restrict = Measure.pi fun i : I 
=> μ i
-/
theorem piContent_eq_infinitePiNat {A : Set (Π n, X n)} (hA : A ∈ measurableCylinders X) :
    piContent μ A = infinitePiNat μ A := by
  obtain ⟨s, S, mS, rfl⟩ : ∃ s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [piContent_cylinder _ mS, cylinder, ← map_apply (measurable_restrict _) mS,
    infinitePiNat_map_restrict]

end Measure

end Nat

section InfinitePi

open Measure

/-! ### Product of infinitely many probability measures -/

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If we push the product measure forward by a reindexing equivalence, we get a product measure
on the reindexed product in the sense that it coincides with `piContent μ` over
measurable cylinders. See `infinitePi_map_piCongrLeft` for a general version. -/
/-
**MeasureTheory.Measure.infinitePiNat_map_piCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)}
 (μ : (i : ι) → MeasureTheory.Measure (X i))   [hμ : ∀ (i : ι), MeasureTheory.Is
ProbabilityMeasure (μ i)] (e : ℕ ≃ ι) {s : Set ((i : ι) → X i)},   s ∈ MeasureTh
eory.measurableCylinders X →     (MeasureTheory.Measure.map (⇑(MeasurableEquiv.p
iCongrLeft X e))           (MeasureTheory.Measure.infinitePiNat fun n => μ (e n)
))         s =       (MeasureTheory.piContent μ) s
参数：i : ι；X i；μ : (i : ι) → MeasureTheory.Measure (X i)；i : ι；μ i；e : ℕ ≃ ι；(i : 
ι) → X i；MeasureTheory.Measure.map (⇑(MeasurableEquiv.piCongrLeft X e))         
  (MeasureTheory.Measure.infinitePiNat fun n => μ (e n))；MeasureTheory.piContent
 μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasurableSet.cylinder`：∀ {ι : Type u_2} {α : ι → Type u_1} [inst : (i :
 ι) → MeasurableSpace (α i)] (s : Finset ι) {S : Set ((i : ↥s) → α ↑i)},   Measu
rableSet S →…
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `MeasurableEquiv.coe_piCongrLeft`：coe_piCongrLeft (f : δ ≃ δ') : ⇑(Measur
ableEquiv.piCongrLeft π f) = f.piCongrLeft π
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `Finset.restrict_comp_piCongrLeft`：Finset.restrict_comp_piCongrLeft {π : 
β -> Type*} (s : Finset β) (e : α ≃ β) : s.restrict ∘ ⇑(e.piCongrLeft π) = ⇑((e.
restrictPreimageFinset…
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `measurable_piCongrLeft`：measurable_piCongrLeft (f : δ' ≃ δ) : Measurable
 (Equiv.piCongrLeft X f)
· 使用引理 `MeasureTheory.Measure.infinitePiNat_map_restrict`：infinitePiNat_map_rest
rict (I : Finset Nat) : (infinitePiNat μ).map I.restrict = Measure.pi fun i : I 
=> μ i
· 使用引理 `MeasureTheory.piContent_cylinder`：piContent_cylinder {I : Finset ι} {S :
 Set (Π i : I, X i)} (hS : MeasurableSet S) : piContent μ (cylinder I S) = Measu
re.pi (fun i : I => μ …
· 使用定理 `MeasureTheory.Measure.pi_map_piCongrLeft`：∀ {ι : Type u_1} {ι' : Type u_
2} [inst : Fintype ι] [inst_1 : Fintype ι'] (e : ι ≃ ι') {β : ι' → Type u_4}   [
inst_2 : (i : ι') → Measurable…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If we push the product measure forward by a reindexing equivalence, we get a pro
duct measure
on the reindexed product in the sense that it coincides with `piContent μ` over
measurable cylinders. See `infinitePi_map_piCongrLeft` for a general version.
-/
lemma Measure.infinitePiNat_map_piCongrLeft (e : ℕ ≃ ι) {s : Set (Π i, X i)}
    (hs : s ∈ measurableCylinders X) :
    (infinitePiNat (fun n ↦ μ (e n))).map (piCongrLeft X e) s = piContent μ s := by
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
  rw [map_apply _ hS.cylinder, cylinder, ← Set.preimage_comp, coe_piCongrLeft,
    restrict_comp_piCongrLeft, Set.preimage_comp, ← map_apply,
    infinitePiNat_map_restrict (fun n ↦ μ (e n)), ← cylinder, piContent_cylinder μ hS,
    ← pi_map_piCongrLeft (e.restrictPreimageFinset I), map_apply _ hS, coe_piCongrLeft]
  · simp
  any_goals fun_prop
  exact hS.preimage (by fun_prop)

set_option backward.isDefEq.respectTransparency.types false in
/-- This is the key theorem to build the product of an arbitrary family of probability measures:
the `piContent` of a decreasing sequence of cylinders with empty intersection converges to `0`.

This implies the `σ`-additivity of `piContent` (see `addContent_iUnion_eq_sum_of_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem. -/
/-
**MeasureTheory.piContent_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：piContent_tendsto_zero {A : Nat -> Set (Π i, X i)} (A_mem : forall n, A n 
in measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) : Tends
to (fun n => piContent μ (A n)) atTop (𝓝 0)
参数：Π i, X i；A_mem : forall n, A n in measurableCylinders X；A_anti : Antitone A；A
_inter : ⋂ n, A n = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_isProbabilityMeasure`：nonempty_of_isProbabilit
yMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `measurable_piCongrLeft`：measurable_piCongrLeft (f : δ' ≃ δ) : Measurable
 (Equiv.piCongrLeft X f)
· 使用定理 `MeasurableSet.of_mem_measurableCylinders`：∀ {ι : Type u_1} {α : ι → Type
 u_2} [inst : (i : ι) → MeasurableSpace (α i)] {s : Set ((i : ι) → α i)},   s ∈ 
MeasureTheory.measurableCylind…
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用引理 `MeasureTheory.piContent_cylinder`：piContent_cylinder {I : Finset ι} {S :
 Set (Π i : I, X i)} (hS : MeasurableSet S) : piContent μ (cylinder I S) = Measu
re.pi (fun i : I => μ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_map_piCongrLeft`：∀ {ι : Type u_1} {ι' : Type u_
2} [inst : Fintype ι] [inst_1 : Fintype ι'] (e : ι ≃ ι') {β : ι' → Type u_4}   [
inst_2 : (i : ι') → Measurable…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
This is the key theorem to build the product of an arbitrary family of probabili
ty measures:
the `piContent` of a decreasing sequence of cylinders with empty intersection co
nverges to `0`.

This implies the `σ`-additivity of `piContent` (see `addContent_iUnion_eq_sum_of
_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem.
-/
theorem piContent_tendsto_zero {A : ℕ → Set (Π i, X i)} (A_mem : ∀ n, A n ∈ measurableCylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ piContent μ (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := fun i ↦ nonempty_of_isProbabilityMeasure (μ i)
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set, because on the product indexed
  -- by this countable set we can build a measure. To do so we have to pull back our cylinders
  -- along the injection from `Π i : u, X i` to `Π i, X i`.
  let u := ⋃ n, (s n : Set ι)
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t n : Finset u := (s n).preimage Subtype.val Subtype.val_injective.injOn
  classical
  -- The map `f` allows to pull back `Aₙ`
  let f : (Π i : u, X i) → Π i, X i :=
    fun x i ↦ if hi : i ∈ u then x ⟨i, hi⟩ else Classical.ofNonempty
  -- `aux` is the obvious equivalence between `sₙ` and `tₙ`
  let aux n : t n ≃ s n :=
    { toFun := fun i ↦ ⟨i.1.1, mem_preimage.1 i.2⟩
      invFun := fun i ↦ ⟨⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩, mem_preimage.2 i.2⟩
      left_inv := fun i ↦ by simp
      right_inv := fun i ↦ by simp }
  -- Finally `gₙ` is the equivalence between the product indexed by `tₙ` and the one indexed by `sₙ`
  let g n := (aux n).piCongrLeft (fun i : s n ↦ X i)
  -- Mapping from the product indexed by `u` by `f` and then restricting to `sₙ` is the same as
  -- first restricting to `tₙ` and then mapping by `gₙ`
  have r_comp_f n : (s n).restrict ∘ f = (g n) ∘ (fun (x : Π i : u, X i) i ↦ x i) := by
    ext x i
    simp only [Function.comp_apply, Finset.restrict,
      Equiv.piCongrLeft_apply, Equiv.coe_fn_symm_mk, f, aux, g, t]
    rw [dif_pos (Set.mem_iUnion.2 ⟨n, i.2⟩)]
  -- `Bₙ` is the same as `Aₙ` but in the product indexed by `u`
  let B n := f ⁻¹' (A n)
  -- `Tₙ` is the same as `Sₙ` but in the product indexed by `u`
  let T n := (g n) ⁻¹' (S n)
  -- We now transfer the properties of `Aₙ` and `Sₙ` to `Bₙ` and `Tₙ`
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, r_comp_f]; rfl
  have mT n : MeasurableSet (T n) := (mS n).preimage (by fun_prop)
  have B_mem n : B n ∈ measurableCylinders (fun i : u ↦ X i) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  have mB n : MeasurableSet (B n) := .of_mem_measurableCylinders (B_mem n)
  have B_anti : Antitone B := fun m n hmn ↦ Set.preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  -- We now rewrite `piContent μ (A n)` as `piContent (fun i : u ↦ μ i) (B n)`. Then there are two
  -- cases: either `u` is finite and we rewrite it to the finite product measure, either
  -- it is countable and we rewrite it to the pushforward measure of `infinitePiNat`. In both cases
  -- we have an actual measure and we can conclude with `tendsto_measure_iInter_atTop`.
  conv =>
    enter [1]; ext n
    rw [A_eq, piContent_cylinder μ (mS n), ← pi_map_piCongrLeft (aux n),
      map_apply (by fun_prop) (mS n)]
    change (Measure.pi (fun i : t n ↦ μ i)) (T n)
    rw [← piContent_cylinder (fun i : u ↦ μ i) (mT n), ← B_eq n]
  obtain u_fin | u_inf := finite_or_infinite u
  · let _ := Fintype.ofFinite u
    simp_rw [fun n ↦ piContent_eq_measure_pi (fun i : u ↦ μ i) (mB n)]
    convert!
      tendsto_measure_iInter_atTop (fun n ↦ (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ u) nonempty_equiv_of_countable
    conv => enter [1]; ext n; rw [← infinitePiNat_map_piCongrLeft _ φ (B_mem n)]
    convert!
      tendsto_measure_iInter_atTop (fun n ↦ (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance

/-- The `projectiveFamilyContent` associated to a family of probability measures is
σ-subadditive. -/
/-
**MeasureTheory.isSigmaSubadditive_piContent** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：isSigmaSubadditive_piContent : (piContent μ).IsSigmaSubadditive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum`：isSigmaSu
badditive_of_addContent_iUnion_eq_tsum {m : AddContent Real>=0∞ C} (hC : IsSetRi
ng C) (m_iUnion : forall (f : Nat -> Set α) (_ : fo…
· 使用引理 `MeasureTheory.isSetRing_measurableCylinders`：isSetRing_measurableCylinde
rs : IsSetRing (measurableCylinders α)
· 使用定理 `MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero`：addContent_iUnio
n_eq_sum_of_tendsto_zero (hC : IsSetRing C) (m : AddContent Real>=0∞ C) (hm_ne_t
op : forall s in C, m s != ∞) (hm_tendsto : …
· 使用引理 `MeasureTheory.projectiveFamilyContent_ne_top`：projectiveFamilyContent_ne
_top [forall J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) : proj
ectiveFamilyContent hP s != ∞
· 使用定理 `MeasureTheory.Measure.pi.instIsFiniteMeasure`：∀ {ι : Type u_1} {α : ι → 
Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (
i : ι) → MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用引理 `MeasureTheory.isProjectiveMeasureFamily_pi`：isProjectiveMeasureFamily_pi
 : IsProjectiveMeasureFamily (fun I : Finset ι => (Measure.pi (fun i : I => μ i)
))
· 使用定理 `MeasureTheory.piContent_tendsto_zero`：piContent_tendsto_zero {A : Nat ->
 Set (Π i, X i)} (A_mem : forall n, A n in measurableCylinders X) (A_anti : Anti
tone A) (A_inter : ⋂ n, A …

--- 原说明 ---
The `projectiveFamilyContent` associated to a family of probability measures is
σ-subadditive.
-/
theorem isSigmaSubadditive_piContent : (piContent μ).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (piContent μ) (fun s hs ↦ projectiveFamilyContent_ne_top _)
    (fun _ ↦ piContent_tendsto_zero μ) hf hf_Union hf'

namespace Measure

open scoped Classical in
/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the associated product
measure.

It is defined via an `if ... then ... else` so that it can be manipulated without carrying
a proof that the measures are probability measures. -/
/-
**MeasureTheory.Measure.infinitePi** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：infinitePi : Measure (Π i, X i)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isSetSemiring_measurableCylinders`：isSetSemiring_measurabl
eCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α)
· 使用定理 `MeasureTheory.isSigmaSubadditive_piContent`：isSigmaSubadditive_piContent
 : (piContent μ).IsSigmaSubadditive

--- 原说明 ---
The product measure of an arbitrary family of probability measures. It is define
d as the unique
extension of the function which gives to cylinders the measure given by the asso
ciated product
measure.

It is defined via an `if ... then ... else` so that it can be manipulated withou
t carrying
a proof that the measures are probability measures.
-/
noncomputable def infinitePi : Measure (Π i, X i) :=
  if h : ∀ i, IsProbabilityMeasure (μ i) then
    (piContent μ).measure isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.ge (isSigmaSubadditive_piContent (hμ := h) μ)
    else 0

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measure applied to cylinders. -/
/-
**MeasureTheory.Measure.isProjectiveLimit_infinitePi** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：isProjectiveLimit_infinitePi : IsProjectiveLimit (infinitePi μ) (fun I : F
inset ι => (Measure.pi (fun i : I => μ i)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用引理 `MeasureTheory.isSetSemiring_measurableCylinders`：isSetSemiring_measurabl
eCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α)
· 使用定理 `MeasureTheory.isSigmaSubadditive_piContent`：isSigmaSubadditive_piContent
 : (piContent μ).IsSigmaSubadditive
· 使用定理 `MeasureTheory.Measure.infinitePi.eq_1`：∀ {ι : Type u_1} {X : ι → Type u_
2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → MeasureTheory.Measure (
X i)),   MeasureTheory.Meas…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.generateFrom_measurableCylinders`：generateFrom_measurableC
ylinders : MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpac
e.pi
· 使用定理 `MeasureTheory.AddContent.measure_eq`：measure_eq [mα : MeasurableSpace α]
 (m : AddContent Real>=0∞ C) (hC : IsSetSemiring C) (hC_gen : mα = MeasurableSpa
ce.generateFrom C) (m_sig…
· 使用定理 `MeasureTheory.cylinder_mem_measurableCylinders`：cylinder_mem_measurableC
ylinders (s : Finset ι) (S : Set (forall i : s, α i)) (hS : MeasurableSet S) : c
ylinder s S in measurableCylinders α
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用引理 `MeasureTheory.piContent_cylinder`：piContent_cylinder {I : Finset ι} {S :
 Set (Π i : I, X i)} (hS : MeasurableSet S) : piContent μ (cylinder I S) = Measu
re.pi (fun i : I => μ …

--- 原说明 ---
The product measure is the projective limit of the partial product measures. Thi
s ensures
uniqueness and expresses the value of the product measure applied to cylinders.
-/
theorem isProjectiveLimit_infinitePi :
    IsProjectiveLimit (infinitePi μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  ext s hs
  rw [map_apply (measurable_restrict I) hs, infinitePi, dif_pos hμ, AddContent.measure_eq,
    ← cylinder, piContent_cylinder μ hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

/-- Restricting the product measure to a product indexed by a finset yields the usual
product measure. -/
/-
**MeasureTheory.Measure.infinitePi_map_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：infinitePi_map_restrict {I : Finset ι} : (Measure.infinitePi μ).map I.rest
rict = Measure.pi fun i : I => μ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProjectiveLimit_infinitePi`：isProjectiveLimit_in
finitePi : IsProjectiveLimit (infinitePi μ) (fun I : Finset ι => (Measure.pi (fu
n i : I => μ i)))

--- 原说明 ---
Restricting the product measure to a product indexed by a finset yields the usua
l
product measure.
-/
theorem infinitePi_map_restrict {I : Finset ι} :
    (Measure.infinitePi μ).map I.restrict = Measure.pi fun i : I ↦ μ i :=
  isProjectiveLimit_infinitePi μ I
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure (infinitePi μ) := by
  constructor
  rw [← cylinder_univ ∅, cylinder, ← map_apply (measurable_restrict _) .univ,
    infinitePi_map_restrict, measure_univ]

/-- To prove that a measure is equal to the product measure it is enough to check that it
it gives the same measure to measurable boxes. -/
/-
**MeasureTheory.Measure.eq_infinitePi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：eq_infinitePi {ν : Measure (Π i, X i)} (hν : forall s : Finset ι, forall t
 : (i : ι) -> Set (X i), (forall i, MeasurableSet (t i)) -> ν (Set.pi s t) = ∏ i
 in s, μ i (t i)) : ν = infinitePi μ
参数：Π i, X i；hν : forall s : Finset ι, forall t : (i : ι) -> Set (X i), (forall i
, MeasurableSet (t i)) -> ν (Set.pi s t) = ∏ i in s, μ i (t i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsProjectiveLimit.unique`：unique [forall i, IsFiniteMeasur
e (P i)] (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) : μ = ν
· 使用定理 `MeasureTheory.Measure.pi.instIsFiniteMeasure`：∀ {ι : Type u_1} {α : ι → 
Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (
i : ι) → MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Measure.isProjectiveLimit_infinitePi`：isProjectiveLimit_in
finitePi : IsProjectiveLimit (infinitePi μ) (fun I : Finset ι => (Measure.pi (fu
n i : I => μ i)))
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Finset.restrict_preimage_univ`：restrict_preimage_univ [DecidablePred (· 
in s)] (t : (i : s) -> Set (π i)) : s.restrict ⁻¹' (Set.univ.pi t) = Set.pi s (f
un i => if h : i in…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
To prove that a measure is equal to the product measure it is enough to check th
at it
it gives the same measure to measurable boxes.
-/
theorem eq_infinitePi {ν : Measure (Π i, X i)}
    (hν : ∀ s : Finset ι, ∀ t : (i : ι) → Set (X i),
      (∀ i, MeasurableSet (t i)) → ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)) :
    ν = infinitePi μ := by
  refine (isProjectiveLimit_infinitePi μ).unique ?_ |>.symm
  refine fun s ↦ (pi_eq fun t ht ↦ ?_).symm
  classical
  rw [Measure.map_apply, restrict_preimage_univ, hν, ← prod_attach, univ_eq_attach]
  · congr with i
    rw [dif_pos i.2]
  any_goals fun_prop
  · rintro i
    split_ifs with hi
    · exact ht ⟨i, hi⟩
    · exact .univ
  · exact .univ_pi ht
/-
**MeasureTheory.Measure.infinitePi_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：infinitePi_pi {s : Finset ι} {t : (i : ι) -> Set (X i)} (mt : forall i in 
s, MeasurableSet (t i)) : infinitePi μ (Set.pi s t) = ∏ i in s, μ i (t i)
参数：i : ι；X i；mt : forall i in s, MeasurableSet (t i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.Measure.infinitePi_map_restrict`：infinitePi_map_restrict {
I : Finset ι} : (Measure.infinitePi μ).map I.restrict = Measure.pi fun i : I => 
μ i
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
-/
lemma infinitePi_pi {s : Finset ι} {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    infinitePi μ (Set.pi s t) = ∏ i ∈ s, μ i (t i) := by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s ↦ t i)) := by
    ext x
    simp
  rw [this, cylinder, ← map_apply, infinitePi_map_restrict, pi_pi]
  · rw [univ_eq_attach, prod_attach _ (fun i ↦ (μ i) (t i))]
  · exact measurable_restrict _
  · exact .univ_pi fun i ↦ mt i.1 i.2
/-
**MeasureTheory.Measure.infinitePi_map_restrict'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：infinitePi_map_restrict' {I : Set ι} : (infinitePi μ).map I.domRestrict = 
infinitePi fun i : I => μ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.eq_infinitePi`：eq_infinitePi {ν : Measure (Π i, X 
i)} (hν : forall s : Finset ι, forall t : (i : ι) -> Set (X i), (forall i, Measu
rableSet (t i)) -> ν (Set…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Set.measurable_restrict`：Set.measurable_restrict (s : Set δ) : Measurabl
e (s.domRestrict (π
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Finset.domRestrict_preimage`：domRestrict_preimage [DecidableEq ι] {I : S
et ι} [DecidablePred (· in I)] (s : Finset I) (u : (i : I) -> Set (π i)) : I.dom
Restrict ⁻¹' Set.…
· 使用引理 `MeasureTheory.Measure.infinitePi_pi`：infinitePi_pi {s : Finset ι} {t : (
i : ι) -> Set (X i)} (mt : forall i in s, MeasurableSet (t i)) : infinitePi μ (S
et.pi s t) = ∏ i in s, μ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem infinitePi_map_restrict' {I : Set ι} :
    (infinitePi μ).map I.domRestrict = infinitePi fun i : I ↦ μ i := by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop), domRestrict_preimage, infinitePi_pi _ (by measurability)]
  · simp
  · exact .pi s.countable_toSet (by measurability)
/-
**MeasureTheory.Measure.infinitePi_pi_of_countable** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：infinitePi_pi_of_countable {s : Set ι} (hs : Countable s) {t : (i : ι) -> 
Set (X i)} (mt : forall i in s, MeasurableSet (t i)) : infinitePi μ (Set.pi s t)
 = ∏' i : s, μ i (t i)
参数：hs : Countable s；i : ι；X i；mt : forall i in s, MeasurableSet (t i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.infinitePi_pi`：infinitePi_pi {s : Finset ι} {t : (
i : ι) -> Set (X i)} (mt : forall i in s, MeasurableSet (t i)) : infinitePi μ (S
et.pi s t) = ∏ i in s, μ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.infinitePi_map_restrict'`：infinitePi_map_restrict'
 {I : Set ι} : (infinitePi μ).map I.domRestrict = infinitePi fun i : I => μ i
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Set.measurable_restrict`：Set.measurable_restrict (s : Set δ) : Measurabl
e (s.domRestrict (π
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用引理 `Finset.domRestrict_preimage`：domRestrict_preimage [DecidableEq ι] {I : S
et ι} [DecidablePred (· in I)] (s : Finset I) (u : (i : I) -> Set (π i)) : I.dom
Restrict ⁻¹' Set.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Set.pi_iUnion_eq_iInter_pi`：pi_iUnion_eq_iInter_pi {α' : Type*} (s : α' 
-> Set α) (t : (a : α) -> Set (π a)) : (⋃ i, s i).pi t = ⋂ i, (s i).pi t
· 使用定理 `Set.iUnion_finset_eq_set`：iUnion_finset_eq_set (s : Set ι) : ⋃ s' : Fins
et s, Subtype.val '' (s' : Set s) = s
· 使用定理 `MeasureTheory.tendsto_measure_iInter_atTop`：tendsto_measure_iInter_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hs : f
orall i, NullMeasurableSet (s i)…
· 使用定理 `Filter.atTop.isCountablyGenerated`：∀ {α : Type u_1} [inst : Preorder α] 
[Countable α], Filter.atTop.IsCountablyGenerated
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
（共 57 条，此处仅展示前 30 条）
-/
lemma infinitePi_pi_of_countable {s : Set ι} (hs : Countable s) {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    infinitePi μ (Set.pi s t) = ∏' i : s, μ i (t i) := by
  wlog s_ne : Nonempty s
  · simp [Set.not_nonempty_iff_eq_empty'.mp s_ne]
  apply tendsto_nhds_unique (f := fun s' : Finset s ↦ ∏ i ∈ s', μ i (t i)) (l := atTop)
  classical
  · conv in ∏ _ ∈ _, _ =>
      rw [← infinitePi_pi _ (by measurability), ← infinitePi_map_restrict', map_apply
        (by fun_prop) (by apply MeasurableSet.pi (countable_toSet _) (by measurability)),
        domRestrict_preimage]
      simp only [coe_image, dite_eq_ite]
    have : s.pi t
      = ⋂ s' : Finset s,
        (Subtype.val '' (s' : Set s)).pi (fun i ↦ if i ∈ s then t i else Set.univ) := by
      rw [← Set.pi_iUnion_eq_iInter_pi, Set.iUnion_finset_eq_set]
      grind
    rw [this]
    apply tendsto_measure_iInter_atTop
    · refine fun s' ↦ MeasurableSet.nullMeasurableSet (MeasurableSet.pi ?_ (by measurability))
      exact (Finset.countable_toSet _).image _
    · intro _ _ h
      simpa using Set.pi_mono' (by simp) (Set.image_mono h)
    · exact ⟨{Nonempty.some s_ne}, by simp⟩
  · rw [ENNReal.tprod_eq_iInf_prod (by simp [prob_le_one])]
    exact tendsto_atTop_iInf (prod_anti_set_of_le_one' (by simp [prob_le_one]))
/-
**MeasureTheory.Measure.infinitePi_pi_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：infinitePi_pi_univ [Countable ι] {t : (i : ι) -> Set (X i)} (mt : forall i
 : ι, MeasurableSet (t i)) : infinitePi μ (Set.univ.pi t) = ∏' i, μ i (t i)
参数：i : ι；X i；mt : forall i : ι, MeasurableSet (t i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.infinitePi_pi_of_countable`：infinitePi_pi_of_count
able {s : Set ι} (hs : Countable s) {t : (i : ι) -> Set (X i)} (mt : forall i in
 s, MeasurableSet (t i)) : infinitePi …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `tprod_univ`：tprod_univ (f : β -> α) : ∏' x : (Set.univ : Set β), f x = ∏
' x, f x
-/
lemma infinitePi_pi_univ [Countable ι] {t : (i : ι) → Set (X i)}
    (mt : ∀ i : ι, MeasurableSet (t i)) :
    infinitePi μ (Set.univ.pi t) = ∏' i, μ i (t i) := by
  rw [infinitePi_pi_of_countable, tprod_univ (f := fun i ↦ μ i (t i))]
  · simpa [Set.countable_univ_iff]
  · measurability

@[simp]
/-
**MeasureTheory.Measure.infinitePi_singleton** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：infinitePi_singleton [Countable ι] [forall i, MeasurableSingletonClass (X 
i)] (f : forall i, X i) : infinitePi μ {f} = ∏' i, μ i {f i}
参数：X i；f : forall i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_singleton`：univ_pi_singleton (f : forall i, α i) : (pi univ 
fun i => {f i}) = ({f} : Set (forall i, α i))
· 使用引理 `MeasureTheory.Measure.infinitePi_pi_univ`：infinitePi_pi_univ [Countable 
ι] {t : (i : ι) -> Set (X i)} (mt : forall i : ι, MeasurableSet (t i)) : infinit
ePi μ (Set.univ.pi t) = ∏' i, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma infinitePi_singleton [Countable ι] [∀ i, MeasurableSingletonClass (X i)]
    (f : ∀ i, X i) : infinitePi μ {f} = ∏' i, μ i {f i} := by
  rw [← Set.univ_pi_singleton, infinitePi_pi_univ _ (by measurability)]
/-
**MeasureTheory.Measure.infinitePi_singleton_of_fintype** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：infinitePi_singleton_of_fintype [Fintype ι] [forall i, MeasurableSingleton
Class (X i)] (f : forall i, X i) : infinitePi μ {f} = ∏ i, μ i {f i}
参数：X i；f : forall i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.infinitePi_singleton`：infinitePi_singleton [Counta
ble ι] [forall i, MeasurableSingletonClass (X i)] (f : forall i, X i) : infinite
Pi μ {f} = ∏' i, μ i {f i}
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `tprod_fintype`：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L
] b, f b = ∏ b, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma infinitePi_singleton_of_fintype [Fintype ι] [∀ i, MeasurableSingletonClass (X i)]
    (f : ∀ i, X i) : infinitePi μ {f} = ∏ i, μ i {f i} := by simp
/-
**MeasureTheory.Measure.infinitePi_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)}
 (f : (i : ι) → X i),   (MeasureTheory.Measure.infinitePi fun i => MeasureTheory
.Measure.dirac (f i)) = MeasureTheory.Measure.dirac f
参数：i : ι；X i；f : (i : ι) → X i；MeasureTheory.Measure.infinitePi fun i => Measure
Theory.Measure.dirac (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.eq_infinitePi`：eq_infinitePi {ν : Measure (Π i, X 
i)} (hν : forall s : Finset ι, forall t : (i : ι) -> Set (X i), (forall i, Measu
rableSet (t i)) -> ν (Set…
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.indicator_pi_one_apply`：∀ {ι : Type u_1} {M₀ : Type u_4} {α : ι → Ty
pe u_5} [inst : CommMonoidWithZero M₀] (s : Finset ι)   (t : (i : ι) → Set (α i)
) (f : (i : ι) →…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma infinitePi_dirac (f : ∀ i, X i) : infinitePi (fun i ↦ dirac (f i)) = dirac f :=
  .symm <| eq_infinitePi _ <| by simp +contextual [MeasurableSet.pi, Finset.countable_toSet]
/-
**MeasureTheory.Measure._root_.measurePreserving_eval_infinitePi** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.measurePreserving_eval_infinitePi (i : ι) :
    MeasurePreserving (Function.eval i) (infinitePi μ) (μ i) where
  measurable := by fun_prop
  map_eq := by
    ext s hs
    have : @Function.eval ι X i =
        (@Function.eval ({i} : Finset ι) (fun j ↦ X j) ⟨i, by simp⟩) ∘
        (Finset.restrict {i}) := by ext; simp
    rw [this, ← map_map, infinitePi_map_restrict, (measurePreserving_eval _ _).map_eq]
    all_goals fun_prop
/-
**MeasureTheory.Measure.infinitePi_map_eval** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：infinitePi_map_eval (i : ι) : (infinitePi μ).map (fun x => x i) = μ i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `measurePreserving_eval_infinitePi`：∀ {ι : Type u_1} {X : ι → Type u_2} {
mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → MeasureTheory.Measure (X i)
)   [hμ : ∀ (i : ι), Me…
-/
lemma infinitePi_map_eval (i : ι) :
    (infinitePi μ).map (fun x ↦ x i) = μ i :=
  (measurePreserving_eval_infinitePi μ i).map_eq
/-
**MeasureTheory.Measure.infinitePi_map_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：infinitePi_map_pi {Y : ι -> Type*} [forall i, MeasurableSpace (Y i)] {f : 
(i : ι) -> X i -> Y i} (hf : forall i, Measurable (f i)) : (infinitePi μ).map (f
un x i => f i (x i)) = infinitePi (fun i => (μ i).map (f i))
参数：Y i；i : ι；hf : forall i, Measurable (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.eq_infinitePi`：eq_infinitePi {ν : Measure (Π i, X 
i)} (hν : forall s : Finset ι, forall t : (i : ι) -> Set (X i), (forall i, Measu
rableSet (t i)) -> ν (Set…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `MeasureTheory.Measure.infinitePi_pi`：infinitePi_pi {s : Finset ι} {t : (
i : ι) -> Set (X i)} (mt : forall i in s, MeasurableSet (t i)) : infinitePi μ (S
et.pi s t) = ∏ i in s, μ …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
lemma infinitePi_map_pi {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)] {f : (i : ι) → X i → Y i}
    (hf : ∀ i, Measurable (f i)) :
    (infinitePi μ).map (fun x i ↦ f i (x i)) = infinitePi (fun i ↦ (μ i).map (f i)) := by
  have (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    isProbabilityMeasure_map (hf i).aemeasurable
  refine eq_infinitePi _ fun s t ht ↦ ?_
  rw [map_apply (by fun_prop) (.pi s.countable_toSet fun _ _ ↦ ht _)]
  have : (fun (x : Π i, X i) i ↦ f i (x i)) ⁻¹' ((s : Set ι).pi t) =
      (s : Set ι).pi (fun i ↦ (f i) ⁻¹' (t i)) := by ext x; simp
  rw [this, infinitePi_pi _ (fun i _ ↦ hf i (ht i))]
  congr! with i hi
  rw [map_apply (by fun_prop) (ht i)]

/-- If we push the product measure forward by a reindexing equivalence, we get a product measure
on the reindexed product. -/
/-
**MeasureTheory.Measure.infinitePi_map_piCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：infinitePi_map_piCongrLeft {α : Type*} (e : α ≃ ι) : (infinitePi (fun i =>
 μ (e i))).map (piCongrLeft X e) = infinitePi μ
参数：e : α ≃ ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.eq_infinitePi`：eq_infinitePi {ν : Measure (Π i, X 
i)} (hν : forall s : Finset ι, forall t : (i : ι) -> Set (X i), (forall i, Measu
rableSet (t i)) -> ν (Set…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.image_preimage`：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '
' e ⁻¹' s = s
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasurableEquiv.coe_piCongrLeft`：coe_piCongrLeft (f : δ ≃ δ') : ⇑(Measur
ableEquiv.piCongrLeft π f) = f.piCongrLeft π
· 使用定理 `Equiv.piCongrLeft_preimage_pi`：piCongrLeft_preimage_pi (f : ι' ≃ ι) (s :
 Set ι') (t : forall i, Set (α i)) : f.piCongrLeft α ⁻¹' (f '' s).pi t = s.pi fu
n i => t (f i)
· 使用引理 `MeasureTheory.Measure.infinitePi_pi`：infinitePi_pi {s : Finset ι} {t : (
i : ι) -> Set (X i)} (mt : forall i in s, MeasurableSet (t i)) : infinitePi μ (S
et.pi s t) = ∏ i in s, μ …
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If we push the product measure forward by a reindexing equivalence, we get a pro
duct measure
on the reindexed product.
-/
theorem infinitePi_map_piCongrLeft {α : Type*} (e : α ≃ ι) :
    (infinitePi (fun i ↦ μ (e i))).map (piCongrLeft X e) = infinitePi μ := by
  refine eq_infinitePi μ fun s t ht ↦ ?_
  conv_lhs => enter [2, 1]; rw [← e.image_preimage s, ← coe_preimage _ e.injective.injOn]
  rw [map_apply, coe_piCongrLeft, Equiv.piCongrLeft_preimage_pi, infinitePi_pi,
    prod_equiv e]
  · simp
  · simp
  · simp_all
  · fun_prop
  · exact .pi ((countable_toSet _).image e) (by simp_all)
/-
**MeasureTheory.Measure.infinitePi_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：infinitePi_eq_pi [Fintype ι] : infinitePi μ = Measure.pi μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用引理 `MeasureTheory.Measure.infinitePi_pi`：infinitePi_pi {s : Finset ι} {t : (
i : ι) -> Set (X i)} (mt : forall i in s, MeasurableSet (t i)) : infinitePi μ (S
et.pi s t) = ∏ i in s, μ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem infinitePi_eq_pi [Fintype ι] : infinitePi μ = Measure.pi μ := by
  refine (pi_eq fun s hs ↦ ?_).symm
  rw [← coe_univ, infinitePi_pi]
  simpa
/-
**MeasureTheory.Measure.infinitePi_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：infinitePi_cylinder {s : Finset ι} {S : Set (Π i : s, X i)} (mS : Measurab
leSet S) : infinitePi μ (cylinder s S) = Measure.pi (fun i : s => μ i) S
参数：Π i : s, X i；mS : MeasurableSet S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `MeasureTheory.Measure.infinitePi_map_restrict`：infinitePi_map_restrict {
I : Finset ι} : (Measure.infinitePi μ).map I.restrict = Measure.pi fun i : I => 
μ i
-/
lemma infinitePi_cylinder {s : Finset ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S) :
    infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply (measurable_restrict _) mS, infinitePi_map_restrict]

section curry

variable {ι : Type*} {κ : ι → Type*} {X : (i : ι) → κ i → Type*}
  {mX : ∀ i, ∀ j, MeasurableSpace (X i j)} (μ : (i : ι) → (j : κ i) → Measure (X i j))
  [hμ : ∀ i j, IsProbabilityMeasure (μ i j)]

/-
**MeasureTheory.Measure.infinitePi_map_piCurry_symm** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：infinitePi_map_piCurry_symm : (infinitePi fun i : ι => infinitePi fun j : 
κ i => μ i j).map (piCurry X).symm = infinitePi fun p : (i : ι) × κ i => μ p.1 p
.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.eq_infinitePi`：eq_infinitePi {ν : Measure (Π i, X 
i)} (hν : forall s : Finset ι, forall t : (i : ι) -> Set (X i), (forall i, Measu
rableSet (t i)) -> ν (Set…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sigma_image_fst_preimage_mk`：sigma_image_fst_preimage_mk {β : α -
> Type*} [DecidableEq α] (s : Finset (Σ a, β a)) : ((s.image Sigma.fst).sigma fu
n a => s.preimage (Sigma…
· 使用引理 `MeasurableEquiv.coe_piCurry_symm`：coe_piCurry_symm {ι : Type*} {κ : ι ->
 Type*} (X : (i : ι) -> κ i -> Type*) [forall i j, MeasurableSpace (X i j)] : ⇑(
piCurry X).symm = Sigm…
· 使用定理 `Finset.coe_sigma`：coe_sigma (s : Finset ι) (t : forall i, Finset (α i)) 
: (s.sigma t : Set (Σ i, α i)) = (s : Set ι).sigma fun i => (t i : Set (α i))
· 使用引理 `Set.uncurry_preimage_sigma_pi`：uncurry_preimage_sigma_pi {β : (i : ι) ->
 α i -> Type*} (s : Set ι) (t : (i : ι) -> Set (α i)) (u : (p : (i : ι) × α i) -
> Set (β p.1 p.2)) …
· 使用引理 `MeasureTheory.Measure.infinitePi_pi`：infinitePi_pi {s : Finset ι} {t : (
i : ι) -> Set (X i)} (mt : forall i in s, MeasurableSet (t i)) : infinitePi μ (S
et.pi s t) = ∏ i in s, μ …
· 使用定理 `MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi`：∀ {ι : T
ype u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) 
→ MeasureTheory.Measure (X i))   [hμ : ∀ (i : ι), Me…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
lemma infinitePi_map_piCurry_symm :
    (infinitePi fun i : ι ↦ infinitePi fun j : κ i ↦ μ i j).map (piCurry X).symm =
      infinitePi fun p : (i : ι) × κ i ↦ μ p.1 p.2 := by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop) (.pi (countable_toSet _) fun _ _ ↦ ht _),
    ← Finset.sigma_image_fst_preimage_mk s, coe_piCurry_symm, Finset.coe_sigma,
    Set.uncurry_preimage_sigma_pi, infinitePi_pi, Finset.prod_sigma]
  · exact Finset.prod_congr rfl (fun _ _ ↦ infinitePi_pi _ fun _ _ ↦ ht _)
  · simp only [mem_image, Sigma.exists, exists_and_right, exists_eq_right, forall_exists_index]
    exact fun i j hij ↦ MeasurableSet.pi (countable_toSet _) fun k hk ↦ by simp_all
/-
**MeasureTheory.Measure.infinitePi_map_piCurry** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：infinitePi_map_piCurry : (infinitePi fun p : (i : ι) × κ i => μ p.1 p.2).m
ap (piCurry X) = infinitePi fun i : ι => infinitePi fun j : κ i => μ i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq`：map_apply_eq_iff_map
_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ μ = ν.map e.symm
· 使用引理 `MeasureTheory.Measure.infinitePi_map_piCurry_symm`：infinitePi_map_piCurr
y_symm : (infinitePi fun i : ι => infinitePi fun j : κ i => μ i j).map (piCurry 
X).symm = infinitePi fun p : (i : ι) × …
-/
lemma infinitePi_map_piCurry :
    (infinitePi fun p : (i : ι) × κ i ↦ μ p.1 p.2).map (piCurry X) =
      infinitePi fun i : ι ↦ infinitePi fun j : κ i ↦ μ i j := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, infinitePi_map_piCurry_symm]

variable {ι κ X : Type*} {mX : MeasurableSpace X} (μ : ι → κ → Measure X)
  [hμ : ∀ i j, IsProbabilityMeasure (μ i j)]
/-
**MeasureTheory.Measure.infinitePi_map_curry_symm** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：infinitePi_map_curry_symm : (infinitePi fun i : ι => infinitePi fun j : κ 
=> μ i j).map (curry ι κ X).symm = infinitePi fun p : ι × κ => μ p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.piCongrLeft'_symm`：∀ {α : Sort u_1} {β : Sort u_4} (P : Sort u_9) 
(e : α ≃ β),   (Equiv.piCongrLeft' (fun x => P) e).symm = Equiv.piCongrLeft' (fu
n a => P) e.s…
· 使用定理 `MeasurableEquiv.mk.congr_simp`：∀ {α : Type u_6} {β : Type u_7} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] (toEquiv toEquiv_1 : α ≃ β)   (e_
toEquiv : toEquiv =…
· 使用定理 `Equiv.piCongrLeft'_apply`：∀ {α : Sort u_1} {β : Sort u_4} (P : α → Sort 
u_9) (e : α ≃ β) (f : (a : α) → P a) (x : β),   (Equiv.piCongrLeft' P e) f x = f
 (e.symm x)
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `MeasurableEquiv.curry_symm_apply`：∀ (ι : Type u_6) (κ : Type u_7) (X : T
ype u_8) [inst : MeasurableSpace X] (a : ι → κ → X) (a_1 : ι × κ),   (Measurable
Equiv.curry ι κ X).sym…
· 使用定理 `MeasurableEquiv.piCurry_symm_apply`：∀ {ι : Type u_6} {κ : ι → Type u_7} 
(X : (i : ι) → κ i → Type u_8)   [inst : (i : ι) → (j : κ i) → MeasurableSpace (
X i j)] (f : (x : ι) → (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.Measure.infinitePi_map_piCurry_symm`：infinitePi_map_piCurr
y_symm : (infinitePi fun i : ι => infinitePi fun j : κ i => μ i j).map (piCurry 
X).symm = infinitePi fun p : (i : ι) × …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.Measure.infinitePi_map_piCongrLeft`：infinitePi_map_piCongr
Left {α : Type*} (e : α ≃ ι) : (infinitePi (fun i => μ (e i))).map (piCongrLeft 
X e) = infinitePi μ
-/
lemma infinitePi_map_curry_symm :
    (infinitePi fun i : ι ↦ infinitePi fun j : κ ↦ μ i j).map (curry ι κ X).symm =
      infinitePi fun p : ι × κ ↦ μ p.1 p.2 := by
  rw [← (MeasurableEquiv.piCongrLeft (fun _ ↦ X)
    (Equiv.sigmaEquivProd ι κ).symm).map_measurableEquiv_injective.eq_iff, map_map]
  · have : (MeasurableEquiv.piCongrLeft (fun _ ↦ X) (Equiv.sigmaEquivProd ι κ).symm) ∘
        (MeasurableEquiv.curry ι κ X).symm = ⇑(MeasurableEquiv.piCurry (fun _ _ ↦ X)).symm := by
      ext; simp [piCongrLeft, Equiv.piCongrLeft, Sigma.uncurry]
    rw [this, infinitePi_map_piCurry_symm]
    convert! infinitePi_map_piCongrLeft (fun p ↦ μ p.1 p.2) (Equiv.sigmaEquivProd ι κ).symm |>.symm
  all_goals fun_prop
/-
**MeasureTheory.Measure.infinitePi_map_curry** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：infinitePi_map_curry : (infinitePi fun p : ι × κ => μ p.1 p.2).map (curry 
ι κ X) = infinitePi fun i : ι => infinitePi fun j : κ => μ i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq`：map_apply_eq_iff_map
_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ μ = ν.map e.symm
· 使用引理 `MeasureTheory.Measure.infinitePi_map_curry_symm`：infinitePi_map_curry_sy
mm : (infinitePi fun i : ι => infinitePi fun j : κ => μ i j).map (curry ι κ X).s
ymm = infinitePi fun p : ι × κ => μ p…
-/
lemma infinitePi_map_curry :
    (infinitePi fun p : ι × κ ↦ μ p.1 p.2).map (curry ι κ X) =
      infinitePi fun i : ι ↦ infinitePi fun j : κ ↦ μ i j := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, infinitePi_map_curry_symm]

end curry

end Measure

section Integral

/-
**MeasureTheory.integral_restrict_infinitePi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_restrict_infinitePi {E : Type*} [NormedAddCommGroup E] [NormedSpa
ce Real E] {s : Finset ι} {f : (Π i : s, X i) -> E} (hf : AEStronglyMeasurable f
 (Measure.pi (fun i : s => μ i))) : ∫ y, f (s.restrict y) ∂infinitePi μ = ∫ y, f
 y ∂Measure.pi (fun i : s => μ i)
参数：Π i : s, X i；hf : AEStronglyMeasurable f (Measure.pi (fun i : s => μ i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `MeasureTheory.Measure.infinitePi_map_restrict`：infinitePi_map_restrict {
I : Finset ι} : (Measure.infinitePi μ).map I.restrict = Measure.pi fun i : I => 
μ i
-/
theorem integral_restrict_infinitePi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : (Π i : s, X i) → E}
    (hf : AEStronglyMeasurable f (Measure.pi (fun i : s ↦ μ i))) :
    ∫ y, f (s.restrict y) ∂infinitePi μ = ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← integral_map, infinitePi_map_restrict]
  · fun_prop
  · rwa [infinitePi_map_restrict]
/-
**MeasureTheory.lintegral_restrict_infinitePi** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：lintegral_restrict_infinitePi {s : Finset ι} {f : (Π i : s, X i) -> Real>=
0∞} (hf : Measurable f) : ∫⁻ y, f (s.restrict y) ∂infinitePi μ = ∫⁻ y, f y ∂Meas
ure.pi (fun i : s => μ i)
参数：Π i : s, X i；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `MeasureTheory.Measure.isProjectiveLimit_infinitePi`：isProjectiveLimit_in
finitePi : IsProjectiveLimit (infinitePi μ) (fun I : Finset ι => (Measure.pi (fu
n i : I => μ i)))
-/
theorem lintegral_restrict_infinitePi {s : Finset ι}
    {f : (Π i : s, X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f (s.restrict y) ∂infinitePi μ = ∫⁻ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf (measurable_restrict _), isProjectiveLimit_infinitePi μ]

open Filtration
/-
**MeasureTheory.integral_infinitePi_of_piFinset** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：integral_infinitePi_of_piFinset [DecidableEq ι] {E : Type*} [NormedAddComm
Group E] [NormedSpace Real E] {s : Finset ι} {f : (Π i, X i) -> E} (mf : Strongl
yMeasurable[piFinset s] f) (x : Π i, X i) : ∫ y, f y ∂infinitePi μ = ∫ y, f (Fun
ction.updateFinset x s y) ∂Measure.pi (fun i : s => μ i)
参数：Π i, X i；mf : StronglyMeasurable[piFinset s] f；x : Π i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.dependsOn_of_piFinset`：∀ {Z : Type u_3}
 {ι : Type u_4} {X : ι → Type u_5} [inst : (i : ι) → MeasurableSpace (X i)] {f :
 ((i : ι) → X i) → Z}   {s : Finset ι} [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_restrict_infinitePi`：integral_restrict_infinitePi
 {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {s : Finset ι} {f : (Π 
i : s, X i) -> E} (hf : AEStrong…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem integral_infinitePi_of_piFinset [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : (Π i, X i) → E}
    (mf : StronglyMeasurable[piFinset s] f) (x : Π i, X i) :
    ∫ y, f y ∂infinitePi μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := by
  let g : (Π i : s, X i) → E := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi ↦ by simp_all [Function.updateFinset]
  rw [← integral_congr_ae <| ae_of_all _ this, integral_restrict_infinitePi]
  exact mf.comp_measurable (measurable_updateFinset.mono le_rfl (piFinset.le s))
    |>.aestronglyMeasurable
/-
**MeasureTheory.lintegral_infinitePi_of_piFinset** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：lintegral_infinitePi_of_piFinset [DecidableEq ι] {s : Finset ι} {f : (Π i,
 X i) -> Real>=0∞} (mf : Measurable[piFinset s] f) (x : Π i, X i) : ∫⁻ y, f y ∂i
nfinitePi μ = (∫⋯∫⁻_s, f ∂μ) x
参数：Π i, X i；mf : Measurable[piFinset s] f；x : Π i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.dependsOn_of_piFinset`：∀ {Z : Type u_3} {ι : Type u_4} {X : ι
 → Type u_5} [inst : (i : ι) → MeasurableSpace (X i)] {f : ((i : ι) → X i) → Z} 
  {s : Finset ι} [inst…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_restrict_infinitePi`：lintegral_restrict_infinite
Pi {s : Finset ι} {f : (Π i : s, X i) -> Real>=0∞} (hf : Measurable f) : ∫⁻ y, f
 (s.restrict y) ∂infinitePi μ = ∫…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem lintegral_infinitePi_of_piFinset [DecidableEq ι] {s : Finset ι}
    {f : (Π i, X i) → ℝ≥0∞} (mf : Measurable[piFinset s] f)
    (x : Π i, X i) : ∫⁻ y, f y ∂infinitePi μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : (Π i : s, X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi ↦ by simp_all [Function.updateFinset]
  rw [← lintegral_congr_ae <| ae_of_all _ this, lintegral_restrict_infinitePi]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono le_rfl (piFinset.le s))

end Integral

end InfinitePi

end MeasureTheory

