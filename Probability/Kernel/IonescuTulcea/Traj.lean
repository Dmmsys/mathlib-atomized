/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
public import Mathlib.Probability.Kernel.SetIntegral

/-!
# Ionescu-Tulcea theorem

This file proves the *Ionescu-Tulcea theorem*. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` will take the trajectory up to time `a` as input and outputs
the distribution of the trajectory on `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem tells us that these compositions can be extended into a
`Kernel (Π i : Iic a, X i) (Π n > a, X n)` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

In this file we construct this "limit" kernel given the family `κ`. More precisely, for any `a : ℕ`,
we construct the kernel `traj κ a : Kernel (Π i : Iic a, X i) (Π n, X n)`, which takes as input
the trajectory in `X 0 × ... × X a` and outputs the distribution of the whole trajectory. The name
`traj` thus stands for "trajectory". We build a kernel with output in `Π n, X n` instead of
`Π i > a, X i` to make manipulations easier. The first coordinates are deterministic.

We also provide tools to compute integrals against `traj κ a` and an expression for the conditional
expectation.

## Main definitions

* `traj κ a`: a kernel from `Π i : Iic a, X i` to `Π n, X n` which takes as input a trajectory
  up to time `a` and outputs the distribution of the trajectory obtained by iterating the kernels
  `κ`. Its existence is given by the Ionescu-Tulcea theorem.
* `trajMeasure μ₀ κ`: a measure on `Π n, X n` that corresponds to the distribution of the trajectory
  obtained by starting with the distribution `μ₀` and then iterating the kernels `κ`.

## Main statements

* `map_traj_succ_self`: the pushforward of `traj κ a` along the the point at time `a + 1` is the
  kernel `κ a`.
* `eq_traj`: Uniqueness of `traj`: to check that `η = traj κ a` it is enough to show that
  the restriction of `η` to variables `≤ b` is `partialTraj κ a b`.
* `traj_comp_partialTraj`: Given the distribution up to time `a`, `partialTraj κ a b`
  gives the distribution of the trajectory up to time `b`, and composing this with
  `traj κ b` gives the distribution of the whole trajectory.
* `condExp_traj`: If `a ≤ b`, the conditional expectation of `f` with respect to `traj κ a`
  given the information up to time `b` is obtained by integrating `f` against `traj κ b`.
* `condDistrib_trajMeasure`: a regular conditional probability distribution of the point at time
  `a + 1` given the trajectory up to time `a` corresponds to the kernel `κ a`.


## Implementation notes

The kernel `traj κ a` is built using the Carathéodory extension theorem. First we build a projective
family of measures using `inducedFamily` and `partialTraj κ a`. Then we build a
`MeasureTheory.AddContent` on `MeasureTheory.measurableCylinders` called `trajContent` using
`projectiveFamilyContent`. Finally we prove `trajContent_tendsto_zero` which implies the
`σ`-additivity of the content, allowing to turn it into a measure.

## References

We follow the proof of Theorem 8.24 in
[O. Kallenberg, *Foundations of Modern Probability*][kallenberg2021]. For a more detailed proof
in the case of constant kernels (i.e. measures),
see Proposition 10.6.1 in [D. L. Cohn, *Measure Theory*][cohn2013measure].

## Tags

Ionescu-Tulcea theorem
-/

@[expose] public section

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal Topology

variable {X : ℕ → Type*}

section castLemmas

/-
**Iic_pi_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Iic_pi_eq {a b : ℕ} (h : a = b) :
    (Π i : Iic a, X i) = (Π i : Iic b, X i) := by cases h; rfl
/-
**cast_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma cast_pi {s t : Set ℕ} (h : s = t) (x : (i : s) → X i) (i : t) :
    cast (congrArg (fun u : Set ℕ ↦ (Π i : u, X i)) h) x i = x ⟨i.1, h.symm ▸ i.2⟩ := by
  cases h; rfl

variable [∀ n, MeasurableSpace (X n)]
/-
**measure_cast** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure (Π i : Iic n, X i)) :
    (μ a).map (cast (Iic_pi_eq h)) = μ b := by
  cases h
  exact Measure.map_id
/-
**heq_measurableSpace_Iic_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma heq_measurableSpace_Iic_pi {a b : ℕ} (h : a = b) :
    (inferInstance : MeasurableSpace (Π i : Iic a, X i)) ≍
      (inferInstance : MeasurableSpace (Π i : Iic b, X i)) := by cases h; rfl

end castLemmas

section iterateInduction

/-- This function takes as input a tuple `(x_₀, ..., x_ₐ)` and `ind` a function which
given `(y_₀, ...,y_ₙ)` outputs `x_{n+1} : X (n + 1)`, and it builds an element of `Π n, X n`
by starting with `(x_₀, ..., x_ₐ)` and then iterating `ind`. -/
/-
**iterateInduction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{X : ℕ → Type u_1} →   {a : ℕ} → ((i : ↥(Finset.Iic a)) → X ↑i) → ((n : ℕ)
 → ((i : ↥(Finset.Iic n)) → X ↑i) → X (n + 1)) → (n : ℕ) → X n
参数：(i : ↥(Finset.Iic a)) → X ↑i；(n : ℕ) → ((i : ↥(Finset.Iic n)) → X ↑i) → X (n 
+ 1)；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This function takes as input a tuple `(x_₀, ..., x_ₐ)` and `ind` a function whic
h
given `(y_₀, ...,y_ₙ)` outputs `x_{n+1} : X (n + 1)`, and it builds an element o
f `Π n, X n`
by starting with `(x_₀, ..., x_ₐ)` and then iterating `ind`.
-/
def iterateInduction {a : ℕ} (x : Π i : Iic a, X i)
    (ind : (n : ℕ) → (Π i : Iic n, X i) → X (n + 1)) : Π n, X n
  | 0 => x ⟨0, mem_Iic.2 zero_le⟩
  | k + 1 => if h : k + 1 ≤ a
      then x ⟨k + 1, mem_Iic.2 h⟩
      else ind k (fun i ↦ iterateInduction x ind i)
  decreasing_by exact Nat.lt_succ_of_le (mem_Iic.1 i.2)
/-
**frestrictLe_iterateInduction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：frestrictLe_iterateInduction {a : Nat} (x : Π i : Iic a, X i) (ind : (n : 
Nat) -> (Π i : Iic n, X i) -> X (n + 1)) : frestrictLe a (iterateInduction x ind
) = x
参数：x : Π i : Iic a, X i；ind : (n : Nat) -> (Π i : Iic n, X i) -> X (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iterateInduction.eq_1`：∀ {X : ℕ → Type u_1} {a : ℕ} (x : (i : ↥(Finset.I
ic a)) → X ↑i)   (ind : (n : ℕ) → ((i : ↥(Finset.Iic n)) → X ↑i) → X (n + 1)), i
terateInduc…
· 使用定理 `iterateInduction.eq_2`：∀ {X : ℕ → Type u_1} {a : ℕ} (x : (i : ↥(Finset.I
ic a)) → X ↑i)   (ind : (n : ℕ) → ((i : ↥(Finset.Iic n)) → X ↑i) → X (n + 1)) (k
 : ℕ),   it…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma frestrictLe_iterateInduction {a : ℕ} (x : Π i : Iic a, X i)
    (ind : (n : ℕ) → (Π i : Iic n, X i) → X (n + 1)) :
    frestrictLe a (iterateInduction x ind) = x := by
  ext i
  simp only [frestrictLe_apply]
  obtain ⟨(zero | j), hj⟩ := i <;> rw [iterateInduction]
  rw [dif_pos (mem_Iic.1 hj)]

end iterateInduction

variable [∀ n, MeasurableSpace (X n)]

section ProjectiveFamily

namespace MeasureTheory

/-! ### Projective families indexed by `Finset ℕ` -/

variable {μ : (n : ℕ) → Measure (Π i : Iic n, X i)}

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`, where `n` is larger than
a given integer. -/
/-
**MeasureTheory.isProjectiveLimit_nat_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：isProjectiveLimit_nat_iff' {μ : (I : Finset Nat) -> Measure (Π i : I, X i)
} (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) (a : Nat) : IsProj
ectiveLimit ν μ ↔ forall ⦃n⦄, a <= n -> ν.map (frestrictLe n) = μ (Iic n)
参数：I : Finset Nat；Π i : I, X i；hμ : IsProjectiveMeasureFamily μ；ν : Measure (Π n
, X n)；a : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finset.subset_Iic_sup_id`：subset_Iic_sup_id [OrderBot α] (s : Finset α) 
: s subseteq Iic (s.sup id)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
To check that a measure `ν` is the projective limit of a projective family of me
asures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`, where `n`
 is larger than
a given integer.
-/
theorem isProjectiveLimit_nat_iff' {μ : (I : Finset ℕ) → Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) (a : ℕ) :
    IsProjectiveLimit ν μ ↔ ∀ ⦃n⦄, a ≤ n → ν.map (frestrictLe n) = μ (Iic n) := by
  refine ⟨fun h n _ ↦ h (Iic n), fun h I ↦ ?_⟩
  have := (I.subset_Iic_sup_id.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))
  rw [← restrict₂_comp_restrict this, ← Measure.map_map, ← frestrictLe, h (le_max_right _ _), ← hμ]
  all_goals fun_prop

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`. -/
/-
**MeasureTheory.isProjectiveLimit_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：isProjectiveLimit_nat_iff {μ : (I : Finset Nat) -> Measure (Π i : I, X i)}
 (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) : IsProjectiveLimit
 ν μ ↔ forall n, ν.map (frestrictLe n) = μ (Iic n)
参数：I : Finset Nat；Π i : I, X i；hμ : IsProjectiveMeasureFamily μ；ν : Measure (Π n
, X n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.isProjectiveLimit_nat_iff'`：isProjectiveLimit_nat_iff' {μ 
: (I : Finset Nat) -> Measure (Π i : I, X i)} (hμ : IsProjectiveMeasureFamily μ)
 (ν : Measure (Π n, X n)) (a :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
To check that a measure `ν` is the projective limit of a projective family of me
asures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`.
-/
theorem isProjectiveLimit_nat_iff {μ : (I : Finset ℕ) → Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) :
    IsProjectiveLimit ν μ ↔ ∀ n, ν.map (frestrictLe n) = μ (Iic n) := by
  rw [isProjectiveLimit_nat_iff' hμ _ 0]
  simp

variable (μ : (n : ℕ) → Measure (Π i : Iic n, X i))

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, we can define a family
of measures indexed by `Finset ℕ` by projecting the measures. -/
/-
**MeasureTheory.inducedFamily** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：inducedFamily (S : Finset Nat) : Measure ((k : S) -> X k)
参数：S : Finset Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, we can de
fine a family
of measures indexed by `Finset ℕ` by projecting the measures.
-/
noncomputable def inducedFamily (S : Finset ℕ) : Measure ((k : S) → X k) :=
    (μ (S.sup id)).map (restrict₂ S.subset_Iic_sup_id)
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ n, SFinite (μ n)] (I : Finset ℕ) :
    SFinite (inducedFamily μ I) := by rw [inducedFamily]; infer_instance
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ n, IsFiniteMeasure (μ n)] (I : Finset ℕ) :
    IsFiniteMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ n, IsZeroOrProbabilityMeasure (μ n)] (I : Finset ℕ) :
    IsZeroOrProbabilityMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ n, IsProbabilityMeasure (μ n)] (I : Finset ℕ) :
    IsProbabilityMeasure (inducedFamily μ I) := by
  rw [inducedFamily]
  exact Measure.isProbabilityMeasure_map (measurable_restrict₂ _).aemeasurable

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induced family
equals `μ` over the intervals `Iic n`. -/
/-
**MeasureTheory.inducedFamily_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：inducedFamily_Iic (n : Nat) : inducedFamily μ (Iic n) = μ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.inducedFamily.eq_1`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) →
 MeasurableSpace (X n)]   (μ : (n : ℕ) → MeasureTheory.Measure ((i : ↥(Finset.Ii
c n)) → X ↑i)) (S : Fi…
· 使用定理 `_private.Mathlib.Probability.Kernel.IonescuTulcea.Traj.0.Iic_pi_eq`：∀ {X
 : ℕ → Type u_1} {a b : ℕ}, a = b → ((i : ↥(Finset.Iic a)) → X ↑i) = ((i : ↥(Fin
set.Iic b)) → X ↑i)
· 使用定理 `Finset.sup_Iic`：∀ {α : Type u_2} [inst : SemilatticeSup α] [inst_1 : Loc
allyFiniteOrderBot α] [inst_2 : OrderBot α] (a : α),   (Finset.Iic a).sup id = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Probability.Kernel.IonescuTulcea.Traj.0.measure_cast`：∀
 {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)] {a b : ℕ} (h : a = 
b)   (μ : (n : ℕ) → MeasureTheory.Measure ((i : ↥(Finset.Ii…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.restrict₂.eq_1`：∀ {ι : Type u_2} {π : ι → Type u_3} {s t : Finset
 ι} (hst : s ⊆ t) (f : (i : ↥t) → π ↑i) (i : ↥s),   Finset.restrict₂ hst f i = f
 ⟨↑i, ⋯⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `_private.Mathlib.Probability.Kernel.IonescuTulcea.Traj.0.cast_pi`：∀ {X :
 ℕ → Type u_1} {s t : Set ℕ} (h : s = t) (x : (i : ↑s) → X ↑i) (i : ↑t), cast ⋯ 
x i = x ⟨↑i, ⋯⟩

--- 原说明 ---
Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induc
ed family
equals `μ` over the intervals `Iic n`.
-/
theorem inducedFamily_Iic (n : ℕ) : inducedFamily μ (Iic n) = μ n := by
  rw [inducedFamily, ← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [restrict₂, cast_pi (by rw [sup_Iic n])]

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induced family
will be projective only if `μ` is projective, in the sense that if `a ≤ b`, then projecting
`μ b` gives `μ a`. -/
/-
**MeasureTheory.isProjectiveMeasureFamily_inducedFamily** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：isProjectiveMeasureFamily_inducedFamily (h : forall a b : Nat, forall hab 
: a <= b, (μ b).map (frestrictLe₂ hab) = μ a) : IsProjectiveMeasureFamily (induc
edFamily μ)
参数：h : forall a b : Nat, forall hab : a <= b, (μ b).map (frestrictLe₂ hab) = μ a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.restrict₂_comp_restrict₂`：restrict₂_comp_restrict₂ (hst : s subse
teq t) (htu : t subseteq u) : (restrict₂ (π
· 使用引理 `Finset.subset_Iic_sup_id`：subset_Iic_sup_id [OrderBot α] (s : Finset α) 
: s subseteq Iic (s.sup id)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Preorder.frestrictLe₂.eq_def`：∀ {α : Type u_1} [inst : Preorder α] {π : 
α → Type u_2} [inst_1 : LocallyFiniteOrderBot α] {a b : α} (hab : a ≤ b),   Preo
rder.frestrictLe₂ …

--- 原说明 ---
Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induc
ed family
will be projective only if `μ` is projective, in the sense that if `a ≤ b`, then
 projecting
`μ b` gives `μ a`.
-/
theorem isProjectiveMeasureFamily_inducedFamily
    (h : ∀ a b : ℕ, ∀ hab : a ≤ b, (μ b).map (frestrictLe₂ hab) = μ a) :
    IsProjectiveMeasureFamily (inducedFamily μ) := by
  intro I J hJI
  have sls : J.sup id ≤ I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map, restrict₂_comp_restrict₂,
    ← restrict₂_comp_restrict₂ J.subset_Iic_sup_id (Iic_subset_Iic.2 sls), ← Measure.map_map,
    ← frestrictLe₂.eq_def sls, h (J.sup id) (I.sup id) sls]
  all_goals fun_prop

end MeasureTheory

end ProjectiveFamily

variable {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]

namespace ProbabilityTheory.Kernel

section definition

/-! ### Definition and basic properties of `traj` -/

variable (κ)

/-
**ProbabilityTheory.Kernel.isProjectiveMeasureFamily_partialTraj** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isProjectiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) : 
IsProjectiveMeasureFamily (inducedFamily (fun b => partialTraj κ a b x₀))
参数：x₀ : Π i : Iic a, X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isProjectiveMeasureFamily_inducedFamily`：isProjectiveMeasu
reFamily_inducedFamily (h : forall a b : Nat, forall hab : a <= b, (μ b).map (fr
estrictLe₂ hab) = μ a) : IsProjectiveMeasur…
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_map_frestrictLe₂_apply`：partialTraj
_map_frestrictLe₂_apply (x₀ : Π i : Iic a, X i) (hbc : b <= c) : (partialTraj κ 
a c x₀).map (frestrictLe₂ hbc) = partialTraj κ a …
-/
lemma isProjectiveMeasureFamily_partialTraj {a : ℕ} (x₀ : Π i : Iic a, X i) :
    IsProjectiveMeasureFamily (inducedFamily (fun b ↦ partialTraj κ a b x₀)) :=
  isProjectiveMeasureFamily_inducedFamily _
    (fun _ _ ↦ partialTraj_map_frestrictLe₂_apply (κ := κ) x₀)

/-- Given a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`, and the
trajectory up to time `a` we can construct an additive content over cylinders. It corresponds
to composing the kernels, starting at time `a + 1`. -/
/-
**ProbabilityTheory.Kernel.trajContent** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：trajContent {a : Nat} (x₀ : Π i : Iic a, X i) : AddContent Real>=0∞ (measu
rableCylinders X)
参数：x₀ : Π i : Iic a, X i。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.isProjectiveMeasureFamily_partialTraj`：isProjec
tiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) : IsProjectiveMe
asureFamily (inducedFamily (fun b => partialTraj κ a…

--- 原说明 ---
Given a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`,
 and the
trajectory up to time `a` we can construct an additive content over cylinders. I
t corresponds
to composing the kernels, starting at time `a + 1`.
-/
noncomputable def trajContent {a : ℕ} (x₀ : Π i : Iic a, X i) :
    AddContent ℝ≥0∞ (measurableCylinders X) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_partialTraj κ x₀)

variable {κ}

/-- The `trajContent κ x₀` of a cylinder indexed by first coordinates is given by `partialTraj`. -/
/-
**ProbabilityTheory.Kernel.trajContent_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：trajContent_cylinder {a b : Nat} {S : Set (Π i : Iic b, X i)} (mS : Measur
ableSet S) (x₀ : Π i : Iic a, X i) : trajContent κ x₀ (cylinder (Iic b) S) = par
tialTraj κ a b x₀ S
参数：Π i : Iic b, X i；mS : MeasurableSet S；x₀ : Π i : Iic a, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.isProjectiveMeasureFamily_partialTraj`：isProjec
tiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) : IsProjectiveMe
asureFamily (inducedFamily (fun b => partialTraj κ a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.trajContent.eq_1`：∀ {X : ℕ → Type u_1} [inst : 
(n : ℕ) → MeasurableSpace (X n)]   (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i :
 ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用引理 `MeasureTheory.projectiveFamilyContent_cylinder`：projectiveFamilyContent_
cylinder (hP : IsProjectiveMeasureFamily P) (hS : MeasurableSet S) : projectiveF
amilyContent hP (cylinder I S) = P I…
· 使用定理 `MeasureTheory.inducedFamily_Iic`：inducedFamily_Iic (n : Nat) : inducedFa
mily μ (Iic n) = μ n

--- 原说明 ---
The `trajContent κ x₀` of a cylinder indexed by first coordinates is given by `p
artialTraj`.
-/
theorem trajContent_cylinder {a b : ℕ} {S : Set (Π i : Iic b, X i)} (mS : MeasurableSet S)
    (x₀ : Π i : Iic a, X i) :
    trajContent κ x₀ (cylinder (Iic b) S) = partialTraj κ a b x₀ S := by
  rw [trajContent, projectiveFamilyContent_cylinder _ mS, inducedFamily_Iic]

/-- The `trajContent` of a cylinder is equal to the integral of its indicator function against
`partialTraj`. -/
/-
**ProbabilityTheory.Kernel.trajContent_eq_lmarginalPartialTraj** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：trajContent_eq_lmarginalPartialTraj {b : Nat} {S : Set (Π i : Iic b, X i)}
 (mS : MeasurableSet S) (x₀ : Π n, X n) (a : Nat) : trajContent κ (frestrictLe a
 x₀) (cylinder (Iic b) S) = lmarginalPartialTraj κ a b ((cylinder (Iic b) S).ind
icator 1) x₀
参数：Π i : Iic b, X i；mS : MeasurableSet S；x₀ : Π n, X n；a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.trajContent_cylinder`：trajContent_cylinder {a b
 : Nat} {S : Set (Π i : Iic b, X i)} (mS : MeasurableSet S) (x₀ : Π i : Iic a, X
 i) : trajContent κ x₀ (cylinder (I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
· 使用定理 `ProbabilityTheory.Kernel.lmarginalPartialTraj.eq_1`：∀ {X : ℕ → Type u_1}
 {mX : (n : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kerne
l ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_const_eq_indicator_const`：∀ {α : Type u_1} {β : Type u_2} 
{M : Type u_3} [inst : Zero M] {s : Set α} {a : α} {t : Set β} {b : β} {c : M}, 
  (a ∈ s ↔ b ∈ t) → s.indica…
· 使用定理 `MeasureTheory.mem_cylinder`：mem_cylinder (s : Finset ι) (S : Set (forall
 i : s, α i)) (f : forall i, α i) : f in cylinder s S ↔ s.restrict f in S
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `trajContent` of a cylinder is equal to the integral of its indicator functi
on against
`partialTraj`.
-/
theorem trajContent_eq_lmarginalPartialTraj {b : ℕ} {S : Set (Π i : Iic b, X i)}
    (mS : MeasurableSet S) (x₀ : Π n, X n) (a : ℕ) :
    trajContent κ (frestrictLe a x₀) (cylinder (Iic b) S) =
      lmarginalPartialTraj κ a b ((cylinder (Iic b) S).indicator 1) x₀ := by
  rw [trajContent_cylinder mS, ← lintegral_indicator_one mS, lmarginalPartialTraj]
  congr with x
  apply Set.indicator_const_eq_indicator_const
  rw [mem_cylinder]
  congrm (fun i ↦ ?_) ∈ S
  simp [updateFinset, i.2]
/-
**ProbabilityTheory.Kernel.trajContent_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：trajContent_ne_top {a : Nat} {x : Π i : Iic a, X i} {s : Set (Π n, X n)} :
 trajContent κ x s != ∞
参数：Π n, X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.projectiveFamilyContent_ne_top`：projectiveFamilyContent_ne
_top [forall J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) : proj
ectiveFamilyContent hP s != ∞
· 使用定理 `MeasureTheory.instIsFiniteMeasureForallValNatMemFinsetInducedFamilyOfFor
allIic`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   (μ : (n 
: ℕ) → MeasureTheory.Measure ((i : ↥(Finset.Iic n)) → X ↑i)) [∀ (n :…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelForallValNatMemFinsetIicParti
alTrajOfHAddOfNat`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}  
 {κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.isProjectiveMeasureFamily_partialTraj`：isProjec
tiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) : IsProjectiveMe
asureFamily (inducedFamily (fun b => partialTraj κ a…
-/
lemma trajContent_ne_top {a : ℕ} {x : Π i : Iic a, X i} {s : Set (Π n, X n)} :
    trajContent κ x s ≠ ∞ :=
  projectiveFamilyContent_ne_top (isProjectiveMeasureFamily_partialTraj κ x)

/-- This is an auxiliary result for `trajContent_tendsto_zero`. Consider `f` a sequence of bounded
measurable functions such that `f n` depends only on the first coordinates up to `a n`.
Assume that when integrating `f n` against `partialTraj (k + 1) (a n)`, one gets a non-increasing
sequence of functions which converges to `l`.
Assume then that there exists `ε` and `y : Π i : Iic k, X i` such that
when integrating `f n` against `partialTraj k (a n) y`, you get something at least
`ε` for all `n`. Then there exists `z` such that this remains true when integrating
`f` against `partialTraj (k + 1) (a n) (update y (k + 1) z)`. -/
/-
**ProbabilityTheory.Kernel.le_lmarginalPartialTraj_succ** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：le_lmarginalPartialTraj_succ {f : Nat -> (Π n, X n) -> Real>=0∞} {a : Nat 
-> Nat} (hcte : forall n, DependsOn (f n) (Iic (a n))) (mf : forall n, Measurabl
e (f n)) {bound : Real>=0∞} (fin_bound : bound != ∞) (le_bound : forall n x, f n
 x <= bound) {k : Nat} (anti : forall x, Antitone (fun n => lmarginalPartialTraj
 κ (k + 1) (a n) (f n) x)) {l : (Π n, X n) -> Real>=0∞} (htendsto : forall x, Te
ndsto (fun n => lmarginalPartialTraj κ (k + 1) (a n) (f n) x) atTop (𝓝 (l x))) (
ε : Real>=0∞) (y : Π i : I
参数：Π n, X n；hcte : forall n, DependsOn (f n) (Iic (a n))；mf : forall n, Measurab
le (f n)；fin_bound : bound != ∞；le_bound : forall n x, f n x <= bound；anti : for
all x, Antitone (fun n => lmarginalPartialTraj κ (k + 1) (a n) (f n) x)；Π n, X n
；htendsto : forall x, Tendsto (fun n => lmarginalPartialTraj κ (k + 1) (a n) (f 
n) x) atTop (𝓝 (l x))；ε : Real>=0∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.nonempty_of_isProbabilityMeasure`：nonempty_of_isProbabilit
yMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.lmarginalPartialTraj_self`：lmarginalPartialTraj
_self (hab : a <= b) (hbc : b <= c) {f : (Π n, X n) -> Real>=0∞} (hf : Measurabl
e f) : lmarginalPartialTraj κ a b (lmarg…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ProbabilityTheory.Kernel.lmarginalPartialTraj_le`：lmarginalPartialTraj_l
e (hba : b <= a) {f : (Π n, X n) -> Real>=0∞} (mf : Measurable f) : lmarginalPar
tialTraj κ a b f = f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `DependsOn.lmarginalPartialTraj_of_le`：lmarginalPartialTraj_of_le [forall
 n, IsMarkovKernel (κ n)] (c : Nat) {f : (Π n, X n) -> Real>=0∞} (mf : Measurabl
e f) (hf : DependsOn f (Ii…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.lmarginalPartialTraj.eq_1`：∀ {X : ℕ → Type u_1}
 {mX : (n : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kerne
l ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用引理 `MeasureTheory.lintegral_le_const`：lintegral_le_const [IsProbabilityMeasu
re μ] {f : α -> Real>=0∞} {c : Real>=0∞} (hf : forallᵐ x ∂μ, f x <= c) : ∫⁻ x, f
 x ∂μ <= c
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicParti
alTrajOfHAddOfNat`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}  
 {κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.tendsto_lintegral_of_dominated_convergence`：tendsto_linteg
ral_of_dominated_convergence {F : Nat -> α -> Real>=0∞} {f : α -> Real>=0∞} (bou
nd : α -> Real>=0∞) (hF_meas : forall n, Measu…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `ProbabilityTheory.Kernel.measurable_lmarginalPartialTraj`：measurable_lma
rginalPartialTraj (a b : Nat) {f : (Π n, X n) -> Real>=0∞} (hf : Measurable f) :
 Measurable (lmarginalPartialTraj κ a b f)
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
This is an auxiliary result for `trajContent_tendsto_zero`. Consider `f` a seque
nce of bounded
measurable functions such that `f n` depends only on the first coordinates up to
 `a n`.
Assume that when integrating `f n` against `partialTraj (k + 1) (a n)`, one gets
 a non-increasing
sequence of functions which converges to `l`.
Assume then that there exists `ε` and `y : Π i : Iic k, X i` such that
when integrating `f n` against `partialTraj k (a n) y`, you get something at lea
st
`ε` for all `n`. Then there exists `z` such that this remains true when integrat
ing
`f` against `partialTraj (k + 1) (a n) (update y (k + 1) z)`.
-/
theorem le_lmarginalPartialTraj_succ {f : ℕ → (Π n, X n) → ℝ≥0∞} {a : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (Iic (a n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    (anti : ∀ x, Antitone (fun n ↦ lmarginalPartialTraj κ (k + 1) (a n) (f n) x))
    {l : (Π n, X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ lmarginalPartialTraj κ (k + 1) (a n) (f n) x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : Π i : Iic k, X i)
    (hpos : ∀ x n, ε ≤ lmarginalPartialTraj κ k (a n) (f n) (updateFinset x (Iic k) y)) :
    ∃ z, ∀ x n,
    ε ≤ lmarginalPartialTraj κ (k + 1) (a n) (f n)
      (update (updateFinset x (Iic k) y) (k + 1) z) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨y ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i ↦ @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Fₙ` is the integral of `fₙ` from time `k + 1` to `aₙ`.
  let F n : (Π n, X n) → ℝ≥0∞ := lmarginalPartialTraj κ (k + 1) (a n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `aₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1`.
  have f_eq x n : lmarginalPartialTraj κ k (a n) (f n) x =
      lmarginalPartialTraj κ k (k + 1) (F n) x := by
    simp_rw [F]
    obtain h | h | h := lt_trichotomy (k + 1) (a n)
    · rw [← lmarginalPartialTraj_self k.le_succ h.le (mf n)]
    · rw [← h, lmarginalPartialTraj_le _ le_rfl (mf n)]
    · rw [lmarginalPartialTraj_le _ _ (mf n), (hcte n).lmarginalPartialTraj_of_le _ (mf n),
        (hcte n).lmarginalPartialTraj_of_le _ (mf n)]
      all_goals lia
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simpa [F, lmarginalPartialTraj] using lintegral_le_const (ae_of_all _ fun z ↦ le_bound _ _)
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `a n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n ↦ lmarginalPartialTraj κ k (a n) (f n) x) atTop
      (𝓝 (lmarginalPartialTraj κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPartialTraj]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ (measurable_lmarginalPartialTraj _ _ (mf n)).comp measurable_updateFinset)
      (fun n ↦ Eventually.of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound]) (Eventually.of_forall (fun _ ↦ tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPartialTraj κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε ≤ lmarginalPartialTraj κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : Π n, X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x` such that `ε ≤ l(y, x)`.
  obtain ⟨x, hx⟩ : ∃ x, ε ≤ l (update (updateFinset x_ _ y) (k + 1) x) := by
    have : ∫⁻ x, l (update (updateFinset x_ _ y) (k + 1) x) ∂(κ k y) ≠ ∞ :=
      ne_top_of_le_ne_top fin_bound <| lintegral_le_const <| ae_of_all _
        fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    obtain ⟨x, hx⟩ := exists_lintegral_le this
    refine ⟨x, (ε_le_lint x_).trans ?_⟩
    rwa [lmarginalPartialTraj_succ, frestrictLe_updateFinset]
    exact ENNReal.measurable_of_tendsto (by fun_prop) (tendsto_pi_nhds.2 htendsto)
  refine ⟨x, fun x' n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x)` for any `n`.
  have := le_trans hx ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert! this using 1
  refine (hcte n).dependsOn_lmarginalPartialTraj _ (mf n) fun i hi ↦ ?_
  simp only [update, updateFinset, mem_Iic]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe, mem_Iic] at hi
  lia

/-- This is the key theorem to prove the existence of the `traj`:
the `trajContent` of a decreasing sequence of cylinders with empty intersection
converges to `0`.

This implies the `σ`-additivity of `trajContent`
(see `addContent_iUnion_eq_sum_of_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem. -/
/-
**ProbabilityTheory.Kernel.trajContent_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：trajContent_tendsto_zero {A : Nat -> Set (Π n, X n)} (A_mem : forall n, A 
n in measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) {p : 
Nat} (x₀ : Π i : Iic p, X i) : Tendsto (fun n => trajContent κ x₀ (A n)) atTop (
𝓝 0)
参数：Π n, X n；A_mem : forall n, A n in measurableCylinders X；A_anti : Antitone A；A
_inter : ⋂ n, A n = ∅；x₀ : Π i : Iic p, X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.nonempty_of_isProbabilityMeasure`：nonempty_of_isProbabilit
yMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measurableCylinders_nat`：measurableCylinders_nat {X : Nat 
-> Type*} [forall n, MeasurableSpace (X n)] : measurableCylinders X = ⋃ (a) (S) 
(_ : MeasurableSet S), {cyl…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `measurable_indicator_const_iff`：measurable_indicator_const_iff [Zero β] 
[MeasurableSingletonClass β] (b : β) [NeZero b] : Measurable (s.indicator (fun (
_ : α) => b)) ↔ Meas…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasurableSet.cylinder`：∀ {ι : Type u_2} {α : ι → Type u_1} [inst : (i :
 ι) → MeasurableSpace (α i)] (s : Finset ι) {S : Set ((i : ↥s) → α ↑i)},   Measu
rableSet S →…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.dependsOn_cylinder_indicator_const`：dependsOn_cylinder_ind
icator_const {M : Type*} [Zero M] {I : Finset ι} (S : Set (Π i : I, α i)) (c : M
) : DependsOn ((cylinder I S).indicato…
· 使用定理 `DependsOn.dependsOn_lmarginalPartialTraj`：dependsOn_lmarginalPartialTraj
 [forall n, IsSFiniteKernel (κ n)] (a : Nat) {f : (Π n, X n) -> Real>=0∞} (hf : 
DependsOn f (Iic b)) (mf : Mea…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
This is the key theorem to prove the existence of the `traj`:
the `trajContent` of a decreasing sequence of cylinders with empty intersection
converges to `0`.

This implies the `σ`-additivity of `trajContent`
(see `addContent_iUnion_eq_sum_of_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem.
-/
theorem trajContent_tendsto_zero {A : ℕ → Set (Π n, X n)}
    (A_mem : ∀ n, A n ∈ measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅)
    {p : ℕ} (x₀ : Π i : Iic p, X i) :
    Tendsto (fun n ↦ trajContent κ x₀ (A n)) atTop (𝓝 0) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨x₀ ⟨0, mem_Iic.2 zero_le⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i ↦ @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact nonempty_of_isProbabilityMeasure (κ m Classical.ofNonempty)
  -- `Aₙ` is a cylinder, it can be written as `cylinder (Iic (a n)) Sₙ`.
  have A_cyl n : ∃ a S, MeasurableSet S ∧ A n = cylinder (Iic a) S := by
    simpa [measurableCylinders_nat] using A_mem n
  choose a S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (Π n, X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| (mS n).cylinder
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (a n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator_const ..
  -- Therefore its integral against `partialTraj κ k (a n)` is constant.
  have lma_const x y n :
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) =
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset y _ x₀) := by
    refine (χ_dep n).dependsOn_lmarginalPartialTraj p (mχ n) fun i hi ↦ ?_
    rw [mem_coe, mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := fun m n hmn y ↦ by
    apply Set.indicator_le fun a ha ↦ ?_
    simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : a n ≤ M) :
      lmarginalPartialTraj κ k M (χ n) = lmarginalPartialTraj κ k (a n) (χ n) :=
    (χ_dep n).lmarginalPartialTraj_const_right (mχ n) h le_rfl
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n ↦ lmarginalPartialTraj κ k (a n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((a n).max (a m)) n (le_max_left _ _),
      ← lma_inv k ((a n).max (a m)) m (le_max_right _ _)]
    exact lmarginalPartialTraj_mono _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l, Tendsto (fun n ↦ lmarginalPartialTraj κ k (a n) (χ n) x) atTop (𝓝 l) := by
    obtain h | h := tendsto_atTop_of_antitone (anti_lma k x)
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `lₚ` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l p (updateFinset x _ x₀) = l p (updateFinset y _ x₀) := by
    have := hl p (updateFinset x _ x₀)
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl p _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l p (updateFinset x _ x₀) = ε :=
      ⟨l p (updateFinset Classical.ofNonempty _ x₀), fun x ↦ l_const _ _⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε ≤ lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply `le_lmarginalPartialTraj_succ`.
  -- This allows us to recursively build a sequence `z` with the following property:
  -- for any `k ≥ p` and `n`, integrating `χ n` from time `k` to time `a n`
  -- with the trajectory up to `k` being equal to `z` gives something greater than `ε`.
  choose! ind hind using
    fun k y h ↦ le_lmarginalPartialTraj_succ χ_dep mχ (by simp : (1 : ℝ≥0∞) ≠ ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterateInduction x₀ ind
  have main k (hk : p ≤ k) : ∀ x n,
      ε ≤ lmarginalPartialTraj κ k (a n) (χ n) (updateFinset x _ (frestrictLe k z)) := by
    induction k, hk using Nat.le_induction with
    | base => exact fun x n ↦ by simpa [z, frestrictLe_iterateInduction] using hpos x n
    | succ k hn h =>
      intro x n
      convert! hind k (fun i ↦ z i.1) h x n
      ext i
      simp only [updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite, update, z]
      split_ifs with h1 h2 h3 h4 h5
      any_goals lia
      cases h2
      rw [iterateInduction, dif_neg (by lia)]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `trajContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n :
      trajContent κ x₀ (A n) = lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← frestrictLe_updateFinset x x₀]
    exact trajContent_eq_lmarginalPartialTraj (mS n) ..
  simp_rw [aux z]
  convert! hl p _
  rw [hε]
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > aₙ` we get `ε ≤ χₙ(z₀, ..., z_{aₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  by_contra!
  have mem n : z ∈ A n := by
    have : 0 < χ n z := by
      rw [← lmarginalPartialTraj_le κ (le_max_right p (a n)) (mχ n),
        ← updateFinset_frestrictLe (a := a n) z]
      simpa using lt_of_lt_of_le this.symm.bot_lt (main _ (le_max_left _ _) z n)
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

variable (κ)

/-- The `trajContent` is sigma-subadditive. -/
/-
**ProbabilityTheory.Kernel.isSigmaSubadditive_trajContent** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isSigmaSubadditive_trajContent {a : Nat} (x₀ : Π i : Iic a, X i) : (trajCo
ntent κ x₀).IsSigmaSubadditive
参数：x₀ : Π i : Iic a, X i。
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
· 使用引理 `ProbabilityTheory.Kernel.trajContent_ne_top`：trajContent_ne_top {a : Nat
} {x : Π i : Iic a, X i} {s : Set (Π n, X n)} : trajContent κ x s != ∞
· 使用定理 `ProbabilityTheory.Kernel.trajContent_tendsto_zero`：trajContent_tendsto_z
ero {A : Nat -> Set (Π n, X n)} (A_mem : forall n, A n in measurableCylinders X)
 (A_anti : Antitone A) (A_inter : ⋂ n, …

--- 原说明 ---
The `trajContent` is sigma-subadditive.
-/
theorem isSigmaSubadditive_trajContent {a : ℕ} (x₀ : Π i : Iic a, X i) :
    (trajContent κ x₀).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (trajContent κ x₀) (fun _ _ ↦ trajContent_ne_top) ?_ hf hf_Union hf'
  exact fun s hs anti_s inter_s ↦ trajContent_tendsto_zero hs anti_s inter_s x₀

/-- This function is the kernel given by the Ionescu-Tulcea theorem. It is shown below that it
is measurable and turned into a true kernel in `Kernel.traj`. -/
/-
**ProbabilityTheory.Kernel.trajFun** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：trajFun (a : Nat) (x₀ : Π i : Iic a, X i) : Measure (Π n, X n)
参数：a : Nat；x₀ : Π i : Iic a, X i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isSetSemiring_measurableCylinders`：isSetSemiring_measurabl
eCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α)
· 使用定理 `ProbabilityTheory.Kernel.isSigmaSubadditive_trajContent`：isSigmaSubaddit
ive_trajContent {a : Nat} (x₀ : Π i : Iic a, X i) : (trajContent κ x₀).IsSigmaSu
badditive

--- 原说明 ---
This function is the kernel given by the Ionescu-Tulcea theorem. It is shown bel
ow that it
is measurable and turned into a true kernel in `Kernel.traj`.
-/
noncomputable def trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) : Measure (Π n, X n) :=
  (trajContent κ x₀).measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    (isSigmaSubadditive_trajContent κ x₀)
/-
**ProbabilityTheory.Kernel.isProbabilityMeasure_trajFun** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：isProbabilityMeasure_trajFun (a : Nat) (x₀ : Π i : Iic a, X i) : IsProbabi
lityMeasure (trajFun κ a x₀) where measure_univ
参数：a : Nat；x₀ : Π i : Iic a, X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.cylinder_univ`：cylinder_univ (s : Finset ι) : cylinder s (
univ : Set (forall i : s, α i)) = univ
· 使用引理 `MeasureTheory.isSetSemiring_measurableCylinders`：isSetSemiring_measurabl
eCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α)
· 使用定理 `ProbabilityTheory.Kernel.isSigmaSubadditive_trajContent`：isSigmaSubaddit
ive_trajContent {a : Nat} (x₀ : Π i : Iic a, X i) : (trajContent κ x₀).IsSigmaSu
badditive
· 使用定理 `ProbabilityTheory.Kernel.trajFun.eq_1`：∀ {X : ℕ → Type u_1} [inst : (n :
 ℕ) → MeasurableSpace (X n)]   (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(F
inset.Iic n)) → X ↑i) (X (n…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.generateFrom_measurableCylinders`：generateFrom_measurableC
ylinders : MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpac
e.pi
· 使用定理 `MeasureTheory.AddContent.measure_eq`：measure_eq [mα : MeasurableSpace α]
 (m : AddContent Real>=0∞ C) (hC : IsSetSemiring C) (hC_gen : mα = MeasurableSpa
ce.generateFrom C) (m_sig…
· 使用定理 `MeasureTheory.cylinder_mem_measurableCylinders`：cylinder_mem_measurableC
ylinders (s : Finset ι) (S : Set (forall i : s, α i)) (hS : MeasurableSet S) : c
ylinder s S in measurableCylinders α
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `ProbabilityTheory.Kernel.trajContent_cylinder`：trajContent_cylinder {a b
 : Nat} {S : Set (Π i : Iic b, X i)} (mS : MeasurableSet S) (x₀ : Π i : Iic a, X
 i) : trajContent κ x₀ (cylinder (I…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicParti
alTrajOfHAddOfNat`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}  
 {κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
-/
theorem isProbabilityMeasure_trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) :
    IsProbabilityMeasure (trajFun κ a x₀) where
  measure_univ := by
    rw [← cylinder_univ (Iic 0), trajFun, AddContent.measure_eq, trajContent_cylinder .univ,
      measure_univ]
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ .univ
/-
**ProbabilityTheory.Kernel.isProjectiveLimit_trajFun** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：isProjectiveLimit_trajFun (a : Nat) (x₀ : Π i : Iic a, X i) : IsProjective
Limit (trajFun κ a x₀) (inducedFamily (fun n => partialTraj κ a n x₀))
参数：a : Nat；x₀ : Π i : Iic a, X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.isProjectiveLimit_nat_iff`：isProjectiveLimit_nat_iff {μ : 
(I : Finset Nat) -> Measure (Π i : I, X i)} (hμ : IsProjectiveMeasureFamily μ) (
ν : Measure (Π n, X n)) : IsP…
· 使用引理 `ProbabilityTheory.Kernel.isProjectiveMeasureFamily_partialTraj`：isProjec
tiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) : IsProjectiveMe
asureFamily (inducedFamily (fun b => partialTraj κ a…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用引理 `MeasureTheory.isSetSemiring_measurableCylinders`：isSetSemiring_measurabl
eCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α)
· 使用定理 `ProbabilityTheory.Kernel.isSigmaSubadditive_trajContent`：isSigmaSubaddit
ive_trajContent {a : Nat} (x₀ : Π i : Iic a, X i) : (trajContent κ x₀).IsSigmaSu
badditive
· 使用定理 `ProbabilityTheory.Kernel.trajFun.eq_1`：∀ {X : ℕ → Type u_1} [inst : (n :
 ℕ) → MeasurableSpace (X n)]   (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(F
inset.Iic n)) → X ↑i) (X (n…
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
· 使用定理 `ProbabilityTheory.Kernel.trajContent.eq_1`：∀ {X : ℕ → Type u_1} [inst : 
(n : ℕ) → MeasurableSpace (X n)]   (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i :
 ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用引理 `MeasureTheory.projectiveFamilyContent_congr`：projectiveFamilyContent_con
gr (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i)) (hs_eq : s = cylinder
 I S) (hS : MeasurableSet S) : pr…
-/
theorem isProjectiveLimit_trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) :
    IsProjectiveLimit (trajFun κ a x₀) (inducedFamily (fun n ↦ partialTraj κ a n x₀)) := by
  refine isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj κ x₀) _ |>.2 fun n ↦ ?_
  ext s ms
  rw [Measure.map_apply (measurable_frestrictLe n) ms, trajFun, AddContent.measure_eq, trajContent,
    projectiveFamilyContent_congr _ (frestrictLe n ⁻¹' s) rfl ms]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ ms

variable {κ} in
/-
**ProbabilityTheory.Kernel.measurable_trajFun** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：measurable_trajFun (a : Nat) : Measurable (trajFun κ a)
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_of_measurable_coe`：measurable_of_measur
able_coe (f : β -> Measure α) (h : forall (s : Set α), MeasurableSet s -> Measur
able fun b => f b s) : Measurable f
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.generateFrom_measurableCylinders`：generateFrom_measurableC
ylinders : MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpac
e.pi
· 使用定理 `MeasureTheory.isPiSystem_measurableCylinders`：isPiSystem_measurableCylin
ders : IsPiSystem (measurableCylinders α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measurableCylinders_nat`：measurableCylinders_nat {X : Nat 
-> Type*} [forall n, MeasurableSpace (X n)] : measurableCylinders X = ⋃ (a) (S) 
(_ : MeasurableSet S), {cyl…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `MeasureTheory.isSetSemiring_measurableCylinders`：isSetSemiring_measurabl
eCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α)
· 使用定理 `ProbabilityTheory.Kernel.isSigmaSubadditive_trajContent`：isSigmaSubaddit
ive_trajContent {a : Nat} (x₀ : Π i : Iic a, X i) : (trajContent κ x₀).IsSigmaSu
badditive
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.AddContent.measure_eq`：measure_eq [mα : MeasurableSpace α]
 (m : AddContent Real>=0∞ C) (hC : IsSetSemiring C) (hC_gen : mα = MeasurableSpa
ce.generateFrom C) (m_sig…
· 使用引理 `ProbabilityTheory.Kernel.isProjectiveMeasureFamily_partialTraj`：isProjec
tiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) : IsProjectiveMe
asureFamily (inducedFamily (fun b => partialTraj κ a…
· 使用引理 `MeasureTheory.projectiveFamilyContent_congr`：projectiveFamilyContent_con
gr (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i)) (hs_eq : s = cylinder
 I S) (hS : MeasurableSet S) : pr…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.measurable_measure`：measurable_measure {μ : α -> M
easure β} : Measurable μ ↔ forall (s : Set β), MeasurableSet s -> Measurable fun
 b => μ b s
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.measurable_map`：measurable_map (f : α -> β) (hf : 
Measurable f) : Measurable fun μ : Measure α => map f μ
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用定理 `ProbabilityTheory.Kernel.isProbabilityMeasure_trajFun`：isProbabilityMeas
ure_trajFun (a : Nat) (x₀ : Π i : Iic a, X i) : IsProbabilityMeasure (trajFun κ 
a x₀) where measure_univ
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
（共 46 条，此处仅展示前 30 条）
-/
theorem measurable_trajFun (a : ℕ) : Measurable (trajFun κ a) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ht ↦ Measurable (fun x₀ ↦ trajFun κ a x₀ t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl)
    (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : ∃ N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [measurableCylinders_nat] using ht
    simp_rw [trajFun, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _ ht,
      trajContent, projectiveFamilyContent_congr _ t t_eq mS, inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    exact (Measure.measurable_map _ (measurable_restrict₂ _)).comp (measurable _)
  · have := isProbabilityMeasure_trajFun κ a
    simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

/-- *Ionescu-Tulcea Theorem* : Given a family of kernels `κ n` taking variables in `Iic n` with
value in `X (n + 1)`, the kernel `traj κ a` takes a variable `x` depending on the
variables `i ≤ a` and associates to it a kernel on trajectories depending on all variables,
where the entries with index `≤ a` are those of `x`, and then one follows iteratively the
kernels `κ a`, then `κ (a + 1)`, and so on.

The fact that such a kernel exists on infinite trajectories is not obvious, and is the content of
the Ionescu-Tulcea theorem. -/
/-
**ProbabilityTheory.Kernel.traj** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ker
nel`。
形式化陈述：traj (a : Nat) : Kernel (Π i : Iic a, X i) (Π n, X n) where toFun
参数：a : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measurable_trajFun`：measurable_trajFun (a : Nat
) : Measurable (trajFun κ a)

--- 原说明 ---
*Ionescu-Tulcea Theorem* : Given a family of kernels `κ n` taking variables in `
Iic n` with
value in `X (n + 1)`, the kernel `traj κ a` takes a variable `x` depending on th
e
variables `i ≤ a` and associates to it a kernel on trajectories depending on all
 variables,
where the entries with index `≤ a` are those of `x`, and then one follows iterat
ively the
kernels `κ a`, then `κ (a + 1)`, and so on.

The fact that such a kernel exists on infinite trajectories is not obvious, and 
is the content of
the Ionescu-Tulcea theorem.
-/
noncomputable def traj (a : ℕ) : Kernel (Π i : Iic a, X i) (Π n, X n) where
  toFun := trajFun κ a
  measurable' := measurable_trajFun a

end definition

section basic

/-
**ProbabilityTheory.Kernel.traj_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：traj_apply (a : Nat) (x : Π i : Iic a, X i) : traj κ a x = trajFun κ a x
参数：a : Nat；x : Π i : Iic a, X i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma traj_apply (a : ℕ) (x : Π i : Iic a, X i) : traj κ a x = trajFun κ a x := rfl
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : ℕ) : IsMarkovKernel (traj κ a) := ⟨fun _ ↦ isProbabilityMeasure_trajFun ..⟩
/-
**ProbabilityTheory.Kernel.traj_map_frestrictLe** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：traj_map_frestrictLe (a b : Nat) : (traj κ a).map (frestrictLe b) = partia
lTraj κ a b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用引理 `ProbabilityTheory.Kernel.traj_apply`：traj_apply (a : Nat) (x : Π i : Iic
 a, X i) : traj κ a x = trajFun κ a x
· 使用定理 `Preorder.frestrictLe.eq_1`：∀ {α : Type u_1} [inst : Preorder α] {π : α →
 Type u_2} [inst_1 : LocallyFiniteOrderBot α] (a : α),   Preorder.frestrictLe a 
= (Finset.Iic a…
· 使用定理 `ProbabilityTheory.Kernel.isProjectiveLimit_trajFun`：isProjectiveLimit_tr
ajFun (a : Nat) (x₀ : Π i : Iic a, X i) : IsProjectiveLimit (trajFun κ a x₀) (in
ducedFamily (fun n => partialTraj κ a n …
· 使用定理 `MeasureTheory.inducedFamily_Iic`：inducedFamily_Iic (n : Nat) : inducedFa
mily μ (Iic n) = μ n
-/
lemma traj_map_frestrictLe (a b : ℕ) : (traj κ a).map (frestrictLe b) = partialTraj κ a b := by
  ext x
  rw [map_apply, traj_apply, frestrictLe, isProjectiveLimit_trajFun, inducedFamily_Iic]
  fun_prop
/-
**ProbabilityTheory.Kernel.traj_map_frestrictLe_apply** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：traj_map_frestrictLe_apply (a b : Nat) (x : Π i : Iic a, X i) : (traj κ a 
x).map (frestrictLe b) = partialTraj κ a b x
参数：a b : Nat；x : Π i : Iic a, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
-/
lemma traj_map_frestrictLe_apply (a b : ℕ) (x : Π i : Iic a, X i) :
    (traj κ a x).map (frestrictLe b) = partialTraj κ a b x := by
  rw [← map_apply _ (measurable_frestrictLe b), traj_map_frestrictLe]
/-
**ProbabilityTheory.Kernel.traj_map_frestrictLe_of_le** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：traj_map_frestrictLe_of_le {a b : Nat} (hab : a <= b) : (traj κ b).map (fr
estrictLe a) = deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ _)
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le`：partialTraj_le (hba : b <= a) :
 partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _
)
-/
lemma traj_map_frestrictLe_of_le {a b : ℕ} (hab : a ≤ b) :
    (traj κ b).map (frestrictLe a) =
      deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ _) := by
  rw [traj_map_frestrictLe, partialTraj_le]

/-- The pushforward of `traj κ a` along the the point at time `a + 1` is the kernel `κ a`. -/
/-
**ProbabilityTheory.Kernel.map_traj_succ_self** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：map_traj_succ_self {a : Nat} : (traj κ a).map (fun x => x (a + 1)) = κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.map_comp_right`：map_comp_right (κ : Kernel α β)
 {f : β -> γ} (hf : Measurable f) {g : γ -> δ} (hg : Measurable g) : κ.map (g ∘ 
f) = (κ.map f).map g
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用引理 `ProbabilityTheory.Kernel.map_partialTraj_succ_self`：map_partialTraj_succ
_self (a : Nat) : (partialTraj κ a (a + 1)).map (fun x => x ⟨a + 1, mem_Iic.2 le
_rfl⟩) = κ a

--- 原说明 ---
The pushforward of `traj κ a` along the the point at time `a + 1` is the kernel 
`κ a`.
-/
lemma map_traj_succ_self {a : ℕ} : (traj κ a).map (fun x ↦ x (a + 1)) = κ a := by
  have hf : (fun x : Π n, X n ↦ x (a + 1)) =
      (fun x ↦ x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ frestrictLe (a + 1) := rfl
  rw [hf, map_comp_right _ (by fun_prop) (by fun_prop), traj_map_frestrictLe,
    map_partialTraj_succ_self]

variable (κ)

/-- To check that `η = traj κ a` it is enough to show that the restriction of `η` to variables `≤ b`
is `partialTraj κ a b` for any `b ≥ n`. -/
/-
**ProbabilityTheory.Kernel.eq_traj'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：eq_traj' {a : Nat} (n : Nat) (η : Kernel (Π i : Iic a, X i) (Π n, X n)) (h
η : forall b >= n, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a
参数：n : Nat；η : Kernel (Π i : Iic a, X i) (Π n, X n)；hη : forall b >= n, η.map (f
restrictLe b) = partialTraj κ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsProjectiveLimit.unique`：unique [forall i, IsFiniteMeasur
e (P i)] (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) : μ = ν
· 使用定理 `MeasureTheory.instIsFiniteMeasureForallValNatMemFinsetInducedFamilyOfFor
allIic`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   (μ : (n 
: ℕ) → MeasureTheory.Measure ((i : ↥(Finset.Iic n)) → X ↑i)) [∀ (n :…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelForallValNatMemFinsetIicParti
alTrajOfHAddOfNat`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}  
 {κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.isProjectiveLimit_trajFun`：isProjectiveLimit_tr
ajFun (a : Nat) (x₀ : Π i : Iic a, X i) : IsProjectiveLimit (trajFun κ a x₀) (in
ducedFamily (fun n => partialTraj κ a n …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.isProjectiveLimit_nat_iff'`：isProjectiveLimit_nat_iff' {μ 
: (I : Finset Nat) -> Measure (Π i : I, X i)} (hμ : IsProjectiveMeasureFamily μ)
 (ν : Measure (Π n, X n)) (a :…
· 使用引理 `ProbabilityTheory.Kernel.isProjectiveMeasureFamily_partialTraj`：isProjec
tiveMeasureFamily_partialTraj {a : Nat} (x₀ : Π i : Iic a, X i) : IsProjectiveMe
asureFamily (inducedFamily (fun b => partialTraj κ a…
· 使用定理 `MeasureTheory.inducedFamily_Iic`：inducedFamily_Iic (n : Nat) : inducedFa
mily μ (Iic n) = μ n
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π

--- 原说明 ---
To check that `η = traj κ a` it is enough to show that the restriction of `η` to
 variables `≤ b`
is `partialTraj κ a b` for any `b ≥ n`.
-/
theorem eq_traj' {a : ℕ} (n : ℕ) (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : ∀ b ≥ n, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a := by
  ext x : 1
  refine ((isProjectiveLimit_trajFun _ _ _).unique ?_).symm
  rw [isProjectiveLimit_nat_iff' _ _ n]
  · intro k hk
    rw [inducedFamily_Iic, ← map_apply _ (measurable_frestrictLe k), hη k hk]
  · exact isProjectiveMeasureFamily_partialTraj κ x

/-- To check that `η = traj κ a` it is enough to show that the restriction of `η` to variables `≤ b`
is `partialTraj κ a b`. -/
/-
**ProbabilityTheory.Kernel.eq_traj** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：eq_traj {a : Nat} (η : Kernel (Π i : Iic a, X i) (Π n, X n)) (hη : forall 
b, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a
参数：η : Kernel (Π i : Iic a, X i) (Π n, X n)；hη : forall b, η.map (frestrictLe b)
 = partialTraj κ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.eq_traj'`：eq_traj' {a : Nat} (n : Nat) (η : Ker
nel (Π i : Iic a, X i) (Π n, X n)) (hη : forall b >= n, η.map (frestrictLe b) = 
partialTraj κ a b) : η …

--- 原说明 ---
To check that `η = traj κ a` it is enough to show that the restriction of `η` to
 variables `≤ b`
is `partialTraj κ a b`.
-/
theorem eq_traj {a : ℕ} (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : ∀ b, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a :=
  eq_traj' κ 0 η fun b _ ↦ hη b

variable {κ}

/-- Given the distribution up to tome `a`, `partialTraj κ a b` gives the distribution
of the trajectory up to time `b`, and composing this with `traj κ b` gives the distribution
of the whole trajectory. -/
/-
**ProbabilityTheory.Kernel.traj_comp_partialTraj** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：traj_comp_partialTraj {a b : Nat} (hab : a <= b) : (traj κ b) ∘ₖ (partialT
raj κ a b) = traj κ a
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.eq_traj`：eq_traj {a : Nat} (η : Kernel (Π i : I
ic a, X i) (Π n, X n)) (hη : forall b, η.map (frestrictLe b) = partialTraj κ a b
) : η = traj κ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.map_comp`：map_comp (κ : Kernel α β) (η : Kernel
 β γ) (f : γ -> δ) : (η ∘ₖ κ).map f = (η.map f) ∘ₖ κ
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_comp_partialTraj'`：partialTraj_comp
_partialTraj' (c : Nat) (hab : a <= b) : partialTraj κ b c ∘ₖ partialTraj κ a b 
= partialTraj κ a c

--- 原说明 ---
Given the distribution up to tome `a`, `partialTraj κ a b` gives the distributio
n
of the trajectory up to time `b`, and composing this with `traj κ b` gives the d
istribution
of the whole trajectory.
-/
theorem traj_comp_partialTraj {a b : ℕ} (hab : a ≤ b) :
    (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a := by
  refine eq_traj _ _ fun n ↦ ?_
  rw [map_comp, traj_map_frestrictLe, partialTraj_comp_partialTraj' _ hab]

/-- This theorem shows that `traj κ n` is, up to an equivalence, the product of
a deterministic kernel with another kernel. This is an intermediate result to compute integrals
with respect to this kernel. -/
/-
**ProbabilityTheory.Kernel.traj_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：traj_eq_prod (a : Nat) : traj κ a = (Kernel.id ×ₖ (traj κ a).map (Set.Ioi 
a).domRestrict).map (IicProdIoi a)
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.eq_traj'`：eq_traj' {a : Nat} (n : Nat) (η : Ker
nel (Π i : Iic a, X i) (Π n, X n)) (hη : forall b >= n, η.map (frestrictLe b) = 
partialTraj κ a b) : η …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.map_comp_right`：map_comp_right (κ : Kernel α β)
 {f : β -> γ} (hf : Measurable f) {g : γ -> δ} (hg : Measurable g) : κ.map (g ∘ 
f) = (κ.map f).map g
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用引理 `measurable_IicProdIoc`：measurable_IicProdIoc {m n : ι} : Measurable (Iic
ProdIoc (X
· 使用引理 `ProbabilityTheory.Kernel.map_prod_map`：map_prod_map {ε} {mε : Measurable
Space ε} (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α δ) [IsSFiniteKernel 
η] {f : β -> γ} (hf : Measu…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `Set.measurable_restrict`：Set.measurable_restrict (s : Set δ) : Measurabl
e (s.domRestrict (π
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
· 使用定理 `Finset.restrict₂_comp_restrict`：restrict₂_comp_restrict (hst : s subsete
q t) : (restrict₂ (π
· 使用定理 `Preorder.frestrictLe.eq_1`：∀ {α : Type u_1} [inst : Preorder α] {π : α →
 Type u_2} [inst_1 : LocallyFiniteOrderBot α] (a : α),   Preorder.frestrictLe a 
= (Finset.Iic a…
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
This theorem shows that `traj κ n` is, up to an equivalence, the product of
a deterministic kernel with another kernel. This is an intermediate result to co
mpute integrals
with respect to this kernel.
-/
theorem traj_eq_prod (a : ℕ) :
    traj κ a = (Kernel.id ×ₖ (traj κ a).map (Set.Ioi a).domRestrict).map (IicProdIoi a) := by
  refine (eq_traj' _ (a + 1) _ fun b hb ↦ ?_).symm
  rw [← map_comp_right]
  conv_lhs => enter [2]; change (IicProdIoc a b) ∘
    (Prod.map id (fun x i ↦ x ⟨i.1, Set.mem_Ioi.2 (mem_Ioc.1 i.2).1⟩))
  · rw [map_comp_right, ← map_prod_map, ← map_comp_right]
    · conv_lhs => enter [1, 2, 2]; change (Ioc a b).restrict
      rw [← restrict₂_comp_restrict Ioc_subset_Iic_self, ← frestrictLe, map_comp_right,
        traj_map_frestrictLe, map_id, ← partialTraj_eq_prod]
      all_goals fun_prop
    all_goals fun_prop
  all_goals fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**ProbabilityTheory.Kernel.traj_map_updateFinset** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：traj_map_updateFinset {n : Nat} (x : Π i : Iic n, X i) : (traj κ n x).map 
(updateFinset · (Iic n) x) = traj κ n x
参数：x : Π i : Iic n, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.traj_eq_prod`：traj_eq_prod (a : Nat) : traj κ a
 = (Kernel.id ×ₖ (traj κ a).map (Set.Ioi a).domRestrict).map (IicProdIoi a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Set.measurable_restrict`：Set.measurable_restrict (s : Set δ) : Measurabl
e (s.domRestrict (π
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.Measure.dirac_prod`：dirac_prod (x : α) : (dirac x).prod ν 
= map (Prod.mk x) ν
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
theorem traj_map_updateFinset {n : ℕ} (x : Π i : Iic n, X i) :
    (traj κ n x).map (updateFinset · (Iic n) x) = traj κ n x := by
  nth_rw 2 [traj_eq_prod]
  have : (updateFinset · _ x) = IicProdIoi n ∘ (Prod.mk x) ∘ (Set.Ioi n).domRestrict := by
    ext; simp [IicProdIoi, updateFinset]
  rw [this, ← Function.comp_assoc, ← Measure.map_map, ← Measure.map_map, map_apply, prod_apply,
    map_apply, id_apply, Measure.dirac_prod]
  all_goals fun_prop

end basic

section integral

/-! ### Integrals and `traj` -/

/-
**ProbabilityTheory.Kernel.lintegral_traj** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：lintegral_traj {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> Real>=
0∞} (mf : Measurable f) : ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic 
a) x₀) ∂traj κ a x₀
参数：x₀ : Π i : Iic a, X i；Π n, X n；mf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.lintegral_traj₀`：lintegral_traj₀ {a : Nat} (x₀ 
: Π i : Iic a, X i) {f : (Π n, X n) -> Real>=0∞} (mf : AEMeasurable f (traj κ a 
x₀)) : ∫⁻ x, f x ∂traj κ a x₀ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
### Integrals and `traj`
-/
theorem lintegral_traj₀ {a : ℕ} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) → ℝ≥0∞}
    (mf : AEMeasurable f (traj κ a x₀)) :
    ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ := by
  nth_rw 1 [← traj_map_updateFinset, MeasureTheory.lintegral_map']
  · convert! mf
    exact traj_map_updateFinset x₀
  · exact measurable_updateFinset_left.aemeasurable
/-
**ProbabilityTheory.Kernel.lintegral_traj** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：lintegral_traj {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> Real>=
0∞} (mf : Measurable f) : ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic 
a) x₀) ∂traj κ a x₀
参数：x₀ : Π i : Iic a, X i；Π n, X n；mf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.lintegral_traj₀`：lintegral_traj₀ {a : Nat} (x₀ 
: Π i : Iic a, X i) {f : (Π n, X n) -> Real>=0∞} (mf : AEMeasurable f (traj κ a 
x₀)) : ∫⁻ x, f x ∂traj κ a x₀ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem lintegral_traj {a : ℕ} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) :
    ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ :=
  lintegral_traj₀ x₀ mf.aemeasurable

variable {E : Type*} [NormedAddCommGroup E]
/-
**ProbabilityTheory.Kernel.integrable_traj** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：integrable_traj {a b : Nat} (hab : a <= b) {f : (Π n, X n) -> E} (x₀ : Π i
 : Iic a, X i) (i_f : Integrable f (traj κ a x₀)) : forallᵐ x ∂traj κ a x₀, Inte
grable f (traj κ b (frestrictLe b x))
参数：hab : a <= b；Π n, X n；x₀ : Π i : Iic a, X i；i_f : Integrable f (traj κ a x₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_of_ae_map`：ae_of_ae_map {f : α -> β} (hf : AEMeasurable
 f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y) : forallᵐ x ∂μ, p (f x)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.integrable_comp_iff`：integrable_comp_iff ⦃f : γ -> E⦄ 
(hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) : Integrable f ((η ∘ₖ κ) a) ↔ (forall
ᵐ y ∂κ a, Integrable f (η y…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `ProbabilityTheory.Kernel.traj_comp_partialTraj`：traj_comp_partialTraj {a
 b : Nat} (hab : a <= b) : (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a
-/
theorem integrable_traj {a b : ℕ} (hab : a ≤ b) {f : (Π n, X n) → E}
    (x₀ : Π i : Iic a, X i) (i_f : Integrable f (traj κ a x₀)) :
    ∀ᵐ x ∂traj κ a x₀, Integrable f (traj κ b (frestrictLe b x)) := by
  rw [← traj_comp_partialTraj hab, integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x ↦ Integrable f (traj κ b x))
    · fun_prop
    · convert! i_f.1
      rw [← traj_map_frestrictLe, Kernel.map_apply _ (measurable_frestrictLe _)]
  · exact i_f.aestronglyMeasurable
/-
**ProbabilityTheory.Kernel.aestronglyMeasurable_traj** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：aestronglyMeasurable_traj {a b : Nat} (hab : a <= b) {f : (Π n, X n) -> E}
 {x₀ : Π i : Iic a, X i} (hf : AEStronglyMeasurable f (traj κ a x₀)) : forallᵐ x
 ∂partialTraj κ a b x₀, AEStronglyMeasurable f (traj κ b x)
参数：hab : a <= b；Π n, X n；hf : AEStronglyMeasurable f (traj κ a x₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measur
ableSpace γ} {a : α} {κ : Pro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.traj_comp_partialTraj`：traj_comp_partialTraj {a
 b : Nat} (hab : a <= b) : (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a
-/
theorem aestronglyMeasurable_traj {a b : ℕ} (hab : a ≤ b) {f : (Π n, X n) → E}
    {x₀ : Π i : Iic a, X i} (hf : AEStronglyMeasurable f (traj κ a x₀)) :
    ∀ᵐ x ∂partialTraj κ a b x₀, AEStronglyMeasurable f (traj κ b x) := by
  rw [← traj_comp_partialTraj hab] at hf
  exact hf.comp

variable [NormedSpace ℝ E]

/-- When computing `∫ x, f x ∂traj κ n x₀`, because the trajectory up to time `n` is
determined by `x₀` we can replace `x` by `updateFinset x (Iic a) x₀`. -/
/-
**ProbabilityTheory.Kernel.integral_traj** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：integral_traj {a : Nat} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) -> E} (mf 
: AEStronglyMeasurable f (traj κ a x₀)) : ∫ x, f x ∂traj κ a x₀ = ∫ x, f (update
Finset x (Iic a) x₀) ∂traj κ a x₀
参数：x₀ : Π i : Iic a, X i；Π n, X n；mf : AEStronglyMeasurable f (traj κ a x₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.traj_map_updateFinset`：traj_map_updateFinset {n
 : Nat} (x : Π i : Iic n, X i) : (traj κ n x).map (updateFinset · (Iic n) x) = t
raj κ n x
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_updateFinset_left`：measurable_updateFinset_left [DecidableEq 
δ] {s : Finset δ} {x : Π i : s, X i} : Measurable (updateFinset · s x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
When computing `∫ x, f x ∂traj κ n x₀`, because the trajectory up to time `n` is
determined by `x₀` we can replace `x` by `updateFinset x (Iic a) x₀`.
-/
theorem integral_traj {a : ℕ} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) → E}
    (mf : AEStronglyMeasurable f (traj κ a x₀)) :
    ∫ x, f x ∂traj κ a x₀ = ∫ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ := by
  nth_rw 1 [← traj_map_updateFinset, integral_map]
  · exact measurable_updateFinset_left.aemeasurable
  · convert! mf
    rw [traj_map_updateFinset]
/-
**ProbabilityTheory.Kernel.partialTraj_compProd_traj** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：partialTraj_compProd_traj {a b : Nat} (hab : a <= b) (u : Π i : Iic a, X i
) : (partialTraj κ a b u) otimesₘ (traj κ b) = (traj κ a u).map (fun x => (frest
rictLe b x, x))
参数：hab : a <= b；u : Π i : Iic a, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.traj_comp_partialTraj`：traj_comp_partialTraj {a
 b : Nat} (hab : a <= b) : (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.traj_map_updateFinset`：traj_map_updateFinset {n
 : Nat} (x : Π i : Iic n, X i) : (traj κ n x).map (updateFinset · (Iic n) x) = t
raj κ n x
· 使用定理 `measurable_updateFinset_left`：measurable_updateFinset_left [DecidableEq 
δ] {s : Finset δ} {x : Π i : s, X i} : Measurable (updateFinset · s x)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 32 条，此处仅展示前 30 条）
-/
lemma partialTraj_compProd_traj {a b : ℕ} (hab : a ≤ b) (u : Π i : Iic a, X i) :
    (partialTraj κ a b u) ⊗ₘ (traj κ b) = (traj κ a u).map (fun x ↦ (frestrictLe b x, x)) := by
  ext s ms
  rw [Measure.map_apply, Measure.compProd_apply, ← traj_comp_partialTraj hab, comp_apply']
  · congr 1 with x
    rw [← traj_map_updateFinset, Measure.map_apply, Measure.map_apply]
    · congr 1 with y
      simp only [Set.mem_preimage]
      congrm (fun i ↦ ?_, fun i ↦ ?_) ∈ s <;> simp [updateFinset]
    any_goals fun_prop
    all_goals exact ms.preimage (by fun_prop)
  any_goals exact ms.preimage (by fun_prop)
  fun_prop
/-
**ProbabilityTheory.Kernel.partialTraj_compProd_eq_map_traj** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：partialTraj_compProd_eq_map_traj {a b : Nat} (hab : a <= b) {x₀ : Π n : Ii
c a, X n} : (partialTraj κ a b x₀) otimesₘ (κ b) = (traj κ a x₀).map (fun x => (
frestrictLe b x, x (b + 1)))
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_compProd_traj`：partialTraj_compProd
_traj {a b : Nat} (hab : a <= b) (u : Π i : Iic a, X i) : (partialTraj κ a b u) 
otimesₘ (traj κ b) = (traj κ a u).map (f…
· 使用引理 `MeasureTheory.Measure.compProd_map`：compProd_map [SFinite μ] [IsSFiniteK
ernel κ] {f : β -> γ} (hf : Measurable f) : μ otimesₘ (κ.map f) = (μ otimesₘ κ).
map (Prod.map id f)
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用引理 `ProbabilityTheory.Kernel.map_traj_succ_self`：map_traj_succ_self {a : Nat
} : (traj κ a).map (fun x => x (a + 1)) = κ a
-/
lemma partialTraj_compProd_eq_map_traj {a b : ℕ} (hab : a ≤ b) {x₀ : Π n : Iic a, X n} :
    (partialTraj κ a b x₀) ⊗ₘ (κ b) = (traj κ a x₀).map (fun x ↦ (frestrictLe b x, x (b + 1))) := by
  have hf : (fun x : Π n, X n ↦ (frestrictLe b x, x (b + 1))) =
      (Prod.map id (fun x ↦ x (b + 1))) ∘ (fun x ↦ (frestrictLe b x, x)) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), ← partialTraj_compProd_traj hab,
    ← Measure.compProd_map (by fun_prop), map_traj_succ_self]
/-
**ProbabilityTheory.Kernel.integral_traj_partialTraj'** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：integral_traj_partialTraj' {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X
 i} {f : (Π i : Iic b, X i) -> (Π n : Nat, X n) -> E} (hf : Integrable f.uncurry
 ((partialTraj κ a b x₀) otimesₘ (traj κ b))) : ∫ x, ∫ y, f x y ∂traj κ b x ∂par
tialTraj κ a b x₀ = ∫ x, f (frestrictLe b x) x ∂traj κ a x₀
参数：hab : a <= b；Π i : Iic b, X i；Π n : Nat, X n；hf : Integrable f.uncurry ((part
ialTraj κ a b x₀) otimesₘ (traj κ b))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.integral_compProd`：integral_compProd [SFinite μ] [
IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : 
α × β -> E} (hf : Integrable …
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_compProd_traj`：partialTraj_compProd
_traj {a b : Nat} (hab : a <= b) (u : Π i : Iic a, X i) : (partialTraj κ a b u) 
otimesₘ (traj κ b) = (traj κ a u).map (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_traj_partialTraj' {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π i : Iic b, X i) → (Π n : ℕ, X n) → E}
    (hf : Integrable f.uncurry ((partialTraj κ a b x₀) ⊗ₘ (traj κ b))) :
    ∫ x, ∫ y, f x y ∂traj κ b x ∂partialTraj κ a b x₀ =
    ∫ x, f (frestrictLe b x) x ∂traj κ a x₀ := by
  have hf' := hf
  rw [partialTraj_compProd_traj hab] at hf'
  simp_rw [← uncurry_apply_pair f, ← Measure.integral_compProd hf,
    partialTraj_compProd_traj hab, integral_map (by fun_prop) hf'.1]
/-
**ProbabilityTheory.Kernel.integral_traj_partialTraj** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：integral_traj_partialTraj {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X 
i} {f : (Π n : Nat, X n) -> E} (hf : Integrable f (traj κ a x₀)) : ∫ x, ∫ y, f y
 ∂traj κ b x ∂partialTraj κ a b x₀ = ∫ x, f x ∂traj κ a x₀
参数：hab : a <= b；Π n : Nat, X n；hf : Integrable f (traj κ a x₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.integral_traj_partialTraj'`：integral_traj_parti
alTraj' {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i} {f : (Π i : Iic b, X 
i) -> (Π n : Nat, X n) -> E} (hf : Integr…
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `ProbabilityTheory.Kernel.traj_comp_partialTraj`：traj_comp_partialTraj {a
 b : Nat} (hab : a <= b) : (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem integral_traj_partialTraj {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π n : ℕ, X n) → E} (hf : Integrable f (traj κ a x₀)) :
    ∫ x, ∫ y, f y ∂traj κ b x ∂partialTraj κ a b x₀ = ∫ x, f x ∂traj κ a x₀ := by
  apply integral_traj_partialTraj' hab
  rw [← traj_comp_partialTraj hab, comp_apply, ← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd
/-
**ProbabilityTheory.Kernel.setIntegral_traj_partialTraj'** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：setIntegral_traj_partialTraj' {a b : Nat} (hab : a <= b) {u : (Π i : Iic a
, X i)} {f : (Π i : Iic b, X i) -> (Π n : Nat, X n) -> E} (hf : Integrable f.unc
urry ((partialTraj κ a b u) otimesₘ (traj κ b))) {A : Set (Π i : Iic b, X i)} (h
A : MeasurableSet A) : ∫ x in A, ∫ y, f x y ∂traj κ b x ∂partialTraj κ a b u = ∫
 y in frestrictLe b ⁻¹' A, f (frestrictLe b y) y ∂traj κ a u
参数：hab : a <= b；Π i : Iic a, X i；Π i : Iic b, X i；Π n : Nat, X n；hf : Integrable
 f.uncurry ((partialTraj κ a b u) otimesₘ (traj κ b))；Π i : Iic b, X i；hA : Meas
urableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.integral_integral_indicator`：integral_integral_
indicator (μ : Measure X) (f : X -> Y -> E) {s : Set X} (hs : MeasurableSet s) :
 ∫ x, ∫ y, s.indicator (f · y) x ∂κ x ∂μ =…
· 使用定理 `ProbabilityTheory.Kernel.integral_traj_partialTraj'`：integral_traj_parti
alTraj' {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i} {f : (Π i : Iic b, X 
i) -> (Π n : Nat, X n) -> E} (hf : Integr…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
-/
theorem setIntegral_traj_partialTraj' {a b : ℕ} (hab : a ≤ b) {u : (Π i : Iic a, X i)}
    {f : (Π i : Iic b, X i) → (Π n : ℕ, X n) → E}
    (hf : Integrable f.uncurry ((partialTraj κ a b u) ⊗ₘ (traj κ b)))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f x y ∂traj κ b x ∂partialTraj κ a b u =
      ∫ y in frestrictLe b ⁻¹' A, f (frestrictLe b y) y ∂traj κ a u := by
  rw [← integral_integral_indicator _ _ _ hA, integral_traj_partialTraj' hab]
  · simp_rw [← Set.indicator_comp_right, ← integral_indicator (measurable_frestrictLe b hA)]
    rfl
  convert! hf.indicator (hA.prod .univ)
  ext ⟨x, y⟩
  by_cases hx : x ∈ A <;> simp [uncurry_def, hx]
/-
**ProbabilityTheory.Kernel.setIntegral_traj_partialTraj** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：setIntegral_traj_partialTraj {a b : Nat} (hab : a <= b) {x₀ : (Π i : Iic a
, X i)} {f : (Π n : Nat, X n) -> E} (hf : Integrable f (traj κ a x₀)) {A : Set (
Π i : Iic b, X i)} (hA : MeasurableSet A) : ∫ x in A, ∫ y, f y ∂traj κ b x ∂part
ialTraj κ a b x₀ = ∫ y in frestrictLe b ⁻¹' A, f y ∂traj κ a x₀
参数：hab : a <= b；Π i : Iic a, X i；Π n : Nat, X n；hf : Integrable f (traj κ a x₀)；
Π i : Iic b, X i；hA : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.setIntegral_traj_partialTraj'`：setIntegral_traj
_partialTraj' {a b : Nat} (hab : a <= b) {u : (Π i : Iic a, X i)} {f : (Π i : Ii
c b, X i) -> (Π n : Nat, X n) -> E} (hf : In…
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `ProbabilityTheory.Kernel.traj_comp_partialTraj`：traj_comp_partialTraj {a
 b : Nat} (hab : a <= b) : (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem setIntegral_traj_partialTraj {a b : ℕ} (hab : a ≤ b) {x₀ : (Π i : Iic a, X i)}
    {f : (Π n : ℕ, X n) → E} (hf : Integrable f (traj κ a x₀))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f y ∂traj κ b x ∂partialTraj κ a b x₀ =
      ∫ y in frestrictLe b ⁻¹' A, f y ∂traj κ a x₀ := by
  refine setIntegral_traj_partialTraj' hab ?_ hA
  rw [← traj_comp_partialTraj hab, comp_apply, ← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

variable [CompleteSpace E]

open Filtration
/-
**ProbabilityTheory.Kernel.condExp_traj** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：condExp_traj {a b : Nat} (hab : a <= b) {x₀ : Π i : Iic a, X i} {f : (Π n,
 X n) -> E} (i_f : Integrable f (traj κ a x₀)) : (traj κ a x₀)[f | piLE b] =ᵐ[tr
aj κ a x₀] fun x => ∫ y, f y ∂traj κ b (frestrictLe b x)
参数：hab : a <= b；Π n, X n；i_f : Integrable f (traj κ a x₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用定理 `MeasureTheory.Integrable.integral_comp`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} 
  {mγ : MeasurableSpace γ} […
· 使用定理 `ProbabilityTheory.Kernel.traj_comp_partialTraj`：traj_comp_partialTraj {a
 b : Nat} (hab : a <= b) : (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.comp_aemeasurable`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `MeasureTheory.Filtration.piLE_eq_comap_frestrictLe`：piLE_eq_comap_frestr
ictLe (i : ι) : piLE (X
· 使用定理 `MeasureTheory.setIntegral_map`：setIntegral_map {Y} [MeasurableSpace Y] {
g : X -> Y} {f : Y -> E} {s : Set Y} (hs : MeasurableSet s) (hf : AEStronglyMeas
urable f (Measure.m…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.Kernel.setIntegral_traj_partialTraj`：setIntegral_traj_
partialTraj {a b : Nat} (hab : a <= b) {x₀ : (Π i : Iic a, X i)} {f : (Π n : Nat
, X n) -> E} (hf : Integrable f (traj κ a x…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_ae_measurable'`：∀ {α : Type u_1}
 {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] {mα : MeasurableSpace
 α}   {x : MeasurableSpace γ} {f : α → β} {μ…
-/
theorem condExp_traj {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π n, X n) → E} (i_f : Integrable f (traj κ a x₀)) :
    (traj κ a x₀)[f | piLE b] =ᵐ[traj κ a x₀]
      fun x ↦ ∫ y, f y ∂traj κ b (frestrictLe b x) := by
  have i_f' : Integrable (fun x ↦ ∫ y, f y ∂(traj κ b) x)
      (((traj κ a) x₀).map (frestrictLe b)) := by
    rw [← map_apply _ (measurable_frestrictLe _), traj_map_frestrictLe _ _]
    rw [← traj_comp_partialTraj hab] at i_f
    exact i_f.integral_comp
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le _) i_f
    (fun s _ _ ↦ i_f'.comp_aemeasurable (measurable_frestrictLe b).aemeasurable |>.integrableOn)
    ?_ ?_ |>.symm <;> rw [piLE_eq_comap_frestrictLe]
  · rintro - ⟨t, mt, rfl⟩ -
    simp_rw [Function.comp_apply]
    rw [← setIntegral_map mt i_f'.1, ← map_apply, traj_map_frestrictLe,
      setIntegral_traj_partialTraj hab i_f mt]
    all_goals fun_prop
  · exact (i_f'.1.comp_ae_measurable' (measurable_frestrictLe b).aemeasurable)
/-
**ProbabilityTheory.Kernel.condExp_traj'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：condExp_traj' {a b c : Nat} (hab : a <= b) (hbc : b <= c) (x₀ : Π i : Iic 
a, X i) (f : (Π n, X n) -> E) : (traj κ a x₀)[f | piLE b] =ᵐ[traj κ a x₀] fun x 
=> ∫ y, ((traj κ a x₀)[f | piLE c]) (updateFinset x (Iic c) y) ∂partialTraj κ b 
c (frestrictLe b x)
参数：hab : a <= b；hbc : b <= c；x₀ : Π i : Iic a, X i；f : (Π n, X n) -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.condExp_traj`：condExp_traj {a b : Nat} (hab : a
 <= b) {x₀ : Π i : Iic a, X i} {f : (Π n, X n) -> E} (i_f : Integrable f (traj κ
 a x₀)) : (traj κ a x₀)[f |…
· 使用定理 `MeasureTheory.Filtration.condExp_condExp`：∀ {Ω : Type u_1} {ι : Type u_2
} {m : MeasurableSpace Ω} [inst : Preorder ι] {E : Type u_3}   [inst_1 : NormedA
ddCommGroup E] [inst_2 : Norme…
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicForal
lTraj`：∀ {X : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.StronglyMeasurable.dependsOn_of_piLE`：∀ {Z : Type u_3} {ι 
: Type u_4} {X : ι → Type u_5} [inst : (i : ι) → MeasurableSpace (X i)] {f : ((i
 : ι) → X i) → Z}   [inst_1 : Preorder ι…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
（共 35 条，此处仅展示前 30 条）
-/
theorem condExp_traj' {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (x₀ : Π i : Iic a, X i) (f : (Π n, X n) → E) :
    (traj κ a x₀)[f | piLE b] =ᵐ[traj κ a x₀]
      fun x ↦ ∫ y, ((traj κ a x₀)[f | piLE c]) (updateFinset x (Iic c) y)
        ∂partialTraj κ b c (frestrictLe b x) := by
  have i_cf : Integrable ((traj κ a x₀)[f | piLE c]) (traj κ a x₀) :=
    integrable_condExp
  have mcf : StronglyMeasurable ((traj κ a x₀)[f | piLE c]) :=
    stronglyMeasurable_condExp.mono (piLE.le c)
  filter_upwards [piLE.condExp_condExp f hbc, condExp_traj hab i_cf] with x h1 h2
  rw [← h1, h2, ← traj_map_frestrictLe, Kernel.map_apply, integral_map]
  · congr with y
    apply stronglyMeasurable_condExp.dependsOn_of_piLE
    simp only [Set.mem_Iic, updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite]
    exact fun i hi ↦ (if_pos hi).symm
  any_goals fun_prop
  exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable

end integral

section trajMeasure

/-- Distribution of the trajectory obtained by starting with `μ₀` and iterating the kernels `κ`. -/
noncomputable
/-
**ProbabilityTheory.Kernel.trajMeasure** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：trajMeasure (μ₀ : Measure (X 0)) (κ : (n : Nat) -> Kernel (Π i : Iic n, X 
i) (X (n + 1))) [forall n, IsMarkovKernel (κ n)] : Measure (Π n, X n)
参数：μ₀ : Measure (X 0)；κ : (n : Nat) -> Kernel (Π i : Iic n, X i) (X (n + 1))；κ n
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def trajMeasure (μ₀ : Measure (X 0)) (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] :
    Measure (Π n, X n) :=
  (traj κ 0) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm)

variable {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]

set_option backward.isDefEq.respectTransparency false in
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure (trajMeasure μ₀ κ) := by
  rw [trajMeasure]
  have : IsProbabilityMeasure (μ₀.map (MeasurableEquiv.piUnique ((fun i : Iic 0 ↦ X i))).symm) :=
    Measure.isProbabilityMeasure_map <| by fun_prop
  infer_instance
/-
**ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasu
re** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure {a : Nat} : (trajM
easure μ₀ κ).map (frestrictLe a) otimesₘ κ a = (trajMeasure μ₀ κ).map (fun x => 
(frestrictLe a x, x (a + 1)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
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
· 使用定理 `ProbabilityTheory.Kernel.instIsProbabilityMeasureForallTrajMeasure`：∀ {X
 : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n : ℕ) → Proba
bilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.trajMeasure.eq_1`：∀ {X : ℕ → Type u_1} [inst : 
(n : ℕ) → MeasurableSpace (X n)] (μ₀ : MeasureTheory.Measure (X 0))   (κ : (n : 
ℕ) → ProbabilityTheory.Kernel (…
· 使用引理 `MeasureTheory.Measure.map_comp`：map_comp (μ : Measure α) (κ : Kernel α β
) {f : β -> γ} (hf : Measurable f) : (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用引理 `ProbabilityTheory.Kernel.traj_map_frestrictLe`：traj_map_frestrictLe (a b
 : Nat) : (traj κ a).map (frestrictLe b) = partialTraj κ a b
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_compProd_eq_map_traj`：partialTraj_c
ompProd_eq_map_traj {a b : Nat} (hab : a <= b) {x₀ : Π n : Iic a, X n} : (partia
lTraj κ a b x₀) otimesₘ (κ b) = (traj κ a x₀).m…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure {a : ℕ} :
    (trajMeasure μ₀ κ).map (frestrictLe a) ⊗ₘ κ a =
      (trajMeasure μ₀ κ).map (fun x ↦ (frestrictLe a x, x (a + 1))) := by
  rw [Measure.compProd_eq_comp_prod, trajMeasure, Measure.map_comp _ _ (by fun_prop),
    traj_map_frestrictLe, Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [comp_apply, ← Measure.compProd_eq_comp_prod, map_apply _ (by fun_prop),
    partialTraj_compProd_eq_map_traj zero_le]

/-- A regular conditional probability distribution of the point at time `a + 1` given the
trajectory up to time `a` corresponds to the kernel `κ a`. -/
/-
**ProbabilityTheory.Kernel.condDistrib_trajMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：condDistrib_trajMeasure {a : Nat} [StandardBorelSpace (X (a + 1))] [Nonemp
ty (X (a + 1))] : condDistrib (fun x => x (a + 1)) (frestrictLe a) (trajMeasure 
μ₀ κ) =ᵐ[(trajMeasure μ₀ κ).map (frestrictLe a)] κ a
参数：X (a + 1)；X (a + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
`：condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hX : Measurable X) (hY
 : Measurable Y) {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.m…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.Kernel.instIsProbabilityMeasureForallTrajMeasure`：∀ {X
 : ℕ → Type u_1} [inst : (n : ℕ) → MeasurableSpace (X n)]   {κ : (n : ℕ) → Proba
bilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n…
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_tra
jMeasure`：map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure {a : Nat} : (t
rajMeasure μ₀ κ).map (frestrictLe a) otimesₘ κ a = (trajMeasure μ₀ κ).…

--- 原说明 ---
A regular conditional probability distribution of the point at time `a + 1` give
n the
trajectory up to time `a` corresponds to the kernel `κ a`.
-/
lemma condDistrib_trajMeasure {a : ℕ} [StandardBorelSpace (X (a + 1))] [Nonempty (X (a + 1))] :
    condDistrib (fun x ↦ x (a + 1)) (frestrictLe a) (trajMeasure μ₀ κ)
      =ᵐ[(trajMeasure μ₀ κ).map (frestrictLe a)] κ a := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
  exact map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

end trajMeasure

end ProbabilityTheory.Kernel

