/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Marginals of multivariate functions

In this file, we define a convenient way to compute integrals of multivariate functions, especially
if you want to write expressions where you integrate only over some of the variables that the
function depends on. This is common in induction arguments involving integrals of multivariate
functions.
This constructions allows working with iterated integrals and applying Tonelli's theorem
and Fubini's theorem, without using measurable equivalences by changing the representation of your
space (e.g. `((ι ⊕ ι') → ℝ) ≃ (ι → ℝ) × (ι' → ℝ)`).

## Main Definitions

* Assume that `∀ i : ι, X i` is a product of measurable spaces with measures `μ i` on `X i`,
  `f : (∀ i, X i) → ℝ≥0∞` is a function and `s : Finset ι`.
  Then `lmarginal μ s f` or `∫⋯∫⁻_s, f ∂μ` is the function that integrates `f`
  over all variables in `s`. It returns a function that still takes the same variables as `f`,
  but is constant in the variables in `s`. Mathematically, if `s = {i₁, ..., iₖ}`,
  then `lmarginal μ s f` is the expression
  $$
  \vec{x}\mapsto \int\!\!\cdots\!\!\int f(\vec{x}[\vec{y}])dy_{i_1}\cdots dy_{i_k}.
  $$
  where $\vec{x}[\vec{y}]$ is the vector $\vec{x}$ with $x_{i_j}$ replaced by $y_{i_j}$ for all
  $1 \le j \le k$.
  If `f` is the distribution of a random variable, this is the marginal distribution of all
  variables not in `s` (but not the most general notion, since we only consider product measures
  here).
  Note that the notation `∫⋯∫⁻_s, f ∂μ` is not a binder, and returns a function.

## Main Results

* `lmarginal_union` is the analogue of Tonelli's theorem for iterated integrals. It states that
  for measurable functions `f` and disjoint finsets `s` and `t` we have
  `∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ`.

## Implementation notes

The function `f` can have an arbitrary product as its domain (even infinite products), but the
set `s` of integration variables is a `Finset`. We are assuming that the function `f` is measurable
for most of this file. Note that asking whether it is `AEMeasurable` is not even well-posed,
since there is no well-behaved measure on the domain of `f`.

## TODO

* Define the marginal function for functions taking values in a Banach space.

-/

@[expose] public section


open scoped ENNReal
open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

section LMarginal

variable {δ δ' : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [DecidableEq δ]
variable {s t : Finset δ} {f : (∀ i, X i) → ℝ≥0∞} {x : ∀ i, X i}

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s` when the considered measure
  is the product measure. -/
/-
**MeasureTheory.lmarginal** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal (μ : forall i, Measure (X i)) (s : Finset δ) (f : (forall i, X i
) -> Real>=0∞) (x : forall i, X i) : Real>=0∞
参数：μ : forall i, Measure (X i)；s : Finset δ；f : (forall i, X i) -> Real>=0∞；x : 
forall i, X i。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function 
in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s` when the conside
red measure
  is the product measure.
-/
def lmarginal (μ : ∀ i, Measure (X i)) (s : Finset δ) (f : (∀ i, X i) → ℝ≥0∞)
    (x : ∀ i, X i) : ℝ≥0∞ :=
  ∫⁻ y : ∀ i : s, X i, f (updateFinset x s y) ∂Measure.pi fun i : s => μ i

-- Note: this notation is not a binder. This is more convenient since it returns a function.
@[inherit_doc]
notation "∫⋯∫⁻_" s ", " f " ∂" μ:70 => lmarginal μ s f

@[inherit_doc lmarginal]
notation3 "∫⋯∫⁻_" s ", " f => lmarginal (fun _ ↦ volume) s f

variable (μ)
/-
**MeasureTheory._root_.Measurable.lmarginal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Measurable.lmarginal [∀ i, SigmaFinite (μ i)] (hf : Measurable f) :
    Measurable (∫⋯∫⁻_s, f ∂μ) :=
  Measurable.lintegral_prod_right (hf.comp measurable_updateFinset')
/-
**MeasureTheory.lmarginal_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {δ : Type u_1} {X : δ → Type u_3} [inst : (i : δ) → MeasurableSpace (X i
)] (μ : (i : δ) → MeasureTheory.Measure (X i))   [inst_1 : DecidableEq δ] (f : (
(i : δ) → X i) → ENNReal), ∫⋯∫⁻_∅, f ∂μ = f
参数：i : δ；X i；μ : (i : δ) → MeasureTheory.Measure (X i)；f : ((i : δ) → X i) → ENN
Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_of_empty`：pi_of_empty {α : Type*} [Fintype α] [
IsEmpty α] {β : α -> Type*} {m : forall a, MeasurableSpace (β a)} (μ : forall a 
: α, Measure (β a)) (x …
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `Subsingleton.measurable`：Subsingleton.measurable [Subsingleton α] : Meas
urable f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
@[simp] theorem lmarginal_empty (f : (∀ i, X i) → ℝ≥0∞) : ∫⋯∫⁻_∅, f ∂μ = f := by
  ext1 x
  simp_rw [lmarginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable

/-- The marginal distribution is independent of the variables in `s`. -/
/-
**MeasureTheory.lmarginal_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_congr {x y : forall i, X i} (f : (forall i, X i) -> Real>=0∞) (h
 : forall i ∉ s, x i = y i) : (∫⋯∫⁻_s, f ∂μ) x = (∫⋯∫⁻_s, f ∂μ) y
参数：f : (forall i, X i) -> Real>=0∞；h : forall i ∉ s, x i = y i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)

--- 原说明 ---
The marginal distribution is independent of the variables in `s`.
-/
theorem lmarginal_congr {x y : ∀ i, X i} (f : (∀ i, X i) → ℝ≥0∞)
    (h : ∀ i ∉ s, x i = y i) :
    (∫⋯∫⁻_s, f ∂μ) x = (∫⋯∫⁻_s, f ∂μ) y := by
  dsimp [lmarginal, updateFinset_def]; rcongr; exact h _ ‹_›
/-
**MeasureTheory.lmarginal_update_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：lmarginal_update_of_mem {i : δ} (hi : i in s) (f : (forall i, X i) -> Real
>=0∞) (x : forall i, X i) (y : X i) : (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (
∫⋯∫⁻_s, f ∂μ) x
参数：hi : i in s；f : (forall i, X i) -> Real>=0∞；x : forall i, X i；y : X i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lmarginal_update_of_mem {i : δ} (hi : i ∈ s)
    (f : (∀ i, X i) → ℝ≥0∞) (x : ∀ i, X i) (y : X i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∂μ) x := by
  grind [MeasureTheory.lmarginal_congr]

variable {μ} in
/-
**MeasureTheory.lmarginal_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_singleton (f : (forall i, X i) -> Real>=0∞) (i : δ) : ∫⋯∫⁻_{i}, 
f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i
参数：f : (forall i, X i) -> Real>=0∞；i : δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_map_equiv`：∀ {α : Type u_1} {β
 : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : Measur
eTheory.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.measurePreserving_piUnique`：measurePreserving_piUnique {X 
: ι -> Type*} [Unique ι] {m : forall i, MeasurableSpace (X i)} (μ : forall i, Me
asure (X i)) : MeasurePreservi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_eq_updateFinset`：update_eq_updateFinset {y} : Function.u
pdate x i y = updateFinset x {i} (uniqueElim y)
-/
theorem lmarginal_singleton (f : (∀ i, X i) → ℝ≥0∞) (i : δ) :
    ∫⋯∫⁻_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α ↦ X j).symm
  ext1 x
  calc (∫⋯∫⁻_{i}, f ∂μ) x
      = ∫⁻ (y : X (default : α)), f (updateFinset x {i} (e y)) ∂μ (default : α) := by
        simp_rw [lmarginal,
          measurePreserving_piUnique (fun j : ({i} : Finset δ) ↦ μ j) |>.symm _
            |>.lintegral_map_equiv, e, α]
    _ = ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateFinset]; rfl

variable {μ} in
@[gcongr]
/-
**MeasureTheory.lmarginal_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_mono {f g : (forall i, X i) -> Real>=0∞} (hfg : f <= g) : ∫⋯∫⁻_s
, f ∂μ <= ∫⋯∫⁻_s, g ∂μ
参数：forall i, X i；hfg : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
-/
theorem lmarginal_mono {f g : (∀ i, X i) → ℝ≥0∞} (hfg : f ≤ g) : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _

variable [∀ i, SigmaFinite (μ i)]
/-
**MeasureTheory.lmarginal_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_union (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) (hst
 : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ
参数：f : (forall i, X i) -> Real>=0∞；hf : Measurable f；hst : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_map_equiv`：∀ {α : Type u_1} {β
 : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : Measur
eTheory.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.measurePreserving_piFinsetUnion`：measurePreserving_piFinse
tUnion {ι : Type*} {α : ι -> Type*} {_ : forall i, MeasurableSpace (α i)} [Decid
ableEq ι] {s t : Finset ι} (h : Dis…
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Function.updateFinset_updateFinset`：updateFinset_updateFinset (hst : Dis
joint s t) : updateFinset (updateFinset x s y) t z = updateFinset x (s union t) 
(Equiv.piFinsetUnion π h…
-/
theorem lmarginal_union (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f)
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ := by
  ext1 x
  let e := MeasurableEquiv.piFinsetUnion X hst
  calc (∫⋯∫⁻_s ∪ t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s ∪ t)) → X i), f (updateFinset x (s ∪ t) y)
          ∂.pi fun i' : ↥(s ∪ t) ↦ μ i' := rfl
    _ = ∫⁻ (y : ((i : s) → X i) × ((j : t) → X j)), f (updateFinset x (s ∪ t) _)
          ∂(Measure.pi fun i : s ↦ μ i).prod (.pi fun j : t ↦ μ j) := by
        rw [measurePreserving_piFinsetUnion hst μ |>.lintegral_map_equiv]
    _ = ∫⁻ (y : (i : s) → X i), ∫⁻ (z : (j : t) → X j), f (updateFinset x (s ∪ t) (e (y, z)))
          ∂.pi fun j : t ↦ μ j ∂.pi fun i : s ↦ μ i := by
        apply lintegral_prod
        apply Measurable.aemeasurable
        exact hf.comp <| measurable_updateFinset.comp e.measurable
    _ = (∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ) x := by
        simp_rw [lmarginal, updateFinset_updateFinset hst]
        rfl
/-
**MeasureTheory.lmarginal_union'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_union' (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {s 
t : Finset δ} (hst : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_t, ∫⋯∫⁻_s, f ∂μ
 ∂μ
参数：f : (forall i, X i) -> Real>=0∞；hf : Measurable f；hst : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `MeasureTheory.lmarginal_union`：lmarginal_union (f : (forall i, X i) -> R
eal>=0∞) (hf : Measurable f) (hst : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_
s, ∫⋯∫⁻_t, f ∂μ ∂μ
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem lmarginal_union' (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_t, ∫⋯∫⁻_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, lmarginal_union μ f hf hst.symm]

variable {μ}

/-- Peel off a single integral from a `lmarginal` integral at the beginning (compare with
`lmarginal_insert'`, which peels off an integral at the end). -/
/-
**MeasureTheory.lmarginal_insert** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_insert (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i 
: δ} (hi : i ∉ s) (x : forall i, X i) : (∫⋯∫⁻_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻
_s, f ∂μ) (Function.update x i xᵢ) ∂μ i
参数：f : (forall i, X i) -> Real>=0∞；hf : Measurable f；hi : i ∉ s；x : forall i, X 
i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
· 使用定理 `MeasureTheory.lmarginal_union`：lmarginal_union (f : (forall i, X i) -> R
eal>=0∞) (hf : Measurable f) (hst : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_
s, ∫⋯∫⁻_t, f ∂μ ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `MeasureTheory.lmarginal_singleton`：lmarginal_singleton (f : (forall i, X
 i) -> Real>=0∞) (i : δ) : ∫⋯∫⁻_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x
 i xᵢ) ∂μ i

--- 原说明 ---
Peel off a single integral from a `lmarginal` integral at the beginning (compare
 with
`lmarginal_insert'`, which peels off an integral at the end).
-/
theorem lmarginal_insert (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) (x : ∀ i, X i) :
    (∫⋯∫⁻_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq, lmarginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi),
    lmarginal_singleton]

/-- Peel off a single integral from a `lmarginal` integral at the beginning (compare with
`lmarginal_erase'`, which peels off an integral at the end). -/
/-
**MeasureTheory.lmarginal_erase** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_erase (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i :
 δ} (hi : i in s) (x : forall i, X i) : (∫⋯∫⁻_s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_(erase s
 i), f ∂μ) (Function.update x i xᵢ) ∂μ i
参数：f : (forall i, X i) -> Real>=0∞；hf : Measurable f；hi : i in s；x : forall i, X
 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lmarginal.congr_simp`：∀ {δ : Type u_1} {X : δ → Type u_3} 
[inst : (i : δ) → MeasurableSpace (X i)] {inst_1 : DecidableEq δ}   [inst_2 : De
cidableEq δ] (μ μ_1 : (i…
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `MeasureTheory.lmarginal_insert`：lmarginal_insert (f : (forall i, X i) ->
 Real>=0∞) (hf : Measurable f) {i : δ} (hi : i ∉ s) (x : forall i, X i) : (∫⋯∫⁻_
insert i s, f ∂μ) x …
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a

--- 原说明 ---
Peel off a single integral from a `lmarginal` integral at the beginning (compare
 with
`lmarginal_erase'`, which peels off an integral at the end).
-/
theorem lmarginal_erase (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_(erase s i), f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  simpa [insert_erase hi] using lmarginal_insert _ hf (notMem_erase i s) x

/-- Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_insert`, which peels off an integral at the beginning). -/
/-
**MeasureTheory.lmarginal_insert'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_insert' (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i
 : δ} (hi : i ∉ s) : ∫⋯∫⁻_insert i s, f ∂μ = ∫⋯∫⁻_s, (fun x => ∫⁻ xᵢ, f (Functio
n.update x i xᵢ) ∂μ i) ∂μ
参数：f : (forall i, X i) -> Real>=0∞；hf : Measurable f；hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `MeasureTheory.lmarginal_union`：lmarginal_union (f : (forall i, X i) -> R
eal>=0∞) (hf : Measurable f) (hst : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_
s, ∫⋯∫⁻_t, f ∂μ ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `MeasureTheory.lmarginal_singleton`：lmarginal_singleton (f : (forall i, X
 i) -> Real>=0∞) (i : δ) : ∫⋯∫⁻_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x
 i xᵢ) ∂μ i

--- 原说明 ---
Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_insert`, which peels off an integral at the beginning).
-/
theorem lmarginal_insert' (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) :
    ∫⋯∫⁻_insert i s, f ∂μ = ∫⋯∫⁻_s, (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  rw [Finset.insert_eq, Finset.union_comm,
    lmarginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi), lmarginal_singleton]

/-- Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_erase`, which peels off an integral at the beginning). -/
/-
**MeasureTheory.lmarginal_erase'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_erase' (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i 
: δ} (hi : i in s) : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_(erase s i), (fun x => ∫⁻ xᵢ, f (Functi
on.update x i xᵢ) ∂μ i) ∂μ
参数：f : (forall i, X i) -> Real>=0∞；hf : Measurable f；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `MeasureTheory.lmarginal_insert'`：lmarginal_insert' (f : (forall i, X i) 
-> Real>=0∞) (hf : Measurable f) {i : δ} (hi : i ∉ s) : ∫⋯∫⁻_insert i s, f ∂μ = 
∫⋯∫⁻_s, (fun x => ∫⁻ …
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a

--- 原说明 ---
Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_erase`, which peels off an integral at the beginning).
-/
theorem lmarginal_erase' (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) :
    ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_(erase s i), (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  simpa [insert_erase hi] using lmarginal_insert' _ hf (notMem_erase i s)
/-
**MeasureTheory.lmarginal_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {δ : Type u_1} {X : δ → Type u_3} [inst : (i : δ) → MeasurableSpace (X i
)] {μ : (i : δ) → MeasureTheory.Measure (X i)}   [inst_1 : DecidableEq δ] [∀ (i 
: δ), MeasureTheory.SigmaFinite (μ i)] [inst_3 : Fintype δ]   {f : ((i : δ) → X 
i) → ENNReal},   ∫⋯∫⁻_Finset.univ, f ∂μ = fun x => ∫⁻ (x : (i : δ) → X i), f x ∂
MeasureTheory.Measure.pi μ
参数：i : δ；X i；i : δ；X i；i : δ；μ i；(i : δ) → X i；x : (i : δ) → X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_map_equiv`：∀ {α : Type u_1} {β
 : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : Measur
eTheory.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.measurePreserving_piCongrLeft`：measurePreserving_piCongrLe
ft (f : ι' ≃ ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (Measure.p
i fun i' => μ (f i')) (Measure.pi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
@[simp] theorem lmarginal_univ [Fintype δ] {f : (∀ i, X i) → ℝ≥0∞} :
    ∫⋯∫⁻_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [lmarginal, measurePreserving_piCongrLeft μ e |>.lintegral_map_equiv, updateFinset_def]
  simp
  rfl
/-
**MeasureTheory.lintegral_eq_lmarginal_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lintegral_eq_lmarginal_univ [Fintype δ] {f : (forall i, X i) -> Real>=0∞} 
(x : forall i, X i) : ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫⁻_univ, f ∂μ) x
参数：forall i, X i；x : forall i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.lmarginal_univ`：∀ {δ : Type u_1} {X : δ → Type u_3} [inst 
: (i : δ) → MeasurableSpace (X i)] {μ : (i : δ) → MeasureTheory.Measure (X i)}  
 [inst_1 : Decidab…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_eq_lmarginal_univ [Fintype δ] {f : (∀ i, X i) → ℝ≥0∞} (x : ∀ i, X i) :
    ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫⁻_univ, f ∂μ) x := by simp
/-
**MeasureTheory.lmarginal_image** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lmarginal_image [DecidableEq δ'] {e : δ' -> δ} (he : Injective e) (s : Fin
set δ') {f : (forall i, X (e i)) -> Real>=0∞} (hf : Measurable f) (x : forall i,
 X i) : (∫⋯∫⁻_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫⁻_s, f ∂μ ∘' e) (x ∘' e)
参数：he : Injective e；s : Finset δ'；forall i, X (e i)；hf : Measurable f；x : forall
 i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.lmarginal_empty`：∀ {δ : Type u_1} {X : δ → Type u_3} [inst
 : (i : δ) → MeasurableSpace (X i)] (μ : (i : δ) → MeasureTheory.Measure (X i)) 
  [inst_1 : Decidab…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用定理 `MeasureTheory.lmarginal_insert`：lmarginal_insert (f : (forall i, X i) ->
 Real>=0∞) (hf : Measurable f) {i : δ} (hi : i ∉ s) (x : forall i, X i) : (∫⋯∫⁻_
insert i s, f ∂μ) x …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Function.Injective.mem_finset_image`：∀ {α : Type u_1} {β : Type u_2} [in
st : DecidableEq β] {f : α → β} {s : Finset α} {a : α},   Function.Injective f →
 (f a ∈ Finset.image f s …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lmarginal.congr_simp`：∀ {δ : Type u_1} {X : δ → Type u_3} 
[inst : (i : δ) → MeasurableSpace (X i)] {inst_1 : DecidableEq δ}   [inst_2 : De
cidableEq δ] (μ μ_1 : (i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_comp_eq_of_injective'`：update_comp_eq_of_injective' (g :
 forall a, β a) {f : α' -> α} (hf : Function.Injective f) (i : α') (a : β (f i))
 : (fun j => update g (f i)…
-/
theorem lmarginal_image [DecidableEq δ'] {e : δ' → δ} (he : Injective e) (s : Finset δ')
    {f : (∀ i, X (e i)) → ℝ≥0∞} (hf : Measurable f) (x : ∀ i, X i) :
      (∫⋯∫⁻_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫⁻_s, f ∂μ ∘' e) (x ∘' e) := by
  have h : Measurable ((· ∘' e) : (∀ i, X i) → _) :=
    measurable_pi_iff.mpr <| fun i ↦ measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert _ _ hi ih =>
    rw [image_insert, lmarginal_insert _ (hf.comp h) (he.mem_finset_image.not.mpr hi),
      lmarginal_insert _ hf hi]
    simp_rw [ih, ← update_comp_eq_of_injective' x he]
/-
**MeasureTheory.lmarginal_update_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lmarginal_update_of_notMem {i : δ} {f : (forall i, X i) -> Real>=0∞} (hf :
 Measurable f) (hi : i ∉ s) (x : forall i, X i) (y : X i) : (∫⋯∫⁻_s, f ∂μ) (Func
tion.update x i y) = (∫⋯∫⁻_s, f ∘ (Function.update · i y) ∂μ) x
参数：forall i, X i；hf : Measurable f；hi : i ∉ s；x : forall i, X i；y : X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.lmarginal_empty`：∀ {δ : Type u_1} {X : δ → Type u_3} [inst
 : (i : δ) → MeasurableSpace (X i)] (μ : (i : δ) → MeasureTheory.Measure (X i)) 
  [inst_1 : Decidab…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lmarginal_insert`：lmarginal_insert (f : (forall i, X i) ->
 Real>=0∞) (hf : Measurable f) {i : δ} (hi : i ∉ s) (x : forall i, X i) : (∫⋯∫⁻_
insert i s, f ∂μ) x …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_update_left`：measurable_update_left {a : δ} [DecidableEq δ] {
x : X a} : Measurable (update · a x)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lmarginal.congr_simp`：∀ {δ : Type u_1} {X : δ → Type u_3} 
[inst : (i : δ) → MeasurableSpace (X i)] {inst_1 : DecidableEq δ}   [inst_2 : De
cidableEq δ] (μ μ_1 : (i…
· 使用定理 `Function.update_comm`：update_comm {α} [DecidableEq α] {β : α -> Sort*} {
a b : α} (h : a != b) (v : β a) (w : β b) (f : forall a, β a) : update (update f
 a v) b w …
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem lmarginal_update_of_notMem {i : δ}
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) (hi : i ∉ s) (x : ∀ i, X i) (y : X i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∘ (Function.update · i y) ∂μ) x := by
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert i' s hi' ih =>
    rw [lmarginal_insert _ hf hi', lmarginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i ≠ i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_comm hii', ih (mt Finset.mem_insert_of_mem hi)]
/-
**MeasureTheory.lmarginal_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lmarginal_eq_of_subset {f g : (forall i, X i) -> Real>=0∞} (hst : s subset
eq t) (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ
) : ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_t, g ∂μ
参数：forall i, X i；hst : s subseteq t；hf : Measurable f；hg : Measurable g；hfg : ∫⋯
∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.union_sdiff_of_subset`：union_sdiff_of_subset (h : s subseteq t) :
 s union t \ s = t
· 使用定理 `MeasureTheory.lmarginal_union'`：lmarginal_union' (f : (forall i, X i) ->
 Real>=0∞) (hf : Measurable f) {s t : Finset δ} (hst : Disjoint s t) : ∫⋯∫⁻_s un
ion t, f ∂μ = ∫⋯∫⁻_t…
· 使用定理 `Finset.disjoint_sdiff`：disjoint_sdiff : Disjoint s (t \ s)
-/
theorem lmarginal_eq_of_subset {f g : (∀ i, X i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, lmarginal_union' μ f hf disjoint_sdiff,
    lmarginal_union' μ g hg disjoint_sdiff, hfg]
/-
**MeasureTheory.lmarginal_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lmarginal_le_of_subset {f g : (forall i, X i) -> Real>=0∞} (hst : s subset
eq t) (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂
μ) : ∫⋯∫⁻_t, f ∂μ <= ∫⋯∫⁻_t, g ∂μ
参数：forall i, X i；hst : s subseteq t；hf : Measurable f；hg : Measurable g；hfg : ∫⋯
∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.union_sdiff_of_subset`：union_sdiff_of_subset (h : s subseteq t) :
 s union t \ s = t
· 使用定理 `MeasureTheory.lmarginal_union'`：lmarginal_union' (f : (forall i, X i) ->
 Real>=0∞) (hf : Measurable f) {s t : Finset δ} (hst : Disjoint s t) : ∫⋯∫⁻_s un
ion t, f ∂μ = ∫⋯∫⁻_t…
· 使用定理 `Finset.disjoint_sdiff`：disjoint_sdiff : Disjoint s (t \ s)
· 使用定理 `MeasureTheory.lmarginal_mono`：lmarginal_mono {f g : (forall i, X i) -> R
eal>=0∞} (hfg : f <= g) : ∫⋯∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂μ
-/
theorem lmarginal_le_of_subset {f g : (∀ i, X i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ ≤ ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, lmarginal_union' μ f hf disjoint_sdiff,
    lmarginal_union' μ g hg disjoint_sdiff]
  exact lmarginal_mono hfg
/-
**MeasureTheory.lintegral_eq_of_lmarginal_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：lintegral_eq_of_lmarginal_eq [Fintype δ] (s : Finset δ) {f g : (forall i, 
X i) -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = 
∫⋯∫⁻_s, g ∂μ) : ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, g x ∂Measure.pi μ
参数：s : Finset δ；forall i, X i；hf : Measurable f；hg : Measurable g；hfg : ∫⋯∫⁻_s, 
f ∂μ = ∫⋯∫⁻_s, g ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_of_isEmpty`：lintegral_of_isEmpty {α} [Measurable
Space α] [IsEmpty α] (μ : Measure α) (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_eq_lmarginal_univ`：lintegral_eq_lmarginal_univ [
Fintype δ] {f : (forall i, X i) -> Real>=0∞} (x : forall i, X i) : ∫⁻ x, f x ∂Me
asure.pi μ = (∫⋯∫⁻_univ, f ∂μ) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.lmarginal_eq_of_subset`：lmarginal_eq_of_subset {f g : (for
all i, X i) -> Real>=0∞} (hst : s subseteq t) (hf : Measurable f) (hg : Measurab
le g) (hfg : ∫⋯∫⁻_s, f ∂μ …
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
theorem lintegral_eq_of_lmarginal_eq [Fintype δ] (s : Finset δ) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]
/-
**MeasureTheory.lintegral_le_of_lmarginal_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：lintegral_le_of_lmarginal_le [Fintype δ] (s : Finset δ) {f g : (forall i, 
X i) -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ <=
 ∫⋯∫⁻_s, g ∂μ) : ∫⁻ x, f x ∂Measure.pi μ <= ∫⁻ x, g x ∂Measure.pi μ
参数：s : Finset δ；forall i, X i；hf : Measurable f；hg : Measurable g；hfg : ∫⋯∫⁻_s, 
f ∂μ <= ∫⋯∫⁻_s, g ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_of_isEmpty`：lintegral_of_isEmpty {α} [Measurable
Space α] [IsEmpty α] (μ : Measure α) (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.lintegral_eq_lmarginal_univ`：lintegral_eq_lmarginal_univ [
Fintype δ] {f : (forall i, X i) -> Real>=0∞} (x : forall i, X i) : ∫⁻ x, f x ∂Me
asure.pi μ = (∫⋯∫⁻_univ, f ∂μ) …
· 使用定理 `MeasureTheory.lmarginal_le_of_subset`：lmarginal_le_of_subset {f g : (for
all i, X i) -> Real>=0∞} (hst : s subseteq t) (hf : Measurable f) (hg : Measurab
le g) (hfg : ∫⋯∫⁻_s, f ∂μ …
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
theorem lintegral_le_of_lmarginal_le [Fintype δ] (s : Finset δ) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ ≤ ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

end LMarginal

end MeasureTheory

