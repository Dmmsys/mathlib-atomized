/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!

# Almost everywhere equal functions

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `Mathlib/MeasureTheory/Function/L1Space/AEEqFun.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` is a measurable space, `β` is a topological
  space, and `μ` is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`.
  In comments, `[f]` is also used to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.

## Main statements

* The linear structure of `L⁰` :
  Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
  `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
  of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

  See `mk_add_mk`, `neg_mk`, `mk_sub`, `smul_mk`,
  `coeFn_add`, `coeFn_neg`, `coeFn_sub`, `coeFn_smul`

* The order structure of `L⁰` :
  `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
  And `α →ₘ β` inherits the preorder and partial order of `β`.

  TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
  linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.cast`: To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.toFun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `AEEqFun.mk`: To construct an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`: Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `compMeasurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`: Use `comp₂ g f₁ f₂` to get `[fun a ↦ g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

@[expose] public section

-- Guard against import creep
assert_not_exists InnerProductSpace

noncomputable section

open Topology Set Filter TopologicalSpace ENNReal EMetric MeasureTheory Function

variable {α β γ δ : Type*} [MeasurableSpace α] {μ ν : Measure α}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]
variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
@[instance_reducible]
/--
Definition of `Measure.aeEqSetoid` / `Measure.aeEqSetoid` 的定义

English:
definition Measure.aeEqSetoid
  signature: (μ : Measure α)
  body: ⟨fun f g => (f : α -> β) =ᵐ[μ] g, fun {f} => ae_eq_refl f.val, fun {_ _} => ae_eq_symm,
    fun {_ _ _} => ae_eq_trans⟩

中文:
定义 测度.aeEqSetoid
  签名: (μ : 测度 α)
  定义体: ⟨fun f g => (f : α -> β) =ᵐ[μ] g, fun {f} => ae_eq_refl f.val, fun {_ _} => ae_eq_symm,
    fun {_ _ _} => ae_eq_trans⟩

Depends on / 依赖: ae_eq_refl, ae_eq_symm, ae_eq_trans, f.val
-/
def Measure.aeEqSetoid (μ : Measure α) : Setoid { f : α -> β // AEStronglyMeasurable f μ } :=
  ⟨fun f g => (f : α -> β) =ᵐ[μ] g, fun {f} => ae_eq_refl f.val, fun {_ _} => ae_eq_symm,
    fun {_ _ _} => ae_eq_trans⟩

variable (α)

/--
Definition of `AEEqFun` / `AEEqFun` 的定义

English:
definition AEEqFun
  signature: (μ : Measure α)
  body: Quotient (μ.aeEqSetoid β)

中文:
定义 AEEqFun
  签名: (μ : 测度 α)
  定义体: Quotient (μ.aeEqSetoid β)

Depends on / 依赖: Quotient, aeEqSetoid
-/
def AEEqFun (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid β)

variable {α β}

@[inherit_doc MeasureTheory.AEEqFun]
notation:25 α " ->ₘ[" μ "] " β => AEEqFun α β μ

end MeasurableSpace

variable [TopologicalSpace δ]

namespace AEEqFun

section
variable [TopologicalSpace β]

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {β : Type*} [TopologicalSpace β] (f : α -> β) (hf : AEStronglyMeasurable f μ)
  body: Quotient.mk'' ⟨f, hf⟩

中文:
定义 mk
  签名: {β : 类型} [拓扑空间 β] (f : α -> β) (hf : AEStronglyMeasurable f μ)
  定义体: Quotient.mk'' ⟨f, hf⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk {β : Type*} [TopologicalSpace β] (f : α -> β) (hf : AEStronglyMeasurable f μ) : α ->ₘ[μ] β :=
  Quotient.mk'' ⟨f, hf⟩

open scoped Classical in
/-- Coercion from a space of equivalence classes of almost everywhere strongly measurable
functions to functions. We ensure that if `f` has a constant representative,
then we choose that one. -/
@[coe]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: (f : α ->ₘ[μ] β)
  body: if h : exists (b : β), f = mk (const α b) aestronglyMeasurable_const then
const α Classical.choose h else
    AEStronglyMeasurable.mk _ (Quotient.out f : { f : α -> β // AEStronglyMeasurable f μ }).2

中文:
定义 cast
  签名: (f : α ->ₘ[μ] β)
  定义体: if h : exists (b : β), f = mk (const α b) aestronglyMeasurable_const then
const α Classical.choose h else
    AEStronglyMeasurable.mk _ (Quotient.out f : { f : α -> β // AEStronglyMeasurable f μ }).2

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.mk, Classical, Classical.choose, Quotient, Quotient.out, aestronglyMeasurable_const
-/
def cast (f : α ->ₘ[μ] β) : α -> β :=
  if h : exists (b : β), f = mk (const α b) aestronglyMeasurable_const then
const α Classical.choose h else
    AEStronglyMeasurable.mk _ (Quotient.out f : { f : α -> β // AEStronglyMeasurable f μ }).2

/--
Instance `instCoeFun` / 实例 `instCoeFun`

English:
instance instCoeFun
  signature: : CoeFun (α ->ₘ[μ] β) fun _ => α -> β
  body: ⟨cast⟩

@[fun_prop]

中文:
实例 instCoeFun
  签名: : CoeFun (α ->ₘ[μ] β) fun _ => α -> β
  定义体: ⟨cast⟩

@[fun_prop]
-/
instance instCoeFun : CoeFun (α ->ₘ[μ] β) fun _ => α -> β := ⟨cast⟩

@[fun_prop]
/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: (f : α ->ₘ[μ] β)
  statement: StronglyMeasurable f
  proof: by
  simp only [cast]
  split_ifs with h
  · exact stronglyMeasurable_const
  · apply AEStronglyMeasurable.stronglyMeasurable_mk

@[fun_prop]

中文:
定理 stronglyMeasurable
  条件: (f : α ->ₘ[μ] β)
  结论: StronglyMeasurable f
  证明: by
  simp only [cast]
  split_ifs with h
  · exact stronglyMeasurable_const
  · apply AEStronglyMeasurable.stronglyMeasurable_mk

@[fun_prop]
-/
protected theorem stronglyMeasurable (f : α ->ₘ[μ] β) : StronglyMeasurable f := by
  simp only [cast]
  split_ifs with h
  · exact stronglyMeasurable_const
  · apply AEStronglyMeasurable.stronglyMeasurable_mk

@[fun_prop]
/--
theorem `aestronglyMeasurable` / 定理 `aestronglyMeasurable`

English:
theorem aestronglyMeasurable
  given: (f : α ->ₘ[μ] β)
  statement: AEStronglyMeasurable f μ
  proof: f.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]

中文:
定理 aestronglyMeasurable
  条件: (f : α ->ₘ[μ] β)
  结论: AEStronglyMeasurable f μ
  证明: f.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]
-/
protected theorem aestronglyMeasurable (f : α ->ₘ[μ] β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]
/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  statement: [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  proof: f.stronglyMeasurable.measurable

@[fun_prop]

中文:
定理 measurable
  结论: [PseudoMetrizable空间 β] [可测空间 β] [Borel空间 β]
  证明: f.stronglyMeasurable.measurable

@[fun_prop]
-/
protected theorem measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α ->ₘ[μ] β) : Measurable f :=
  f.stronglyMeasurable.measurable

@[fun_prop]
/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  statement: [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  proof: f.measurable.aemeasurable

@[simp]

中文:
定理 aemeasurable
  结论: [PseudoMetrizable空间 β] [可测空间 β] [Borel空间 β]
  证明: f.measurable.aemeasurable

@[simp]
-/
protected theorem aemeasurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α ->ₘ[μ] β) : AEMeasurable f μ :=
  f.measurable.aemeasurable

@[simp]
/--
theorem `quot_mk_eq_mk` / 定理 `quot_mk_eq_mk`

English:
theorem quot_mk_eq_mk
  given: (f : α -> β) (hf)
  proof: rfl

@[simp]

中文:
定理 quot_mk_eq_mk
  条件: (f : α -> β) (hf)
  证明: rfl

@[simp]
-/
theorem quot_mk_eq_mk (f : α -> β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid β) ⟨f, hf⟩ : α ->ₘ[μ] β) = mk f hf :=
  rfl

@[simp]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {f g : α -> β} {hf hg}
  statement: (mk f hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g
  proof: Quotient.eq''

@[simp]

中文:
定理 mk_eq_mk
  条件: {f g : α -> β} {hf hg}
  结论: (mk f hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g
  证明: Quotient.eq''

@[simp]

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem mk_eq_mk {f g : α -> β} {hf hg} : (mk f hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotient.eq''

@[simp]
/--
theorem `mk_coeFn` / 定理 `mk_coeFn`

English:
theorem mk_coeFn
  given: (f : α ->ₘ[μ] β)
  statement: mk f f.aestronglyMeasurable = f
  proof: by
  conv_lhs => simp only [cast]
  split_ifs with h
.symm · exact Classical.choose_spec h
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk]; rw [mk_eq_mk]
  exact (AEStronglyMeasurable.ae_eq_mk _).symm

@[ext]

中文:
定理 mk_coeFn
  条件: (f : α ->ₘ[μ] β)
  结论: mk f f.aestronglyMeasurable = f
  证明: by
  conv_lhs => simp only [cast]
  split_ifs with h
.symm · exact Classical.choose_spec h
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk]; rw [mk_eq_mk]
  exact (AEStronglyMeasurable.ae_eq_mk _).symm

@[ext]

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.ae_eq_mk, Classical, Classical.choose_spec, Quotient, Quotient.out_eq, ae_eq_mk, choose_spec, conv_lhs, conv_rhs, mk_eq_mk, out_eq, split_ifs
-/
theorem mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestronglyMeasurable = f := by
  conv_lhs => simp only [cast]
  split_ifs with h
.symm · exact Classical.choose_spec h
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk]; rw [mk_eq_mk]
  exact (AEStronglyMeasurable.ae_eq_mk _).symm

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g)
  statement: f = g
  proof: by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]

中文:
定理 ext
  条件: {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g)
  结论: f = g
  证明: by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]

Depends on / 依赖: f.mk_coeFn, g.mk_coeFn, mk_coeFn, mk_eq_mk
-/
theorem ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]

/--
theorem `coeFn_mk` / 定理 `coeFn_mk`

English:
theorem coeFn_mk
  given: (f : α -> β) (hf)
  statement: (mk f hf : α ->ₘ[μ] β) =ᵐ[μ] f
  proof: by
  rw [← mk_eq_mk (hf := AEEqFun.aestronglyMeasurable ..) (hg := hf)]; rw [mk_coeFn]

@[elab_as_elim]

中文:
定理 coeFn_mk
  条件: (f : α -> β) (hf)
  结论: (mk f hf : α ->ₘ[μ] β) =ᵐ[μ] f
  证明: by
  rw [← mk_eq_mk (hf := AEEqFun.aestronglyMeasurable ..) (hg := hf)]; rw [mk_coeFn]

@[elab_as_elim]

Depends on / 依赖: AEEqFun, AEEqFun.aestronglyMeasurable, aestronglyMeasurable, mk_coeFn, mk_eq_mk
-/
theorem coeFn_mk (f : α -> β) (hf) : (mk f hf : α ->ₘ[μ] β) =ᵐ[μ] f := by
  rw [← mk_eq_mk (hf := AEEqFun.aestronglyMeasurable ..) (hg := hf)]; rw [mk_coeFn]

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: (f : α ->ₘ[μ] β) {p : (α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf))
  statement: p f
  proof: Quotient.inductionOn' f Subtype.forall.2 H

@[elab_as_elim]

中文:
定理 induction_on
  条件: (f : α ->ₘ[μ] β) {p : (α ->ₘ[μ] β) -> 命题} (H : 对任意 f hf, p (mk f hf))
  结论: p f
  证明: Quotient.inductionOn' f Subtype.forall.2 H

@[elab_as_elim]

Depends on / 依赖: Quotient, Quotient.inductionOn, Subtype, Subtype.forall, inductionOn
-/
theorem induction_on (f : α ->ₘ[μ] β) {p : (α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f :=
Quotient.inductionOn' f Subtype.forall.2 H

@[elab_as_elim]
/--
theorem `induction_on₂` / 定理 `induction_on₂`

English:
theorem induction_on₂
  statement: {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
  proof: induction_on f fun f hf => induction_on f' H f hf

@[elab_as_elim]

中文:
定理 induction_on₂
  结论: {α' β' : 类型} [可测空间 α'] [拓扑空间 β'] {μ' : 测度 α'}
  证明: induction_on f fun f hf => induction_on f' H f hf

@[elab_as_elim]

Depends on / 依赖: induction_on
-/
theorem induction_on₂ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    (f : α ->ₘ[μ] β) (f' : α' ->ₘ[μ'] β') {p : (α ->ₘ[μ] β) -> (α' ->ₘ[μ'] β') -> Prop}
    (H : forall f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
induction_on f fun f hf => induction_on f' H f hf

@[elab_as_elim]
/--
theorem `induction_on₃` / 定理 `induction_on₃`

English:
theorem induction_on₃
  statement: {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
  proof: induction_on f fun f hf => induction_on₂ f' f'' H f hf

中文:
定理 induction_on₃
  结论: {α' β' : 类型} [可测空间 α'] [拓扑空间 β'] {μ' : 测度 α'}
  证明: induction_on f fun f hf => induction_on₂ f' f'' H f hf

Depends on / 依赖: induction_on
-/
theorem induction_on₃ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    {α'' β'' : Type*} [MeasurableSpace α''] [TopologicalSpace β''] {μ'' : Measure α''}
    (f : α ->ₘ[μ] β) (f' : α' ->ₘ[μ'] β') (f'' : α'' ->ₘ[μ''] β'')
    {p : (α ->ₘ[μ] β) -> (α' ->ₘ[μ'] β') -> (α'' ->ₘ[μ''] β'') -> Prop}
    (H : forall f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
induction_on f fun f hf => induction_on₂ f' f'' H f hf

end

/-!
### Composition of an a.e. equal function with a (quasi-)measure-preserving function
-/

section compQuasiMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β} {f : α -> β}

open MeasureTheory.Measure (QuasiMeasurePreserving)

/--
Definition of `compQuasiMeasurePreserving` / `compQuasiMeasurePreserving` 的定义

English:
definition compQuasiMeasurePreserving
  signature: (g : β ->ₘ[ν] γ) (f : α -> β) (hf : QuasiMeasurePreserving f μ ν)
  body: Quotient.liftOn' g (fun g => mk (g ∘ f) <| g.2.comp_quasiMeasurePreserving hf) fun _ _ h =>
mk_eq_mk.2 h.comp_tendsto hf.tendsto_ae

@[simp]

中文:
定义 compQuasiMeasurePreserving
  签名: (g : β ->ₘ[ν] γ) (f : α -> β) (hf : 拟保测 f μ ν)
  定义体: Quotient.liftOn' g (fun g => mk (g ∘ f) <| g.2.comp_quasiMeasurePreserving hf) fun _ _ h =>
mk_eq_mk.2 h.comp_tendsto hf.tendsto_ae

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn, comp_quasiMeasurePreserving, comp_tendsto, h.comp_tendsto, hf.tendsto_ae, liftOn, mk_eq_mk, tendsto_ae
-/
def compQuasiMeasurePreserving (g : β ->ₘ[ν] γ) (f : α -> β) (hf : QuasiMeasurePreserving f μ ν) :
    α ->ₘ[μ] γ :=
  Quotient.liftOn' g (fun g => mk (g ∘ f) <| g.2.comp_quasiMeasurePreserving hf) fun _ _ h =>
mk_eq_mk.2 h.comp_tendsto hf.tendsto_ae

@[simp]
/--
theorem `compQuasiMeasurePreserving_mk` / 定理 `compQuasiMeasurePreserving_mk`

English:
theorem compQuasiMeasurePreserving_mk
  statement: {g : β -> γ} (hg : AEStronglyMeasurable g ν)
  proof: rfl

中文:
定理 compQuasiMeasurePreserving_mk
  结论: {g : β -> γ} (hg : AEStronglyMeasurable g ν)
  证明: rfl
-/
theorem compQuasiMeasurePreserving_mk {g : β -> γ} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) :
    (mk g hg).compQuasiMeasurePreserving f hf = mk (g ∘ f) (hg.comp_quasiMeasurePreserving hf) :=
  rfl

/--
theorem `compQuasiMeasurePreserving_eq_mk` / 定理 `compQuasiMeasurePreserving_eq_mk`

English:
theorem compQuasiMeasurePreserving_eq_mk
  given: (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν)
  proof: by
  rw [← compQuasiMeasurePreserving_mk g.aestronglyMeasurable hf]; rw [mk_coeFn]

中文:
定理 compQuasiMeasurePreserving_eq_mk
  条件: (g : β ->ₘ[ν] γ) (hf : 拟保测 f μ ν)
  证明: by
  rw [← compQuasiMeasurePreserving_mk g.aestronglyMeasurable hf]; rw [mk_coeFn]

Depends on / 依赖: aestronglyMeasurable, compQuasiMeasurePreserving_mk, g.aestronglyMeasurable, mk_coeFn
-/
theorem compQuasiMeasurePreserving_eq_mk (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) :
    g.compQuasiMeasurePreserving f hf =
      mk (g ∘ f) (g.aestronglyMeasurable.comp_quasiMeasurePreserving hf) := by
  rw [← compQuasiMeasurePreserving_mk g.aestronglyMeasurable hf]; rw [mk_coeFn]

/--
theorem `coeFn_compQuasiMeasurePreserving` / 定理 `coeFn_compQuasiMeasurePreserving`

English:
theorem coeFn_compQuasiMeasurePreserving
  given: (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν)
  proof: by
  rw [compQuasiMeasurePreserving_eq_mk]
  apply coeFn_mk

中文:
定理 coeFn_compQuasiMeasurePreserving
  条件: (g : β ->ₘ[ν] γ) (hf : 拟保测 f μ ν)
  证明: by
  rw [compQuasiMeasurePreserving_eq_mk]
  apply coeFn_mk

Depends on / 依赖: coeFn_mk, compQuasiMeasurePreserving_eq_mk
-/
theorem coeFn_compQuasiMeasurePreserving (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) :
    g.compQuasiMeasurePreserving f hf =ᵐ[μ] g ∘ f := by
  rw [compQuasiMeasurePreserving_eq_mk]
  apply coeFn_mk

/--
theorem `compQuasiMeasurePreserving_congr` / 定理 `compQuasiMeasurePreserving_congr`

English:
theorem compQuasiMeasurePreserving_congr
  statement: (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν)
  proof: by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving, h]

@[simp]

中文:
定理 compQuasiMeasurePreserving_congr
  结论: (g : β ->ₘ[ν] γ) (hf : 拟保测 f μ ν)
  证明: by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving, h]

@[simp]

Depends on / 依赖: coeFn_compQuasiMeasurePreserving
-/
theorem compQuasiMeasurePreserving_congr (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν)
    {f' : α -> β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compQuasiMeasurePreserving g f hf = compQuasiMeasurePreserving g f' (hf.congr hf' h) := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving, h]

@[simp]
/--
theorem `compQuasiMeasurePreserving_id` / 定理 `compQuasiMeasurePreserving_id`

English:
theorem compQuasiMeasurePreserving_id
  given: (g : β ->ₘ[ν] γ)
  proof: by
  ext
  exact coeFn_compQuasiMeasurePreserving _ _

中文:
定理 compQuasiMeasurePreserving_id
  条件: (g : β ->ₘ[ν] γ)
  证明: by
  ext
  exact coeFn_compQuasiMeasurePreserving _ _

Depends on / 依赖: coeFn_compQuasiMeasurePreserving
-/
theorem compQuasiMeasurePreserving_id (g : β ->ₘ[ν] γ) :
    compQuasiMeasurePreserving g id (.id ν) = g := by
  ext
  exact coeFn_compQuasiMeasurePreserving _ _

/--
theorem `compQuasiMeasurePreserving_comp` / 定理 `compQuasiMeasurePreserving_comp`

English:
theorem compQuasiMeasurePreserving_comp
  statement: {γ : Type*} {mγ : MeasurableSpace γ}
  proof: by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving,
    coeFn_compQuasiMeasurePreserving, comp_assoc]

中文:
定理 compQuasiMeasurePreserving_comp
  结论: {γ : 类型} {mγ : 可测空间 γ}
  证明: by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving,
    coeFn_compQuasiMeasurePreserving, comp_assoc]

Depends on / 依赖: coeFn_compQuasiMeasurePreserving, comp_assoc
-/
theorem compQuasiMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ ->ₘ[ξ] δ) {f : β -> γ} (hf : QuasiMeasurePreserving f ν ξ) {f' : α -> β}
    (hf' : QuasiMeasurePreserving f' μ ν) :
    compQuasiMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compQuasiMeasurePreserving (compQuasiMeasurePreserving g f hf) f' hf' := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving,
    coeFn_compQuasiMeasurePreserving, comp_assoc]

/--
theorem `compQuasiMeasurePreserving_iterate` / 定理 `compQuasiMeasurePreserving_iterate`

English:
theorem compQuasiMeasurePreserving_iterate
  statement: (g : α ->ₘ[μ] γ) {f : α -> α}
  proof: by
  induction n with
  | zero => simp
  | succ n hind =>
    nth_rewrite 1 [add_comm]
    simp [iterate_add, hind, ← compQuasiMeasurePreserving_comp]

中文:
定理 compQuasiMeasurePreserving_iterate
  结论: (g : α ->ₘ[μ] γ) {f : α -> α}
  证明: by
  induction n with
  | zero => simp
  | succ n hind =>
    nth_rewrite 1 [add_comm]
    simp [iterate_add, hind, ← compQuasiMeasurePreserving_comp]

Depends on / 依赖: add_comm, compQuasiMeasurePreserving_comp, iterate_add, nth_rewrite
-/
theorem compQuasiMeasurePreserving_iterate (g : α ->ₘ[μ] γ) {f : α -> α}
    (hf : QuasiMeasurePreserving f μ μ) (n : Nat) :
    (compQuasiMeasurePreserving · f hf)^[n] g =
    compQuasiMeasurePreserving g (f^[n]) (hf.iterate n) := by
  induction n with
  | zero => simp
  | succ n hind =>
    nth_rewrite 1 [add_comm]
    simp [iterate_add, hind, ← compQuasiMeasurePreserving_comp]

end compQuasiMeasurePreserving

section compMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β}
  {f : α -> β} {g : β -> γ}

/--
Definition of `compMeasurePreserving` / `compMeasurePreserving` 的定义

English:
definition compMeasurePreserving
  signature: (g : β ->ₘ[ν] γ) (f : α -> β) (hf : MeasurePreserving f μ ν)
  body: g.compQuasiMeasurePreserving f hf.quasiMeasurePreserving

@[simp]

中文:
定义 compMeasurePreserving
  签名: (g : β ->ₘ[ν] γ) (f : α -> β) (hf : 保测 f μ ν)
  定义体: g.compQuasiMeasurePreserving f hf.quasiMeasurePreserving

@[simp]

Depends on / 依赖: compQuasiMeasurePreserving, g.compQuasiMeasurePreserving, hf.quasiMeasurePreserving, quasiMeasurePreserving
-/
def compMeasurePreserving (g : β ->ₘ[ν] γ) (f : α -> β) (hf : MeasurePreserving f μ ν) : α ->ₘ[μ] γ :=
  g.compQuasiMeasurePreserving f hf.quasiMeasurePreserving

@[simp]
/--
theorem `compMeasurePreserving_mk` / 定理 `compMeasurePreserving_mk`

English:
theorem compMeasurePreserving_mk
  given: (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν)
  proof: rfl

中文:
定理 compMeasurePreserving_mk
  条件: (hg : AEStronglyMeasurable g ν) (hf : 保测 f μ ν)
  证明: rfl
-/
theorem compMeasurePreserving_mk (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    (mk g hg).compMeasurePreserving f hf =
      mk (g ∘ f) (hg.comp_quasiMeasurePreserving hf.quasiMeasurePreserving) :=
  rfl

/--
theorem `compMeasurePreserving_eq_mk` / 定理 `compMeasurePreserving_eq_mk`

English:
theorem compMeasurePreserving_eq_mk
  given: (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν)
  proof: g.compQuasiMeasurePreserving_eq_mk _

中文:
定理 compMeasurePreserving_eq_mk
  条件: (g : β ->ₘ[ν] γ) (hf : 保测 f μ ν)
  证明: g.compQuasiMeasurePreserving_eq_mk _

Depends on / 依赖: compQuasiMeasurePreserving_eq_mk, g.compQuasiMeasurePreserving_eq_mk
-/
theorem compMeasurePreserving_eq_mk (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    g.compMeasurePreserving f hf =
      mk (g ∘ f) (g.aestronglyMeasurable.comp_quasiMeasurePreserving hf.quasiMeasurePreserving) :=
  g.compQuasiMeasurePreserving_eq_mk _

/--
theorem `coeFn_compMeasurePreserving` / 定理 `coeFn_compMeasurePreserving`

English:
theorem coeFn_compMeasurePreserving
  given: (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν)
  proof: g.coeFn_compQuasiMeasurePreserving _

中文:
定理 coeFn_compMeasurePreserving
  条件: (g : β ->ₘ[ν] γ) (hf : 保测 f μ ν)
  证明: g.coeFn_compQuasiMeasurePreserving _

Depends on / 依赖: coeFn_compQuasiMeasurePreserving, g.coeFn_compQuasiMeasurePreserving
-/
theorem coeFn_compMeasurePreserving (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    g.compMeasurePreserving f hf =ᵐ[μ] g ∘ f :=
  g.coeFn_compQuasiMeasurePreserving _

/--
theorem `compMeasurePreserving_congr` / 定理 `compMeasurePreserving_congr`

English:
theorem compMeasurePreserving_congr
  statement: (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν)
  proof: compQuasiMeasurePreserving_congr _ _ hf' h

@[simp]

中文:
定理 compMeasurePreserving_congr
  结论: (g : β ->ₘ[ν] γ) (hf : 保测 f μ ν)
  证明: compQuasiMeasurePreserving_congr _ _ hf' h

@[simp]

Depends on / 依赖: compQuasiMeasurePreserving_congr
-/
theorem compMeasurePreserving_congr (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν)
    {f' : α -> β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compMeasurePreserving g f hf = compMeasurePreserving g f' (hf.congr hf' h) :=
  compQuasiMeasurePreserving_congr _ _ hf' h

@[simp]
/--
theorem `compMeasurePreserving_id` / 定理 `compMeasurePreserving_id`

English:
theorem compMeasurePreserving_id
  given: (g : β ->ₘ[ν] γ)
  proof: compQuasiMeasurePreserving_id _

中文:
定理 compMeasurePreserving_id
  条件: (g : β ->ₘ[ν] γ)
  证明: compQuasiMeasurePreserving_id _

Depends on / 依赖: compQuasiMeasurePreserving_id
-/
theorem compMeasurePreserving_id (g : β ->ₘ[ν] γ) :
    compMeasurePreserving g id (.id ν) = g :=
  compQuasiMeasurePreserving_id _

/--
theorem `compMeasurePreserving_comp` / 定理 `compMeasurePreserving_comp`

English:
theorem compMeasurePreserving_comp
  statement: {γ : Type*} {mγ : MeasurableSpace γ}
  proof: compQuasiMeasurePreserving_comp _ _ _

中文:
定理 compMeasurePreserving_comp
  结论: {γ : 类型} {mγ : 可测空间 γ}
  证明: compQuasiMeasurePreserving_comp _ _ _

Depends on / 依赖: compQuasiMeasurePreserving_comp
-/
theorem compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ ->ₘ[ξ] δ) {f : β -> γ} (hf : MeasurePreserving f ν ξ) {f' : α -> β}
    (hf' : MeasurePreserving f' μ ν) :
    compMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compMeasurePreserving (compMeasurePreserving g f hf) f' hf' :=
  compQuasiMeasurePreserving_comp _ _ _

/--
theorem `compMeasurePreserving_iterate` / 定理 `compMeasurePreserving_iterate`

English:
theorem compMeasurePreserving_iterate
  statement: (g : α ->ₘ[μ] γ) {f : α -> α}
  proof: compQuasiMeasurePreserving_iterate _ _ _

中文:
定理 compMeasurePreserving_iterate
  结论: (g : α ->ₘ[μ] γ) {f : α -> α}
  证明: compQuasiMeasurePreserving_iterate _ _ _

Depends on / 依赖: compQuasiMeasurePreserving_iterate
-/
theorem compMeasurePreserving_iterate (g : α ->ₘ[μ] γ) {f : α -> α}
    (hf : MeasurePreserving f μ μ) (n : Nat) :
    (compMeasurePreserving · f hf)^[n] g = compMeasurePreserving g (f^[n]) (hf.iterate n) :=
  compQuasiMeasurePreserving_iterate _ _ _

end compMeasurePreserving

variable [TopologicalSpace β] [TopologicalSpace γ]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β)
  body: Quotient.liftOn' f (fun f => mk (g ∘ (f : α -> β)) (hg.comp_aestronglyMeasurable f.2))
fun _ _ H => mk_eq_mk.2 H.fun_comp g

@[simp]

中文:
定义 comp
  签名: (g : β -> γ) (hg : 连续 g) (f : α ->ₘ[μ] β)
  定义体: Quotient.liftOn' f (fun f => mk (g ∘ (f : α -> β)) (hg.comp_aestronglyMeasurable f.2))
fun _ _ H => mk_eq_mk.2 H.fun_comp g

@[simp]

Depends on / 依赖: H.fun_comp, Quotient, Quotient.liftOn, comp_aestronglyMeasurable, fun_comp, hg.comp_aestronglyMeasurable, liftOn, mk_eq_mk
-/
def comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ :=
  Quotient.liftOn' f (fun f => mk (g ∘ (f : α -> β)) (hg.comp_aestronglyMeasurable f.2))
fun _ _ H => mk_eq_mk.2 H.fun_comp g

@[simp]
/--
theorem `comp_mk` / 定理 `comp_mk`

English:
theorem comp_mk
  given: (g : β -> γ) (hg : Continuous g) (f : α -> β) (hf)
  proof: rfl

@[simp]

中文:
定理 comp_mk
  条件: (g : β -> γ) (hg : 连续 g) (f : α -> β) (hf)
  证明: rfl

@[simp]
-/
theorem comp_mk (g : β -> γ) (hg : Continuous g) (f : α -> β) (hf) :
    comp g hg (mk f hf : α ->ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestronglyMeasurable hf) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->ₘ[μ] β)
  statement: comp id (continuous_id) f = f
  proof: by
  rcases f; rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->ₘ[μ] β)
  结论: comp id (continuous_id) f = f
  证明: by
  rcases f; rfl

@[simp]
-/
theorem comp_id (f : α ->ₘ[μ] β) : comp id (continuous_id) f = f := by
  rcases f; rfl

@[simp]
/--
theorem `comp_comp` / 定理 `comp_comp`

English:
theorem comp_comp
  statement: (g : γ -> δ) (g' : β -> γ) (hg : Continuous g) (hg' : Continuous g')
  proof: by
  rcases f; rfl

中文:
定理 comp_comp
  结论: (g : γ -> δ) (g' : β -> γ) (hg : 连续 g) (hg' : 连续 g')
  证明: by
  rcases f; rfl
-/
theorem comp_comp (g : γ -> δ) (g' : β -> γ) (hg : Continuous g) (hg' : Continuous g')
    (f : α ->ₘ[μ] β) : comp g hg (comp g' hg' f) = comp (g ∘ g') (hg.comp hg') f := by
  rcases f; rfl

/--
theorem `comp_eq_mk` / 定理 `comp_eq_mk`

English:
theorem comp_eq_mk
  given: (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β)
  proof: by
  rw [← comp_mk g hg f f.aestronglyMeasurable]; rw [mk_coeFn]

中文:
定理 comp_eq_mk
  条件: (g : β -> γ) (hg : 连续 g) (f : α ->ₘ[μ] β)
  证明: by
  rw [← comp_mk g hg f f.aestronglyMeasurable]; rw [mk_coeFn]

Depends on / 依赖: aestronglyMeasurable, comp_mk, f.aestronglyMeasurable, mk_coeFn
-/
theorem comp_eq_mk (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable f.aestronglyMeasurable) := by
  rw [← comp_mk g hg f f.aestronglyMeasurable]; rw [mk_coeFn]

/--
theorem `coeFn_comp` / 定理 `coeFn_comp`

English:
theorem coeFn_comp
  given: (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β)
  statement: comp g hg f =ᵐ[μ] g ∘ f
  proof: by
  rw [comp_eq_mk]
  apply coeFn_mk

中文:
定理 coeFn_comp
  条件: (g : β -> γ) (hg : 连续 g) (f : α ->ₘ[μ] β)
  结论: comp g hg f =ᵐ[μ] g ∘ f
  证明: by
  rw [comp_eq_mk]
  apply coeFn_mk

Depends on / 依赖: coeFn_mk, comp_eq_mk
-/
theorem coeFn_comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f := by
  rw [comp_eq_mk]
  apply coeFn_mk

/--
theorem `comp_compQuasiMeasurePreserving` / 定理 `comp_compQuasiMeasurePreserving`

English:
theorem comp_compQuasiMeasurePreserving
  proof: by
  rcases f; rfl

中文:
定理 comp_compQuasiMeasurePreserving
  证明: by
  rcases f; rfl
-/
theorem comp_compQuasiMeasurePreserving
    {β : Type*} [MeasurableSpace β] {ν} (g : γ -> δ) (hg : Continuous g)
    (f : β ->ₘ[ν] γ) {φ : α -> β} (hφ : Measure.QuasiMeasurePreserving φ μ ν) :
    (comp g hg f).compQuasiMeasurePreserving φ hφ =
      comp g hg (f.compQuasiMeasurePreserving φ hφ) := by
  rcases f; rfl

section CompMeasurable

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [MeasurableSpace γ]
  [PseudoMetrizableSpace γ] [OpensMeasurableSpace γ] [SecondCountableTopology γ]

/--
Definition of `compMeasurable` / `compMeasurable` 的定义

English:
definition compMeasurable
  signature: (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β)
  body: Quotient.liftOn' f
    (fun f' => mk (g ∘ (f' : α -> β)) (hg.comp_aemeasurable f'.2.aemeasurable).aestronglyMeasurable)
fun _ _ H => mk_eq_mk.2 H.fun_comp g

@[simp]

中文:
定义 compMeasurable
  签名: (g : β -> γ) (hg : 可测 g) (f : α ->ₘ[μ] β)
  定义体: Quotient.liftOn' f
    (fun f' => mk (g ∘ (f' : α -> β)) (hg.comp_aemeasurable f'.2.aemeasurable).aestronglyMeasurable)
fun _ _ H => mk_eq_mk.2 H.fun_comp g

@[simp]

Depends on / 依赖: H.fun_comp, Quotient, Quotient.liftOn, aemeasurable, aestronglyMeasurable, comp_aemeasurable, fun_comp, hg.comp_aemeasurable, liftOn, mk_eq_mk
-/
def compMeasurable (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ :=
  Quotient.liftOn' f
    (fun f' => mk (g ∘ (f' : α -> β)) (hg.comp_aemeasurable f'.2.aemeasurable).aestronglyMeasurable)
fun _ _ H => mk_eq_mk.2 H.fun_comp g

@[simp]
/--
theorem `compMeasurable_mk` / 定理 `compMeasurable_mk`

English:
theorem compMeasurable_mk
  statement: (g : β -> γ) (hg : Measurable g) (f : α -> β)
  proof: rfl

中文:
定理 compMeasurable_mk
  结论: (g : β -> γ) (hg : 可测 g) (f : α -> β)
  证明: rfl
-/
theorem compMeasurable_mk (g : β -> γ) (hg : Measurable g) (f : α -> β)
    (hf : AEStronglyMeasurable f μ) :
    compMeasurable g hg (mk f hf : α ->ₘ[μ] β) =
      mk (g ∘ f) (hg.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable :=
  rfl

/--
theorem `compMeasurable_eq_mk` / 定理 `compMeasurable_eq_mk`

English:
theorem compMeasurable_eq_mk
  given: (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β)
  proof: by
  rw [← compMeasurable_mk g hg f f.aestronglyMeasurable]; rw [mk_coeFn]

中文:
定理 compMeasurable_eq_mk
  条件: (g : β -> γ) (hg : 可测 g) (f : α ->ₘ[μ] β)
  证明: by
  rw [← compMeasurable_mk g hg f f.aestronglyMeasurable]; rw [mk_coeFn]

Depends on / 依赖: aestronglyMeasurable, compMeasurable_mk, f.aestronglyMeasurable, mk_coeFn
-/
theorem compMeasurable_eq_mk (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) :
    compMeasurable g hg f =
    mk (g ∘ f) (hg.comp_aemeasurable f.aemeasurable).aestronglyMeasurable := by
  rw [← compMeasurable_mk g hg f f.aestronglyMeasurable]; rw [mk_coeFn]

/--
theorem `coeFn_compMeasurable` / 定理 `coeFn_compMeasurable`

English:
theorem coeFn_compMeasurable
  given: (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β)
  proof: by
  rw [compMeasurable_eq_mk]
  apply coeFn_mk

中文:
定理 coeFn_compMeasurable
  条件: (g : β -> γ) (hg : 可测 g) (f : α ->ₘ[μ] β)
  证明: by
  rw [compMeasurable_eq_mk]
  apply coeFn_mk

Depends on / 依赖: coeFn_mk, compMeasurable_eq_mk
-/
theorem coeFn_compMeasurable (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) :
    compMeasurable g hg f =ᵐ[μ] g ∘ f := by
  rw [compMeasurable_eq_mk]
  apply coeFn_mk

end CompMeasurable

/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  body: Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prodMk g.2))
fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 Hf.prodMk Hg

@[simp]

中文:
定义 pair
  签名: (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  定义体: Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prodMk g.2))
fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 Hf.prodMk Hg

@[simp]

Depends on / 依赖: Hf.prodMk, Quotient, Quotient.liftOn, mk_eq_mk, prodMk
-/
def pair (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) : α ->ₘ[μ] β × γ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prodMk g.2))
fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 Hf.prodMk Hg

@[simp]
/--
theorem `pair_mk_mk` / 定理 `pair_mk_mk`

English:
theorem pair_mk_mk
  given: (f : α -> β) (hf) (g : α -> γ) (hg)
  proof: rfl

中文:
定理 pair_mk_mk
  条件: (f : α -> β) (hf) (g : α -> γ) (hg)
  证明: rfl
-/
theorem pair_mk_mk (f : α -> β) (hf) (g : α -> γ) (hg) :
    (mk f hf : α ->ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prodMk hg) :=
  rfl

/--
theorem `pair_eq_mk` / 定理 `pair_eq_mk`

English:
theorem pair_eq_mk
  given: (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  proof: by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyMeasurable, g.aestronglyMeasurable]

中文:
定理 pair_eq_mk
  条件: (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  证明: by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyMeasurable, g.aestronglyMeasurable]

Depends on / 依赖: aestronglyMeasurable, f.aestronglyMeasurable, g.aestronglyMeasurable, mk_coeFn, pair_mk_mk
-/
theorem pair_eq_mk (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) :
    f.pair g =
      mk (fun x => (f x, g x)) (f.aestronglyMeasurable.prodMk g.aestronglyMeasurable) := by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyMeasurable, g.aestronglyMeasurable]

/--
theorem `coeFn_pair` / 定理 `coeFn_pair`

English:
theorem coeFn_pair
  given: (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  statement: f.pair g =ᵐ[μ] fun x => (f x, g x)
  proof: by
  rw [pair_eq_mk]
  apply coeFn_mk

中文:
定理 coeFn_pair
  条件: (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  结论: f.pair g =ᵐ[μ] fun x => (f x, g x)
  证明: by
  rw [pair_eq_mk]
  apply coeFn_mk

Depends on / 依赖: coeFn_mk, pair_eq_mk
-/
theorem coeFn_pair (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) := by
  rw [pair_eq_mk]
  apply coeFn_mk

/--
Definition of `comp₂` / `comp₂` 的定义

English:
definition comp₂
  signature: (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ)
  body: comp _ hg (f₁.pair f₂)

@[simp]

中文:
定义 comp₂
  签名: (g : β -> γ -> δ) (hg : 连续 (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ)
  定义体: comp _ hg (f₁.pair f₂)

@[simp]
-/
def comp₂ (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) :
    α ->ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)

@[simp]
/--
theorem `comp₂_mk_mk` / 定理 `comp₂_mk_mk`

English:
theorem comp₂_mk_mk
  statement: (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α -> β) (f₂ : α -> γ)
  proof: rfl

中文:
定理 comp₂_mk_mk
  结论: (g : β -> γ -> δ) (hg : 连续 (uncurry g)) (f₁ : α -> β) (f₂ : α -> γ)
  证明: rfl
-/
theorem comp₂_mk_mk (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α -> β) (f₂ : α -> γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α ->ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_aestronglyMeasurable (hf₁.prodMk hf₂)) :=
  rfl

/--
theorem `comp₂_eq_pair` / 定理 `comp₂_eq_pair`

English:
theorem comp₂_eq_pair
  statement: (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
  proof: rfl

中文:
定理 comp₂_eq_pair
  结论: (g : β -> γ -> δ) (hg : 连续 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  证明: rfl
-/
theorem comp₂_eq_pair (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl

/--
theorem `comp₂_eq_mk` / 定理 `comp₂_eq_mk`

English:
theorem comp₂_eq_mk
  statement: (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
  proof: by
  rw [comp₂_eq_pair]; rw [pair_eq_mk]; rw [comp_mk]; rfl

中文:
定理 comp₂_eq_mk
  结论: (g : β -> γ -> δ) (hg : 连续 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  证明: by
  rw [comp₂_eq_pair]; rw [pair_eq_mk]; rw [comp_mk]; rfl

Depends on / 依赖: comp_mk, pair_eq_mk
-/
theorem comp₂_eq_mk (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) : comp₂ g hg f₁ f₂ = mk (fun a => g (f₁ a) (f₂ a))
      (hg.comp_aestronglyMeasurable (f₁.aestronglyMeasurable.prodMk f₂.aestronglyMeasurable)) := by
  rw [comp₂_eq_pair]; rw [pair_eq_mk]; rw [comp_mk]; rfl

/--
theorem `coeFn_comp₂` / 定理 `coeFn_comp₂`

English:
theorem coeFn_comp₂
  statement: (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
  proof: by
  rw [comp₂_eq_mk]
  apply coeFn_mk

中文:
定理 coeFn_comp₂
  结论: (g : β -> γ -> δ) (hg : 连续 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  证明: by
  rw [comp₂_eq_mk]
  apply coeFn_mk

Depends on / 依赖: coeFn_mk
-/
theorem coeFn_comp₂ (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂_eq_mk]
  apply coeFn_mk

section

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
  [MeasurableSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] [SecondCountableTopologyEither β γ]
  [MeasurableSpace δ] [PseudoMetrizableSpace δ] [OpensMeasurableSpace δ] [SecondCountableTopology δ]

/--
Definition of `comp₂Measurable` / `comp₂Measurable` 的定义

English:
definition comp₂Measurable
  signature: (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
  body: compMeasurable _ hg (f₁.pair f₂)

@[simp]

中文:
定义 comp₂Measurable
  签名: (g : β -> γ -> δ) (hg : 可测 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  定义体: compMeasurable _ hg (f₁.pair f₂)

@[simp]

Depends on / 依赖: compMeasurable
-/
def comp₂Measurable (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) : α ->ₘ[μ] δ :=
  compMeasurable _ hg (f₁.pair f₂)

@[simp]
/--
theorem `comp₂Measurable_mk_mk` / 定理 `comp₂Measurable_mk_mk`

English:
theorem comp₂Measurable_mk_mk
  statement: (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α -> β)
  proof: rfl

中文:
定理 comp₂Measurable_mk_mk
  结论: (g : β -> γ -> δ) (hg : 可测 (uncurry g)) (f₁ : α -> β)
  证明: rfl
-/
theorem comp₂Measurable_mk_mk (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α -> β)
    (f₂ : α -> γ) (hf₁ hf₂) :
    comp₂Measurable g hg (mk f₁ hf₁ : α ->ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (hf₁.aemeasurable.prodMk hf₂.aemeasurable)).aestronglyMeasurable :=
  rfl

/--
theorem `comp₂Measurable_eq_pair` / 定理 `comp₂Measurable_eq_pair`

English:
theorem comp₂Measurable_eq_pair
  statement: (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
  proof: rfl

中文:
定理 comp₂Measurable_eq_pair
  结论: (g : β -> γ -> δ) (hg : 可测 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  证明: rfl
-/
theorem comp₂Measurable_eq_pair (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ = compMeasurable _ hg (f₁.pair f₂) :=
  rfl

/--
theorem `comp₂Measurable_eq_mk` / 定理 `comp₂Measurable_eq_mk`

English:
theorem comp₂Measurable_eq_mk
  statement: (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
  proof: by
  rw [comp₂Measurable_eq_pair]; rw [pair_eq_mk]; rw [compMeasurable_mk]; rfl

中文:
定理 comp₂Measurable_eq_mk
  结论: (g : β -> γ -> δ) (hg : 可测 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  证明: by
  rw [comp₂Measurable_eq_pair]; rw [pair_eq_mk]; rw [compMeasurable_mk]; rfl

Depends on / 依赖: compMeasurable_mk, pair_eq_mk
-/
theorem comp₂Measurable_eq_mk (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (f₁.aemeasurable.prodMk f₂.aemeasurable)).aestronglyMeasurable := by
  rw [comp₂Measurable_eq_pair]; rw [pair_eq_mk]; rw [compMeasurable_mk]; rfl

/--
theorem `coeFn_comp₂Measurable` / 定理 `coeFn_comp₂Measurable`

English:
theorem coeFn_comp₂Measurable
  statement: (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
  proof: by
  rw [comp₂Measurable_eq_mk]
  apply coeFn_mk

中文:
定理 coeFn_comp₂Measurable
  结论: (g : β -> γ -> δ) (hg : 可测 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  证明: by
  rw [comp₂Measurable_eq_mk]
  apply coeFn_mk

Depends on / 依赖: coeFn_mk
-/
theorem coeFn_comp₂Measurable (g : β -> γ -> δ) (hg : Measurable (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂Measurable_eq_mk]
  apply coeFn_mk

end

/--
Definition of `toGerm` / `toGerm` 的定义

English:
definition toGerm
  signature: (f : α ->ₘ[μ] β)
  body: Quotient.liftOn' f (fun f => ((f : α -> β) : Germ (ae μ) β)) fun _ _ H => Germ.coe_eq.2 H

@[simp]

中文:
定义 toGerm
  签名: (f : α ->ₘ[μ] β)
  定义体: Quotient.liftOn' f (fun f => ((f : α -> β) : Germ (ae μ) β)) fun _ _ H => Germ.coe_eq.2 H

@[simp]

Depends on / 依赖: Germ.coe_eq, Quotient, Quotient.liftOn, coe_eq, liftOn
-/
def toGerm (f : α ->ₘ[μ] β) : Germ (ae μ) β :=
  Quotient.liftOn' f (fun f => ((f : α -> β) : Germ (ae μ) β)) fun _ _ H => Germ.coe_eq.2 H

@[simp]
/--
theorem `mk_toGerm` / 定理 `mk_toGerm`

English:
theorem mk_toGerm
  given: (f : α -> β) (hf)
  statement: (mk f hf : α ->ₘ[μ] β).toGerm = f
  proof: rfl

中文:
定理 mk_toGerm
  条件: (f : α -> β) (hf)
  结论: (mk f hf : α ->ₘ[μ] β).toGerm = f
  证明: rfl
-/
theorem mk_toGerm (f : α -> β) (hf) : (mk f hf : α ->ₘ[μ] β).toGerm = f :=
  rfl

/--
theorem `toGerm_eq` / 定理 `toGerm_eq`

English:
theorem toGerm_eq
  given: (f : α ->ₘ[μ] β)
  statement: f.toGerm = (f : α -> β)
  proof: by
  rw [← mk_toGerm f f.aestronglyMeasurable]; rw [mk_coeFn]

中文:
定理 toGerm_eq
  条件: (f : α ->ₘ[μ] β)
  结论: f.toGerm = (f : α -> β)
  证明: by
  rw [← mk_toGerm f f.aestronglyMeasurable]; rw [mk_coeFn]

Depends on / 依赖: aestronglyMeasurable, f.aestronglyMeasurable, mk_coeFn, mk_toGerm
-/
theorem toGerm_eq (f : α ->ₘ[μ] β) : f.toGerm = (f : α -> β) := by
  rw [← mk_toGerm f f.aestronglyMeasurable]; rw [mk_coeFn]

/--
theorem `toGerm_injective` / 定理 `toGerm_injective`

English:
theorem toGerm_injective
  statement: Injective (toGerm : (α ->ₘ[μ] β) -> Germ (ae μ) β)
  proof: fun f g H =>
ext Germ.coe_eq.1 by rwa [← toGerm_eq, ← toGerm_eq]

@[simp]

中文:
定理 toGerm_injective
  结论: 单射 (toGerm : (α ->ₘ[μ] β) -> Germ (ae μ) β)
  证明: fun f g H =>
ext Germ.coe_eq.1 by rwa [← toGerm_eq, ← toGerm_eq]

@[simp]
-/
theorem toGerm_injective : Injective (toGerm : (α ->ₘ[μ] β) -> Germ (ae μ) β) := fun f g H =>
ext Germ.coe_eq.1 by rwa [← toGerm_eq, ← toGerm_eq]

@[simp]
/--
theorem `compQuasiMeasurePreserving_toGerm` / 定理 `compQuasiMeasurePreserving_toGerm`

English:
theorem compQuasiMeasurePreserving_toGerm
  statement: {β : Type*} [MeasurableSpace β] {f : α -> β} {ν}
  proof: by
  rcases g; rfl

@[simp]

中文:
定理 compQuasiMeasurePreserving_toGerm
  结论: {β : 类型} [可测空间 β] {f : α -> β} {ν}
  证明: by
  rcases g; rfl

@[simp]
-/
theorem compQuasiMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α -> β} {ν}
    (g : β ->ₘ[ν] γ) (hf : Measure.QuasiMeasurePreserving f μ ν) :
    (g.compQuasiMeasurePreserving f hf).toGerm = g.toGerm.compTendsto f hf.tendsto_ae := by
  rcases g; rfl

@[simp]
/--
theorem `compMeasurePreserving_toGerm` / 定理 `compMeasurePreserving_toGerm`

English:
theorem compMeasurePreserving_toGerm
  statement: {β : Type*} [MeasurableSpace β] {f : α -> β} {ν}
  proof: compQuasiMeasurePreserving_toGerm _ _

中文:
定理 compMeasurePreserving_toGerm
  结论: {β : 类型} [可测空间 β] {f : α -> β} {ν}
  证明: compQuasiMeasurePreserving_toGerm _ _

Depends on / 依赖: compQuasiMeasurePreserving_toGerm
-/
theorem compMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α -> β} {ν}
    (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    (g.compMeasurePreserving f hf).toGerm =
      g.toGerm.compTendsto f hf.quasiMeasurePreserving.tendsto_ae :=
  compQuasiMeasurePreserving_toGerm _ _

/--
theorem `comp_toGerm` / 定理 `comp_toGerm`

English:
theorem comp_toGerm
  given: (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β)
  proof: induction_on f fun f _ => by simp

中文:
定理 comp_toGerm
  条件: (g : β -> γ) (hg : 连续 g) (f : α ->ₘ[μ] β)
  证明: induction_on f fun f _ => by simp

Depends on / 依赖: induction_on
-/
theorem comp_toGerm (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) :
    (comp g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp

/--
theorem `compMeasurable_toGerm` / 定理 `compMeasurable_toGerm`

English:
theorem compMeasurable_toGerm
  statement: [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β]
  proof: induction_on f fun f _ => by simp

中文:
定理 compMeasurable_toGerm
  结论: [可测空间 β] [Borel空间 β] [PseudoMetrizable空间 β]
  证明: induction_on f fun f _ => by simp

Depends on / 依赖: induction_on
-/
theorem compMeasurable_toGerm [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) :
    (compMeasurable g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp₂_toGerm` / 定理 `comp₂_toGerm`

English:
theorem comp₂_toGerm
  statement: (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
  proof: induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

中文:
定理 comp₂_toGerm
  结论: (g : β -> γ -> δ) (hg : 连续 (uncurry g)) (f₁ : α ->ₘ[μ] β)
  证明: induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp
-/
theorem comp₂_toGerm (g : β -> γ -> δ) (hg : Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β)
    (f₂ : α ->ₘ[μ] γ) : (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp₂Measurable_toGerm` / 定理 `comp₂Measurable_toGerm`

English:
theorem comp₂Measurable_toGerm
  statement: [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  proof: induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

中文:
定理 comp₂Measurable_toGerm
  结论: [PseudoMetrizable空间 β] [可测空间 β] [Borel空间 β]
  证明: induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp
-/
theorem comp₂Measurable_toGerm [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopologyEither β γ]
    [MeasurableSpace γ] [BorelSpace γ] [PseudoMetrizableSpace δ] [SecondCountableTopology δ]
    [MeasurableSpace δ] [OpensMeasurableSpace δ] (g : β -> γ -> δ) (hg : Measurable (uncurry g))
    (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) :
    (comp₂Measurable g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

/--
Definition of `LiftPred` / `LiftPred` 的定义

English:
definition LiftPred
  signature: (p : β -> Prop) (f : α ->ₘ[μ] β)
  body: f.toGerm.LiftPred p

中文:
定义 LiftPred
  签名: (p : β -> 命题) (f : α ->ₘ[μ] β)
  定义体: f.toGerm.LiftPred p

Depends on / 依赖: LiftPred, f.toGerm.LiftPred, toGerm
-/
def LiftPred (p : β -> Prop) (f : α ->ₘ[μ] β) : Prop :=
  f.toGerm.LiftPred p

/--
Definition of `LiftRel` / `LiftRel` 的定义

English:
definition LiftRel
  signature: (r : β -> γ -> Prop) (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  body: f.toGerm.LiftRel r g.toGerm

中文:
定义 LiftRel
  签名: (r : β -> γ -> 命题) (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ)
  定义体: f.toGerm.LiftRel r g.toGerm

Depends on / 依赖: LiftRel, f.toGerm.LiftRel, g.toGerm, toGerm
-/
def LiftRel (r : β -> γ -> Prop) (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm

/--
theorem `liftRel_mk_mk` / 定理 `liftRel_mk_mk`

English:
theorem liftRel_mk_mk
  given: {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} {hf hg}
  proof: Iff.rfl

中文:
定理 liftRel_mk_mk
  条件: {r : β -> γ -> 命题} {f : α -> β} {g : α -> γ} {hf hg}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem liftRel_mk_mk {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} {hf hg} :
    LiftRel r (mk f hf : α ->ₘ[μ] β) (mk g hg) ↔ forallᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl

/--
theorem `liftRel_iff_coeFn` / 定理 `liftRel_iff_coeFn`

English:
theorem liftRel_iff_coeFn
  given: {r : β -> γ -> Prop} {f : α ->ₘ[μ] β} {g : α ->ₘ[μ] γ}
  proof: by
  rw [← liftRel_mk_mk (hf := f.aestronglyMeasurable) (hg := g.aestronglyMeasurable)]; rw [mk_coeFn]; rw [mk_coeFn]

中文:
定理 liftRel_iff_coeFn
  条件: {r : β -> γ -> 命题} {f : α ->ₘ[μ] β} {g : α ->ₘ[μ] γ}
  证明: by
  rw [← liftRel_mk_mk (hf := f.aestronglyMeasurable) (hg := g.aestronglyMeasurable)]; rw [mk_coeFn]; rw [mk_coeFn]

Depends on / 依赖: aestronglyMeasurable, f.aestronglyMeasurable, g.aestronglyMeasurable, liftRel_mk_mk, mk_coeFn
-/
theorem liftRel_iff_coeFn {r : β -> γ -> Prop} {f : α ->ₘ[μ] β} {g : α ->ₘ[μ] γ} :
    LiftRel r f g ↔ forallᵐ a ∂μ, r (f a) (g a) := by
  rw [← liftRel_mk_mk (hf := f.aestronglyMeasurable) (hg := g.aestronglyMeasurable)]; rw [mk_coeFn]; rw [mk_coeFn]

section Order

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: [Preorder β]
  body: Preorder.lift toGerm

@[simp]

中文:
实例 instPreorder
  签名: [预序 β]
  定义体: Preorder.lift toGerm

@[simp]

Depends on / 依赖: Preorder, Preorder.lift, toGerm
-/
instance instPreorder [Preorder β] : Preorder (α ->ₘ[μ] β) :=
  Preorder.lift toGerm

@[simp]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: [Preorder β] {f g : α -> β} (hf hg)
  statement: (mk f hf : α ->ₘ[μ] β) <= mk g hg ↔ f <=ᵐ[μ] g
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mk_le_mk
  条件: [预序 β] {f g : α -> β} (hf hg)
  结论: (mk f hf : α ->ₘ[μ] β) <= mk g hg ↔ f <=ᵐ[μ] g
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk [Preorder β] {f g : α -> β} (hf hg) : (mk f hf : α ->ₘ[μ] β) <= mk g hg ↔ f <=ᵐ[μ] g :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coeFn_le` / 定理 `coeFn_le`

English:
theorem coeFn_le
  given: [Preorder β] {f g : α ->ₘ[μ] β}
  statement: (f : α -> β) <=ᵐ[μ] g ↔ f <= g
  proof: liftRel_iff_coeFn.symm

中文:
定理 coeFn_le
  条件: [预序 β] {f g : α ->ₘ[μ] β}
  结论: (f : α -> β) <=ᵐ[μ] g ↔ f <= g
  证明: liftRel_iff_coeFn.symm

Depends on / 依赖: liftRel_iff_coeFn, liftRel_iff_coeFn.symm
-/
theorem coeFn_le [Preorder β] {f g : α ->ₘ[μ] β} : (f : α -> β) <=ᵐ[μ] g ↔ f <= g :=
  liftRel_iff_coeFn.symm

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: [PartialOrder β]
  body: PartialOrder.lift toGerm toGerm_injective

中文:
实例 instPartialOrder
  签名: [偏序 β]
  定义体: PartialOrder.lift toGerm toGerm_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, toGerm, toGerm_injective
-/
instance instPartialOrder [PartialOrder β] : PartialOrder (α ->ₘ[μ] β) :=
  PartialOrder.lift toGerm toGerm_injective

section Lattice

section Sup

variable [SemilatticeSup β] [ContinuousSup β]

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max (α ->ₘ[μ] β) where max f g
  body: AEEqFun.comp₂ (· ⊔ ·) continuous_sup f g

中文:
实例 instSup
  签名: : 最大值 (α ->ₘ[μ] β) where 最大值 f g
  定义体: AEEqFun.comp₂ (· ⊔ ·) continuous_sup f g

Depends on / 依赖: AEEqFun, AEEqFun.comp, continuous_sup
-/
instance instSup : Max (α ->ₘ[μ] β) where max f g := AEEqFun.comp₂ (· ⊔ ·) continuous_sup f g

/--
theorem `coeFn_sup` / 定理 `coeFn_sup`

English:
theorem coeFn_sup
  given: (f g : α ->ₘ[μ] β)
  statement: ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x
  proof: coeFn_comp₂ _ _ _ _

中文:
定理 coeFn_sup
  条件: (f g : α ->ₘ[μ] β)
  结论: ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x
  证明: coeFn_comp₂ _ _ _ _
-/
theorem coeFn_sup (f g : α ->ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x :=
  coeFn_comp₂ _ _ _ _

/--
theorem `le_sup_left` / 定理 `le_sup_left`

English:
theorem le_sup_left
  given: (f g : α ->ₘ[μ] β)
  statement: f <= f ⊔ g
  proof: by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_left

中文:
定理 le_sup_left
  条件: (f g : α ->ₘ[μ] β)
  结论: f <= f ⊔ g
  证明: by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_left
-/
protected theorem le_sup_left (f g : α ->ₘ[μ] β) : f <= f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_left

/--
theorem `le_sup_right` / 定理 `le_sup_right`

English:
theorem le_sup_right
  given: (f g : α ->ₘ[μ] β)
  statement: g <= f ⊔ g
  proof: by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_right

中文:
定理 le_sup_right
  条件: (f g : α ->ₘ[μ] β)
  结论: g <= f ⊔ g
  证明: by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_right
-/
protected theorem le_sup_right (f g : α ->ₘ[μ] β) : g <= f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_right

/--
theorem `sup_le` / 定理 `sup_le`

English:
theorem sup_le
  given: (f g f' : α ->ₘ[μ] β) (hf : f <= f') (hg : g <= f')
  statement: f ⊔ g <= f'
  proof: by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_sup f g] with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag

中文:
定理 sup_le
  条件: (f g f' : α ->ₘ[μ] β) (hf : f <= f') (hg : g <= f')
  结论: f ⊔ g <= f'
  证明: by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_sup f g] with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag
-/
protected theorem sup_le (f g f' : α ->ₘ[μ] β) (hf : f <= f') (hg : g <= f') : f ⊔ g <= f' := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_sup f g] with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag

end Sup

section Inf

variable [SemilatticeInf β] [ContinuousInf β]

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (α ->ₘ[μ] β) where min f g
  body: AEEqFun.comp₂ (· ⊓ ·) continuous_inf f g

中文:
实例 instInf
  签名: : 最小值 (α ->ₘ[μ] β) where 最小值 f g
  定义体: AEEqFun.comp₂ (· ⊓ ·) continuous_inf f g

Depends on / 依赖: AEEqFun, AEEqFun.comp, continuous_inf
-/
instance instInf : Min (α ->ₘ[μ] β) where min f g := AEEqFun.comp₂ (· ⊓ ·) continuous_inf f g

/--
theorem `coeFn_inf` / 定理 `coeFn_inf`

English:
theorem coeFn_inf
  given: (f g : α ->ₘ[μ] β)
  statement: ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x
  proof: coeFn_comp₂ _ _ _ _

中文:
定理 coeFn_inf
  条件: (f g : α ->ₘ[μ] β)
  结论: ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x
  证明: coeFn_comp₂ _ _ _ _
-/
theorem coeFn_inf (f g : α ->ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x :=
  coeFn_comp₂ _ _ _ _

/--
theorem `inf_le_left` / 定理 `inf_le_left`

English:
theorem inf_le_left
  given: (f g : α ->ₘ[μ] β)
  statement: f ⊓ g <= f
  proof: by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_left

中文:
定理 inf_le_left
  条件: (f g : α ->ₘ[μ] β)
  结论: f ⊓ g <= f
  证明: by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_left
-/
protected theorem inf_le_left (f g : α ->ₘ[μ] β) : f ⊓ g <= f := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_left

/--
theorem `inf_le_right` / 定理 `inf_le_right`

English:
theorem inf_le_right
  given: (f g : α ->ₘ[μ] β)
  statement: f ⊓ g <= g
  proof: by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_right

中文:
定理 inf_le_right
  条件: (f g : α ->ₘ[μ] β)
  结论: f ⊓ g <= g
  证明: by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_right
-/
protected theorem inf_le_right (f g : α ->ₘ[μ] β) : f ⊓ g <= g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_right

/--
theorem `le_inf` / 定理 `le_inf`

English:
theorem le_inf
  given: (f' f g : α ->ₘ[μ] β) (hf : f' <= f) (hg : f' <= g)
  statement: f' <= f ⊓ g
  proof: by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_inf f g] with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag

中文:
定理 le_inf
  条件: (f' f g : α ->ₘ[μ] β) (hf : f' <= f) (hg : f' <= g)
  结论: f' <= f ⊓ g
  证明: by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_inf f g] with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag
-/
protected theorem le_inf (f' f g : α ->ₘ[μ] β) (hf : f' <= f) (hg : f' <= g) : f' <= f ⊓ g := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_inf f g] with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag

end Inf

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: [Lattice β] [TopologicalLattice β]
  body: { AEEqFun.instPartialOrder with
    sup := max
    le_sup_left := AEEqFun.le_sup_left
    le_sup_right := AEEqFun.le_sup_right
    sup_le := AEEqFun.sup_le
    inf := min
    inf_le_left := AEEqFun.inf_le_left
    inf_le_right := AEEqFun.inf_le_right
    le_inf := AEEqFun.le_inf }

中文:
实例 instLattice
  签名: [格 β] [拓扑格 β]
  定义体: { AEEqFun.instPartialOrder with
    sup := max
    le_sup_left := AEEqFun.le_sup_left
    le_sup_right := AEEqFun.le_sup_right
    sup_le := AEEqFun.sup_le
    inf := min
    inf_le_left := AEEqFun.inf_le_left
    inf_le_right := AEEqFun.inf_le_right
    le_inf := AEEqFun.le_inf }

Depends on / 依赖: AEEqFun, AEEqFun.inf_le_left, AEEqFun.inf_le_right, AEEqFun.instPartialOrder, AEEqFun.le_inf, AEEqFun.le_sup_left, AEEqFun.le_sup_right, AEEqFun.sup_le, inf_le_left, inf_le_right, instPartialOrder, le_inf, le_sup_left, le_sup_right, sup_le
-/
instance instLattice [Lattice β] [TopologicalLattice β] : Lattice (α ->ₘ[μ] β) :=
  { AEEqFun.instPartialOrder with
    sup := max
    le_sup_left := AEEqFun.le_sup_left
    le_sup_right := AEEqFun.le_sup_right
    sup_le := AEEqFun.sup_le
    inf := min
    inf_le_left := AEEqFun.inf_le_left
    inf_le_right := AEEqFun.inf_le_right
    le_inf := AEEqFun.le_inf }

end Lattice

end Order

variable (α)

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (b : β)
  body: mk (fun _ : α => b) aestronglyMeasurable_const

中文:
定义 const
  签名: (b : β)
  定义体: mk (fun _ : α => b) aestronglyMeasurable_const

Depends on / 依赖: aestronglyMeasurable_const
-/
def const (b : β) : α ->ₘ[μ] β :=
  mk (fun _ : α => b) aestronglyMeasurable_const

/--
theorem `coeFn_const` / 定理 `coeFn_const`

English:
theorem coeFn_const
  given: (b : β)
  statement: (const α b : α ->ₘ[μ] β) =ᵐ[μ] Function.const α b
  proof: coeFn_mk _ _

中文:
定理 coeFn_const
  条件: (b : β)
  结论: (const α b : α ->ₘ[μ] β) =ᵐ[μ] 函数.const α b
  证明: coeFn_mk _ _

Depends on / 依赖: coeFn_mk
-/
theorem coeFn_const (b : β) : (const α b : α ->ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coeFn_mk _ _

set_option backward.isDefEq.respectTransparency false in
/-- If the measure is nonzero, we can strengthen `coeFn_const` to get an equality. -/
@[simp]
/--
theorem `coeFn_const_eq` / 定理 `coeFn_const_eq`

English:
theorem coeFn_const_eq
  given: [NeZero μ] (b : β) (x : α)
  statement: (const α b : α ->ₘ[μ] β) x = b
  proof: by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  have := Classical.choose_spec h
  set b' := Classical.choose h
  simp_rw [const, mk_eq_mk, EventuallyEq, ← const_def, eventually_const] at this
  rw [Function.const]; rw [this]

中文:
定理 coeFn_const_eq
  条件: [NeZero μ] (b : β) (x : α)
  结论: (const α b : α ->ₘ[μ] β) x = b
  证明: by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  have := Classical.choose_spec h
  set b' := Classical.choose h
  simp_rw [const, mk_eq_mk, EventuallyEq, ← const_def, eventually_const] at this
  rw [Function.const]; rw [this]

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, EventuallyEq, Function, Function.const, choose_spec, const_def, eventually_const, h.elim, mk_eq_mk, simp_rw, split_ifs
-/
theorem coeFn_const_eq [NeZero μ] (b : β) (x : α) : (const α b : α ->ₘ[μ] β) x = b := by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  have := Classical.choose_spec h
  set b' := Classical.choose h
  simp_rw [const, mk_eq_mk, EventuallyEq, ← const_def, eventually_const] at this
  rw [Function.const]; rw [this]

/--
theorem `coeFn_const_eq'` / 定理 `coeFn_const_eq'`

English:
theorem coeFn_const_eq'
  given: (b : β)
  statement: exists b', ((const α b : α ->ₘ[μ] β) : α -> β) = fun _ => b'
  proof: by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  exact ⟨Classical.choose h, by ext; simp⟩

中文:
定理 coeFn_const_eq'
  条件: (b : β)
  结论: 存在 b', ((const α b : α ->ₘ[μ] β) : α -> β) = fun _ => b'
  证明: by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  exact ⟨Classical.choose h, by ext; simp⟩

Depends on / 依赖: Classical, Classical.choose, h.elim, split_ifs
-/
theorem coeFn_const_eq' (b : β) : exists b', ((const α b : α ->ₘ[μ] β) : α -> β) = fun _ => b' := by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  exact ⟨Classical.choose h, by ext; simp⟩

variable {α}

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Inhabited β]
  body: ⟨const α default⟩

@[to_additive]

中文:
实例 instInhabited
  签名: [可居 β]
  定义体: ⟨const α default⟩

@[to_additive]
-/
instance instInhabited [Inhabited β] : Inhabited (α ->ₘ[μ] β) :=
  ⟨const α default⟩

@[to_additive]
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: [One β]
  body: ⟨const α 1⟩

@[to_additive]

中文:
实例 instOne
  签名: [幺 β]
  定义体: ⟨const α 1⟩

@[to_additive]
-/
instance instOne [One β] : One (α ->ₘ[μ] β) :=
  ⟨const α 1⟩

@[to_additive]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  given: [One β]
  statement: (1 : α ->ₘ[μ] β) = mk (fun _ : α => 1) aestronglyMeasurable_const
  proof: rfl

@[to_additive]

中文:
定理 one_def
  条件: [幺 β]
  结论: (1 : α ->ₘ[μ] β) = mk (fun _ : α => 1) aestronglyMeasurable_const
  证明: rfl

@[to_additive]
-/
theorem one_def [One β] : (1 : α ->ₘ[μ] β) = mk (fun _ : α => 1) aestronglyMeasurable_const :=
  rfl

@[to_additive]
/--
theorem `coeFn_one` / 定理 `coeFn_one`

English:
theorem coeFn_one
  given: [One β]
  statement: ⇑(1 : α ->ₘ[μ] β) =ᵐ[μ] 1
  proof: coeFn_const ..

@[to_additive (attr := simp)]

中文:
定理 coeFn_one
  条件: [幺 β]
  结论: ⇑(1 : α ->ₘ[μ] β) =ᵐ[μ] 1
  证明: coeFn_const ..

@[to_additive (attr := simp)]

Depends on / 依赖: coeFn_const
-/
theorem coeFn_one [One β] : ⇑(1 : α ->ₘ[μ] β) =ᵐ[μ] 1 :=
  coeFn_const ..

@[to_additive (attr := simp)]
/--
theorem `coeFn_one_eq` / 定理 `coeFn_one_eq`

English:
theorem coeFn_one_eq
  given: [NeZero μ] [One β] {x : α}
  statement: (1 : α ->ₘ[μ] β) x = 1
  proof: coeFn_const_eq ..

@[to_additive (attr := simp)]

中文:
定理 coeFn_one_eq
  条件: [NeZero μ] [幺 β] {x : α}
  结论: (1 : α ->ₘ[μ] β) x = 1
  证明: coeFn_const_eq ..

@[to_additive (attr := simp)]

Depends on / 依赖: coeFn_const_eq
-/
theorem coeFn_one_eq [NeZero μ] [One β] {x : α} : (1 : α ->ₘ[μ] β) x = 1 :=
  coeFn_const_eq ..

@[to_additive (attr := simp)]
/--
theorem `one_toGerm` / 定理 `one_toGerm`

English:
theorem one_toGerm
  given: [One β]
  statement: (1 : α ->ₘ[μ] β).toGerm = 1
  proof: rfl

中文:
定理 one_toGerm
  条件: [幺 β]
  结论: (1 : α ->ₘ[μ] β).toGerm = 1
  证明: rfl
-/
theorem one_toGerm [One β] : (1 : α ->ₘ[μ] β).toGerm = 1 :=
  rfl

-- Note we set up the scalar actions before the `Monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section SMul

variable {𝕜 𝕜' : Type*}
variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]
variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul 𝕜 (α ->ₘ[μ] γ)
  body: ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩

@[simp]

中文:
实例 instSMul
  签名: : 标量乘法 𝕜 (α ->ₘ[μ] γ)
  定义体: ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩

@[simp]

Depends on / 依赖: const_smul, continuous_id, continuous_id.const_smul
-/
instance instSMul : SMul 𝕜 (α ->ₘ[μ] γ) :=
  ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩

@[simp]
/--
theorem `smul_mk` / 定理 `smul_mk`

English:
theorem smul_mk
  given: (c : 𝕜) (f : α -> γ) (hf : AEStronglyMeasurable f μ)
  proof: rfl

中文:
定理 smul_mk
  条件: (c : 𝕜) (f : α -> γ) (hf : AEStronglyMeasurable f μ)
  证明: rfl
-/
theorem smul_mk (c : 𝕜) (f : α -> γ) (hf : AEStronglyMeasurable f μ) :
    c • (mk f hf : α ->ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl

/--
theorem `coeFn_smul` / 定理 `coeFn_smul`

English:
theorem coeFn_smul
  given: (c : 𝕜) (f : α ->ₘ[μ] γ)
  statement: ⇑(c • f) =ᵐ[μ] c • ⇑f
  proof: coeFn_comp _ _ _

中文:
定理 coeFn_smul
  条件: (c : 𝕜) (f : α ->ₘ[μ] γ)
  结论: ⇑(c • f) =ᵐ[μ] c • ⇑f
  证明: coeFn_comp _ _ _

Depends on / 依赖: coeFn_comp
-/
theorem coeFn_smul (c : 𝕜) (f : α ->ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  coeFn_comp _ _ _

/--
theorem `smul_toGerm` / 定理 `smul_toGerm`

English:
theorem smul_toGerm
  given: (c : 𝕜) (f : α ->ₘ[μ] γ)
  statement: (c • f).toGerm = c • f.toGerm
  proof: comp_toGerm _ _ _

中文:
定理 smul_toGerm
  条件: (c : 𝕜) (f : α ->ₘ[μ] γ)
  结论: (c • f).toGerm = c • f.toGerm
  证明: comp_toGerm _ _ _

Depends on / 依赖: comp_toGerm
-/
theorem smul_toGerm (c : 𝕜) (f : α ->ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass 𝕜 𝕜' γ]
  body: ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩

中文:
实例 instSMulCommClass
  签名: [标量交换类 𝕜 𝕜' γ]
  定义体: ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩

Depends on / 依赖: induction_on, simp_rw, smul_comm, smul_mk
-/
instance instSMulCommClass [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α ->ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ]
  body: ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩

中文:
实例 instIsScalarTower
  签名: [标量乘法 𝕜 𝕜'] [标量塔 𝕜 𝕜' γ]
  定义体: ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩

Depends on / 依赖: induction_on, simp_rw, smul_assoc, smul_mk
-/
instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α ->ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ]
  body: ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

中文:
实例 instIsCentralScalar
  签名: [标量乘法 𝕜ᵐᵒᵖ γ] [中心标量 𝕜 γ]
  定义体: ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

Depends on / 依赖: induction_on, op_smul_eq_smul, simp_rw, smul_mk
-/
instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 𝕜 (α ->ₘ[μ] γ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

end SMul

section Mul

variable [Mul γ] [ContinuousMul γ]

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (α ->ₘ[μ] γ)
  body: ⟨comp₂ (· * ·) continuous_mul⟩

@[to_additive (attr := simp)]

中文:
实例 instMul
  签名: : 乘法 (α ->ₘ[μ] γ)
  定义体: ⟨comp₂ (· * ·) continuous_mul⟩

@[to_additive (attr := simp)]

Depends on / 依赖: continuous_mul
-/
instance instMul : Mul (α ->ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩

@[to_additive (attr := simp)]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  proof: rfl

@[to_additive]

中文:
定理 mk_mul_mk
  条件: (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  证明: rfl

@[to_additive]
-/
theorem mk_mul_mk (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    (mk f hf : α ->ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl

@[to_additive]
/--
theorem `coeFn_mul` / 定理 `coeFn_mul`

English:
theorem coeFn_mul
  given: (f g : α ->ₘ[μ] γ)
  statement: ⇑(f * g) =ᵐ[μ] f * g
  proof: coeFn_comp₂ _ _ _ _

@[to_additive (attr := simp)]

中文:
定理 coeFn_mul
  条件: (f g : α ->ₘ[μ] γ)
  结论: ⇑(f * g) =ᵐ[μ] f * g
  证明: coeFn_comp₂ _ _ _ _

@[to_additive (attr := simp)]
-/
theorem coeFn_mul (f g : α ->ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coeFn_comp₂ _ _ _ _

@[to_additive (attr := simp)]
/--
theorem `mul_toGerm` / 定理 `mul_toGerm`

English:
theorem mul_toGerm
  given: (f g : α ->ₘ[μ] γ)
  statement: (f * g).toGerm = f.toGerm * g.toGerm
  proof: comp₂_toGerm _ _ _ _

中文:
定理 mul_toGerm
  条件: (f g : α ->ₘ[μ] γ)
  结论: (f * g).toGerm = f.toGerm * g.toGerm
  证明: comp₂_toGerm _ _ _ _
-/
theorem mul_toGerm (f g : α ->ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _

end Mul

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: [AddMonoid γ] [ContinuousAdd γ]
  body: toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

中文:
实例 instAddMonoid
  签名: [加法幺半群 γ] [连续加法 γ]
  定义体: toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

Depends on / 依赖: addMonoid, add_toGerm, smul_toGerm, toGerm, toGerm_injective, toGerm_injective.addMonoid, zero_toGerm
-/
instance instAddMonoid [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α ->ₘ[μ] γ) :=
  toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid γ] [ContinuousAdd γ]
  body: toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

中文:
实例 instAddCommMonoid
  签名: [加法交换幺半群 γ] [连续加法 γ]
  定义体: toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

Depends on / 依赖: addCommMonoid, add_toGerm, smul_toGerm, toGerm, toGerm_injective, toGerm_injective.addCommMonoid, zero_toGerm
-/
instance instAddCommMonoid [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α ->ₘ[μ] γ) :=
  toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

section Monoid

variable [Monoid γ] [ContinuousMul γ]

/--
Instance `instPowNat` / 实例 `instPowNat`

English:
instance instPowNat
  signature: : Pow (α ->ₘ[μ] γ) Nat
  body: ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]

中文:
实例 instPow自然数
  签名: : 幂 (α ->ₘ[μ] γ) 自然数
  定义体: ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]

Depends on / 依赖: continuous_pow
-/
instance instPowNat : Pow (α ->ₘ[μ] γ) Nat :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]
/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: (f : α -> γ) (hf) (n : Nat)
  proof: rfl

中文:
定理 mk_pow
  条件: (f : α -> γ) (hf) (n : 自然数)
  证明: rfl
-/
theorem mk_pow (f : α -> γ) (hf) (n : Nat) :
    (mk f hf : α ->ₘ[μ] γ) ^ n =
      mk (f ^ n) ((_root_.continuous_pow n).comp_aestronglyMeasurable hf) :=
  rfl

/--
theorem `coeFn_pow` / 定理 `coeFn_pow`

English:
theorem coeFn_pow
  given: (f : α ->ₘ[μ] γ) (n : Nat)
  statement: ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n
  proof: coeFn_comp _ _ _

@[simp]

中文:
定理 coeFn_pow
  条件: (f : α ->ₘ[μ] γ) (n : 自然数)
  结论: ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n
  证明: coeFn_comp _ _ _

@[simp]

Depends on / 依赖: coeFn_comp
-/
theorem coeFn_pow (f : α ->ₘ[μ] γ) (n : Nat) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
/--
theorem `pow_toGerm` / 定理 `pow_toGerm`

English:
theorem pow_toGerm
  given: (f : α ->ₘ[μ] γ) (n : Nat)
  statement: (f ^ n).toGerm = f.toGerm ^ n
  proof: comp_toGerm _ _ _

@[to_additive existing]

中文:
定理 pow_toGerm
  条件: (f : α ->ₘ[μ] γ) (n : 自然数)
  结论: (f ^ n).toGerm = f.toGerm ^ n
  证明: comp_toGerm _ _ _

@[to_additive existing]

Depends on / 依赖: comp_toGerm
-/
theorem pow_toGerm (f : α ->ₘ[μ] γ) (n : Nat) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

@[to_additive existing]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (α ->ₘ[μ] γ)
  body: toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm

中文:
实例 instMonoid
  签名: : 幺半群 (α ->ₘ[μ] γ)
  定义体: toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm

Depends on / 依赖: monoid, mul_toGerm, one_toGerm, pow_toGerm, toGerm, toGerm_injective, toGerm_injective.monoid
-/
instance instMonoid : Monoid (α ->ₘ[μ] γ) :=
  toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm

/-- `AEEqFun.toGerm` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `AEEqFun.toGerm` as an `AddMonoidHom`. -/]
/--
Definition of `toGermMonoidHom` / `toGermMonoidHom` 的定义

English:
definition toGermMonoidHom
  signature: : (α ->ₘ[μ] γ) ->* (ae μ).Germ γ where
  body: toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm

中文:
定义 toGermMonoidHom
  签名: : (α ->ₘ[μ] γ) ->* (ae μ).Germ γ where
  定义体: toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm

Depends on / 依赖: toGerm
-/
def toGermMonoidHom : (α ->ₘ[μ] γ) ->* (ae μ).Germ γ where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm

end Monoid

@[to_additive existing]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid γ] [ContinuousMul γ]
  body: toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm

@[to_additive]

中文:
实例 instCommMonoid
  签名: [交换幺半群 γ] [连续乘法 γ]
  定义体: toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm

@[to_additive]

Depends on / 依赖: commMonoid, mul_toGerm, one_toGerm, pow_toGerm, toGerm, toGerm_injective, toGerm_injective.commMonoid
-/
instance instCommMonoid [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α ->ₘ[μ] γ) :=
  toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm

@[to_additive]
/--
theorem `coeFn_finsetProd` / 定理 `coeFn_finsetProd`

English:
theorem coeFn_finsetProd
  statement: [CommMonoid γ] [ContinuousMul γ]
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp [coeFn_one]
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.prod_insert]
    grw [coeFn_mul, ih]

@[to_additive]

中文:
定理 coeFn_finsetProd
  结论: [交换幺半群 γ] [连续乘法 γ]
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp [coeFn_one]
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.prod_insert]
    grw [coeFn_mul, ih]

@[to_additive]

Depends on / 依赖: Finset, Finset.induction, Finset.prod_insert, classical, coeFn_mul, coeFn_one, insert, not_false_eq_true, prod_insert
-/
theorem coeFn_finsetProd [CommMonoid γ] [ContinuousMul γ]
    {ι : Type*} (s : Finset ι) (f : ι -> α ->ₘ[μ] γ) :
    ⇑(∏ i in s, f i) =ᵐ[μ] ∏ i in s, ⇑(f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeFn_one]
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.prod_insert]
    grw [coeFn_mul, ih]

@[to_additive]
/--
theorem `coeFn_fun_finsetProd` / 定理 `coeFn_fun_finsetProd`

English:
theorem coeFn_fun_finsetProd
  statement: [CommMonoid γ] [ContinuousMul γ]
  proof: by
  grw [coeFn_finsetProd]
  filter_upwards with x using by simp

中文:
定理 coeFn_fun_finsetProd
  结论: [交换幺半群 γ] [连续乘法 γ]
  证明: by
  grw [coeFn_finsetProd]
  filter_upwards with x using by simp

Depends on / 依赖: coeFn_finsetProd, filter_upwards
-/
theorem coeFn_fun_finsetProd [CommMonoid γ] [ContinuousMul γ]
    {ι : Type*} (s : Finset ι) (f : ι -> α ->ₘ[μ] γ) :
    ⇑(∏ i in s, f i) =ᵐ[μ] fun x => ∏ i in s, f i x := by
  grw [coeFn_finsetProd]
  filter_upwards with x using by simp

section Group

variable [Group γ] [IsTopologicalGroup γ]

section Inv

@[to_additive]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv (α ->ₘ[μ] γ)
  body: ⟨comp Inv.inv continuous_inv⟩

@[to_additive (attr := simp)]

中文:
实例 instInv
  签名: : 取逆 (α ->ₘ[μ] γ)
  定义体: ⟨comp Inv.inv continuous_inv⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Inv.inv, continuous_inv
-/
instance instInv : Inv (α ->ₘ[μ] γ) :=
  ⟨comp Inv.inv continuous_inv⟩

@[to_additive (attr := simp)]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  given: (f : α -> γ) (hf)
  statement: (mk f hf : α ->ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv
  proof: rfl

@[to_additive]

中文:
定理 inv_mk
  条件: (f : α -> γ) (hf)
  结论: (mk f hf : α ->ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv
  证明: rfl

@[to_additive]
-/
theorem inv_mk (f : α -> γ) (hf) : (mk f hf : α ->ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl

@[to_additive]
/--
theorem `coeFn_inv` / 定理 `coeFn_inv`

English:
theorem coeFn_inv
  given: (f : α ->ₘ[μ] γ)
  statement: ⇑f⁻¹ =ᵐ[μ] f⁻¹
  proof: coeFn_comp _ _ _

@[to_additive]

中文:
定理 coeFn_inv
  条件: (f : α ->ₘ[μ] γ)
  结论: ⇑f⁻¹ =ᵐ[μ] f⁻¹
  证明: coeFn_comp _ _ _

@[to_additive]

Depends on / 依赖: coeFn_comp
-/
theorem coeFn_inv (f : α ->ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coeFn_comp _ _ _

@[to_additive]
/--
theorem `inv_toGerm` / 定理 `inv_toGerm`

English:
theorem inv_toGerm
  given: (f : α ->ₘ[μ] γ)
  statement: f⁻¹.toGerm = f.toGerm⁻¹
  proof: comp_toGerm _ _ _

中文:
定理 inv_toGerm
  条件: (f : α ->ₘ[μ] γ)
  结论: f⁻¹.toGerm = f.toGerm⁻¹
  证明: comp_toGerm _ _ _

Depends on / 依赖: comp_toGerm
-/
theorem inv_toGerm (f : α ->ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _

end Inv

section Div

@[to_additive]
/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: : Div (α ->ₘ[μ] γ)
  body: ⟨comp₂ Div.div continuous_div'⟩

@[to_additive (attr := simp)]

中文:
实例 instDiv
  签名: : 除法 (α ->ₘ[μ] γ)
  定义体: ⟨comp₂ Div.div continuous_div'⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Div.div, continuous_div
-/
instance instDiv : Div (α ->ₘ[μ] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩

@[to_additive (attr := simp)]
/--
theorem `mk_div` / 定理 `mk_div`

English:
theorem mk_div
  given: (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  proof: rfl

@[to_additive]

中文:
定理 mk_div
  条件: (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  证明: rfl

@[to_additive]
-/
theorem mk_div (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (f / g) (hf.div hg) = (mk f hf : α ->ₘ[μ] γ) / mk g hg :=
  rfl

@[to_additive]
/--
theorem `coeFn_div` / 定理 `coeFn_div`

English:
theorem coeFn_div
  given: (f g : α ->ₘ[μ] γ)
  statement: ⇑(f / g) =ᵐ[μ] f / g
  proof: coeFn_comp₂ _ _ _ _

@[to_additive]

中文:
定理 coeFn_div
  条件: (f g : α ->ₘ[μ] γ)
  结论: ⇑(f / g) =ᵐ[μ] f / g
  证明: coeFn_comp₂ _ _ _ _

@[to_additive]
-/
theorem coeFn_div (f g : α ->ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coeFn_comp₂ _ _ _ _

@[to_additive]
/--
theorem `div_toGerm` / 定理 `div_toGerm`

English:
theorem div_toGerm
  given: (f g : α ->ₘ[μ] γ)
  statement: (f / g).toGerm = f.toGerm / g.toGerm
  proof: comp₂_toGerm _ _ _ _

中文:
定理 div_toGerm
  条件: (f g : α ->ₘ[μ] γ)
  结论: (f / g).toGerm = f.toGerm / g.toGerm
  证明: comp₂_toGerm _ _ _ _
-/
theorem div_toGerm (f g : α ->ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _

end Div

section ZPow

/--
Instance `instPowInt` / 实例 `instPowInt`

English:
instance instPowInt
  signature: : Pow (α ->ₘ[μ] γ) Int
  body: ⟨fun f n => comp _ (continuous_zpow n) f⟩

@[simp]

中文:
实例 instPow整数
  签名: : 幂 (α ->ₘ[μ] γ) 整数
  定义体: ⟨fun f n => comp _ (continuous_zpow n) f⟩

@[simp]

Depends on / 依赖: continuous_zpow
-/
instance instPowInt : Pow (α ->ₘ[μ] γ) Int :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩

@[simp]
/--
theorem `mk_zpow` / 定理 `mk_zpow`

English:
theorem mk_zpow
  given: (f : α -> γ) (hf) (n : Int)
  proof: rfl

中文:
定理 mk_zpow
  条件: (f : α -> γ) (hf) (n : 整数)
  证明: rfl
-/
theorem mk_zpow (f : α -> γ) (hf) (n : Int) :
    (mk f hf : α ->ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_aestronglyMeasurable hf) :=
  rfl

/--
theorem `coeFn_zpow` / 定理 `coeFn_zpow`

English:
theorem coeFn_zpow
  given: (f : α ->ₘ[μ] γ) (n : Int)
  statement: ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n
  proof: coeFn_comp _ _ _

@[simp]

中文:
定理 coeFn_zpow
  条件: (f : α ->ₘ[μ] γ) (n : 整数)
  结论: ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n
  证明: coeFn_comp _ _ _

@[simp]

Depends on / 依赖: coeFn_comp
-/
theorem coeFn_zpow (f : α ->ₘ[μ] γ) (n : Int) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
/--
theorem `zpow_toGerm` / 定理 `zpow_toGerm`

English:
theorem zpow_toGerm
  given: (f : α ->ₘ[μ] γ) (n : Int)
  statement: (f ^ n).toGerm = f.toGerm ^ n
  proof: comp_toGerm _ _ _

中文:
定理 zpow_toGerm
  条件: (f : α ->ₘ[μ] γ) (n : 整数)
  结论: (f ^ n).toGerm = f.toGerm ^ n
  证明: comp_toGerm _ _ _

Depends on / 依赖: comp_toGerm
-/
theorem zpow_toGerm (f : α ->ₘ[μ] γ) (n : Int) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

end ZPow

end Group

/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: [AddGroup γ] [IsTopologicalAddGroup γ]
  body: toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

中文:
实例 instAddGroup
  签名: [加法群 γ] [是拓扑加群 γ]
  定义体: toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

Depends on / 依赖: addGroup, add_toGerm, neg_toGerm, smul_toGerm, sub_toGerm, toGerm, toGerm_injective, toGerm_injective.addGroup, zero_toGerm
-/
instance instAddGroup [AddGroup γ] [IsTopologicalAddGroup γ] : AddGroup (α ->ₘ[μ] γ) :=
  toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup γ] [IsTopologicalAddGroup γ]
  body: { add_comm := add_comm }

@[to_additive existing]

中文:
实例 instAddCommGroup
  签名: [加法交换群 γ] [是拓扑加群 γ]
  定义体: { add_comm := add_comm }

@[to_additive existing]

Depends on / 依赖: add_comm
-/
instance instAddCommGroup [AddCommGroup γ] [IsTopologicalAddGroup γ] : AddCommGroup (α ->ₘ[μ] γ) :=
  { add_comm := add_comm }

@[to_additive existing]
/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: [Group γ] [IsTopologicalGroup γ]
  body: toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive existing]

中文:
实例 instGroup
  签名: [群 γ] [是拓扑群 γ]
  定义体: toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive existing]

Depends on / 依赖: div_toGerm, inv_toGerm, mul_toGerm, one_toGerm, pow_toGerm, toGerm_injective, toGerm_injective.group, zpow_toGerm
-/
instance instGroup [Group γ] [IsTopologicalGroup γ] : Group (α ->ₘ[μ] γ) :=
  toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive existing]
/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: [CommGroup γ] [IsTopologicalGroup γ]
  body: { mul_comm := mul_comm }

中文:
实例 instCommGroup
  签名: [交换群 γ] [是拓扑群 γ]
  定义体: { mul_comm := mul_comm }

Depends on / 依赖: mul_comm
-/
instance instCommGroup [CommGroup γ] [IsTopologicalGroup γ] : CommGroup (α ->ₘ[μ] γ) :=
  { mul_comm := mul_comm }

section Module

variable {𝕜 : Type*}

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ]
  body: toGerm_injective.mulAction toGerm smul_toGerm

中文:
实例 instMulAction
  签名: [幺半群 𝕜] [乘法作用 𝕜 γ] [连续常数标量乘法 𝕜 γ]
  定义体: toGerm_injective.mulAction toGerm smul_toGerm

Depends on / 依赖: mulAction, smul_toGerm, toGerm, toGerm_injective, toGerm_injective.mulAction
-/
instance instMulAction [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    MulAction 𝕜 (α ->ₘ[μ] γ) :=
  toGerm_injective.mulAction toGerm smul_toGerm

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
  body: toGerm_injective.distribMulAction (toGermAddMonoidHom : (α ->ₘ[μ] γ) ->+ _) fun c : 𝕜 =>
    smul_toGerm c

中文:
实例 instDistribMulAction
  签名: [幺半群 𝕜] [加法幺半群 γ] [连续加法 γ] [分配乘法作用 𝕜 γ]
  定义体: toGerm_injective.distribMulAction (toGermAddMonoidHom : (α ->ₘ[μ] γ) ->+ _) fun c : 𝕜 =>
    smul_toGerm c

Depends on / 依赖: distribMulAction, smul_toGerm, toGermAddMonoidHom, toGerm_injective, toGerm_injective.distribMulAction
-/
instance instDistribMulAction [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α ->ₘ[μ] γ) :=
  toGerm_injective.distribMulAction (toGermAddMonoidHom : (α ->ₘ[μ] γ) ->+ _) fun c : 𝕜 =>
    smul_toGerm c

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ]
  body: toGerm_injective.module 𝕜 (toGermAddMonoidHom : (α ->ₘ[μ] γ) ->+ _) smul_toGerm

中文:
实例 instModule
  签名: [半环 𝕜] [加法交换幺半群 γ] [连续加法 γ] [模 𝕜 γ]
  定义体: toGerm_injective.module 𝕜 (toGermAddMonoidHom : (α ->ₘ[μ] γ) ->+ _) smul_toGerm

Depends on / 依赖: module, smul_toGerm, toGermAddMonoidHom, toGerm_injective, toGerm_injective.module
-/
instance instModule [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : Module 𝕜 (α ->ₘ[μ] γ) :=
  toGerm_injective.module 𝕜 (toGermAddMonoidHom : (α ->ₘ[μ] γ) ->+ _) smul_toGerm

end Module

open ENNReal

/--
Definition of `lintegral` / `lintegral` 的定义

English:
definition lintegral
  signature: (f : α ->ₘ[μ] Real>=0∞)
  body: Quotient.liftOn' f (fun f => ∫⁻ a, (f : α -> Real>=0∞) a ∂μ) fun _ _ => lintegral_congr_ae

@[simp]

中文:
定义 lintegral
  签名: (f : α ->ₘ[μ] 实数>=0∞)
  定义体: Quotient.liftOn' f (fun f => ∫⁻ a, (f : α -> Real>=0∞) a ∂μ) fun _ _ => lintegral_congr_ae

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn, liftOn, lintegral_congr_ae
-/
def lintegral (f : α ->ₘ[μ] Real>=0∞) : Real>=0∞ :=
  Quotient.liftOn' f (fun f => ∫⁻ a, (f : α -> Real>=0∞) a ∂μ) fun _ _ => lintegral_congr_ae

@[simp]
/--
theorem `lintegral_mk` / 定理 `lintegral_mk`

English:
theorem lintegral_mk
  given: (f : α -> Real>=0∞) (hf)
  statement: (mk f hf : α ->ₘ[μ] Real>=0∞).lintegral = ∫⁻ a, f a ∂μ
  proof: rfl

中文:
定理 lintegral_mk
  条件: (f : α -> 实数>=0∞) (hf)
  结论: (mk f hf : α ->ₘ[μ] 实数>=0∞).lintegral = ∫⁻ a, f a ∂μ
  证明: rfl
-/
theorem lintegral_mk (f : α -> Real>=0∞) (hf) : (mk f hf : α ->ₘ[μ] Real>=0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl

/--
theorem `lintegral_coeFn` / 定理 `lintegral_coeFn`

English:
theorem lintegral_coeFn
  given: (f : α ->ₘ[μ] Real>=0∞)
  statement: ∫⁻ a, f a ∂μ = f.lintegral
  proof: by
  rw [← lintegral_mk (hf := f.aestronglyMeasurable)]; rw [mk_coeFn]

@[simp]
nonrec theorem lintegral_zero : lintegral (0 : α ->ₘ[μ] Real>=0∞) = 0 :=
  lintegral_zero

@[simp]

中文:
定理 lintegral_coeFn
  条件: (f : α ->ₘ[μ] 实数>=0∞)
  结论: ∫⁻ a, f a ∂μ = f.lintegral
  证明: by
  rw [← lintegral_mk (hf := f.aestronglyMeasurable)]; rw [mk_coeFn]

@[simp]
nonrec theorem lintegral_zero : lintegral (0 : α ->ₘ[μ] Real>=0∞) = 0 :=
  lintegral_zero

@[simp]

Depends on / 依赖: aestronglyMeasurable, f.aestronglyMeasurable, lintegral_mk, mk_coeFn
-/
theorem lintegral_coeFn (f : α ->ₘ[μ] Real>=0∞) : ∫⁻ a, f a ∂μ = f.lintegral := by
  rw [← lintegral_mk (hf := f.aestronglyMeasurable)]; rw [mk_coeFn]

@[simp]
nonrec theorem lintegral_zero : lintegral (0 : α ->ₘ[μ] Real>=0∞) = 0 :=
  lintegral_zero

@[simp]
/--
theorem `lintegral_eq_zero_iff` / 定理 `lintegral_eq_zero_iff`

English:
theorem lintegral_eq_zero_iff
  given: {f : α ->ₘ[μ] Real>=0∞}
  statement: lintegral f = 0 ↔ f = 0
  proof: induction_on f fun _f hf => (lintegral_eq_zero_iff' hf.aemeasurable).trans mk_eq_mk.symm

中文:
定理 lintegral_eq_zero_iff
  条件: {f : α ->ₘ[μ] 实数>=0∞}
  结论: lintegral f = 0 ↔ f = 0
  证明: induction_on f fun _f hf => (lintegral_eq_zero_iff' hf.aemeasurable).trans mk_eq_mk.symm

Depends on / 依赖: aemeasurable, hf.aemeasurable, induction_on, lintegral_eq_zero_iff, mk_eq_mk, mk_eq_mk.symm
-/
theorem lintegral_eq_zero_iff {f : α ->ₘ[μ] Real>=0∞} : lintegral f = 0 ↔ f = 0 :=
  induction_on f fun _f hf => (lintegral_eq_zero_iff' hf.aemeasurable).trans mk_eq_mk.symm

/--
theorem `lintegral_add` / 定理 `lintegral_add`

English:
theorem lintegral_add
  given: (f g : α ->ₘ[μ] Real>=0∞)
  statement: lintegral (f + g) = lintegral f + lintegral g
  proof: induction_on₂ f g fun f hf g _ => by simp [lintegral_add_left' hf.aemeasurable]

中文:
定理 lintegral_add
  条件: (f g : α ->ₘ[μ] 实数>=0∞)
  结论: lintegral (f + g) = lintegral f + lintegral g
  证明: induction_on₂ f g fun f hf g _ => by simp [lintegral_add_left' hf.aemeasurable]

Depends on / 依赖: aemeasurable, hf.aemeasurable, lintegral_add_left
-/
theorem lintegral_add (f g : α ->ₘ[μ] Real>=0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  induction_on₂ f g fun f hf g _ => by simp [lintegral_add_left' hf.aemeasurable]

/--
theorem `lintegral_mono` / 定理 `lintegral_mono`

English:
theorem lintegral_mono
  given: {f g : α ->ₘ[μ] Real>=0∞}
  statement: f <= g -> lintegral f <= lintegral g
  proof: induction_on₂ f g fun _f _ _g _ hfg => lintegral_mono_ae hfg

中文:
定理 lintegral_mono
  条件: {f g : α ->ₘ[μ] 实数>=0∞}
  结论: f <= g -> lintegral f <= lintegral g
  证明: induction_on₂ f g fun _f _ _g _ hfg => lintegral_mono_ae hfg

Depends on / 依赖: lintegral_mono_ae
-/
theorem lintegral_mono {f g : α ->ₘ[μ] Real>=0∞} : f <= g -> lintegral f <= lintegral g :=
  induction_on₂ f g fun _f _ _g _ hfg => lintegral_mono_ae hfg

section Abs

/--
theorem `coeFn_abs` / 定理 `coeFn_abs`

English:
theorem coeFn_abs
  statement: {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroup β]
  proof: by
  simp_rw [abs]
  filter_upwards [AEEqFun.coeFn_sup f (-f), AEEqFun.coeFn_neg f] with x hx_sup hx_neg
  rw [hx_sup]; rw [hx_neg]; rw [Pi.neg_apply]

中文:
定理 coeFn_abs
  结论: {β} [拓扑空间 β] [格 β] [拓扑格 β] [加法群 β]
  证明: by
  simp_rw [abs]
  filter_upwards [AEEqFun.coeFn_sup f (-f), AEEqFun.coeFn_neg f] with x hx_sup hx_neg
  rw [hx_sup]; rw [hx_neg]; rw [Pi.neg_apply]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_neg, AEEqFun.coeFn_sup, Pi.neg_apply, coeFn_neg, coeFn_sup, filter_upwards, hx_neg, hx_sup, neg_apply, simp_rw
-/
theorem coeFn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroup β]
    [IsTopologicalAddGroup β] (f : α ->ₘ[μ] β) : ⇑|f| =ᵐ[μ] fun x => |f x| := by
  simp_rw [abs]
  filter_upwards [AEEqFun.coeFn_sup f (-f), AEEqFun.coeFn_neg f] with x hx_sup hx_neg
  rw [hx_sup]; rw [hx_neg]; rw [Pi.neg_apply]

end Abs

section Star

variable {R : Type*} [TopologicalSpace R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [ContinuousStar R] : Star (α ->ₘ[μ] R) where
  body: (AEEqFun.comp _ continuous_star f)

中文:
实例 [对合
  签名: R] [余ntinuousStar R] : 对合 (α ->ₘ[μ] R) where
  定义体: (AEEqFun.comp _ continuous_star f)

Depends on / 依赖: AEEqFun, AEEqFun.comp, continuous_star
-/
instance [Star R] [ContinuousStar R] : Star (α ->ₘ[μ] R) where
  star f := (AEEqFun.comp _ continuous_star f)

/--
lemma `coeFn_star` / 引理 `coeFn_star`

English:
lemma coeFn_star
  given: [Star R] [ContinuousStar R] (f : α ->ₘ[μ] R)
  statement: ↑(star f) =ᵐ[μ] (star f : α -> R)
  proof: coeFn_comp _ (continuous_star) f

中文:
引理 coeFn_star
  条件: [对合 R] [余ntinuousStar R] (f : α ->ₘ[μ] R)
  结论: ↑(star f) =ᵐ[μ] (star f : α -> R)
  证明: coeFn_comp _ (continuous_star) f

Depends on / 依赖: coeFn_comp, continuous_star
-/
lemma coeFn_star [Star R] [ContinuousStar R] (f : α ->ₘ[μ] R) : ↑(star f) =ᵐ[μ] (star f : α -> R) :=
  coeFn_comp _ (continuous_star) f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: R] [ContinuousStar R] : InvolutiveStar (α ->ₘ[μ] R) where
  body: comp_comp _ _ _ _ f

中文:
实例 [InvolutiveStar
  签名: R] [余ntinuousStar R] : InvolutiveStar (α ->ₘ[μ] R) where
  定义体: comp_comp _ _ _ _ f

Depends on / 依赖: comp_comp
-/
instance [InvolutiveStar R] [ContinuousStar R] : InvolutiveStar (α ->ₘ[μ] R) where
.trans by simp [star_involutive.comp_self] star_involutive f := comp_comp _ _ _ _ f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [TrivialStar R] [ContinuousStar R] : TrivialStar (α ->ₘ[μ] R) where
  body: show comp _ _ f = f by simp [funext star_trivial, ← Function.id_def]

中文:
实例 [对合
  签名: R] [TrivialStar R] [余ntinuousStar R] : TrivialStar (α ->ₘ[μ] R) where
  定义体: show comp _ _ f = f by simp [funext star_trivial, ← Function.id_def]

Depends on / 依赖: Function, Function.id_def, id_def, star_trivial
-/
instance [Star R] [TrivialStar R] [ContinuousStar R] : TrivialStar (α ->ₘ[μ] R) where
  star_trivial f := show comp _ _ f = f by simp [funext star_trivial, ← Function.id_def]

end Star

section PosPart

variable [LinearOrder γ] [OrderClosedTopology γ] [Zero γ]

/--
Definition of `posPart` / `posPart` 的定义

English:
definition posPart
  signature: (f : α ->ₘ[μ] γ)
  body: comp (fun x => max x 0) (by fun_prop) f

@[simp]

中文:
定义 posPart
  签名: (f : α ->ₘ[μ] γ)
  定义体: comp (fun x => max x 0) (by fun_prop) f

@[simp]

Depends on / 依赖: fun_prop
-/
def posPart (f : α ->ₘ[μ] γ) : α ->ₘ[μ] γ :=
  comp (fun x => max x 0) (by fun_prop) f

@[simp]
/--
theorem `posPart_mk` / 定理 `posPart_mk`

English:
theorem posPart_mk
  given: (f : α -> γ) (hf)
  proof: rfl

中文:
定理 posPart_mk
  条件: (f : α -> γ) (hf)
  证明: rfl
-/
theorem posPart_mk (f : α -> γ) (hf) :
    posPart (mk f hf : α ->ₘ[μ] γ) = mk (fun x => max (f x) 0) (by fun_prop) :=
  rfl

/--
theorem `coeFn_posPart` / 定理 `coeFn_posPart`

English:
theorem coeFn_posPart
  given: (f : α ->ₘ[μ] γ)
  statement: ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0
  proof: coeFn_comp _ _ _

中文:
定理 coeFn_posPart
  条件: (f : α ->ₘ[μ] γ)
  结论: ⇑(posPart f) =ᵐ[μ] fun a => 最大值 (f a) 0
  证明: coeFn_comp _ _ _

Depends on / 依赖: coeFn_comp
-/
theorem coeFn_posPart (f : α ->ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  coeFn_comp _ _ _

end PosPart

section AELimit

/--
theorem `tendsto_ae_unique` / 定理 `tendsto_ae_unique`

English:
theorem tendsto_ae_unique
  statement: {ι : Type*} [T2Space β]
  proof: by
  filter_upwards [hg, hh] with ω hg1 hh1 using tendsto_nhds_unique hg1 hh1

中文:
定理 tendsto_ae_unique
  结论: {ι : 类型} [T2空间 β]
  证明: by
  filter_upwards [hg, hh] with ω hg1 hh1 using tendsto_nhds_unique hg1 hh1

Depends on / 依赖: filter_upwards, tendsto_nhds_unique
-/
theorem tendsto_ae_unique {ι : Type*} [T2Space β]
    {g h : α -> β} {f : ι -> α -> β} {l : Filter ι} [l.NeBot]
    (hg : forallᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (g ω)))
    (hh : forallᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (h ω))) : g =ᵐ[μ] h := by
  filter_upwards [hg, hh] with ω hg1 hh1 using tendsto_nhds_unique hg1 hh1

end AELimit

end AEEqFun

end MeasureTheory

namespace ContinuousMap

open MeasureTheory

variable [TopologicalSpace α] [BorelSpace α] (μ)
variable [TopologicalSpace β] [SecondCountableTopologyEither α β] [PseudoMetrizableSpace β]

/--
Definition of `toAEEqFun` / `toAEEqFun` 的定义

English:
definition toAEEqFun
  signature: (f : C(α, β))
  body: AEEqFun.mk f f.continuous.aestronglyMeasurable

中文:
定义 toAEEqFun
  签名: (f : C(α, β))
  定义体: AEEqFun.mk f f.continuous.aestronglyMeasurable

Depends on / 依赖: AEEqFun, AEEqFun.mk, aestronglyMeasurable, continuous, f.continuous.aestronglyMeasurable
-/
def toAEEqFun (f : C(α, β)) : α ->ₘ[μ] β :=
  AEEqFun.mk f f.continuous.aestronglyMeasurable

/--
theorem `coeFn_toAEEqFun` / 定理 `coeFn_toAEEqFun`

English:
theorem coeFn_toAEEqFun
  given: (f : C(α, β))
  statement: f.toAEEqFun μ =ᵐ[μ] f
  proof: AEEqFun.coeFn_mk f _

中文:
定理 coeFn_toAEEqFun
  条件: (f : C(α, β))
  结论: f.toAEEqFun μ =ᵐ[μ] f
  证明: AEEqFun.coeFn_mk f _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_mk, coeFn_mk
-/
theorem coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqFun μ =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _

variable [Group β] [IsTopologicalGroup β]

/-- The `MulHom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive /-- The `AddHom` from the group of continuous maps from `α` to `β` to the group of
equivalence classes of `μ`-almost-everywhere measurable functions. -/]
/--
Definition of `toAEEqFunMulHom` / `toAEEqFunMulHom` 的定义

English:
definition toAEEqFunMulHom
  signature: : C(α, β) ->* α ->ₘ[μ] β where
  body: ContinuousMap.toAEEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AEEqFun.mk_mul_mk _ _ f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable

中文:
定义 toAEEqFunMulHom
  签名: : C(α, β) ->* α ->ₘ[μ] β where
  定义体: ContinuousMap.toAEEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AEEqFun.mk_mul_mk _ _ f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable

Depends on / 依赖: ContinuousMap, ContinuousMap.toAEEqFun, toAEEqFun
-/
def toAEEqFunMulHom : C(α, β) ->* α ->ₘ[μ] β where
  toFun := ContinuousMap.toAEEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AEEqFun.mk_mul_mk _ _ f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable

variable {𝕜 : Type*} [Semiring 𝕜]
variable [TopologicalSpace γ] [PseudoMetrizableSpace γ] [AddCommGroup γ] [Module 𝕜 γ]
  [IsTopologicalAddGroup γ] [ContinuousConstSMul 𝕜 γ] [SecondCountableTopologyEither α γ]

/--
Definition of `toAEEqFunLinearMap` / `toAEEqFunLinearMap` 的定义

English:
definition toAEEqFunLinearMap
  signature: : C(α, γ) ->ₗ[𝕜] α ->ₘ[μ] γ
  body: { toAEEqFunAddHom μ with
    map_smul' := fun c f => AEEqFun.smul_mk c f f.continuous.aestronglyMeasurable }

中文:
定义 toAEEqFunLinearMap
  签名: : C(α, γ) ->ₗ[𝕜] α ->ₘ[μ] γ
  定义体: { toAEEqFunAddHom μ with
    map_smul' := fun c f => AEEqFun.smul_mk c f f.continuous.aestronglyMeasurable }

Depends on / 依赖: AEEqFun, AEEqFun.smul_mk, aestronglyMeasurable, continuous, f.continuous.aestronglyMeasurable, map_smul, smul_mk, toAEEqFunAddHom
-/
def toAEEqFunLinearMap : C(α, γ) ->ₗ[𝕜] α ->ₘ[μ] γ :=
  { toAEEqFunAddHom μ with
    map_smul' := fun c f => AEEqFun.smul_mk c f f.continuous.aestronglyMeasurable }

end ContinuousMap
