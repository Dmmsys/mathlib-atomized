/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Probability.Process.Stopping

/-!
# Martingales

A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ i] =ᵐ[μ] f i`. On the other hand, `f : ι → Ω → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is strongly adapted with respect to
`ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] ≤ᵐ[μ] f i`. Finally, `f : ι → Ω → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is strongly adapted
with respect to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ i]`.

### Definitions

* `MeasureTheory.Martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `MeasureTheory.Supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `MeasureTheory.Submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `MeasureTheory.martingale_condExp f ℱ μ`: the sequence `fun i => μ[f | ℱ i]` is a
  martingale with respect to `ℱ` and `μ`.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E ι : Type*} [Preorder ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace Real E] {f g : ι -> Ω -> E} {ℱ : Filtration ι m0}

/--
Definition of `Martingale` / `Martingale` 的定义

English:
definition Martingale
  signature: (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  body: StronglyAdapted ℱ f ∧ forall i j, i <= j -> μ[f j | ℱ i] =ᵐ[μ] f i

中文:
定义 Martingale
  签名: (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  定义体: StronglyAdapted ℱ f ∧ forall i j, i <= j -> μ[f j | ℱ i] =ᵐ[μ] f i

Depends on / 依赖: StronglyAdapted
-/
def Martingale (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ forall i j, i <= j -> μ[f j | ℱ i] =ᵐ[μ] f i

/--
Definition of `Supermartingale` / `Supermartingale` 的定义

English:
definition Supermartingale
  signature: [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  body: StronglyAdapted ℱ f ∧ (forall i j, i <= j -> μ[f j | ℱ i] <=ᵐ[μ] f i) ∧ forall i, Integrable (f i) μ

中文:
定义 Supermartingale
  签名: [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  定义体: StronglyAdapted ℱ f ∧ (forall i j, i <= j -> μ[f j | ℱ i] <=ᵐ[μ] f i) ∧ forall i, Integrable (f i) μ

Depends on / 依赖: Integrable, StronglyAdapted
-/
def Supermartingale [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (forall i j, i <= j -> μ[f j | ℱ i] <=ᵐ[μ] f i) ∧ forall i, Integrable (f i) μ

/--
Definition of `Submartingale` / `Submartingale` 的定义

English:
definition Submartingale
  signature: [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  body: StronglyAdapted ℱ f ∧ (forall i j, i <= j -> f i <=ᵐ[μ] μ[f j | ℱ i]) ∧ forall i, Integrable (f i) μ

中文:
定义 Submartingale
  签名: [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  定义体: StronglyAdapted ℱ f ∧ (forall i j, i <= j -> f i <=ᵐ[μ] μ[f j | ℱ i]) ∧ forall i, Integrable (f i) μ

Depends on / 依赖: Integrable, StronglyAdapted
-/
def Submartingale [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (forall i j, i <= j -> f i <=ᵐ[μ] μ[f j | ℱ i]) ∧ forall i, Integrable (f i) μ

/--
theorem `martingale_const` / 定理 `martingale_const`

English:
theorem martingale_const
  given: (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ] (x : E)
  proof: ⟨stronglyAdapted_const ℱ _, fun i j _ => by rw [condExp_const (ℱ.le _)]⟩

中文:
定理 martingale_const
  条件: (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ] (x : E)
  证明: ⟨stronglyAdapted_const ℱ _, fun i j _ => by rw [condExp_const (ℱ.le _)]⟩

Depends on / 依赖: condExp_const, stronglyAdapted_const
-/
theorem martingale_const (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ] (x : E) :
    Martingale (fun _ _ => x) ℱ μ :=
  ⟨stronglyAdapted_const ℱ _, fun i j _ => by rw [condExp_const (ℱ.le _)]⟩

/--
theorem `martingale_const_fun` / 定理 `martingale_const_fun`

English:
theorem martingale_const_fun
  statement: [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω)
  proof: by
refine ⟨fun i => hf.mono ℱ.mono bot_le, fun i j _ => ?_⟩
  rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.mono <| ℱ.mono bot_le) hfint]

中文:
定理 martingale_const_fun
  结论: [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω)
  证明: by
refine ⟨fun i => hf.mono ℱ.mono bot_le, fun i j _ => ?_⟩
  rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.mono <| ℱ.mono bot_le) hfint]

Depends on / 依赖: bot_le, condExp_of_stronglyMeasurable, hf.mono
-/
theorem martingale_const_fun [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ]
    {f : Ω -> E} (hf : StronglyMeasurable[ℱ ⊥] f) (hfint : Integrable f μ) :
    Martingale (fun _ => f) ℱ μ := by
refine ⟨fun i => hf.mono ℱ.mono bot_le, fun i j _ => ?_⟩
  rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.mono <| ℱ.mono bot_le) hfint]

variable (E) in
/--
theorem `martingale_zero` / 定理 `martingale_zero`

English:
theorem martingale_zero
  given: (ℱ : Filtration ι m0) (μ : Measure Ω)
  statement: Martingale (0 : ι -> Ω -> E) ℱ μ
  proof: ⟨stronglyAdapted_zero E ℱ, fun i j _ => by simp⟩

中文:
定理 martingale_zero
  条件: (ℱ : Filtration ι m0) (μ : Measure Ω)
  结论: Martingale (0 : ι -> Ω -> E) ℱ μ
  证明: ⟨stronglyAdapted_zero E ℱ, fun i j _ => by simp⟩

Depends on / 依赖: stronglyAdapted_zero
-/
theorem martingale_zero (ℱ : Filtration ι m0) (μ : Measure Ω) : Martingale (0 : ι -> Ω -> E) ℱ μ :=
  ⟨stronglyAdapted_zero E ℱ, fun i j _ => by simp⟩

namespace Martingale

/--
theorem `stronglyAdapted` / 定理 `stronglyAdapted`

English:
theorem stronglyAdapted
  given: (hf : Martingale f ℱ μ)
  statement: StronglyAdapted ℱ f
  proof: hf.1

中文:
定理 stronglyAdapted
  条件: (hf : Martingale f ℱ μ)
  结论: StronglyAdapted ℱ f
  证明: hf.1
-/
protected theorem stronglyAdapted (hf : Martingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: (hf : Martingale f ℱ μ) (i : ι)
  proof: hf.stronglyAdapted i

中文:
定理 stronglyMeasurable
  条件: (hf : Martingale f ℱ μ) (i : ι)
  证明: hf.stronglyAdapted i

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finite, Monoid, Monoid.exponent, Monoid.pow_exponent_eq_one, MonoidHom, MonoidHom.ext, S.subtype.comp, codRestrict, coe_injective, exponent, map_one, map_pow, mem_rootsOfUnity, of_injective, of_surjective, pow_exponent_eq_one, rootsOfUnity, subtype
-/
protected theorem stronglyMeasurable (hf : Martingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

/--
theorem `condExp_ae_eq` / 定理 `condExp_ae_eq`

English:
theorem condExp_ae_eq
  given: (hf : Martingale f ℱ μ) {i j : ι} (hij : i <= j)
  statement: μ[f j | ℱ i] =ᵐ[μ] f i
  proof: hf.2 i j hij

中文:
定理 condExp_ae_eq
  条件: (hf : Martingale f ℱ μ) {i j : ι} (hij : i <= j)
  结论: μ[f j | ℱ i] =ᵐ[μ] f i
  证明: hf.2 i j hij
-/
theorem condExp_ae_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i <= j) : μ[f j | ℱ i] =ᵐ[μ] f i :=
  hf.2 i j hij

variable [CompleteSpace E]

/--
theorem `integrable` / 定理 `integrable`

English:
theorem integrable
  given: (hf : Martingale f ℱ μ) (i : ι)
  statement: Integrable (f i) μ
  proof: integrable_condExp.congr (hf.condExp_ae_eq (le_refl i))

中文:
定理 integrable
  条件: (hf : Martingale f ℱ μ) (i : ι)
  结论: 整数egrable (f i) μ
  证明: integrable_condExp.congr (hf.condExp_ae_eq (le_refl i))
-/
protected theorem integrable (hf : Martingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  integrable_condExp.congr (hf.condExp_ae_eq (le_refl i))

/--
theorem `setIntegral_eq` / 定理 `setIntegral_eq`

English:
theorem setIntegral_eq
  statement: [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : ι} (hij : i <= j)
  proof: by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_congr_ae (ℱ.le i s hs) ?_
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm

中文:
定理 setIntegral_eq
  结论: [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : ι} (hij : i <= j)
  证明: by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_congr_ae (ℱ.le i s hs) ?_
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm

Depends on / 依赖: filter_upwards, heq.symm, hf.integrable, integrable, setIntegral_condExp, setIntegral_congr_ae
-/
theorem setIntegral_eq [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : ι} (hij : i <= j)
    {s : Set Ω} (hs : MeasurableSet[ℱ i] s) : ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ := by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_congr_ae (ℱ.le i s hs) ?_
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq : forall t, f t =ᵐ[μ] g t)
  proof: by
  refine ⟨hg, fun i j hij => ?_⟩
  calc μ[g j | ℱ i] =ᵐ[μ] μ[f j | ℱ i] := (condExp_congr_ae (h_eq j)).symm
    _ =ᵐ[μ] g i := (hf.2 i j hij).trans (h_eq i)

中文:
引理 congr
  条件: (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq : 对任意 t, f t =ᵐ[μ] g t)
  证明: by
  refine ⟨hg, fun i j hij => ?_⟩
  calc μ[g j | ℱ i] =ᵐ[μ] μ[f j | ℱ i] := (condExp_congr_ae (h_eq j)).symm
    _ =ᵐ[μ] g i := (hf.2 i j hij).trans (h_eq i)

Depends on / 依赖: condExp_congr_ae, h_eq
-/
lemma congr (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq : forall t, f t =ᵐ[μ] g t) :
    Martingale g ℱ μ := by
  refine ⟨hg, fun i j hij => ?_⟩
  calc μ[g j | ℱ i] =ᵐ[μ] μ[f j | ℱ i] := (condExp_congr_ae (h_eq j)).symm
    _ =ᵐ[μ] g i := (hf.2 i j hij).trans (h_eq i)

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
  statement: Martingale (f + g) ℱ μ
  proof: by
  refine ⟨hf.stronglyAdapted.add hg.stronglyAdapted, fun i j hij => ?_⟩
  exact (condExp_add (hf.integrable j) (hg.integrable j) _).trans
    ((hf.2 i j hij).add (hg.2 i j hij))

中文:
定理 add
  条件: (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
  结论: Martingale (f + g) ℱ μ
  证明: by
  refine ⟨hf.stronglyAdapted.add hg.stronglyAdapted, fun i j hij => ?_⟩
  exact (condExp_add (hf.integrable j) (hg.integrable j) _).trans
    ((hf.2 i j hij).add (hg.2 i j hij))

Depends on / 依赖: condExp_add, hf.integrable, hf.stronglyAdapted.add, hg.integrable, hg.stronglyAdapted, integrable, stronglyAdapted
-/
theorem add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ μ := by
  refine ⟨hf.stronglyAdapted.add hg.stronglyAdapted, fun i j hij => ?_⟩
  exact (condExp_add (hf.integrable j) (hg.integrable j) _).trans
    ((hf.2 i j hij).add (hg.2 i j hij))

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hf : Martingale f ℱ μ)
  statement: Martingale (-f) ℱ μ
  proof: ⟨hf.stronglyAdapted.neg, fun i j hij => (condExp_neg ..).trans (hf.2 i j hij).neg⟩

中文:
定理 neg
  条件: (hf : Martingale f ℱ μ)
  结论: Martingale (-f) ℱ μ
  证明: ⟨hf.stronglyAdapted.neg, fun i j hij => (condExp_neg ..).trans (hf.2 i j hij).neg⟩

Depends on / 依赖: condExp_neg, hf.stronglyAdapted.neg, stronglyAdapted
-/
theorem neg (hf : Martingale f ℱ μ) : Martingale (-f) ℱ μ :=
  ⟨hf.stronglyAdapted.neg, fun i j hij => (condExp_neg ..).trans (hf.2 i j hij).neg⟩

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
  statement: Martingale (f - g) ℱ μ
  proof: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

中文:
定理 sub
  条件: (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
  结论: Martingale (f - g) ℱ μ
  证明: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (c : Real) (hf : Martingale f ℱ μ)
  statement: Martingale (c • f) ℱ μ
  proof: by
  refine ⟨hf.stronglyAdapted.smul c, fun i j hij => ?_⟩
  refine (condExp_smul ..).trans ((hf.2 i j hij).mono fun x hx => ?_)
  simp only [Pi.smul_apply, hx]

中文:
定理 smul
  条件: (c : 实数) (hf : Martingale f ℱ μ)
  结论: Martingale (c • f) ℱ μ
  证明: by
  refine ⟨hf.stronglyAdapted.smul c, fun i j hij => ?_⟩
  refine (condExp_smul ..).trans ((hf.2 i j hij).mono fun x hx => ?_)
  simp only [Pi.smul_apply, hx]

Depends on / 依赖: Pi.smul_apply, condExp_smul, hf.stronglyAdapted.smul, smul_apply, stronglyAdapted
-/
theorem smul (c : Real) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ := by
  refine ⟨hf.stronglyAdapted.smul c, fun i j hij => ?_⟩
  refine (condExp_smul ..).trans ((hf.2 i j hij).mono fun x hx => ?_)
  simp only [Pi.smul_apply, hx]

/--
theorem `supermartingale` / 定理 `supermartingale`

English:
theorem supermartingale
  given: [Preorder E] (hf : Martingale f ℱ μ)
  statement: Supermartingale f ℱ μ
  proof: ⟨hf.1, fun i j hij => (hf.2 i j hij).le, fun i => hf.integrable i⟩

中文:
定理 supermartingale
  条件: [Preorder E] (hf : Martingale f ℱ μ)
  结论: Supermartingale f ℱ μ
  证明: ⟨hf.1, fun i j hij => (hf.2 i j hij).le, fun i => hf.integrable i⟩

Depends on / 依赖: hf.integrable, integrable
-/
theorem supermartingale [Preorder E] (hf : Martingale f ℱ μ) : Supermartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).le, fun i => hf.integrable i⟩

/--
theorem `submartingale` / 定理 `submartingale`

English:
theorem submartingale
  given: [Preorder E] (hf : Martingale f ℱ μ)
  statement: Submartingale f ℱ μ
  proof: ⟨hf.1, fun i j hij => (hf.2 i j hij).symm.le, fun i => hf.integrable i⟩

中文:
定理 submartingale
  条件: [Preorder E] (hf : Martingale f ℱ μ)
  结论: Submartingale f ℱ μ
  证明: ⟨hf.1, fun i j hij => (hf.2 i j hij).symm.le, fun i => hf.integrable i⟩

Depends on / 依赖: hf.integrable, integrable, symm.le
-/
theorem submartingale [Preorder E] (hf : Martingale f ℱ μ) : Submartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).symm.le, fun i => hf.integrable i⟩

end Martingale

/--
theorem `martingale_iff` / 定理 `martingale_iff`

English:
theorem martingale_iff
  given: [CompleteSpace E] [PartialOrder E]
  proof: ⟨fun hf => ⟨hf.supermartingale, hf.submartingale⟩, fun ⟨hf₁, hf₂⟩ =>
    ⟨hf₁.1, fun i j hij => (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

中文:
定理 martingale_iff
  条件: [CompleteSpace E] [PartialOrder E]
  证明: ⟨fun hf => ⟨hf.supermartingale, hf.submartingale⟩, fun ⟨hf₁, hf₂⟩ =>
    ⟨hf₁.1, fun i j hij => (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

Depends on / 依赖: antisymm, hf.submartingale, hf.supermartingale, submartingale, supermartingale
-/
theorem martingale_iff [CompleteSpace E] [PartialOrder E] :
    Martingale f ℱ μ ↔ Supermartingale f ℱ μ ∧ Submartingale f ℱ μ :=
  ⟨fun hf => ⟨hf.supermartingale, hf.submartingale⟩, fun ⟨hf₁, hf₂⟩ =>
    ⟨hf₁.1, fun i j hij => (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

/--
theorem `martingale_condExp` / 定理 `martingale_condExp`

English:
theorem martingale_condExp
  statement: [CompleteSpace E] (f : Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  proof: ⟨fun _ => stronglyMeasurable_condExp, fun _ j hij => condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)⟩

中文:
定理 martingale_condExp
  结论: [CompleteSpace E] (f : Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
  证明: ⟨fun _ => stronglyMeasurable_condExp, fun _ j hij => condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)⟩

Depends on / 依赖: condExp_condExp_of_le, stronglyMeasurable_condExp
-/
theorem martingale_condExp [CompleteSpace E] (f : Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ] : Martingale (fun i => μ[f | ℱ i]) ℱ μ :=
  ⟨fun _ => stronglyMeasurable_condExp, fun _ j hij => condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)⟩

namespace Supermartingale

/--
theorem `stronglyAdapted` / 定理 `stronglyAdapted`

English:
theorem stronglyAdapted
  given: [LE E] (hf : Supermartingale f ℱ μ)
  statement: StronglyAdapted ℱ f
  proof: hf.1

中文:
定理 stronglyAdapted
  条件: [LE E] (hf : Supermartingale f ℱ μ)
  结论: StronglyAdapted ℱ f
  证明: hf.1
-/
protected theorem stronglyAdapted [LE E] (hf : Supermartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: [LE E] (hf : Supermartingale f ℱ μ) (i : ι)
  proof: hf.stronglyAdapted i

中文:
定理 stronglyMeasurable
  条件: [LE E] (hf : Supermartingale f ℱ μ) (i : ι)
  证明: hf.stronglyAdapted i
-/
protected theorem stronglyMeasurable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

/--
theorem `integrable` / 定理 `integrable`

English:
theorem integrable
  given: [LE E] (hf : Supermartingale f ℱ μ) (i : ι)
  statement: Integrable (f i) μ
  proof: hf.2.2 i

中文:
定理 integrable
  条件: [LE E] (hf : Supermartingale f ℱ μ) (i : ι)
  结论: 整数egrable (f i) μ
  证明: hf.2.2 i
-/
protected theorem integrable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

/--
theorem `condExp_ae_le` / 定理 `condExp_ae_le`

English:
theorem condExp_ae_le
  given: [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i <= j)
  proof: hf.2.1 i j hij

中文:
定理 condExp_ae_le
  条件: [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i <= j)
  证明: hf.2.1 i j hij
-/
theorem condExp_ae_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i <= j) :
    μ[f j | ℱ i] <=ᵐ[μ] f i :=
  hf.2.1 i j hij

variable [CompleteSpace E]

/--
theorem `setIntegral_le` / 定理 `setIntegral_le`

English:
theorem setIntegral_le
  statement: [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule Real E]
  proof: by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_mono_ae integrable_condExp.integrableOn (hf.integrable i).integrableOn ?_
  filter_upwards [hf.2.1 i j hij] with _ heq using heq

中文:
定理 setIntegral_le
  结论: [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule 实数 E]
  证明: by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_mono_ae integrable_condExp.integrableOn (hf.integrable i).integrableOn ?_
  filter_upwards [hf.2.1 i j hij] with _ heq using heq

Depends on / 依赖: filter_upwards, hf.integrable, integrable, integrableOn, integrable_condExp, integrable_condExp.integrableOn, setIntegral_condExp, setIntegral_mono_ae
-/
theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule Real E]
    [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} (hf : Supermartingale f ℱ μ)
    {i j : ι} (hij : i <= j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f j ω ∂μ <= ∫ ω in s, f i ω ∂μ := by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_mono_ae integrable_condExp.integrableOn (hf.integrable i).integrableOn ?_
  filter_upwards [hf.2.1 i j hij] with _ heq using heq

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  statement: [LE E] (hf : Supermartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
  proof: by
  refine ⟨hg, fun i j hij => ?_, fun i => (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  filter_upwards [condExp_ae_le hf hij, condExp_congr_ae (h_eq j), h_eq i] with ω h_le hcond h_eq
  rwa [← hcond, ← h_eq]

中文:
引理 congr
  结论: [LE E] (hf : Supermartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
  证明: by
  refine ⟨hg, fun i j hij => ?_, fun i => (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  filter_upwards [condExp_ae_le hf hij, condExp_congr_ae (h_eq j), h_eq i] with ω h_le hcond h_eq
  rwa [← hcond, ← h_eq]

Depends on / 依赖: condExp_ae_le, condExp_congr_ae, filter_upwards, h_eq, h_le, hf.integrable, integrable, integrable_congr
-/
lemma congr [LE E] (hf : Supermartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
    (h_eq : forall t, f t =ᵐ[μ] g t) :
    Supermartingale g ℱ μ := by
  refine ⟨hg, fun i j hij => ?_, fun i => (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  filter_upwards [condExp_ae_le hf hij, condExp_congr_ae (h_eq j), h_eq i] with ω h_le hcond h_eq
  rwa [← hcond, ← h_eq]

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
  proof: by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine (condExp_add (hf.integrable j) (hg.integrable j) _).le.trans ?_
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

中文:
定理 add
  结论: [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
  证明: by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine (condExp_add (hf.integrable j) (hg.integrable j) _).le.trans ?_
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

Depends on / 依赖: add_le_add, condExp_add, filter_upwards, hf.integrable, hg.integrable, integrable, intros, le.trans
-/
theorem add [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
    (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine (condExp_add (hf.integrable j) (hg.integrable j) _).le.trans ?_
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

/--
theorem `add_martingale` / 定理 `add_martingale`

English:
theorem add_martingale
  statement: [Preorder E] [AddLeftMono E]
  proof: hf.add hg.supermartingale

中文:
定理 add_martingale
  结论: [Preorder E] [AddLeftMono E]
  证明: hf.add hg.supermartingale

Depends on / 依赖: hf.add, hg.supermartingale, supermartingale
-/
theorem add_martingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f + g) ℱ μ :=
  hf.add hg.supermartingale

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
  proof: by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  refine EventuallyLE.trans ?_ (condExp_neg ..).symm.le
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

中文:
定理 neg
  条件: [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
  证明: by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  refine EventuallyLE.trans ?_ (condExp_neg ..).symm.le
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

Depends on / 依赖: EventuallyLE, EventuallyLE.trans, condExp_neg, filter_upwards, symm.le
-/
theorem neg [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) :
    Submartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  refine EventuallyLE.trans ?_ (condExp_neg ..).symm.le
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

end Supermartingale

namespace Submartingale

/--
theorem `stronglyAdapted` / 定理 `stronglyAdapted`

English:
theorem stronglyAdapted
  given: [LE E] (hf : Submartingale f ℱ μ)
  statement: StronglyAdapted ℱ f
  proof: hf.1

中文:
定理 stronglyAdapted
  条件: [LE E] (hf : Submartingale f ℱ μ)
  结论: StronglyAdapted ℱ f
  证明: hf.1
-/
protected theorem stronglyAdapted [LE E] (hf : Submartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: [LE E] (hf : Submartingale f ℱ μ) (i : ι)
  proof: hf.stronglyAdapted i

中文:
定理 stronglyMeasurable
  条件: [LE E] (hf : Submartingale f ℱ μ) (i : ι)
  证明: hf.stronglyAdapted i
-/
protected theorem stronglyMeasurable [LE E] (hf : Submartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

/--
theorem `integrable` / 定理 `integrable`

English:
theorem integrable
  given: [LE E] (hf : Submartingale f ℱ μ) (i : ι)
  statement: Integrable (f i) μ
  proof: hf.2.2 i

中文:
定理 integrable
  条件: [LE E] (hf : Submartingale f ℱ μ) (i : ι)
  结论: 整数egrable (f i) μ
  证明: hf.2.2 i
-/
protected theorem integrable [LE E] (hf : Submartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

/--
theorem `ae_le_condExp` / 定理 `ae_le_condExp`

English:
theorem ae_le_condExp
  given: [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i <= j)
  proof: hf.2.1 i j hij

中文:
定理 ae_le_condExp
  条件: [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i <= j)
  证明: hf.2.1 i j hij
-/
theorem ae_le_condExp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i <= j) :
    f i <=ᵐ[μ] μ[f j | ℱ i] :=
  hf.2.1 i j hij

variable [CompleteSpace E]

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  statement: [LE E] (hf : Submartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
  proof: by
  refine ⟨hg, fun i j hij => ?_, fun i => (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  exact (Filter.eventuallyLE_congr (h_eq i) (condExp_congr_ae (h_eq j))).mp (ae_le_condExp hf hij)

中文:
引理 congr
  结论: [LE E] (hf : Submartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
  证明: by
  refine ⟨hg, fun i j hij => ?_, fun i => (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  exact (Filter.eventuallyLE_congr (h_eq i) (condExp_congr_ae (h_eq j))).mp (ae_le_condExp hf hij)

Depends on / 依赖: Filter, Filter.eventuallyLE_congr, ae_le_condExp, condExp_congr_ae, eventuallyLE_congr, h_eq, hf.integrable, integrable, integrable_congr
-/
lemma congr [LE E] (hf : Submartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
    (h_eq : forall t, f t =ᵐ[μ] g t) :
    Submartingale g ℱ μ := by
  refine ⟨hg, fun i j hij => ?_, fun i => (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  exact (Filter.eventuallyLE_congr (h_eq i) (condExp_congr_ae (h_eq j))).mp (ae_le_condExp hf hij)

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  proof: by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine EventuallyLE.trans ?_ (condExp_add (hf.integrable j) (hg.integrable j) _).symm.le
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

中文:
定理 add
  结论: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  证明: by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine EventuallyLE.trans ?_ (condExp_add (hf.integrable j) (hg.integrable j) _).symm.le
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

Depends on / 依赖: EventuallyLE, EventuallyLE.trans, add_le_add, condExp_add, filter_upwards, hf.integrable, hg.integrable, integrable, intros, symm.le
-/
theorem add [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) : Submartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine EventuallyLE.trans ?_ (condExp_add (hf.integrable j) (hg.integrable j) _).symm.le
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

/--
theorem `add_martingale` / 定理 `add_martingale`

English:
theorem add_martingale
  statement: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  proof: hf.add hg.submartingale

中文:
定理 add_martingale
  结论: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  证明: hf.add hg.submartingale

Depends on / 依赖: hf.add, hg.submartingale, submartingale
-/
theorem add_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f + g) ℱ μ :=
  hf.add hg.submartingale

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  proof: by
  refine ⟨hf.1.neg, fun i j hij => (condExp_neg ..).le.trans ?_, fun i => (hf.2.2 i).neg⟩
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

中文:
定理 neg
  条件: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  证明: by
  refine ⟨hf.1.neg, fun i j hij => (condExp_neg ..).le.trans ?_, fun i => (hf.2.2 i).neg⟩
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

Depends on / 依赖: condExp_neg, filter_upwards, le.trans
-/
theorem neg [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) :
    Supermartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => (condExp_neg ..).le.trans ?_, fun i => (hf.2.2 i).neg⟩
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

/--
theorem `setIntegral_le` / 定理 `setIntegral_le`

English:
theorem setIntegral_le
  statement: [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule Real E]
  proof: by
  rw [← neg_le_neg_iff]; rw [← integral_neg]; rw [← integral_neg]
  exact Supermartingale.setIntegral_le hf.neg hij hs

中文:
定理 setIntegral_le
  结论: [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule 实数 E]
  证明: by
  rw [← neg_le_neg_iff]; rw [← integral_neg]; rw [← integral_neg]
  exact Supermartingale.setIntegral_le hf.neg hij hs

Depends on / 依赖: Supermartingale, Supermartingale.setIntegral_le, hf.neg, integral_neg, neg_le_neg_iff, setIntegral_le
-/
theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule Real E]
    [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} (hf : Submartingale f ℱ μ)
    {i j : ι} (hij : i <= j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f i ω ∂μ <= ∫ ω in s, f j ω ∂μ := by
  rw [← neg_le_neg_iff]; rw [← integral_neg]; rw [← integral_neg]
  exact Supermartingale.setIntegral_le hf.neg hij hs

/--
theorem `sub_supermartingale` / 定理 `sub_supermartingale`

English:
theorem sub_supermartingale
  statement: [Preorder E] [AddLeftMono E]
  proof: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

中文:
定理 sub_supermartingale
  结论: [Preorder E] [AddLeftMono E]
  证明: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem sub_supermartingale [Preorder E] [AddLeftMono E]
    (hf : Submartingale f ℱ μ) (hg : Supermartingale g ℱ μ) : Submartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/--
theorem `sub_martingale` / 定理 `sub_martingale`

English:
theorem sub_martingale
  statement: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  proof: hf.sub_supermartingale hg.supermartingale

中文:
定理 sub_martingale
  结论: [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
  证明: hf.sub_supermartingale hg.supermartingale

Depends on / 依赖: hf.sub_supermartingale, hg.supermartingale, sub_supermartingale, supermartingale
-/
theorem sub_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f - g) ℱ μ :=
  hf.sub_supermartingale hg.supermartingale

/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  proof: by
  refine ⟨fun i =>
    @StronglyMeasurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.stronglyAdapted i) (hg.stronglyAdapted i),
    fun i j hij => ?_, fun i => Integrable.sup (hf.integrable _) (hg.integrable _)⟩
  refine EventuallyLE.sup_le ?_ ?_
  · exact EventuallyLE.trans (hf.2.1 i j hij)
      (condExp_mon

中文:
定理 sup
  结论: [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  证明: by
  refine ⟨fun i =>
    @StronglyMeasurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.stronglyAdapted i) (hg.stronglyAdapted i),
    fun i j hij => ?_, fun i => Integrable.sup (hf.integrable _) (hg.integrable _)⟩
  refine EventuallyLE.sup_le ?_ ?_
  · exact EventuallyLE.trans (hf.2.1 i j hij)
      (condExp_mon
-/
protected theorem sup [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    [IsOrderedModule Real E] {f g : ι -> Ω -> E} (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) :
    Submartingale (f ⊔ g) ℱ μ := by
  refine ⟨fun i =>
    @StronglyMeasurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.stronglyAdapted i) (hg.stronglyAdapted i),
    fun i j hij => ?_, fun i => Integrable.sup (hf.integrable _) (hg.integrable _)⟩
  refine EventuallyLE.sup_le ?_ ?_
  · exact EventuallyLE.trans (hf.2.1 i j hij)
      (condExp_mono (hf.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (Eventually.of_forall fun x => le_sup_left))
  · exact EventuallyLE.trans (hg.2.1 i j hij)
      (condExp_mono (hg.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (Eventually.of_forall fun x => le_sup_right))

/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  statement: [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  proof: hf.sup (martingale_zero _ _ _).submartingale

中文:
定理 pos
  结论: [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  证明: hf.sup (martingale_zero _ _ _).submartingale
-/
protected theorem pos [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    [IsOrderedModule Real E] {f : ι -> Ω -> E} (hf : Submartingale f ℱ μ) :
    Submartingale (f⁺) ℱ μ :=
  hf.sup (martingale_zero _ _ _).submartingale

end Submartingale

section Submartingale

/--
theorem `submartingale_of_setIntegral_le` / 定理 `submartingale_of_setIntegral_le`

English:
theorem submartingale_of_setIntegral_le
  statement: [SigmaFiniteFiltration μ ℱ]
  proof: by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  suffices f i <=ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] by exact ae_le_of_ae_le_trim this
  suffices 0 <=ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg
    ((inte

中文:
定理 submartingale_of_setIntegral_le
  结论: [SigmaFiniteFiltration μ ℱ]
  证明: by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  suffices f i <=ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] by exact ae_le_of_ae_le_trim this
  suffices 0 <=ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg
    ((inte

Depends on / 依赖: ae_le_of_ae_le_trim, ae_nonneg_of_forall_setIntegral_nonneg, filter_upwards, integrabl, integrable_condExp, integrable_condExp.sub, integral_sub, setIntegral_trim, specialize, stronglyMeasurable_condExp, stronglyMeasurable_condExp.sub, sub_nonneg
-/
theorem submartingale_of_setIntegral_le [SigmaFiniteFiltration μ ℱ]
    {f : ι -> Ω -> Real} (hadp : StronglyAdapted ℱ f)
    (hint : forall i, Integrable (f i) μ) (hf : forall i j : ι,
      i <= j -> forall s : Set Ω, MeasurableSet[ℱ i] s -> ∫ ω in s, f i ω ∂μ <= ∫ ω in s, f j ω ∂μ) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  suffices f i <=ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] by exact ae_le_of_ae_le_trim this
  suffices 0 <=ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg
    ((integrable_condExp.sub (hint i)).trim _ (stronglyMeasurable_condExp.sub <| hadp i))
      fun s hs _ => ?_
  specialize hf i j hij s hs
  rwa [← setIntegral_trim _ (stronglyMeasurable_condExp.sub <| hadp i) hs,
    integral_sub' integrable_condExp.integrableOn (hint i).integrableOn, sub_nonneg,
    setIntegral_condExp (ℱ.le i) (hint j) hs]

variable [CompleteSpace E]

/--
theorem `submartingale_of_condExp_sub_nonneg` / 定理 `submartingale_of_condExp_sub_nonneg`

English:
theorem submartingale_of_condExp_sub_nonneg
  statement: [PartialOrder E] [IsOrderedAddMonoid E]
  proof: by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rw [← condExp_of_stronglyMeasurable (ℱ.le _) (hadp _) (hint _)]; rw [← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i j hij) (condExp_sub (hint _) (hint _) _).le

中文:
定理 submartingale_of_condExp_sub_nonneg
  结论: [PartialOrder E] [IsOrderedAddMonoid E]
  证明: by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rw [← condExp_of_stronglyMeasurable (ℱ.le _) (hadp _) (hint _)]; rw [← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i j hij) (condExp_sub (hint _) (hint _) _).le

Depends on / 依赖: EventuallyLE, EventuallyLE.trans, condExp_of_stronglyMeasurable, condExp_sub, eventually_sub_nonneg
-/
theorem submartingale_of_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} (hadp : StronglyAdapted ℱ f)
    (hint : forall i, Integrable (f i) μ) (hf : forall i j, i <= j -> 0 <=ᵐ[μ] μ[f j - f i | ℱ i]) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rw [← condExp_of_stronglyMeasurable (ℱ.le _) (hadp _) (hint _)]; rw [← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i j hij) (condExp_sub (hint _) (hint _) _).le

/--
theorem `Submartingale.condExp_sub_nonneg` / 定理 `Submartingale.condExp_sub_nonneg`

English:
theorem Submartingale.condExp_sub_nonneg
  statement: [PartialOrder E] [IsOrderedAddMonoid E]
  proof: by
  by_cases h : SigmaFinite (μ.trim (ℱ.le i))
  swap; · rw [condExp_of_not_sigmaFinite (ℱ.le i) h]
  refine EventuallyLE.trans ?_ (condExp_sub (hf.integrable _) (hf.integrable _) _).symm.le
  rw [eventually_sub_nonneg]; rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.stronglyAdapted _) (hf.integrab

中文:
定理 Submartingale.condExp_sub_nonneg
  结论: [PartialOrder E] [IsOrderedAddMonoid E]
  证明: by
  by_cases h : SigmaFinite (μ.trim (ℱ.le i))
  swap; · rw [condExp_of_not_sigmaFinite (ℱ.le i) h]
  refine EventuallyLE.trans ?_ (condExp_sub (hf.integrable _) (hf.integrable _) _).symm.le
  rw [eventually_sub_nonneg]; rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.stronglyAdapted _) (hf.integrab

Depends on / 依赖: EventuallyLE, EventuallyLE.trans, SigmaFinite, condExp_of_not_sigmaFinite, condExp_of_stronglyMeasurable, condExp_sub, eventually_sub_nonneg, hf.integrable, hf.stronglyAdapted, integrable, stronglyAdapted, symm.le
-/
theorem Submartingale.condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    {f : ι -> Ω -> E} (hf : Submartingale f ℱ μ) {i j : ι}
    (hij : i <= j) : 0 <=ᵐ[μ] μ[f j - f i | ℱ i] := by
  by_cases h : SigmaFinite (μ.trim (ℱ.le i))
  swap; · rw [condExp_of_not_sigmaFinite (ℱ.le i) h]
  refine EventuallyLE.trans ?_ (condExp_sub (hf.integrable _) (hf.integrable _) _).symm.le
  rw [eventually_sub_nonneg]; rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.stronglyAdapted _) (hf.integrable _)]
  exact hf.2.1 i j hij

/--
theorem `submartingale_iff_condExp_sub_nonneg` / 定理 `submartingale_iff_condExp_sub_nonneg`

English:
theorem submartingale_iff_condExp_sub_nonneg
  statement: [PartialOrder E] [IsOrderedAddMonoid E]
  proof: ⟨fun h => ⟨h.stronglyAdapted, h.integrable, fun _ _ => h.condExp_sub_nonneg⟩,
   fun ⟨hadp, hint, h⟩ => submartingale_of_condExp_sub_nonneg hadp hint h⟩

中文:
定理 submartingale_iff_condExp_sub_nonneg
  结论: [PartialOrder E] [IsOrderedAddMonoid E]
  证明: ⟨fun h => ⟨h.stronglyAdapted, h.integrable, fun _ _ => h.condExp_sub_nonneg⟩,
   fun ⟨hadp, hint, h⟩ => submartingale_of_condExp_sub_nonneg hadp hint h⟩

Depends on / 依赖: condExp_sub_nonneg, h.condExp_sub_nonneg, h.integrable, h.stronglyAdapted, integrable, stronglyAdapted, submartingale_of_condExp_sub_nonneg
-/
theorem submartingale_iff_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} :
    Submartingale f ℱ μ ↔
      StronglyAdapted ℱ f ∧ (forall i, Integrable (f i) μ) ∧ forall i j, i <= j -> 0 <=ᵐ[μ] μ[f j - f i | ℱ i] :=
  ⟨fun h => ⟨h.stronglyAdapted, h.integrable, fun _ _ => h.condExp_sub_nonneg⟩,
   fun ⟨hadp, hint, h⟩ => submartingale_of_condExp_sub_nonneg hadp hint h⟩

end Submartingale

namespace Supermartingale

/--
theorem `sub_submartingale` / 定理 `sub_submartingale`

English:
theorem sub_submartingale
  statement: [CompleteSpace E] [Preorder E] [AddLeftMono E]
  proof: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

中文:
定理 sub_submartingale
  结论: [CompleteSpace E] [Preorder E] [AddLeftMono E]
  证明: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem sub_submartingale [CompleteSpace E] [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Supermartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/--
theorem `sub_martingale` / 定理 `sub_martingale`

English:
theorem sub_martingale
  statement: [CompleteSpace E] [Preorder E] [AddLeftMono E]
  proof: hf.sub_submartingale hg.submartingale

中文:
定理 sub_martingale
  结论: [CompleteSpace E] [Preorder E] [AddLeftMono E]
  证明: hf.sub_submartingale hg.submartingale

Depends on / 依赖: hf.sub_submartingale, hg.submartingale, sub_submartingale, submartingale
-/
theorem sub_martingale [CompleteSpace E] [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f - g) ℱ μ :=
  hf.sub_submartingale hg.submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [NormedSpace Real F] [CompleteSpace F]
  [IsOrderedModule Real F]

/--
theorem `smul_nonneg` / 定理 `smul_nonneg`

English:
theorem smul_nonneg
  given: {f : ι -> Ω -> F} {c : Real} (hc : 0 <= c) (hf : Supermartingale f ℱ μ)
  proof: by
  refine ⟨hf.1.smul c, fun i j hij => ?_, fun i => (hf.2.2 i).smul c⟩
  filter_upwards [condExp_smul c (f j) (ℱ i), hf.2.1 i j hij] with ω hω hle
  simpa only [hω, Pi.smul_apply] using smul_le_smul_of_nonneg_left hle hc

中文:
定理 smul_nonneg
  条件: {f : ι -> Ω -> F} {c : 实数} (hc : 0 <= c) (hf : Supermartingale f ℱ μ)
  证明: by
  refine ⟨hf.1.smul c, fun i j hij => ?_, fun i => (hf.2.2 i).smul c⟩
  filter_upwards [condExp_smul c (f j) (ℱ i), hf.2.1 i j hij] with ω hω hle
  simpa only [hω, Pi.smul_apply] using smul_le_smul_of_nonneg_left hle hc

Depends on / 依赖: Pi.smul_apply, condExp_smul, filter_upwards, smul_apply, smul_le_smul_of_nonneg_left
-/
theorem smul_nonneg {f : ι -> Ω -> F} {c : Real} (hc : 0 <= c) (hf : Supermartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  refine ⟨hf.1.smul c, fun i j hij => ?_, fun i => (hf.2.2 i).smul c⟩
  filter_upwards [condExp_smul c (f j) (ℱ i), hf.2.1 i j hij] with ω hω hle
  simpa only [hω, Pi.smul_apply] using smul_le_smul_of_nonneg_left hle hc

/--
theorem `smul_nonpos` / 定理 `smul_nonpos`

English:
theorem smul_nonpos
  statement: [IsOrderedAddMonoid F] {f : ι -> Ω -> F} {c : Real}
  proof: by
  rw [← neg_neg c]; rw [neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

中文:
定理 smul_nonpos
  结论: [IsOrderedAddMonoid F] {f : ι -> Ω -> F} {c : 实数}
  证明: by
  rw [← neg_neg c]; rw [neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

Depends on / 依赖: hf.smul_nonneg, neg_neg, neg_nonneg, neg_smul, smul_nonneg
-/
theorem smul_nonpos [IsOrderedAddMonoid F] {f : ι -> Ω -> F} {c : Real}
    (hc : c <= 0) (hf : Supermartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg c]; rw [neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Supermartingale

namespace Submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
  [NormedSpace Real F] [CompleteSpace F] [IsOrderedModule Real F]

/--
theorem `smul_nonneg` / 定理 `smul_nonneg`

English:
theorem smul_nonneg
  given: {f : ι -> Ω -> F} {c : Real} (hc : 0 <= c) (hf : Submartingale f ℱ μ)
  proof: by
  rw [← neg_neg (c • f)]; rw [← smul_neg]
  exact Supermartingale.neg (hf.neg.smul_nonneg hc)

中文:
定理 smul_nonneg
  条件: {f : ι -> Ω -> F} {c : 实数} (hc : 0 <= c) (hf : Submartingale f ℱ μ)
  证明: by
  rw [← neg_neg (c • f)]; rw [← smul_neg]
  exact Supermartingale.neg (hf.neg.smul_nonneg hc)

Depends on / 依赖: Supermartingale, Supermartingale.neg, hf.neg.smul_nonneg, neg_neg, smul_neg, smul_nonneg
-/
theorem smul_nonneg {f : ι -> Ω -> F} {c : Real} (hc : 0 <= c) (hf : Submartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg (c • f)]; rw [← smul_neg]
  exact Supermartingale.neg (hf.neg.smul_nonneg hc)

/--
theorem `smul_nonpos` / 定理 `smul_nonpos`

English:
theorem smul_nonpos
  given: {f : ι -> Ω -> F} {c : Real} (hc : c <= 0) (hf : Submartingale f ℱ μ)
  proof: by
  rw [← neg_neg c]; rw [neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

中文:
定理 smul_nonpos
  条件: {f : ι -> Ω -> F} {c : 实数} (hc : c <= 0) (hf : Submartingale f ℱ μ)
  证明: by
  rw [← neg_neg c]; rw [neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

Depends on / 依赖: hf.smul_nonneg, neg_neg, neg_nonneg, neg_smul, smul_nonneg
-/
theorem smul_nonpos {f : ι -> Ω -> F} {c : Real} (hc : c <= 0) (hf : Submartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  rw [← neg_neg c]; rw [neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Submartingale

section Nat

variable {𝒢 : Filtration Nat m0}

section SubSuper

section OfSetIntegral

/--
theorem `submartingale_of_setIntegral_le_succ` / 定理 `submartingale_of_setIntegral_le_succ`

English:
theorem submartingale_of_setIntegral_le_succ
  statement: [IsFiniteMeasure μ] {f : Nat -> Ω -> Real}
  proof: by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  induction hij with
  | refl => rfl
  | step hk₁ hk₂ => exact hk₂.trans (hf _ s (𝒢.mono hk₁ _ hs))

中文:
定理 submartingale_of_setIntegral_le_succ
  结论: [IsFiniteMeasure μ] {f : 自然数 -> Ω -> 实数}
  证明: by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  induction hij with
  | refl => rfl
  | step hk₁ hk₂ => exact hk₂.trans (hf _ s (𝒢.mono hk₁ _ hs))

Depends on / 依赖: submartingale_of_setIntegral_le
-/
theorem submartingale_of_setIntegral_le_succ [IsFiniteMeasure μ] {f : Nat -> Ω -> Real}
    (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ)
    (hf : forall i, forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f i ω ∂μ <= ∫ ω in s, f (i + 1) ω ∂μ) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  induction hij with
  | refl => rfl
  | step hk₁ hk₂ => exact hk₂.trans (hf _ s (𝒢.mono hk₁ _ hs))

/--
theorem `supermartingale_of_setIntegral_succ_le` / 定理 `supermartingale_of_setIntegral_succ_le`

English:
theorem supermartingale_of_setIntegral_succ_le
  statement: [IsFiniteMeasure μ] {f : Nat -> Ω -> Real}
  proof: by
  rw [← neg_neg f]
  refine (submartingale_of_setIntegral_le_succ hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [integral_neg, Pi.neg_apply, neg_le_neg_iff]

中文:
定理 supermartingale_of_setIntegral_succ_le
  结论: [IsFiniteMeasure μ] {f : 自然数 -> Ω -> 实数}
  证明: by
  rw [← neg_neg f]
  refine (submartingale_of_setIntegral_le_succ hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [integral_neg, Pi.neg_apply, neg_le_neg_iff]

Depends on / 依赖: Pi.neg_apply, hadp.neg, integral_neg, neg_apply, neg_le_neg_iff, neg_neg, submartingale_of_setIntegral_le_succ
-/
theorem supermartingale_of_setIntegral_succ_le [IsFiniteMeasure μ] {f : Nat -> Ω -> Real}
    (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ)
    (hf : forall i, forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f (i + 1) ω ∂μ <= ∫ ω in s, f i ω ∂μ) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_setIntegral_le_succ hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [integral_neg, Pi.neg_apply, neg_le_neg_iff]

end OfSetIntegral

section OfSucc

variable [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E] [ClosedIciTopology E]
  [IsOrderedModule Real E]

/--
theorem `submartingale_nat` / 定理 `submartingale_nat`

English:
theorem submartingale_nat
  statement: [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f)
  proof: by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ => ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_mono (hint k) integrable_condExp (hf k),
  

中文:
定理 submartingale_nat
  结论: [IsFiniteMeasure μ] {f : 自然数 -> Ω -> E} (hadp : StronglyAdapted 𝒢 f)
  证明: by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ => ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_mono (hint k) integrable_condExp (hf k),
  

Depends on / 依赖: Nat.le_induction, ae_of_all, condExp_condExp, condExp_mono, condExp_of_stronglyMeasurable, filter_upwards, integrable_condExp, le_induction
-/
theorem submartingale_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f)
    (hint : forall i, Integrable (f i) μ) (hf : forall i, f i <=ᵐ[μ] μ[f (i + 1) | 𝒢 i]) :
    Submartingale f 𝒢 μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ => ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_mono (hint k) integrable_condExp (hf k),
      𝒢.condExp_condExp (f (k + 1)) hik] with ω hω1 hω2 hω3
    grw [hω1, hω2, hω3]

/--
theorem `supermartingale_nat` / 定理 `supermartingale_nat`

English:
theorem supermartingale_nat
  statement: [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f)
  proof: by
  rw [← neg_neg f]
  refine (submartingale_nat hadp.neg (fun i => (hint i).neg) fun i =>
    EventuallyLE.trans ?_ (condExp_neg ..).symm.le).neg
  filter_upwards [hf i] with x hx using neg_le_neg hx

中文:
定理 supermartingale_nat
  结论: [IsFiniteMeasure μ] {f : 自然数 -> Ω -> E} (hadp : StronglyAdapted 𝒢 f)
  证明: by
  rw [← neg_neg f]
  refine (submartingale_nat hadp.neg (fun i => (hint i).neg) fun i =>
    EventuallyLE.trans ?_ (condExp_neg ..).symm.le).neg
  filter_upwards [hf i] with x hx using neg_le_neg hx

Depends on / 依赖: EventuallyLE, EventuallyLE.trans, condExp_neg, filter_upwards, hadp.neg, neg_le_neg, neg_neg, submartingale_nat, symm.le
-/
theorem supermartingale_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f)
    (hint : forall i, Integrable (f i) μ) (hf : forall i, μ[f (i + 1) | 𝒢 i] <=ᵐ[μ] f i) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_nat hadp.neg (fun i => (hint i).neg) fun i =>
    EventuallyLE.trans ?_ (condExp_neg ..).symm.le).neg
  filter_upwards [hf i] with x hx using neg_le_neg hx

/--
theorem `submartingale_of_condExp_sub_nonneg_nat` / 定理 `submartingale_of_condExp_sub_nonneg_nat`

English:
theorem submartingale_of_condExp_sub_nonneg_nat
  statement: [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
  proof: by
  refine submartingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _)]; rw [← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i) (condExp_sub (hint _) (hint _) _).le

中文:
定理 submartingale_of_condExp_sub_nonneg_nat
  结论: [IsFiniteMeasure μ] {f : 自然数 -> Ω -> E}
  证明: by
  refine submartingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _)]; rw [← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i) (condExp_sub (hint _) (hint _) _).le

Depends on / 依赖: EventuallyLE, EventuallyLE.trans, condExp_of_stronglyMeasurable, condExp_sub, eventually_sub_nonneg, submartingale_nat
-/
theorem submartingale_of_condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
    (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ)
    (hf : forall i, 0 <=ᵐ[μ] μ[f (i + 1) - f i | 𝒢 i]) : Submartingale f 𝒢 μ := by
  refine submartingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _)]; rw [← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i) (condExp_sub (hint _) (hint _) _).le

/--
theorem `supermartingale_of_condExp_sub_nonneg_nat` / 定理 `supermartingale_of_condExp_sub_nonneg_nat`

English:
theorem supermartingale_of_condExp_sub_nonneg_nat
  statement: [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
  proof: by
  rw [← neg_neg f]
  refine (submartingale_of_condExp_sub_nonneg_nat hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [Pi.zero_apply, Pi.neg_apply, neg_sub_neg]

中文:
定理 supermartingale_of_condExp_sub_nonneg_nat
  结论: [IsFiniteMeasure μ] {f : 自然数 -> Ω -> E}
  证明: by
  rw [← neg_neg f]
  refine (submartingale_of_condExp_sub_nonneg_nat hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [Pi.zero_apply, Pi.neg_apply, neg_sub_neg]

Depends on / 依赖: Pi.neg_apply, Pi.zero_apply, hadp.neg, neg_apply, neg_neg, neg_sub_neg, submartingale_of_condExp_sub_nonneg_nat, zero_apply
-/
theorem supermartingale_of_condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
    (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ)
    (hf : forall i, 0 <=ᵐ[μ] μ[f i - f (i + 1) | 𝒢 i]) : Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_condExp_sub_nonneg_nat hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [Pi.zero_apply, Pi.neg_apply, neg_sub_neg]

end OfSucc

section Preorder

variable [Preorder E]

-- Note that one cannot use `Submartingale.zero_le_of_predictable` to prove the other two
-- corresponding lemmas without imposing more restrictions to the ordering of `E`
/--
theorem `Submartingale.zero_le_of_predictable` / 定理 `Submartingale.zero_le_of_predictable`

English:
theorem Submartingale.zero_le_of_predictable
  statement: [SigmaFiniteFiltration μ 𝒢] {f : Nat -> Ω -> E}
  proof: by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ih.trans ((hfmgle.2.1 k (k + 1) k.le_succ).trans_eq <| Germ.coe_eq.mp <|
congr_arg Germ.ofFun condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _) hfmgle.integrable _)

中文:
定理 Submartingale.zero_le_of_predictable
  结论: [SigmaFiniteFiltration μ 𝒢] {f : 自然数 -> Ω -> E}
  证明: by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ih.trans ((hfmgle.2.1 k (k + 1) k.le_succ).trans_eq <| Germ.coe_eq.mp <|
congr_arg Germ.ofFun condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _) hfmgle.integrable _)

Depends on / 依赖: Germ.coe_eq.mp, Germ.ofFun, coe_eq, condExp_of_stronglyMeasurable, congr_arg, hfmgle, hfmgle.integrable, ih.trans, integrable, k.le_succ, le_succ, trans_eq
-/
theorem Submartingale.zero_le_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : Nat -> Ω -> E}
    (hfmgle : Submartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1)) (n : Nat) :
    f 0 <=ᵐ[μ] f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ih.trans ((hfmgle.2.1 k (k + 1) k.le_succ).trans_eq <| Germ.coe_eq.mp <|
congr_arg Germ.ofFun condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _) hfmgle.integrable _)

/--
theorem `Supermartingale.le_zero_of_predictable` / 定理 `Supermartingale.le_zero_of_predictable`

English:
theorem Supermartingale.le_zero_of_predictable
  statement: [SigmaFiniteFiltration μ 𝒢] {f : Nat -> Ω -> E}
  proof: by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp <| congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _)
(hfadp _) hfmgle.integrable _).symm.trans_le (hfmgle.2.1 k (k + 1) k.le_succ)).trans ih

中文:
定理 Supermartingale.le_zero_of_predictable
  结论: [SigmaFiniteFiltration μ 𝒢] {f : 自然数 -> Ω -> E}
  证明: by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp <| congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _)
(hfadp _) hfmgle.integrable _).symm.trans_le (hfmgle.2.1 k (k + 1) k.le_succ)).trans ih

Depends on / 依赖: Germ.coe_eq.mp, Germ.ofFun, coe_eq, condExp_of_stronglyMeasurable, congr_arg, hfmgle, hfmgle.integrable, integrable, k.le_succ, le_succ, symm.trans_le, trans_le
-/
theorem Supermartingale.le_zero_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : Nat -> Ω -> E}
    (hfmgle : Supermartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1))
    (n : Nat) : f n <=ᵐ[μ] f 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp <| congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _)
(hfadp _) hfmgle.integrable _).symm.trans_le (hfmgle.2.1 k (k + 1) k.le_succ)).trans ih

end Preorder

end SubSuper

/--
theorem `martingale_nat` / 定理 `martingale_nat`

English:
theorem martingale_nat
  statement: [CompleteSpace E] [IsFiniteMeasure μ]
  proof: by
  refine ⟨hadp, fun i j hij => ?_⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ => ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_congr_ae (hf k), 𝒢.condExp_condExp (f (k + 1)) hi

中文:
定理 martingale_nat
  结论: [CompleteSpace E] [IsFiniteMeasure μ]
  证明: by
  refine ⟨hadp, fun i j hij => ?_⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ => ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_congr_ae (hf k), 𝒢.condExp_condExp (f (k + 1)) hi

Depends on / 依赖: Nat.le_induction, ae_of_all, condExp_condExp, condExp_congr_ae, condExp_of_stronglyMeasurable, filter_upwards, le_induction
-/
theorem martingale_nat [CompleteSpace E] [IsFiniteMeasure μ]
    {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f)
    (hint : forall i, Integrable (f i) μ) (hf : forall i, f i =ᵐ[μ] μ[f (i + 1) | 𝒢 i]) :
    Martingale f 𝒢 μ := by
  refine ⟨hadp, fun i j hij => ?_⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ => ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_congr_ae (hf k), 𝒢.condExp_condExp (f (k + 1)) hik]
      with ω hω1 hω2 hω3
    rw [← hω1]; rw [hω2]; rw [hω3]

/--
theorem `martingale_of_setIntegral_eq_succ` / 定理 `martingale_of_setIntegral_eq_succ`

English:
theorem martingale_of_setIntegral_eq_succ
  statement: [CompleteSpace E] [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
  proof: by
refine martingale_nat hadp hint fun n => ae_eq_of_ae_eq_trim
    ((hint n).trim (𝒢.le n) (hadp n)).ae_eq_of_forall_setIntegral_eq _ _
    (integrable_condExp.trim (𝒢.le n) stronglyMeasurable_condExp) fun s ms hs => ?_
  rw [← setIntegral_trim (𝒢.le n) (hadp n) ms]; rw [← setIntegral_trim (𝒢.le n)

中文:
定理 martingale_of_setIntegral_eq_succ
  结论: [CompleteSpace E] [IsFiniteMeasure μ] {f : 自然数 -> Ω -> E}
  证明: by
refine martingale_nat hadp hint fun n => ae_eq_of_ae_eq_trim
    ((hint n).trim (𝒢.le n) (hadp n)).ae_eq_of_forall_setIntegral_eq _ _
    (integrable_condExp.trim (𝒢.le n) stronglyMeasurable_condExp) fun s ms hs => ?_
  rw [← setIntegral_trim (𝒢.le n) (hadp n) ms]; rw [← setIntegral_trim (𝒢.le n)

Depends on / 依赖: ae_eq_of_ae_eq_trim, ae_eq_of_forall_setIntegral_eq, integrable_condExp, integrable_condExp.trim, martingale_nat, setIntegral_condExp, setIntegral_trim, stronglyMeasurable_condExp
-/
theorem martingale_of_setIntegral_eq_succ [CompleteSpace E] [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
    (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ)
    (hf : forall i, forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f i ω ∂μ = ∫ ω in s, f (i + 1) ω ∂μ) :
    Martingale f 𝒢 μ := by
refine martingale_nat hadp hint fun n => ae_eq_of_ae_eq_trim
    ((hint n).trim (𝒢.le n) (hadp n)).ae_eq_of_forall_setIntegral_eq _ _
    (integrable_condExp.trim (𝒢.le n) stronglyMeasurable_condExp) fun s ms hs => ?_
  rw [← setIntegral_trim (𝒢.le n) (hadp n) ms]; rw [← setIntegral_trim (𝒢.le n) stronglyMeasurable_condExp ms]; rw [setIntegral_condExp (𝒢.le n) (hint (n + 1)) ms]; rw [hf n s ms]

/--
theorem `martingale_of_condExp_sub_eq_zero_nat` / 定理 `martingale_of_condExp_sub_eq_zero_nat`

English:
theorem martingale_of_condExp_sub_eq_zero_nat
  statement: [CompleteSpace E] [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
  proof: by
  refine martingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _)]; rw [eventuallyEq_comm]; rw [eventuallyEq_iff_sub]
  exact EventuallyEq.trans (condExp_sub (hint _) (hint _) _).symm (hf i)

中文:
定理 martingale_of_condExp_sub_eq_zero_nat
  结论: [CompleteSpace E] [IsFiniteMeasure μ] {f : 自然数 -> Ω -> E}
  证明: by
  refine martingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _)]; rw [eventuallyEq_comm]; rw [eventuallyEq_iff_sub]
  exact EventuallyEq.trans (condExp_sub (hint _) (hint _) _).symm (hf i)

Depends on / 依赖: EventuallyEq, EventuallyEq.trans, condExp_of_stronglyMeasurable, condExp_sub, eventuallyEq_comm, eventuallyEq_iff_sub, martingale_nat
-/
theorem martingale_of_condExp_sub_eq_zero_nat [CompleteSpace E] [IsFiniteMeasure μ] {f : Nat -> Ω -> E}
    (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ)
    (hf : forall i, μ[f (i + 1) - f i | 𝒢 i] =ᵐ[μ] 0) : Martingale f 𝒢 μ := by
  refine martingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _)]; rw [eventuallyEq_comm]; rw [eventuallyEq_iff_sub]
  exact EventuallyEq.trans (condExp_sub (hint _) (hint _) _).symm (hf i)

/--
theorem `Martingale.eq_zero_of_predictable` / 定理 `Martingale.eq_zero_of_predictable`

English:
theorem Martingale.eq_zero_of_predictable
  statement: [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
  proof: by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp (congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _)
      (hfmgle.integrable _))).symm.trans (hfmgle.2 k (k + 1) k.le_succ)).trans ih

中文:
定理 Martingale.eq_zero_of_predictable
  结论: [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
  证明: by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp (congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _)
      (hfmgle.integrable _))).symm.trans (hfmgle.2 k (k + 1) k.le_succ)).trans ih

Depends on / 依赖: Germ.coe_eq.mp, Germ.ofFun, coe_eq, condExp_of_stronglyMeasurable, congr_arg, hfmgle, hfmgle.integrable, integrable, k.le_succ, le_succ, symm.trans
-/
theorem Martingale.eq_zero_of_predictable [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
    {f : Nat -> Ω -> E}
    (hfmgle : Martingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1)) (n : Nat) :
    f n =ᵐ[μ] f 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp (congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _)
      (hfmgle.integrable _))).symm.trans (hfmgle.2 k (k + 1) k.le_succ)).trans ih

section IsStronglyPredictable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `Submartingale.zero_le_of_predictable'` / 定理 `Submartingale.zero_le_of_predictable'`

English:
theorem Submartingale.zero_le_of_predictable'
  statement: [Preorder E] [SigmaFiniteFiltration μ 𝒢]
  proof: zero_le_of_predictable hfmgle hf.measurable_add_one n

中文:
定理 Submartingale.zero_le_of_predictable'
  结论: [Preorder E] [SigmaFiniteFiltration μ 𝒢]
  证明: zero_le_of_predictable hfmgle hf.measurable_add_one n

Depends on / 依赖: hf.measurable_add_one, hfmgle, measurable_add_one, zero_le_of_predictable
-/
theorem Submartingale.zero_le_of_predictable' [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : Nat -> Ω -> E} (hfmgle : Submartingale f 𝒢 μ) (hf : IsStronglyPredictable 𝒢 f) (n : Nat) :
    f 0 <=ᵐ[μ] f n :=
  zero_le_of_predictable hfmgle hf.measurable_add_one n

/--
theorem `Supermartingale.le_zero_of_predictable'` / 定理 `Supermartingale.le_zero_of_predictable'`

English:
theorem Supermartingale.le_zero_of_predictable'
  statement: [Preorder E] [SigmaFiniteFiltration μ 𝒢]
  proof: le_zero_of_predictable hfmgle hfadp.measurable_add_one n

中文:
定理 Supermartingale.le_zero_of_predictable'
  结论: [Preorder E] [SigmaFiniteFiltration μ 𝒢]
  证明: le_zero_of_predictable hfmgle hfadp.measurable_add_one n

Depends on / 依赖: hfadp.measurable_add_one, hfmgle, le_zero_of_predictable, measurable_add_one
-/
theorem Supermartingale.le_zero_of_predictable' [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : Nat -> Ω -> E} (hfmgle : Supermartingale f 𝒢 μ) (hfadp : IsStronglyPredictable 𝒢 f)
    (n : Nat) : f n <=ᵐ[μ] f 0 :=
  le_zero_of_predictable hfmgle hfadp.measurable_add_one n

/--
theorem `Martingale.eq_zero_of_predictable'` / 定理 `Martingale.eq_zero_of_predictable'`

English:
theorem Martingale.eq_zero_of_predictable'
  statement: [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
  proof: eq_zero_of_predictable hfmgle hfadp.measurable_add_one n

中文:
定理 Martingale.eq_zero_of_predictable'
  结论: [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
  证明: eq_zero_of_predictable hfmgle hfadp.measurable_add_one n

Depends on / 依赖: eq_zero_of_predictable, hfadp.measurable_add_one, hfmgle, measurable_add_one
-/
theorem Martingale.eq_zero_of_predictable' [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
    {f : Nat -> Ω -> E}
    (hfmgle : Martingale f 𝒢 μ) (hfadp : IsStronglyPredictable 𝒢 f) (n : Nat) : f n =ᵐ[μ] f 0 :=
  eq_zero_of_predictable hfmgle hfadp.measurable_add_one n

end IsStronglyPredictable

namespace Submartingale

/--
theorem `integrable_stoppedValue` / 定理 `integrable_stoppedValue`

English:
theorem integrable_stoppedValue
  statement: [LE E] {f : Nat -> Ω -> E} (hf : Submartingale f 𝒢 μ)
  proof: integrable_stoppedValue Nat hτ hf.integrable hbdd

中文:
定理 integrable_stoppedValue
  结论: [LE E] {f : 自然数 -> Ω -> E} (hf : Submartingale f 𝒢 μ)
  证明: integrable_stoppedValue Nat hτ hf.integrable hbdd
-/
protected theorem integrable_stoppedValue [LE E] {f : Nat -> Ω -> E} (hf : Submartingale f 𝒢 μ)
    {τ : Ω -> Nat∞} (hτ : IsStoppingTime 𝒢 τ) {N : Nat} (hbdd : forall ω, τ ω <= N) :
    Integrable (stoppedValue f τ) μ :=
  integrable_stoppedValue Nat hτ hf.integrable hbdd

end Submartingale

section SumSMul

variable [CompleteSpace E] [PartialOrder E] [IsOrderedModule Real E] [ClosedIciTopology E]
  [IsOrderedAddMonoid E]

/--
theorem `Submartingale.sum_smul_sub` / 定理 `Submartingale.sum_smul_sub`

English:
theorem Submartingale.sum_smul_sub
  statement: [IsFiniteMeasure μ] {R : Real}
  proof: by
  have hξbdd : forall i, exists C, forall ω, ‖ξ i ω‖ <= C := fun i =>
    ⟨R, fun ω => (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩
  choose C hC using hξbdd
  have hint : forall m, Integrable (∑ k in Finset.range m, ξ k • (f (k + 1) - f k)) μ := fun m =>
      integrable_finsetSum' _ fun i

中文:
定理 Submartingale.sum_smul_sub
  结论: [IsFiniteMeasure μ] {R : 实数}
  证明: by
  have hξbdd : forall i, exists C, forall ω, ‖ξ i ω‖ <= C := fun i =>
    ⟨R, fun ω => (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩
  choose C hC using hξbdd
  have hint : forall m, Integrable (∑ k in Finset.range m, ξ k • (f (k + 1) - f k)) μ := fun m =>
      integrable_finsetSum' _ fun i

Depends on / 依赖: Finset, Finset.range, Integrable, Integrable.bdd_smul, StronglyAdapted, abs_of_nonneg, ae_of_all, aestronglyMeasurable, bdd_smul, hf.integrable, hnonneg, integrable, integrable_finsetSum, stronglyMeasurable, stronglyMeasurable.aestronglyMeasurable, trans_le
-/
theorem Submartingale.sum_smul_sub [IsFiniteMeasure μ] {R : Real}
    {f : Nat -> Ω -> E} {ξ : Nat -> Ω -> Real}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : forall n ω, ξ n ω <= R)
    (hnonneg : forall n ω, 0 <= ξ n ω) :
    Submartingale (fun n => ∑ k in Finset.range n, ξ k • (f (k + 1) - f k)) 𝒢 μ := by
  have hξbdd : forall i, exists C, forall ω, ‖ξ i ω‖ <= C := fun i =>
    ⟨R, fun ω => (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩
  choose C hC using hξbdd
  have hint : forall m, Integrable (∑ k in Finset.range m, ξ k • (f (k + 1) - f k)) μ := fun m =>
      integrable_finsetSum' _ fun i _ => Integrable.bdd_smul
        ((hf.integrable _).sub (hf.integrable _)) (C i)
        hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC i))
  have hadp : StronglyAdapted 𝒢 fun n => ∑ k in Finset.range n, ξ k • (f (k + 1) - f k) := by
    intro m
    refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact (hξ.stronglyMeasurable_le hi.le).smul
      ((hf.stronglyAdapted.stronglyMeasurable_le (Nat.succ_le_of_lt hi)).sub
        (hf.stronglyAdapted.stronglyMeasurable_le hi.le))
  refine submartingale_of_condExp_sub_nonneg_nat hadp hint fun i => ?_
  simp only [← Finset.sum_Ico_eq_sub _ (Nat.le_succ _), Nat.succ_eq_add_one, Nat.Ico_succ_singleton,
    Finset.sum_singleton]
  filter_upwards [hf.condExp_sub_nonneg i.le_succ,
    condExp_smul_of_aestronglyMeasurable_left (hξ i).aestronglyMeasurable
      (((hf.integrable (i + 1)).sub (hf.integrable i)).bdd_smul
      (C i) hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC i)))
      ((hf.integrable _).sub (hf.integrable _))] with ω hω1 hω2
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, Pi.smul_apply'] at hω1 hω2 ⊢
  grw [← smul_zero (0 : Real), hnonneg i ω, hω1, hω2]
  · exact hnonneg i ω
  · simp

/--
theorem `Submartingale.sum_smul_sub'` / 定理 `Submartingale.sum_smul_sub'`

English:
theorem Submartingale.sum_smul_sub'
  statement: [IsFiniteMeasure μ] {R : Real} {ξ : Nat -> Ω -> Real} {f : Nat -> Ω -> E}
  proof: hf.sum_smul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _

中文:
定理 Submartingale.sum_smul_sub'
  结论: [IsFiniteMeasure μ] {R : 实数} {ξ : 自然数 -> Ω -> 实数} {f : 自然数 -> Ω -> E}
  证明: hf.sum_smul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _

Depends on / 依赖: hf.sum_smul_sub, hnonneg, sum_smul_sub
-/
theorem Submartingale.sum_smul_sub' [IsFiniteMeasure μ] {R : Real} {ξ : Nat -> Ω -> Real} {f : Nat -> Ω -> E}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (n + 1)) (hbdd : forall n ω, ξ n ω <= R)
    (hnonneg : forall n ω, 0 <= ξ n ω) :
    Submartingale (fun n => ∑ k in Finset.range n, ξ (k + 1) • (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _

/--
theorem `Submartingale.sum_mul_sub` / 定理 `Submartingale.sum_mul_sub`

English:
theorem Submartingale.sum_mul_sub
  statement: [IsFiniteMeasure μ] {R : Real} {ξ f : Nat -> Ω -> Real}
  proof: hf.sum_smul_sub hξ hbdd hnonneg

中文:
定理 Submartingale.sum_mul_sub
  结论: [IsFiniteMeasure μ] {R : 实数} {ξ f : 自然数 -> Ω -> 实数}
  证明: hf.sum_smul_sub hξ hbdd hnonneg

Depends on / 依赖: hf.sum_smul_sub, hnonneg, sum_smul_sub
-/
theorem Submartingale.sum_mul_sub [IsFiniteMeasure μ] {R : Real} {ξ f : Nat -> Ω -> Real}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : forall n ω, ξ n ω <= R)
    (hnonneg : forall n ω, 0 <= ξ n ω) :
    Submartingale (fun n => ∑ k in Finset.range n, ξ k * (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub hξ hbdd hnonneg

/--
theorem `Submartingale.sum_mul_sub'` / 定理 `Submartingale.sum_mul_sub'`

English:
theorem Submartingale.sum_mul_sub'
  statement: [IsFiniteMeasure μ] {R : Real} {ξ f : Nat -> Ω -> Real}
  proof: hf.sum_smul_sub' hξ hbdd hnonneg

中文:
定理 Submartingale.sum_mul_sub'
  结论: [IsFiniteMeasure μ] {R : 实数} {ξ f : 自然数 -> Ω -> 实数}
  证明: hf.sum_smul_sub' hξ hbdd hnonneg

Depends on / 依赖: hf.sum_smul_sub, hnonneg, sum_smul_sub
-/
theorem Submartingale.sum_mul_sub' [IsFiniteMeasure μ] {R : Real} {ξ f : Nat -> Ω -> Real}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (n + 1)) (hbdd : forall n ω, ξ n ω <= R)
    (hnonneg : forall n ω, 0 <= ξ n ω) :
    Submartingale (fun n => ∑ k in Finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub' hξ hbdd hnonneg

end SumSMul

end Nat

end MeasureTheory
