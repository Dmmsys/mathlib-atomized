/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# Continuity of `MeasureTheory.Lp.compMeasurePreserving`

In this file we prove that the composition of an `L^p` function `g`
with a continuous measure-preserving map `f` is continuous in both arguments.

First, we prove it for indicator functions,
in terms of convergence of `μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))` to zero.

Then we prove the continuity of the function of two arguments
defined on `MeasureTheory.Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν}`.

Finally, we provide dot notation convenience lemmas.
-/

public section

open Filter Set MeasureTheory
open scoped ENNReal Topology symmDiff

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
  {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

namespace MeasureTheory
namespace Lp

variable (μ ν)
variable (E : Type*) [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compact sets
and `ν` is a locally finite measure.
Let `1 ≤ p < ∞` be an extended nonnegative real number.
Then the composition of a function `g : Lp E p ν`
and a measure-preserving continuous function `f : C(X, Y)`
is continuous in both variables. -/
/-
**MeasureTheory.Lp.compMeasurePreserving_continuous** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Lp`。
形式化陈述：compMeasurePreserving_continuous (hp : p != ∞) : Continuous fun gf : Lp E 
p ν × {f : C(X, Y) // MeasurePreserving f μ ν} => compMeasurePreserving gf.2.1 g
f.2.2 gf.1
参数：hp : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `continuous_prod_of_dense_continuous_lipschitzWith`：continuous_prod_of_de
nse_continuous_lipschitzWith [PseudoEMetricSpace α] [TopologicalSpace β] [Pseudo
EMetricSpace γ] (f : α × β -> γ) (K : R…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.Lp.simpleFunc.dense`：∀ {α : Type u_1} {E : Type u_4} [inst
 : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Measu
reTheory.Measure α} [in…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `MeasureTheory.Lp.simpleFunc.induction`：∀ {α : Type u_1} {E : Type u_4} [
inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : M
easureTheory.Measure α},   …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.continuous_indicatorConstLp_set`：continuous_indicatorConst
Lp_set [Fact (1 <= p)] {X : Type*} [TopologicalSpace X] {s : X -> Set α} {hs : f
orall x, MeasurableSet (s x)} {hμs …
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero`：tendsto_measu
re_symmDiff_preimage_nhds_zero {l : Filter α} {f : α -> C(X, Y)} {g : C(X, Y)} {
s : Set Y} (hfg : Tendsto f l (𝓝 g)) (hf : fora…
· 使用定理 `continuousAt_subtype_val`：continuousAt_subtype_val {p : X -> Prop} {x : 
Subtype p} : ContinuousAt ((↑) : Subtype p -> X) x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `MeasureTheory.Lp.isometry_compMeasurePreserving`：isometry_compMeasurePre
serving [Fact (1 <= p)] (hf : MeasurePreserving f μ μb) : Isometry (compMeasureP
reserving f hf : Lp E p μb -> Lp E p …

--- 原说明 ---
Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compac
t sets
and `ν` is a locally finite measure.
Let `1 ≤ p < ∞` be an extended nonnegative real number.
Then the composition of a function `g : Lp E p ν`
and a measure-preserving continuous function `f : C(X, Y)`
is continuous in both variables.
-/
theorem compMeasurePreserving_continuous (hp : p ≠ ∞) :
    Continuous fun gf : Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν} ↦
      compMeasurePreserving gf.2.1 gf.2.2 gf.1 := by
  have hp₀ : p ≠ 0 := (one_pos.trans_le Fact.out).ne'
  refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (MeasureTheory.Lp.simpleFunc.dense hp) ?_ fun f ↦ (isometry_compMeasurePreserving f.2).lipschitz
  intro f hf
  lift f to Lp.simpleFunc E p ν using hf
  induction f using Lp.simpleFunc.induction hp₀ hp with
  | add hfp hgp _ ihf ihg => exact ihf.add ihg
  | @indicatorConst c s hs hνs =>
    dsimp only [Lp.simpleFunc.coe_indicatorConst, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set hp fun f ↦ ?_
    apply tendsto_measure_symmDiff_preimage_nhds_zero continuousAt_subtype_val _ f.2
      hs.nullMeasurableSet hνs.ne
    exact .of_forall Subtype.property

end Lp

end MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-
**Filter.Tendsto.compMeasurePreservingLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.compMeasurePreservingLp {α : Type*} {l : Filter α} {f : α -
> Lp E p ν} {f₀ : Lp E p ν} {g : α -> C(X, Y)} {g₀ : C(X, Y)} (hf : Tendsto f l 
(𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀)) (hgm : forall a, MeasurePreserving (g a) μ ν) 
(hgm₀ : MeasurePreserving g₀ μ ν) (hp : p != ∞) : Tendsto (fun a => Lp.compMeasu
rePreserving (g a) (hgm a) (f a)) l (𝓝 (Lp.compMeasurePreserving g₀ hgm₀ f₀))
参数：X, Y；X, Y；hf : Tendsto f l (𝓝 f₀)；hg : Tendsto g l (𝓝 g₀)；hgm : forall a, Mea
surePreserving (g a) μ ν；hgm₀ : MeasurePreserving g₀ μ ν；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `MeasureTheory.Lp.compMeasurePreserving_continuous`：compMeasurePreserving
_continuous (hp : p != ∞) : Continuous fun gf : Lp E p ν × {f : C(X, Y) // Measu
rePreserving f μ ν} => compMeasurePrese…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.compMeasurePreservingLp {α : Type*} {l : Filter α}
    {f : α → Lp E p ν} {f₀ : Lp E p ν} {g : α → C(X, Y)} {g₀ : C(X, Y)}
    (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀))
    (hgm : ∀ a, MeasurePreserving (g a) μ ν) (hgm₀ : MeasurePreserving g₀ μ ν) (hp : p ≠ ∞) :
    Tendsto (fun a ↦ Lp.compMeasurePreserving (g a) (hgm a) (f a)) l
      (𝓝 (Lp.compMeasurePreserving g₀ hgm₀ f₀)) := by
  have := (Lp.compMeasurePreserving_continuous μ ν E hp).tendsto ⟨f₀, g₀, hgm₀⟩
  replace hg : Tendsto (fun a ↦ ⟨g a, hgm a⟩ : α → {g : C(X, Y) // MeasurePreserving g μ ν})
      l (𝓝 ⟨g₀, hgm₀⟩) :=
    tendsto_subtype_rng.2 hg
  convert! this.comp (hf.prodMk_nhds hg)

variable {Z : Type*} [TopologicalSpace Z] {f : Z → Lp E p ν} {g : Z → C(X, Y)} {s : Set Z} {z : Z}
/-
**ContinuousWithinAt.compMeasurePreservingLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.compMeasurePreservingLp (hf : ContinuousWithinAt f s z)
 (hg : ContinuousWithinAt g s z) (hgm : forall z, MeasurePreserving (g z) μ ν) (
hp : p != ∞) : ContinuousWithinAt (fun z => Lp.compMeasurePreserving (g z) (hgm 
z) (f z)) s z
参数：hf : ContinuousWithinAt f s z；hg : ContinuousWithinAt g s z；hgm : forall z, M
easurePreserving (g z) μ ν；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.compMeasurePreservingLp`：Filter.Tendsto.compMeasurePreser
vingLp {α : Type*} {l : Filter α} {f : α -> Lp E p ν} {f₀ : Lp E p ν} {g : α -> 
C(X, Y)} {g₀ : C(X, Y)} (hf …
-/
theorem ContinuousWithinAt.compMeasurePreservingLp (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    ContinuousWithinAt (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) s z :=
  Tendsto.compMeasurePreservingLp hf hg _ _ hp
/-
**ContinuousAt.compMeasurePreservingLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.compMeasurePreservingLp (hf : ContinuousAt f z) (hg : Continu
ousAt g z) (hgm : forall z, MeasurePreserving (g z) μ ν) (hp : p != ∞) : Continu
ousAt (fun z => Lp.compMeasurePreserving (g z) (hgm z) (f z)) z
参数：hf : ContinuousAt f z；hg : ContinuousAt g z；hgm : forall z, MeasurePreserving
 (g z) μ ν；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.compMeasurePreservingLp`：Filter.Tendsto.compMeasurePreser
vingLp {α : Type*} {l : Filter α} {f : α -> Lp E p ν} {f₀ : Lp E p ν} {g : α -> 
C(X, Y)} {g₀ : C(X, Y)} (hf …
-/
theorem ContinuousAt.compMeasurePreservingLp (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    ContinuousAt (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) z :=
  Tendsto.compMeasurePreservingLp hf hg _ _ hp
/-
**ContinuousOn.compMeasurePreservingLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.compMeasurePreservingLp (hf : ContinuousOn f s) (hg : Continu
ousOn g s) (hgm : forall z, MeasurePreserving (g z) μ ν) (hp : p != ∞) : Continu
ousOn (fun z => Lp.compMeasurePreserving (g z) (hgm z) (f z)) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s；hgm : forall z, MeasurePreserving
 (g z) μ ν；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousWithinAt.compMeasurePreservingLp`：ContinuousWithinAt.compMeasu
rePreservingLp (hf : ContinuousWithinAt f s z) (hg : ContinuousWithinAt g s z) (
hgm : forall z, MeasurePreservin…
-/
theorem ContinuousOn.compMeasurePreservingLp (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    ContinuousOn (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) s := fun z hz ↦
  (hf z hz).compMeasurePreservingLp (hg z hz) hgm hp
/-
**Continuous.compMeasurePreservingLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.compMeasurePreservingLp (hf : Continuous f) (hg : Continuous g)
 (hgm : forall z, MeasurePreserving (g z) μ ν) (hp : p != ∞) : Continuous (fun z
 => Lp.compMeasurePreserving (g z) (hgm z) (f z))
参数：hf : Continuous f；hg : Continuous g；hgm : forall z, MeasurePreserving (g z) μ
 ν；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.compMeasurePreservingLp`：ContinuousAt.compMeasurePreserving
Lp (hf : ContinuousAt f z) (hg : ContinuousAt g z) (hgm : forall z, MeasurePrese
rving (g z) μ ν) (hp : p !…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.compMeasurePreservingLp (hf : Continuous f) (hg : Continuous g)
    (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    Continuous (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) :=
  continuous_iff_continuousAt.mpr fun _ ↦
    hf.continuousAt.compMeasurePreservingLp hg.continuousAt hgm hp
