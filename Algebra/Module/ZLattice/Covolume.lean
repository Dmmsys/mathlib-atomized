/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of ℤ-lattices

Let `E` be a finite-dimensional real vector space.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `ℤ`-submodule of `E` that spans `E` over `ℝ`.

## Main definitions and results

* `ZLattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
  domain of `L`.

* `ZLattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
  choice of the fundamental domain of `L`.

* `ZLattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
  value of the determinant of any `ℤ`-basis of `L`.

* `ZLattice.covolume_div_covolume_eq_relIndex`: Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the
  index of `L₁` inside `L₂` is equal to `covolume L₁ / covolume L₂`.

* `ZLattice.covolume.tendsto_card_div_pow`: Let `s` be a bounded measurable set of `ι → ℝ`, then
  the number of points in `s ∩ n⁻¹ • L` divided by `n ^ card ι` tends to `volume s / covolume L`
  when `n : ℕ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_div_pow'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_div_pow''` for the general version.

* `ZLattice.covolume.tendsto_card_le_div`: Let `X` be a cone in `ι → ℝ` and let `F : (ι → ℝ) → ℝ`
  be a function such that `F (c • x) = c ^ card ι * F x`. Then the number of points `x ∈ X` such
  that `F x ≤ c` divided by `c` tends to `volume {x ∈ X | F x ≤ 1} / covolume L`
  when `c : ℝ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_le_div'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_le_div''` for the general version.

## Naming convention

Some results are true in the case where the ambient finite-dimensional real vector space is the
pi-space `ι → ℝ` and in the case where it is an `InnerProductSpace`. We use the following
convention: the plain name is for the pi case, for e.g. `volume_image_eq_volume_div_covolume`. For
the same result in the `InnerProductSpace` case, we add a `prime`, for e.g.
`volume_image_eq_volume_div_covolume'`. When the same result exists in the
general case, we had two primes, e.g. `covolume.tendsto_card_div_pow''`.

-/

@[expose] public section

noncomputable section

namespace ZLattice

open Submodule MeasureTheory Module MeasureTheory Module ZSpan

section General

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (L : Submodule ℤ E)

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`ZLattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
/-
**ZLattice.covolume** 是 Mathlib 中的一个定义，位于命名空间 `ZLattice`。
形式化陈述：covolume (μ : Measure E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`ZLattice.covolume_eq_volume` for the proof that the volume does not depend on t
he choice of
the fundamental domain.
-/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.privateInPublic true in
/-
**ZLattice.covolume_eq_measure_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZLat
tice`。
形式化陈述：covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDom
ain L F μ) : covolume L μ = μ.real F
参数：h : IsAddFundamentalDomain L F μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.instMeasurableVAdd`：∀ {G : Type u_2} {α : Type u_3} [inst : 
MeasurableSpace G] [inst_1 : MeasurableSpace α] [inst_2 : AddGroup G]   [inst_3 
: AddAction G α] [Me…
· 使用定理 `measurableVAdd_of_add`：∀ (M : Type u_2) [inst : Add M] [inst_1 : Measura
bleSpace M] [MeasurableAdd M], MeasurableVAdd M M
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Subgroup.vaddInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableSpace α]  
 {μ : MeasureTheory.Measure α} [M…
· 使用定理 `MeasureTheory.Measure.IsAddLeftInvariant.vaddInvariantMeasure`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 : Add G
] [μ.IsAddLeftInvariant],   MeasureTheory.VAddInvar…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.covolume_eq_volume`：∀ {G : Type u_1
} {α : Type u_3} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : Measurab
leSpace α]   (ν : MeasureTheory.Measure α) [C…
· 使用定理 `MeasurableVAdd.toMeasurableConstVAdd`：∀ {M : Type u_2} {α : Type u_3} {i
nst : VAdd M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableVAdd M α], M…
-/
theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = μ.real F := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

set_option backward.privateInPublic true in
/-
**ZLattice.covolume_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice`。
形式化陈述：covolume_ne_zero : covolume L μ != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.covolume_eq_measure_fundamentalDomain`：covolume_eq_measure_fund
amentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) : covolume L μ = μ.
real F
· 使用定理 `ZLattice.isAddFundamentalDomain`：ZLattice.isAddFundamentalDomain {E : Ty
pe*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] {L :
 Submodule Int E} [Di…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.measureReal_ne_zero_iff`：measureReal_ne_zero_iff (h : μ s 
!= ∞
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Bornology.IsBounded.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} [inst : PseudoMetricSpace α] [ProperSpace α] {μ : MeasureTheory.Measure α}
   [MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `ZSpan.fundamentalDomain_isBounded`：fundamentalDomain_isBounded [Finite ι
] [HasSolidNorm K] : IsBounded (fundamentalDomain b)
· 使用定理 `ZSpan.measure_fundamentalDomain_ne_zero`：measure_fundamentalDomain_ne_ze
ro [Finite ι] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddH
aarMeasure μ] : μ (fundamenta…
-/
theorem covolume_ne_zero : covolume L μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    measureReal_ne_zero_iff (ne_of_lt _)]
  · exact measure_fundamentalDomain_ne_zero _
  · exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

set_option backward.privateInPublic true in
/-
**ZLattice.covolume_pos** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice`。
形式化陈述：covolume_pos : 0 < covolume L μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ZLattice.covolume_ne_zero`：covolume_ne_zero : covolume L μ != 0
-/
theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

set_option backward.privateInPublic true in
/-
**ZLattice.covolume_comap** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice`。
形式化陈述：covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [Fi
niteDimensional Real F] [MeasurableSpace F] [BorelSpace F] (ν : Measure F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.covolume_eq_measure_fundamentalDomain`：covolume_eq_measure_fund
amentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) : covolume L μ = μ.
real F
· 使用定理 `ZLattice.isAddFundamentalDomain`：ZLattice.isAddFundamentalDomain {E : Ty
pe*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] {L :
 Submodule Int E} [Di…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instDiscreteTopologySubtypeMemSubmoduleIntComap`：∀ (K : Type u_1) [inst 
: NormedField K] {E : Type u_2} {F : Type u_3} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace K E] [inst_3 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.measureReal_preimage`：measureReal_preima
ge {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurabl
eSet s μb) : μa.real (f ⁻¹' s) = μb.real s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `ZSpan.fundamentalDomain_measurableSet`：fundamentalDomain_measurableSet [
MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] : MeasurableSet (fundamen
talDomain b)
· 使用定理 `ContinuousLinearEquiv.image_symm_eq_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.coe_toLinearEquiv`：coe_toLinearEquiv (f : M₁ ≃SL[σ
₁₂] M₂) : ⇑f.toLinearEquiv = f
· 使用定理 `ZSpan.map_fundamentalDomain`：map_fundamentalDomain {F : Type*} [NormedAd
dCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F) : f '' (fundamentalDomain b) = f
undamentalDomain …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
· 使用定理 `Module.Basis.ofZLatticeComap_apply`：ofZLatticeComap_apply (e : F ≃ₗ[K] E
) {ι : Type*} (b : Basis ι Int L) (i : ι) : b.ofZLatticeComap K L e i = e.symm (
b i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F := by volume_tac) [Measure.IsAddHaarMeasure ν]
    {e : F ≃L[ℝ] E} (he : MeasurePreserving e ν μ) :
    covolume (ZLattice.comap ℝ L e.toLinearMap) ν = covolume L μ := by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeComap ℝ L e.toLinearEquiv) ν)), ← he.measureReal_preimage
    (fundamentalDomain_measurableSet _).nullMeasurableSet, ← e.image_symm_eq_preimage,
    ← e.symm.coe_toLinearEquiv, map_fundamentalDomain]
  congr!
  ext; simp

set_option backward.privateInPublic true in
/-
**ZLattice.covolume_eq_det_mul_measureReal** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice`。
形式化陈述：covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι] (b
 : Basis ι Int L) (b₀ : Basis ι Real E) : covolume L μ = |b₀.det ((↑) ∘ b)| * μ.
real (fundamentalDomain b₀)
参数：b : Basis ι Int L；b₀ : Basis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.covolume_eq_measure_fundamentalDomain`：covolume_eq_measure_fund
amentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) : covolume L μ = μ.
real F
· 使用定理 `ZLattice.isAddFundamentalDomain`：ZLattice.isAddFundamentalDomain {E : Ty
pe*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] {L :
 Submodule Int E} [Di…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ZSpan.measureReal_fundamentalDomain`：measureReal_fundamentalDomain [Fint
ype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E) [BorelSpace E] [Measu
re.IsAddHaarMeasure μ] (b…
· 使用定理 `MeasureTheory.measureReal_congr`：measureReal_congr (H : s =ᵐ[μ] t) : μ.r
eal s = μ.real t
· 使用定理 `ZSpan.fundamentalDomain_ae_parallelepiped`：fundamentalDomain_ae_parallel
epiped [Fintype ι] [MeasurableSpace E] (μ : Measure E) [BorelSpace E] [Measure.I
sAddHaarMeasure μ] : fundamenta…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
-/
theorem covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (b₀ : Basis ι ℝ E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * μ.real (fundamentalDomain b₀) := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    measureReal_fundamentalDomain _ _ b₀,
    measureReal_congr (fundamentalDomain_ae_parallelepiped b₀ μ)]
  congr
  ext
  exact b.ofZLatticeBasis_apply ℝ L _
/-
**ZLattice.covolume_eq_det** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice`。
形式化陈述：covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule Int
 (ι -> Real)) [DiscreteTopology L] [IsZLattice Real L] (b : Basis ι Int L) : cov
olume L = |(Matrix.of ((↑) ∘ b)).det|
参数：L : Submodule Int (ι -> Real)；b : Basis ι Int L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.covolume_eq_measure_fundamentalDomain`：covolume_eq_measure_fund
amentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) : covolume L μ = μ.
real F
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `ZLattice.isAddFundamentalDomain`：ZLattice.isAddFundamentalDomain {E : Ty
pe*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] {L :
 Submodule Int E} [Di…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ZSpan.volume_real_fundamentalDomain`：volume_real_fundamentalDomain [Fint
ype ι] [DecidableEq ι] (b : Basis ι Real (ι -> Real)) : volume.real (fundamental
Domain b) = |(Matrix.of b…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
（共 32 条，此处仅展示前 30 条）
-/
theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    volume_real_fundamentalDomain]
  congr
  ext1
  exact b.ofZLatticeBasis_apply ℝ L _
/-
**ZLattice.covolume_eq_det_inv** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice`。
形式化陈述：covolume_eq_det_inv {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real)
) [DiscreteTopology L] [IsZLattice Real L] (b : Basis ι Int L) : covolume L = |(
LinearEquiv.det (b.ofZLatticeBasis Real L).equivFun : Real)|⁻¹
参数：L : Submodule Int (ι -> Real)；b : Basis ι Int L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.covolume_eq_det`：covolume_eq_det {ι : Type*} [Fintype ι] [Decid
ableEq ι] (L : Submodule Int (ι -> Real)) [DiscreteTopology L] [IsZLattice Real 
L] (b : Basis …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.basisFun_det_apply`：Pi.basisFun_det_apply (v : ι -> ι -> R) : (Pi.bas
isFun R ι).det v = (Matrix.of v).det
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.isUnit_det`：isUnit_det (e' : Basis ι R M) : IsUnit (e.det e
')
· 使用定理 `Module.Basis.det_inv`：det_inv (b : Basis ι A M) (b' : Basis ι A M) : (b.
isUnit_det b').unit⁻¹ = b'.det b
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Module.Basis.det_basis`：det_basis (b : Basis ι A M) (b' : Basis ι A M) :
 LinearMap.det (b'.equiv b (Equiv.refl ι)).toLinearMap = b'.det b
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
-/
theorem covolume_eq_det_inv {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(LinearEquiv.det (b.ofZLatticeBasis ℝ L).equivFun : ℝ)|⁻¹ := by
  classical
  rw [covolume_eq_det L b, ← Pi.basisFun_det_apply, show (((↑) : L → _) ∘ ⇑b) =
    (b.ofZLatticeBasis ℝ) by ext; simp, ← Basis.det_inv, ← abs_inv, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, ← Basis.det_basis, LinearEquiv.coe_det]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the index of `L₁` inside `L₂` is equal to
`covolume L₁ / covolume L₂`.
-/
/-
**ZLattice.covolume_div_covolume_eq_relIndex** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice
`。
形式化陈述：covolume_div_covolume_eq_relIndex {ι : Type*} [Fintype ι] (L₁ L₂ : Submodu
le Int (ι -> Real)) [DiscreteTopology L₁] [IsZLattice Real L₁] [DiscreteTopology
 L₂] [IsZLattice Real L₂] (h : L₁ <= L₂) : covolume L₁ / covolume L₂ = L₁.toAddS
ubgroup.relIndex L₂.toAddSubgroup
参数：L₁ L₂ : Submodule Int (ι -> Real)；h : L₁ <= L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.relIndex_eq_natAbs_det`：AddSubgroup.relIndex_eq_natAbs_det {
E : Type*} [AddCommGroup E] (L₁ L₂ : AddSubgroup E) (H : L₁ <= L₂) {ι : Type*} [
DecidableEq ι] [Fintype …
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.det_mul_det`：det_mul_det (b b' b'' : Basis ι A M) : b.det b
' * b'.det b'' = b.det b''
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Pi.basisFun_det_apply`：Pi.basisFun_det_apply (v : ι -> ι -> R) : (Pi.bas
isFun R ι).det v = (Matrix.of v).det
· 使用定理 `Module.Basis.isUnit_det`：isUnit_det (e' : Basis ι R M) : IsUnit (e.det e
')
· 使用定理 `Module.Basis.det_inv`：det_inv (b : Basis ι A M) (b' : Basis ι A M) : (b.
isUnit_det b').unit⁻¹ = b'.det b
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `ZLattice.covolume_eq_det`：covolume_eq_det {ι : Type*} [Fintype ι] [Decid
ableEq ι] (L : Submodule Int (ι -> Real)) [DiscreteTopology L] [IsZLattice Real 
L] (b : Basis …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `Int.cast_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype 
n] {R : Type v} [inst_2 : CommRing R] (M : Matrix n n ℤ),   ↑M.det = (M.map fun 
x …
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the index of `L₁` inside `L₂` is equ
al to
`covolume L₁ / covolume L₂`.
-/
theorem covolume_div_covolume_eq_relIndex {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    covolume L₁ / covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₁ := IsZLattice.basis L₁
  let b₂ := IsZLattice.basis L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  trans |(b₂.ofZLatticeBasis ℝ).det (b₁.ofZLatticeBasis ℝ)|
  · rw [← Basis.det_mul_det _ (Pi.basisFun ℝ ι) _, abs_mul, Pi.basisFun_det_apply,
      ← Basis.det_inv, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_det_apply,
      covolume_eq_det _ b₁, covolume_eq_det _ b₂, mul_comm, abs_inv]
    congr 3 <;> ext <;> simp
  · rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
    congr; ext i j
    rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, Basis.ofZLatticeBasis_apply]
    exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (coe_mem _)⟩ i)

/--
A more general version of `covolume_div_covolume_eq_relIndex`;
see the `Naming conventions` section in the introduction.
-/
/-
**ZLattice.covolume_div_covolume_eq_relIndex'** 是 Mathlib 中的一个定理，位于命名空间 `ZLattic
e`。
形式化陈述：covolume_div_covolume_eq_relIndex' {E : Type*} [NormedAddCommGroup E] [Inn
erProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpac
e E] (L₁ L₂ : Submodule Int E) [DiscreteTopology L₁] [IsZLattice Real L₁] [Discr
eteTopology L₂] [IsZLattice Real L₂] (h : L₁ <= L₂) : covolume L₁ / covolume L₂ 
= L₁.toAddSubgroup.relIndex L₂.toAddSubgroup
参数：L₁ L₂ : Submodule Int E；h : L₁ <= L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `OrthonormalBasis.measurePreserving_repr_symm`：OrthonormalBasis.measurePr
eserving_repr_symm (b : OrthonormalBasis ι Real F) : MeasurePreserving b.repr.sy
mm volume volume
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`：EuclideanSpa
ce.volume_preserving_symm_measurableEquiv_toLp : MeasurePreserving (MeasurableEq
uiv.toLp 2 (ι -> Real)).symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZLattice.covolume_comap`：covolume_comap {F : Type*} [NormedAddCommGroup 
F] [NormedSpace Real F] [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpa
ce F] (ν : Me…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `ZLattice.covolume_div_covolume_eq_relIndex`：covolume_div_covolume_eq_rel
Index {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule Int (ι -> Real)) [DiscreteTopol
ogy L₁] [IsZLattice Real L₁] [Di…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A more general version of `covolume_div_covolume_eq_relIndex`;
see the `Naming conventions` section in the introduction.
-/
theorem covolume_div_covolume_eq_relIndex' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂]
    [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    covolume L₁ / covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  let f := (EuclideanSpace.equiv _ ℝ).symm.trans
    (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  rw [← covolume_comap L₁ volume volume hf, ← covolume_comap L₂ volume volume hf,
    covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'), ZLattice.comap_toAddSubgroup,
    ZLattice.comap_toAddSubgroup, Nat.cast_inj, LinearEquiv.toAddMonoidHom_commutes,
    AddSubgroup.comap_equiv_eq_map_symm', AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]
/-
**ZLattice.volume_image_eq_volume_div_covolume** 是 Mathlib 中的一个定理，位于命名空间 `ZLatti
ce`。
形式化陈述：volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (L : Submodule
 Int (ι -> Real)) [DiscreteTopology L] [IsZLattice Real L] (b : Basis ι Int L) {
s : Set (ι -> Real)} : volume ((b.ofZLatticeBasis Real L).equivFun '' s) = volum
e s / ENNReal.ofReal (covolume L)
参数：L : Submodule Int (ι -> Real)；b : Basis ι Int L；ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.image_eq_preimage_symm`：∀ {R : Type u_1} {S : Type u_6} {M :
 Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 :
 AddCommMonoid M] [inst_…
· 使用定理 `MeasureTheory.Measure.addHaar_preimage_linearEquiv`：addHaar_preimage_lin
earEquiv (f : E ≃ₗ[Real] E) (s : Set E) : μ (f ⁻¹' s) = ENNReal.ofReal |LinearMa
p.det (f.symm : E ->ₗ[Real] E)| * μ s
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
· 使用定理 `ZLattice.covolume_eq_det_inv`：covolume_eq_det_inv {ι : Type*} [Fintype ι
] (L : Submodule Int (ι -> Real)) [DiscreteTopology L] [IsZLattice Real L] (b : 
Basis ι Int L) : c…
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `ENNReal.ofReal_inv_of_pos`：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : E
NNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
（共 32 条，此处仅展示前 30 条）
-/
theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) {s : Set (ι → ℝ)} :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  rw [LinearEquiv.image_eq_preimage_symm, Measure.addHaar_preimage_linearEquiv,
    LinearEquiv.symm_symm, covolume_eq_det_inv L b, ENNReal.div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero), inv_inv, LinearEquiv.coe_det]

set_option backward.isDefEq.respectTransparency.types false in
/-- A more general version of `ZLattice.volume_image_eq_volume_div_covolume`;
see the `Naming conventions` section in the introduction. -/
/-
**ZLattice.volume_image_eq_volume_div_covolume'** 是 Mathlib 中的一个定理，位于命名空间 `ZLatt
ice`。
形式化陈述：volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E] [I
nnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSp
ace E] (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] {ι : Type*
} [Fintype ι] (b : Basis ι Int L) {s : Set E} (hs : NullMeasurableSet s) : volum
e ((b.ofZLatticeBasis Real).equivFun '' s) = volume s / ENNReal.ofReal (covolume
 L)
参数：L : Submodule Int E；b : Basis ι Int L；hs : NullMeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `OrthonormalBasis.measurePreserving_repr_symm`：OrthonormalBasis.measurePr
eserving_repr_symm (b : OrthonormalBasis ι Real F) : MeasurePreserving b.repr.sy
mm volume volume
· 使用定理 `PiLp.volume_preserving_toLp`：PiLp.volume_preserving_toLp : MeasurePreser
ving (@toLp 2 (ι -> Real))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `ZLattice.covolume_comap`：covolume_comap {F : Type*} [NormedAddCommGroup 
F] [NormedSpace Real F] [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpa
ce F] (ν : Me…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
A more general version of `ZLattice.volume_image_eq_volume_div_covolume`;
see the `Naming conventions` section in the introduction.
-/
theorem volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) {s : Set E} (hs : NullMeasurableSet s) :
    volume ((b.ofZLatticeBasis ℝ).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  let e : Fin (finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis ℝ)])
  let f := (EuclideanSpace.equiv ι ℝ).symm.trans
    ((stdOrthonormalBasis ℝ E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp ι)
  rw [← hf.measure_preimage hs, ← (covolume_comap L volume volume hf),
    ← volume_image_eq_volume_div_covolume (ZLattice.comap ℝ L f.toLinearMap)
    (b.ofZLatticeComap ℝ L f.toLinearEquiv), Basis.ofZLatticeBasis_comap,
    ← f.image_symm_eq_preimage, ← Set.image_comp]
  simp

end Basic

namespace covolume

section General

open Filter Fintype Pointwise Topology BoxIntegral Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

set_option backward.isDefEq.respectTransparency.types false in
/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the general case;
see the `Naming convention` section in the introduction. -/
/-
**ZLattice.covolume.tendsto_card_div_pow''** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice.c
ovolume`。
形式化陈述：tendsto_card_div_pow'' [FiniteDimensional Real E] [MeasurableSpace E] [Bor
elSpace E] {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) (hs₃ : volume
 (frontier ((b.ofZLatticeBasis Real).equivFun '' s)) = 0) : Tendsto (fun n : Nat
 => (Nat.card (s inter (n : Real)⁻¹ • L : Set E) : Real) / n ^ card ι) atTop (𝓝 
(volume.real ((b.ofZLatticeBasis Real).equivFun '' s)))
参数：hs₁ : IsBounded s；hs₂ : MeasurableSet s；hs₃ : volume (frontier ((b.ofZLattice
Basis Real).equivFun '' s)) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.ofZLatticeBasis_span`：ofZLatticeBasis_span : span Int (Set.
range (b.ofZLatticeBasis K)) = L
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.mem_inv_smul_set_iff₀`：mem_inv_smul_set_iff₀ (ha : a != 0) (A : Set 
β) (x : β) : x in a⁻¹ • A ↔ a • x in A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `ZLattice.covolume.tendsto_card_div_pow` for the general case;
see the `Naming convention` section in the introduction.
-/
theorem tendsto_card_div_pow'' [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier ((b.ofZLatticeBasis ℝ).equivFun '' s)) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ card ι)
      atTop (𝓝 (volume.real ((b.ofZLatticeBasis ℝ).equivFun '' s))) := by
  refine Tendsto.congr' ?_
    (tendsto_card_div_pow_atTop_volume ((b.ofZLatticeBasis ℝ).equivFun '' s) ?_ ?_ hs₃)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    congr
    refine Nat.card_congr <| ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.subtypeEquiv fun x ↦ ?_).symm
    simp_rw [Set.mem_inter_iff, ← b.ofZLatticeBasis_span ℝ, LinearEquiv.coe_toEquiv,
      Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, and_congr_right_iff, Set.mem_inv_smul_set_iff₀
      (mod_cast hn.ne' : (n : ℝ) ≠ 0), ← Finsupp.coe_smul, ← map_smul, SetLike.mem_coe,
      Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    exact Bornology.IsVonNBounded.image hs₁ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂
/-
**ZLattice.covolume.tendsto_card_le_div''_aux** 是 Mathlib 中的一个定理，位于命名空间 `ZLattic
e.covolume`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_card_le_div''_aux
    {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x)) {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ card ι} := by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_ofPred_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h ↦ hX h (inv_pos_of_pos hc)⟩

/-- A version of `ZLattice.covolume.tendsto_card_le_div` for the general case;
see the `Naming conventions` section in the introduction. -/
/-
**ZLattice.covolume.tendsto_card_le_div''** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice.co
volume`。
形式化陈述：tendsto_card_le_div'' [FiniteDimensional Real E] [MeasurableSpace E] [Bore
lSpace E] [Nonempty ι] {X : Set E} (hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r 
-> r • x in X) {F : E -> Real} (h₁ : forall x ⦃r : Real⦄, 0 <= r -> F (r • x) = 
r ^ card ι * (F x)) (h₂ : IsBounded {x in X | F x <= 1}) (h₃ : MeasurableSet {x 
in X | F x <= 1}) (h₄ : volume (frontier ((b.ofZLatticeBasis Real L).equivFun ''
 {x | x in X ∧ F x <= 1})) = 0) : Tendsto (fun c : Real => Nat.card ({x in X | F
 x <= c} inter L : Set E) 
参数：hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X；h₁ : forall x ⦃r : 
Real⦄, 0 <= r -> F (r • x) = r ^ card ι * (F x)；h₂ : IsBounded {x in X | F x <= 
1}；h₃ : MeasurableSet {x in X | F x <= 1}；h₄ : volume (frontier ((b.ofZLatticeBa
sis Real L).equivFun '' {x | x in X ∧ F x <= 1})) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Equiv.trans_apply`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) 
(g : β ≃ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `LinearEquiv.coe_toEquiv`：coe_toEquiv : ⇑(e.toEquiv) = e
· 使用定理 `Equiv.smulRight_apply`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWith
Zero α] [inst_1 : MulAction α β] {a : α} (ha : a ≠ 0) (b : β),   (Equiv.smulRigh
t ha) b = a…
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `ZLattice.covolume.tendsto_card_le_div` for the general case;
see the `Naming conventions` section in the introduction.
-/
theorem tendsto_card_le_div'' [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nonempty ι] {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier ((b.ofZLatticeBasis ℝ L).equivFun '' {x | x ∈ X ∧ F x ≤ 1})) = 0) :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 (volume.real ((b.ofZLatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}))) := by
  refine Tendsto.congr' ?_ <| (tendsto_card_div_pow_atTop_volume'
      ((b.ofZLatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}) ?_ ?_ h₄ fun x y hx hy ↦ ?_).comp
        (tendsto_rpow_atTop <| inv_pos.mpr
          (Nat.cast_pos.mpr card_pos) : Tendsto (fun x ↦ x ^ (card ι : ℝ)⁻¹) atTop atTop)
  · filter_upwards [eventually_gt_atTop 0] with c hc
    have aux₁ : (card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr card_ne_zero
    have aux₂ : 0 < c ^ (card ι : ℝ)⁻¹ := Real.rpow_pos_of_pos hc _
    have aux₃ : (c ^ (card ι : ℝ)⁻¹)⁻¹ ≠ 0 := inv_ne_zero aux₂.ne'
    have aux₄ : c ^ (-(card ι : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    obtain ⟨hc₁, hc₂⟩ := lt_iff_le_and_ne.mp hc
    rw [Function.comp_apply, ← Real.rpow_natCast, Real.rpow_inv_rpow hc₁ aux₁, eq_comm]
    congr
    refine Nat.card_congr <| Equiv.subtypeEquiv ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.trans
          (Equiv.smulRight aux₄)) fun _ ↦ ?_
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      Equiv.smulRight_apply, Real.rpow_neg hc₁, Set.smul_mem_smul_set_iff₀ aux₃,
      ← Set.mem_smul_set_iff_inv_smul_mem₀ aux₂.ne', ← image_smul_set,
      tendsto_card_le_div''_aux hX h₁ aux₂, ← Real.rpow_natCast, ← Real.rpow_mul hc₁,
      inv_mul_cancel₀ aux₁, Real.rpow_one]
    simp_rw [SetLike.mem_coe, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
      and_congr_right_iff, ← b.ofZLatticeBasis_span ℝ, Basis.mem_span_iff_repr_mem,
      Pi.basisFun_repr, Basis.equivFun_apply, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at h₂ ⊢
    exact Bornology.IsVonNBounded.image h₂ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr h₃
  · simp_rw [← image_smul_set]
    apply Set.image_mono
    rw [tendsto_card_le_div''_aux hX h₁ hx,
      tendsto_card_le_div''_aux hX h₁ (lt_of_lt_of_le hx hy)]
    exact fun a ⟨ha₁, ha₂⟩ ↦ ⟨ha₁, le_trans ha₂ <| pow_le_pow_left₀ (le_of_lt hx) hy _⟩

end General

section Pi

open Filter Fintype Pointwise Topology Bornology

/-
**ZLattice.covolume.frontier_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice.covolu
me`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem frontier_equivFun {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Finite ι]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (b : Basis ι ℝ E) (s : Set E) :
    frontier (b.equivFun '' s) = b.equivFun '' (frontier s) := by
  rw [LinearEquiv.image_eq_preimage_symm, LinearEquiv.image_eq_preimage_symm]
  exact (Homeomorph.preimage_frontier b.equivFunL.toHomeomorph.symm s).symm

variable {ι : Type*} [Fintype ι]
variable (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
/-
**ZLattice.covolume.tendsto_card_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice.cov
olume`。
形式化陈述：tendsto_card_div_pow (b : Basis ι Int L) {s : Set (ι -> Real)} (hs₁ : IsBo
unded s) (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) : Tendsto (fun 
n : Nat => (Nat.card (s inter (n : Real)⁻¹ • L : Set (ι -> Real)) : Real) / n ^ 
card ι) atTop (𝓝 (volume.real s / covolume L))
参数：b : Basis ι Int L；ι -> Real；hs₁ : IsBounded s；hs₂ : MeasurableSet s；hs₃ : vol
ume (frontier s) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `ZLattice.volume_image_eq_volume_div_covolume`：volume_image_eq_volume_div
_covolume {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real)) [DiscreteTopol
ogy L] [IsZLattice Real L] (b : Ba…
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ZLattice.covolume_pos`：covolume_pos : 0 < covolume L μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `ZLattice.covolume.tendsto_card_div_pow''`：tendsto_card_div_pow'' [Finite
Dimensional Real E] [MeasurableSpace E] [BorelSpace E] {s : Set E} (hs₁ : IsBoun
ded s) (hs₂ : MeasurableSet s)…
· 使用定理 `_private.Mathlib.Algebra.Module.ZLattice.Covolume.0.ZLattice.covolume.fr
ontier_equivFun`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Modul
e ℝ E] {ι : Type u_2} [inst_2 : Finite ι]   [inst_3 : TopologicalSpace E] [Is…
（共 37 条，此处仅展示前 30 条）
-/
theorem tendsto_card_div_pow (b : Basis ι ℤ L) {s : Set (ι → ℝ)} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set (ι → ℝ)) : ℝ) / n ^ card ι)
      atTop (𝓝 (volume.real s / covolume L)) := by
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, hs₃, ENNReal.zero_div]
/-
**ZLattice.covolume.tendsto_card_le_div** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice.covo
lume`。
形式化陈述：tendsto_card_le_div {X : Set (ι -> Real)} (hX : forall ⦃x⦄ ⦃r : Real⦄, x i
n X -> 0 < r -> r • x in X) {F : (ι -> Real) -> Real} (h₁ : forall x ⦃r : Real⦄,
 0 <= r -> F (r • x) = r ^ card ι * (F x)) (h₂ : IsBounded {x in X | F x <= 1}) 
(h₃ : MeasurableSet {x in X | F x <= 1}) (h₄ : volume (frontier {x | x in X ∧ F 
x <= 1}) = 0) [Nonempty ι] : Tendsto (fun c : Real => Nat.card ({x in X | F x <=
 c} inter L : Set (ι -> Real)) / (c : Real)) atTop (𝓝 (volume.real {x in X | F x
 <= 1} / covolume L))
参数：ι -> Real；hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X；ι -> Real
；h₁ : forall x ⦃r : Real⦄, 0 <= r -> F (r • x) = r ^ card ι * (F x)；h₂ : IsBound
ed {x in X | F x <= 1}；h₃ : MeasurableSet {x in X | F x <= 1}；h₄ : volume (front
ier {x | x in X ∧ F x <= 1}) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `ZLattice.rank`：ZLattice.rank [hs : IsZLattice K L] : finrank Int L = fin
rank K E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ZLattice.volume_image_eq_volume_div_covolume`：volume_image_eq_volume_div
_covolume {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real)) [DiscreteTopol
ogy L] [IsZLattice Real L] (b : Ba…
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ZLattice.covolume_pos`：covolume_pos : 0 < covolume L μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
（共 41 条，此处仅展示前 30 条）
-/
theorem tendsto_card_le_div {X : Set (ι → ℝ)} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : (ι → ℝ) → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier {x | x ∈ X ∧ F x ≤ 1}) = 0) [Nonempty ι] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set (ι → ℝ)) / (c : ℝ))
        atTop (𝓝 (volume.real {x ∈ X | F x ≤ 1} / covolume L)) := by
  let e : Free.ChooseBasisIndex ℤ ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis ℤ L).reindex e
  convert! tendsto_card_le_div'' b hX h₁ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, h₄, ENNReal.zero_div]

end Pi

section InnerProductSpace

open Filter Pointwise Topology Bornology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the `InnerProductSpace` case;
see the `Naming convention` section in the introduction. -/
/-
**ZLattice.covolume.tendsto_card_div_pow'** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice.co
volume`。
形式化陈述：tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet
 s) (hs₃ : volume (frontier s) = 0) : Tendsto (fun n : Nat => (Nat.card (s inter
 (n : Real)⁻¹ • L : Set E) : Real) / n ^ finrank Real E) atTop (𝓝 (volume.real s
 / covolume L))
参数：hs₁ : IsBounded s；hs₂ : MeasurableSet s；hs₃ : volume (frontier s) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `ZLattice.rank`：ZLattice.rank [hs : IsZLattice K L] : finrank Int L = fin
rank K E
· 使用定理 `ZLattice.volume_image_eq_volume_div_covolume'`：volume_image_eq_volume_di
v_covolume' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [Finit
eDimensional Real E] [MeasurableSpa…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ZLattice.covolume_pos`：covolume_pos : 0 < covolume L μ
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `ZLattice.covolume.tendsto_card_div_pow''`：tendsto_card_div_pow'' [Finite
Dimensional Real E] [MeasurableSpace E] [BorelSpace E] {s : Set E} (hs₁ : IsBoun
ded s) (hs₂ : MeasurableSet s)…
· 使用定理 `_private.Mathlib.Algebra.Module.ZLattice.Covolume.0.ZLattice.covolume.fr
ontier_equivFun`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Modul
e ℝ E] {ι : Type u_2} [inst_2 : Finite ι]   [inst_3 : TopologicalSpace E] [Is…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0

--- 原说明 ---
A version of `ZLattice.covolume.tendsto_card_div_pow` for the `InnerProductSpace
` case;
see the `Naming convention` section in the introduction.
-/
theorem tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (volume.real s / covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b hs₂.nullMeasurableSet, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume', hs₃, ENNReal.zero_div]
    exact NullMeasurableSet.of_null hs₃

/-- A version of `ZLattice.covolume.tendsto_card_le_div` for the `InnerProductSpace` case;
see the `Naming convention` section in the introduction. -/
/-
**ZLattice.covolume.tendsto_card_le_div'** 是 Mathlib 中的一个定理，位于命名空间 `ZLattice.cov
olume`。
形式化陈述：tendsto_card_le_div' [Nontrivial E] {X : Set E} {F : E -> Real} (hX : fora
ll ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X) (h₁ : forall x ⦃r : Real⦄, 0 <
= r -> F (r • x) = r ^ finrank Real E * (F x)) (h₂ : IsBounded {x in X | F x <= 
1}) (h₃ : MeasurableSet {x in X | F x <= 1}) (h₄ : volume (frontier {x in X | F 
x <= 1}) = 0) : Tendsto (fun c : Real => Nat.card ({x in X | F x <= c} inter L :
 Set E) / (c : Real)) atTop (𝓝 (volume.real {x in X | F x <= 1} / covolume L))
参数：hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X；h₁ : forall x ⦃r : 
Real⦄, 0 <= r -> F (r • x) = r ^ finrank Real E * (F x)；h₂ : IsBounded {x in X |
 F x <= 1}；h₃ : MeasurableSet {x in X | F x <= 1}；h₄ : volume (frontier {x in X 
| F x <= 1}) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.volume_image_eq_volume_div_covolume'`：volume_image_eq_volume_di
v_covolume' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [Finit
eDimensional Real E] [MeasurableSpa…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ZLattice.covolume_pos`：covolume_pos : 0 < covolume L μ
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `ZLattice.covolume.tendsto_card_le_div''`：tendsto_card_le_div'' [FiniteDi
mensional Real E] [MeasurableSpace E] [BorelSpace E] [Nonempty ι] {X : Set E} (h
X : forall ⦃x⦄ ⦃r : Real⦄, x …
· 使用定理 `Module.nontrivial_of_finrank_pos`：Module.nontrivial_of_finrank_pos (h : 
0 < finrank R M) : Nontrivial M
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `ZLattice.rank`：ZLattice.rank [hs : IsZLattice K L] : finrank Int L = fin
rank K E
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `_private.Mathlib.Algebra.Module.ZLattice.Covolume.0.ZLattice.covolume.fr
ontier_equivFun`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Modul
e ℝ E] {ι : Type u_2} [inst_2 : Finite ι]   [inst_3 : TopologicalSpace E] [Is…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0

--- 原说明 ---
A version of `ZLattice.covolume.tendsto_card_le_div` for the `InnerProductSpace`
 case;
see the `Naming convention` section in the introduction.
-/
theorem tendsto_card_le_div' [Nontrivial E] {X : Set E} {F : E → ℝ}
    (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ finrank ℝ E * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier {x ∈ X | F x ≤ 1}) = 0) :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 (volume.real {x ∈ X | F x ≤ 1} / covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert! tendsto_card_le_div'' b hX ?_ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b h₃.nullMeasurableSet, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · have : Nontrivial L := nontrivial_of_finrank_pos <| (ZLattice.rank ℝ L).symm ▸ finrank_pos
    infer_instance
  · rwa [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume', h₄, ENNReal.zero_div]
    exact NullMeasurableSet.of_null h₄

end InnerProductSpace

end covolume

end ZLattice

