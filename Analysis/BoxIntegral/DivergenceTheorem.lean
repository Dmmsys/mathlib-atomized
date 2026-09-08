/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.Analysis.BoxIntegral.Partition.Additive
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Divergence integral for Henstock-Kurzweil integral

In this file we prove the Divergence Theorem for a Henstock-Kurzweil style integral. The theorem
says the following. Let `f : ℝⁿ → Eⁿ` be a function differentiable on a closed rectangular box
`I` with derivative `f' x : ℝⁿ →L[ℝ] Eⁿ` at `x ∈ I`. Then the divergence `fun x ↦ ∑ k, f' x eₖ k`,
where `eₖ = Pi.single k 1` is the `k`-th basis vector, is integrable on `I`, and its integral is
equal to the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

To make the proof work, we had to ban tagged partitions with “long and thin” boxes. More precisely,
we use the following generalization of one-dimensional Henstock-Kurzweil integral to functions
defined on a box in `ℝⁿ` (it corresponds to the value `BoxIntegral.IntegrationParams.GP = ⊥` of
`BoxIntegral.IntegrationParams` in the definition of `BoxIntegral.HasIntegral`).

We say that `f : ℝⁿ → E` has integral `y : E` over a box `I ⊆ ℝⁿ` if for an arbitrarily small
positive `ε` and an arbitrarily large `c`, there exists a function `r : ℝⁿ → (0, ∞)` such that for
any tagged partition `π` of `I` such that

* `π` is a Henstock partition, i.e., each tag belongs to its box;
* `π` is subordinate to `r`;
* for every box of `π`, the maximum of the ratios of its sides is less than or equal to `c`,

the integral sum of `f` over `π` is `ε`-close to `y`. In case of dimension one, the last condition
trivially holds for any `c ≥ 1`, so this definition is equivalent to the standard definition of
Henstock-Kurzweil integral.

## Tags

Henstock-Kurzweil integral, integral, Stokes theorem, divergence theorem
-/

public section

open scoped NNReal ENNReal Topology BoxIntegral

open ContinuousLinearMap (lsmul)

open Filter Set Finset Metric

open BoxIntegral.IntegrationParams (GP gp_le)

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace BoxIntegral

variable [CompleteSpace E] (I : Box (Fin (n + 1))) {i : Fin (n + 1)}

open MeasureTheory

/-- Auxiliary lemma for the divergence theorem. -/
/-
**BoxIntegral.norm_volume_sub_integral_face_upper_sub_lower_smul_le** 是 Mathlib 
中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：norm_volume_sub_integral_face_upper_sub_lower_smul_le {f : (Fin (n + 1) ->
 Real) -> E} {f' : (Fin (n + 1) -> Real) ->L[Real] E} (hfc : ContinuousOn f (Box
.Icc I)) {x : Fin (n + 1) -> Real} (hxI : x in (Box.Icc I)) {a : E} {ε : Real} (
h0 : 0 < ε) (hε : forall y in (Box.Icc I), ‖f y - a - f' (y - x)‖ <= ε * ‖y - x‖
) {c : Real>=0} (hc : I.distortion <= c) : ‖(∏ j, (I.upper j - I.lower j)) • f' 
(Pi.single i 1) - (integral (I.face i) ⊥ (f ∘ i.insertNth (α
参数：Fin (n + 1) -> Real；Fin (n + 1) -> Real；hfc : ContinuousOn f (Box.Icc I)；n + 
1；hxI : x in (Box.Icc I)；h0 : 0 < ε；hε : forall y in (Box.Icc I), ‖f y - a - f' 
(y - x)‖ <= ε * ‖y - x‖；hc : I.distortion <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `BoxIntegral.integrable_of_continuousOn`：integrable_of_continuousOn [Comp
leteSpace E] {I : Box ι} {f : Realⁿ -> E} (hc : ContinuousOn f (Box.Icc I)) (μ :
 Measure Realⁿ) [IsLocallyFi…
· 使用定理 `BoxIntegral.Box.continuousOn_face_Icc`：continuousOn_face_Icc {X} [Topolo
gicalSpace X] {n} {f : (Fin (n + 1) -> Real) -> X} {I : Box (Fin (n + 1))} (h : 
ContinuousOn f (Box.Icc I))…
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
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
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.insertNth_sub_same`：∀ {n : ℕ} {α : Fin (n + 1) → Type u_1} [inst : (
j : Fin (n + 1)) → AddGroup (α j)] (i : Fin (n + 1)) (x y : α i)   (p : (j : Fin
 n) → α (i.s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.map_sub`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
· 使用定理 `_private.Mathlib.Analysis.BoxIntegral.DivergenceTheorem.0.BoxIntegral.no
rm_volume_sub_integral_face_upper_sub_lower_smul_le._abel_1_1`：∀ {E : Type u_1} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {n : ℕ} (I : BoxIntegra
l.Box (Fin (n + 1)))   {i : Fin (n + 1)} {f…
· 使用定理 `BoxIntegral.Box.mapsTo_insertNth_face_Icc`：mapsTo_insertNth_face_Icc {n}
 (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : Real} (hx : x in Icc (I.lower i)
 (I.upper i)) : MapsTo (i.inser…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for the divergence theorem.
-/
theorem norm_volume_sub_integral_face_upper_sub_lower_smul_le {f : (Fin (n + 1) → ℝ) → E}
    {f' : (Fin (n + 1) → ℝ) →L[ℝ] E} (hfc : ContinuousOn f (Box.Icc I)) {x : Fin (n + 1) → ℝ}
    (hxI : x ∈ (Box.Icc I)) {a : E} {ε : ℝ} (h0 : 0 < ε)
    (hε : ∀ y ∈ (Box.Icc I), ‖f y - a - f' (y - x)‖ ≤ ε * ‖y - x‖) {c : ℝ≥0}
    (hc : I.distortion ≤ c) :
    ‖(∏ j, (I.upper j - I.lower j)) • f' (Pi.single i 1) -
      (integral (I.face i) ⊥ (f ∘ i.insertNth (α := fun _ ↦ ℝ) (I.upper i)) BoxAdditiveMap.volume -
        integral (I.face i) ⊥ (f ∘ i.insertNth (α := fun _ ↦ ℝ) (I.lower i))
          BoxAdditiveMap.volume)‖ ≤
      2 * ε * c * ∏ j, (I.upper j - I.lower j) := by
  -- Porting note: Lean fails to find `α` in the next line
  set e : ℝ → (Fin n → ℝ) → (Fin (n + 1) → ℝ) := i.insertNth (α := fun _ ↦ ℝ)
  /- **Plan of the proof**. The difference of the integrals of the affine function
    `fun y ↦ a + f' (y - x)` over the faces `x i = I.upper i` and `x i = I.lower i` is equal to the
    volume of `I` multiplied by `f' (Pi.single i 1)`, so it suffices to show that the integral of
    `f y - a - f' (y - x)` over each of these faces is less than or equal to `ε * c * vol I`. We
    integrate a function of the norm `≤ ε * diam I.Icc` over a box of volume
    `∏ j ≠ i, (I.upper j - I.lower j)`. Since `diam I.Icc ≤ c * (I.upper i - I.lower i)`, we get the
    required estimate. -/
  have Hl : I.lower i ∈ Icc (I.lower i) (I.upper i) := Set.left_mem_Icc.2 (I.lower_le_upper i)
  have Hu : I.upper i ∈ Icc (I.lower i) (I.upper i) := Set.right_mem_Icc.2 (I.lower_le_upper i)
  have Hi : ∀ x ∈ Icc (I.lower i) (I.upper i),
      Integrable.{0, u, u} (I.face i) ⊥ (f ∘ e x) BoxAdditiveMap.volume := fun x hx =>
    integrable_of_continuousOn _ (Box.continuousOn_face_Icc hfc hx) volume
  /- We start with an estimate: the difference of the values of `f` at the corresponding points
    of the faces `x i = I.lower i` and `x i = I.upper i` is `(2 * ε * diam I.Icc)`-close to the
    value of `f'` on `Pi.single i (I.upper i - I.lower i) = lᵢ • eᵢ`, where
    `lᵢ = I.upper i - I.lower i` is the length of `i`-th edge of `I` and `eᵢ = Pi.single i 1` is the
    `i`-th unit vector. -/
  have : ∀ y ∈ Box.Icc (I.face i),
      ‖f' (Pi.single i (I.upper i - I.lower i)) -
          (f (e (I.upper i) y) - f (e (I.lower i) y))‖ ≤
        2 * ε * diam (Box.Icc I) := fun y hy ↦ by
    set g := fun y => f y - a - f' (y - x) with hg
    change ∀ y ∈ (Box.Icc I), ‖g y‖ ≤ ε * ‖y - x‖ at hε
    clear_value g; obtain rfl : f = fun y => a + f' (y - x) + g y := by simp [hg]
    convert_to ‖g (e (I.lower i) y) - g (e (I.upper i) y)‖ ≤ _
    · congr 1
      have := Fin.insertNth_sub_same (α := fun _ ↦ ℝ) i (I.upper i) (I.lower i) y
      simp only [← this, f'.map_sub]; abel
    · have : ∀ z ∈ Icc (I.lower i) (I.upper i), e z y ∈ (Box.Icc I) := fun z hz =>
        I.mapsTo_insertNth_face_Icc hz hy
      replace hε : ∀ y ∈ (Box.Icc I), ‖g y‖ ≤ ε * diam (Box.Icc I) := by
        intro y hy
        refine (hε y hy).trans (mul_le_mul_of_nonneg_left ?_ h0.le)
        rw [← dist_eq_norm]
        exact dist_le_diam_of_mem I.isCompact_Icc.isBounded hy hxI
      rw [two_mul, add_mul]
      exact norm_sub_le_of_le (hε _ (this _ Hl)) (hε _ (this _ Hu))
  calc
    ‖(∏ j, (I.upper j - I.lower j)) • f' (Pi.single i 1) -
            (integral (I.face i) ⊥ (f ∘ e (I.upper i)) BoxAdditiveMap.volume -
              integral (I.face i) ⊥ (f ∘ e (I.lower i)) BoxAdditiveMap.volume)‖ =
        ‖integral.{0, u, u} (I.face i) ⊥
            (fun x : Fin n → ℝ =>
              f' (Pi.single i (I.upper i - I.lower i)) -
                (f (e (I.upper i) x) - f (e (I.lower i) x)))
            BoxAdditiveMap.volume‖ := by
      rw [← integral_sub (Hi _ Hu) (Hi _ Hl), ← Box.volume_face_mul i, mul_smul, ← Box.volume_apply,
        ← BoxAdditiveMap.toSMul_apply, ← integral_const, ← BoxAdditiveMap.volume,
        ← integral_sub (integrable_const _) ((Hi _ Hu).sub (Hi _ Hl))]
      simp only [(· ∘ ·), Pi.sub_def, ← f'.map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
    _ ≤ (volume (I.face i : Set (Fin n → ℝ))).toReal * (2 * ε * c * (I.upper i - I.lower i)) := by
      -- The hard part of the estimate was done above, here we just replace `diam I.Icc`
      -- with `c * (I.upper i - I.lower i)`
      refine norm_integral_le_of_le_const (fun y hy => (this y hy).trans ?_) volume
      rw [mul_assoc (2 * ε)]
      gcongr
      exact I.diam_Icc_le_of_distortion_le i hc
    _ = 2 * ε * c * ∏ j, (I.upper j - I.lower j) := by
      rw [← measureReal_def, ← Measure.toBoxAdditive_apply, Box.volume_apply,
        ← I.volume_face_mul i]
      ac_rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `f : ℝⁿ⁺¹ → E` is differentiable on a closed rectangular box `I` with derivative `f'`, then
the partial derivative `fun x ↦ f' x (Pi.single i 1)` is Henstock-Kurzweil integrable with integral
equal to the difference of integrals of `f` over the faces `x i = I.upper i` and `x i = I.lower i`.

More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
we allow `f` to be non-differentiable (but still continuous) at a countable set of points.

TODO: If `n > 0`, then the condition at `x ∈ s` can be replaced by a much weaker estimate but this
requires either better integrability theorems, or usage of a filter depending on the countable set
`s` (we need to ensure that none of the faces of a partition contain a point from `s`). -/
/-
**BoxIntegral.hasIntegral_GP_pderiv** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：hasIntegral_GP_pderiv (f : (Fin (n + 1) -> Real) -> E) (f' : (Fin (n + 1) 
-> Real) -> (Fin (n + 1) -> Real) ->L[Real] E) (s : Set (Fin (n + 1) -> Real)) (
hs : s.Countable) (Hs : forall x in s, ContinuousWithinAt f (Box.Icc I) x) (Hd :
 forall x in (Box.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x) (i : Fin
 (n + 1)) : HasIntegral.{0, u, u} I GP (fun x => f' x (Pi.single i 1)) BoxAdditi
veMap.volume (integral.{0, u, u} (I.face i) GP (fun x => f (i.insertNth (I.upper
 i) x)) BoxAdditiveMap.vol
参数：f : (Fin (n + 1) -> Real) -> E；f' : (Fin (n + 1) -> Real) -> (Fin (n + 1) -> 
Real) ->L[Real] E；s : Set (Fin (n + 1) -> Real)；hs : s.Countable；Hs : forall x i
n s, ContinuousWithinAt f (Box.Icc I) x；Hd : forall x in (Box.Icc I) \ s, HasFDe
rivWithinAt f (f' x) (Box.Icc I) x；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
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
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
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
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `BoxIntegral.integrable_of_continuousOn`：integrable_of_continuousOn [Comp
leteSpace E] {I : Box ι} {f : Realⁿ -> E} (hc : ContinuousOn f (Box.Icc I)) (μ :
 Measure Realⁿ) [IsLocallyFi…
· 使用定理 `BoxIntegral.Box.continuousOn_face_Icc`：continuousOn_face_Icc {X} [Topolo
gicalSpace X] {n} {f : (Fin (n + 1) -> Real) -> X} {I : Box (Fin (n + 1))} (h : 
ContinuousOn f (Box.Icc I))…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `BoxIntegral.HasIntegral.of_le_Henstock_of_forall_isLittleO`：∀ {ι : Type 
u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace
 ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 …
· 使用定理 `BoxIntegral.IntegrationParams.gp_le`：gp_le : GP <= l
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
（共 131 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℝⁿ⁺¹ → E` is differentiable on a closed rectangular box `I` with derivat
ive `f'`, then
the partial derivative `fun x ↦ f' x (Pi.single i 1)` is Henstock-Kurzweil integ
rable with integral
equal to the difference of integrals of `f` over the faces `x i = I.upper i` and
 `x i = I.lower i`.

More precisely, we use a non-standard generalization of the Henstock-Kurzweil in
tegral and
we allow `f` to be non-differentiable (but still continuous) at a countable set 
of points.

TODO: If `n > 0`, then the condition at `x ∈ s` can be replaced by a much weaker
 estimate but this
requires either better integrability theorems, or usage of a filter depending on
 the countable set
`s` (we need to ensure that none of the faces of a partition contain a point fro
m `s`).
-/
theorem hasIntegral_GP_pderiv (f : (Fin (n + 1) → ℝ) → E)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E) (s : Set (Fin (n + 1) → ℝ))
    (hs : s.Countable) (Hs : ∀ x ∈ s, ContinuousWithinAt f (Box.Icc I) x)
    (Hd : ∀ x ∈ (Box.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x) (i : Fin (n + 1)) :
    HasIntegral.{0, u, u} I GP (fun x => f' x (Pi.single i 1)) BoxAdditiveMap.volume
      (integral.{0, u, u} (I.face i) GP (fun x => f (i.insertNth (I.upper i) x))
          BoxAdditiveMap.volume -
        integral.{0, u, u} (I.face i) GP (fun x => f (i.insertNth (I.lower i) x))
          BoxAdditiveMap.volume) := by
  /- Note that `f` is continuous on `I.Icc`, hence it is integrable on the faces of all boxes
    `J ≤ I`, thus the difference of integrals over `x i = J.upper i` and `x i = J.lower i` is a
    box-additive function of `J ≤ I`. -/
  have Hc : ContinuousOn f (Box.Icc I) := fun x hx ↦ by
    by_cases hxs : x ∈ s
    exacts [Hs x hxs, (Hd x ⟨hx, hxs⟩).continuousWithinAt]
  set fI : ℝ → Box (Fin n) → E := fun y J =>
    integral.{0, u, u} J GP (fun x => f (i.insertNth y x)) BoxAdditiveMap.volume
  set fb : Icc (I.lower i) (I.upper i) → Fin n →ᵇᵃ[↑(I.face i)] E := fun x =>
    (integrable_of_continuousOn GP (Box.continuousOn_face_Icc Hc x.2) volume).toBoxAdditive
  set F : Fin (n + 1) →ᵇᵃ[I] E := BoxAdditiveMap.upperSubLower I i fI fb fun x _ J => rfl
  -- Thus our statement follows from some local estimates.
  change HasIntegral I GP (fun x => f' x (Pi.single i 1)) _ (F I)
  refine HasIntegral.of_le_Henstock_of_forall_isLittleO gp_le ?_ ?_ _ s hs ?_ ?_
  · -- We use the volume as an upper estimate.
    exact (volume : Measure (Fin (n + 1) → ℝ)).toBoxAdditive.restrict _ le_top
  · exact fun J => ENNReal.toReal_nonneg
  · intro c x hx ε ε0
    /- Near `x ∈ s` we choose `δ` so that both vectors are small. `volume J • eᵢ` is small because
        `volume J ≤ (2 * δ) ^ (n + 1)` is small, and the difference of the integrals is small
        because each of the integrals is close to `volume (J.face i) • f x`.
        TODO: there should be a shorter and more readable way to formalize this simple proof. -/
    have : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioc (0 : ℝ) (1 / 2) ∧
        (∀ᵉ (y₁ ∈ closedBall x δ ∩ (Box.Icc I)) (y₂ ∈ closedBall x δ ∩ (Box.Icc I)),
              ‖f y₁ - f y₂‖ ≤ ε / 2) ∧ (2 * δ) ^ (n + 1) * ‖f' x (Pi.single i 1)‖ ≤ ε / 2 := by
      refine .and (Ioc_mem_nhdsGT one_half_pos) (.and ?_ ?_)
      · rcases ((nhdsWithin_hasBasis nhds_basis_closedBall _).tendsto_iff nhds_basis_closedBall).1
            (Hs x hx.2) _ (half_pos <| half_pos ε0) with ⟨δ₁, δ₁0, hδ₁⟩
        filter_upwards [Ioc_mem_nhdsGT δ₁0] with δ hδ y₁ hy₁ y₂ hy₂
        have : closedBall x δ ∩ (Box.Icc I) ⊆ closedBall x δ₁ ∩ (Box.Icc I) := by gcongr; exact hδ.2
        rw [← dist_eq_norm]
        calc
          dist (f y₁) (f y₂) ≤ dist (f y₁) (f x) + dist (f y₂) (f x) := dist_triangle_right _ _ _
          _ ≤ ε / 2 / 2 + ε / 2 / 2 := add_le_add (hδ₁ _ <| this hy₁) (hδ₁ _ <| this hy₂)
          _ = ε / 2 := add_halves _
      · have : ContinuousWithinAt (fun δ : ℝ => (2 * δ) ^ (n + 1) * ‖f' x (Pi.single i 1)‖)
            (Ioi 0) 0 := ((continuousWithinAt_id.const_mul _).pow _).mul_const _
        refine this.eventually (ge_mem_nhds ?_)
        simpa using half_pos ε0
    rcases this.exists with ⟨δ, ⟨hδ0, hδ12⟩, hdfδ, hδ⟩
    refine ⟨δ, hδ0, fun J hJI hJδ _ _ => add_halves ε ▸ ?_⟩
    have Hl : J.lower i ∈ Icc (J.lower i) (J.upper i) := Set.left_mem_Icc.2 (J.lower_le_upper i)
    have Hu : J.upper i ∈ Icc (J.lower i) (J.upper i) := Set.right_mem_Icc.2 (J.lower_le_upper i)
    have Hi : ∀ x ∈ Icc (J.lower i) (J.upper i),
        Integrable.{0, u, u} (J.face i) GP (fun y => f (i.insertNth x y))
          BoxAdditiveMap.volume := fun x hx =>
      integrable_of_continuousOn _ (Box.continuousOn_face_Icc (Hc.mono <| Box.le_iff_Icc.1 hJI) hx)
        volume
    have hJδ' : Box.Icc J ⊆ closedBall x δ ∩ (Box.Icc I) := subset_inter hJδ (Box.le_iff_Icc.1 hJI)
    have Hmaps : ∀ z ∈ Icc (J.lower i) (J.upper i),
        MapsTo (i.insertNth z) (Box.Icc (J.face i)) (closedBall x δ ∩ (Box.Icc I)) := fun z hz =>
      (J.mapsTo_insertNth_face_Icc hz).mono Subset.rfl hJδ'
    simp only [dist_eq_norm]; dsimp [F]
    rw [← integral_sub (Hi _ Hu) (Hi _ Hl)]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · simp_rw [BoxAdditiveMap.volume_apply, norm_smul, Real.norm_eq_abs, abs_prod]
      refine (mul_le_mul_of_nonneg_right ?_ <| norm_nonneg _).trans hδ
      have : ∀ j, |J.upper j - J.lower j| ≤ 2 * δ := fun j ↦
        calc
          dist (J.upper j) (J.lower j) ≤ dist J.upper J.lower := dist_le_pi_dist _ _ _
          _ ≤ dist J.upper x + dist J.lower x := dist_triangle_right _ _ _
          _ ≤ δ + δ := add_le_add (hJδ J.upper_mem_Icc) (hJδ J.lower_mem_Icc)
          _ = 2 * δ := (two_mul δ).symm
      calc
        ∏ j, |J.upper j - J.lower j| ≤ ∏ j : Fin (n + 1), 2 * δ := by
          gcongr with j _; exact this j
        _ = (2 * δ) ^ (n + 1) := by simp
    · refine (norm_integral_le_of_le_const (fun y hy => hdfδ _ (Hmaps _ Hu hy) _
        (Hmaps _ Hl hy)) volume).trans ?_
      refine (mul_le_mul_of_nonneg_right ?_ (half_pos ε0).le).trans_eq (one_mul _)
      rw [Box.coe_eq_pi, measureReal_def, Real.volume_pi_Ioc_toReal (Box.lower_le_upper _)]
      refine prod_le_one (fun _ _ => sub_nonneg.2 <| Box.lower_le_upper _ _) fun j _ => ?_
      calc
        J.upper (i.succAbove j) - J.lower (i.succAbove j) ≤
            dist (J.upper (i.succAbove j)) (J.lower (i.succAbove j)) :=
          le_abs_self _
        _ ≤ dist J.upper J.lower := dist_le_pi_dist J.upper J.lower (i.succAbove j)
        _ ≤ dist J.upper x + dist J.lower x := dist_triangle_right _ _ _
        _ ≤ δ + δ := add_le_add (hJδ J.upper_mem_Icc) (hJδ J.lower_mem_Icc)
        _ ≤ 1 / 2 + 1 / 2 := by gcongr
        _ = 1 := add_halves 1
  · intro c x hx ε ε0
    /- At a point `x ∉ s`, we unfold the definition of Fréchet differentiability, then use
        an estimate we proved earlier in this file. -/
    rcases exists_pos_mul_lt ε0 (2 * c) with ⟨ε', ε'0, hlt⟩
    rcases (nhdsWithin_hasBasis nhds_basis_closedBall _).mem_iff.1
      ((Hd x hx).isLittleO.def ε'0) with ⟨δ, δ0, Hδ⟩
    refine ⟨δ, δ0, fun J hle hJδ hxJ hJc => ?_⟩
    simp only [BoxAdditiveMap.volume_apply, dist_eq_norm]
    refine (norm_volume_sub_integral_face_upper_sub_lower_smul_le _
      (Hc.mono <| Box.le_iff_Icc.1 hle) hxJ ε'0 (fun y hy => Hδ ?_) (hJc rfl)).trans ?_
    · exact ⟨hJδ hy, Box.le_iff_Icc.1 hle hy⟩
    · rw [mul_right_comm (2 : ℝ), ← Box.volume_apply]
      gcongr
      exacts [by dsimp; positivity, by simp]

/-- Divergence theorem for a Henstock-Kurzweil style integral.

If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with derivative `f'`, then
the divergence `∑ i, f' x (Pi.single i 1) i` is Henstock-Kurzweil integrable with integral equal to
the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
we allow `f` to be non-differentiable (but still continuous) at a countable set of points. -/
/-
**BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt** 是 Mathlib 中
的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：hasIntegral_GP_divergence_of_forall_hasDerivWithinAt (f : (Fin (n + 1) -> 
Real) -> Fin (n + 1) -> E) (f' : (Fin (n + 1) -> Real) -> (Fin (n + 1) -> Real) 
->L[Real] (Fin (n + 1) -> E)) (s : Set (Fin (n + 1) -> Real)) (hs : s.Countable)
 (Hs : forall x in s, ContinuousWithinAt f (Box.Icc I) x) (Hd : forall x in (Box
.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x) : HasIntegral.{0, u, u} I
 GP (fun x => ∑ i, f' x (Pi.single i 1) i) BoxAdditiveMap.volume (∑ i, (integral
.{0, u, u} (I.face i) GP (
参数：f : (Fin (n + 1) -> Real) -> Fin (n + 1) -> E；f' : (Fin (n + 1) -> Real) -> (
Fin (n + 1) -> Real) ->L[Real] (Fin (n + 1) -> E)；s : Set (Fin (n + 1) -> Real)；
hs : s.Countable；Hs : forall x in s, ContinuousWithinAt f (Box.Icc I) x；Hd : for
all x in (Box.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.HasIntegral.sum`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.hasIntegral_GP_pderiv`：hasIntegral_GP_pderiv (f : (Fin (n + 
1) -> Real) -> E) (f' : (Fin (n + 1) -> Real) -> (Fin (n + 1) -> Real) ->L[Real]
 E) (s : Set (Fin (n + …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Divergence theorem for a Henstock-Kurzweil style integral.

If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with deri
vative `f'`, then
the divergence `∑ i, f' x (Pi.single i 1) i` is Henstock-Kurzweil integrable wit
h integral equal to
the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

More precisely, we use a non-standard generalization of the Henstock-Kurzweil in
tegral and
we allow `f` to be non-differentiable (but still continuous) at a countable set 
of points.
-/
theorem hasIntegral_GP_divergence_of_forall_hasDerivWithinAt
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → E)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → E))
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable)
    (Hs : ∀ x ∈ s, ContinuousWithinAt f (Box.Icc I) x)
    (Hd : ∀ x ∈ (Box.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x) :
    HasIntegral.{0, u, u} I GP (fun x => ∑ i, f' x (Pi.single i 1) i) BoxAdditiveMap.volume
      (∑ i,
        (integral.{0, u, u} (I.face i) GP (fun x => f (i.insertNth (I.upper i) x) i)
            BoxAdditiveMap.volume -
          integral.{0, u, u} (I.face i) GP (fun x => f (i.insertNth (I.lower i) x) i)
            BoxAdditiveMap.volume)) := by
  refine HasIntegral.sum fun i _ => ?_
  simp only [hasFDerivWithinAt_pi', continuousWithinAt_pi] at Hd Hs
  exact hasIntegral_GP_pderiv I _ _ s hs (fun x hx => Hs x hx i) (fun x hx => Hd x hx i) i

end BoxIntegral

