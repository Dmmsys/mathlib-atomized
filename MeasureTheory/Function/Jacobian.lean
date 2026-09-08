/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Change of variables in higher-dimensional integrals

Let `μ` be a Lebesgue measure on a finite-dimensional real vector space `E`.
Let `f : E → E` be a function which is injective and differentiable on a measurable set `s`,
with derivative `f'`. Then we prove that `f '' s` is measurable, and
its measure is given by the formula `μ (f '' s) = ∫⁻ x in s, |(f' x).det| ∂μ` (where `(f' x).det`
is almost everywhere measurable, but not Borel-measurable in general). This formula is proved in
`lintegral_abs_det_fderiv_eq_addHaar_image`. We deduce the change of variables
formula for the Lebesgue and Bochner integrals, in `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
and `integral_image_eq_integral_abs_det_fderiv_smul` respectively.

Specialized versions in one dimension (using the derivative instead of the determinant of the
Fréchet derivative) can be found in the file `Mathlib/MeasureTheory/Function/JacobianOneDim.lean`,
together with versions for monotone and antitone functions.

## Main results

* `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`: if `f` is differentiable on a
  set `s` with zero measure, then `f '' s` also has zero measure.
* `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`: if `f` is differentiable on a set `s`, and
  its derivative is never invertible, then `f '' s` has zero measure (a version of Sard's lemma).
* `aemeasurable_fderivWithin`: if `f` is differentiable on a measurable set `s`, then `f'`
  is almost everywhere measurable on `s`.

For the next statements, `s` is a measurable set and `f` is differentiable on `s`
(with a derivative `f'`) and injective on `s`.

* `measurable_image_of_fderivWithin`: the image `f '' s` is measurable.
* `measurableEmbedding_of_fderivWithin`: the function `s.domRestrict f` is a measurable embedding.
* `lintegral_abs_det_fderiv_eq_addHaar_image`: the image measure is given by
    `μ (f '' s) = ∫⁻ x in s, |(f' x).det| ∂μ`.
* `lintegral_image_eq_lintegral_abs_det_fderiv_mul`: for `g : E → ℝ≥0∞`, one has
    `∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ`.
* `integral_image_eq_integral_abs_det_fderiv_smul`: for `g : E → F`, one has
    `∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ`.
* `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`: for `g : E → F`, the function `g` is
  integrable on `f '' s` if and only if `|(f' x).det| • g (f x)` is integrable on `s`.

## Implementation

Typical versions of these results in the literature have much stronger assumptions: `s` would
typically be open, and the derivative `f' x` would depend continuously on `x` and be invertible
everywhere, to have the local inverse theorem at our disposal. The proof strategy under our weaker
assumptions is more involved. We follow [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2].

The first remark is that, if `f` is sufficiently well approximated by a linear map `A` on a set
`s`, then `f` expands the volume of `s` by at least `A.det - ε` and at most `A.det + ε`, where
the closeness condition depends on `A` in a non-explicit way (see `addHaar_image_le_mul_of_det_lt`
and `mul_le_addHaar_image_of_lt_det`). This fact holds for balls by a simple inclusion argument,
and follows for general sets using the Besicovitch covering theorem to cover the set by balls with
measures adding up essentially to `μ s`.

When `f` is differentiable on `s`, one may partition `s` into countably many subsets `s ∩ t n`
(where `t n` is measurable), on each of which `f` is well approximated by a linear map, so that the
above results apply. See `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, which
follows from the pointwise differentiability (in a non-completely trivial way, as one should ensure
a form of uniformity on the sets of the partition).

Combining the above two results would give the conclusion, except for two difficulties: it is not
obvious why `f '' s` and `f'` should be measurable, which prevents us from using countable
additivity for the measure and the integral. It turns out that `f '' s` is indeed measurable,
and that `f'` is almost everywhere measurable, which is enough to recover countable additivity.

The measurability of `f '' s` follows from the deep Lusin-Souslin theorem ensuring that, in a
Polish space, a continuous injective image of a measurable set is measurable.

The key point to check the almost everywhere measurability of `f'` is that, if `f` is approximated
up to `δ` by a linear map on a set `s`, then `f'` is within `δ` of `A` on a full measure subset
of `s` (namely, its density points). With the above approximation argument, it follows that `f'`
is the almost everywhere limit of a sequence of measurable functions (which are constant on the
pieces of the good discretization), and is therefore almost everywhere measurable.

## Tags
Change of variables in integrals

## References
[Fremlin, *Measure Theory* (volume 2)][fremlin_vol2]
-/

public section

open MeasureTheory MeasureTheory.Measure Metric Filter Set Module Asymptotics
  TopologicalSpace

open scoped NNReal ENNReal Topology Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}

/-!
### Decomposition lemmas

We state lemmas ensuring that a differentiable function can be approximated, on countably many
measurable pieces, by linear maps (with a prescribed precision depending on the linear map).
-/

/-- Assume that a function `f` has a derivative at every point of a set `s`. Then one may cover `s`
with countably many closed sets `t n` on which `f` is well approximated by linear maps `A n`. -/
/-
**exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt [SecondCount
ableTopology F] (f : E -> F) (s : Set E) (f' : E -> E ->L[Real] F) (hf' : forall
 x in s, HasFDerivWithinAt f (f' x) s x) (r : (E ->L[Real] F) -> Real>=0) (rpos 
: forall A, r A != 0) : exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] F), (f
orall n, IsClosed (t n)) ∧ (s subseteq ⋃ n, t n) ∧ (forall n, ApproximatesLinear
On f (A n) (s inter t n) (r (A n))) ∧ (s.Nonempty -> forall n, exists y in s, A 
n = f' y)
参数：f : E -> F；s : Set E；f' : E -> E ->L[Real] F；hf' : forall x in s, HasFDerivWi
thinAt f (f' x) s x；r : (E ->L[Real] F) -> Real>=0；rpos : forall A, r A != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.isOpen_iUnion_countable`：isOpen_iUnion_countable [Secon
dCountableTopology α] {ι} (s : ι -> Set α) (H : forall i, IsOpen (s i)) : exists
 T : Set ι, T.Countable ∧ ⋃ i …
· 使用定理 `instSecondCountableTopologyContinuousLinearMapIdOfFiniteDimensional`：∀ {
𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type v} [inst_1 : NormedAddC
ommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type w} [in…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
（共 177 条，此处仅展示前 30 条）

--- 原说明 ---
Assume that a function `f` has a derivative at every point of a set `s`. Then on
e may cover `s`
with countably many closed sets `t n` on which `f` is well approximated by linea
r maps `A n`.
-/
theorem exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E → F) (s : Set E) (f' : E → E →L[ℝ] F) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (r : (E →L[ℝ] F) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] F),
      (∀ n, IsClosed (t n)) ∧
        (s ⊆ ⋃ n, t n) ∧
          (∀ n, ApproximatesLinearOn f (A n) (s ∩ t n) (r (A n))) ∧
            (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) := by
  /- Choose countably many linear maps `f' z`. For every such map, if `f` has a derivative at `x`
    close enough to `f' z`, then `f y - f x` is well approximated by `f' z (y - x)` for `y` close
    enough to `x`, say on a ball of radius `r` (or even `u n` for some `n`, where `u` is a fixed
    sequence tending to `0`).
    Let `M n z` be the points where this happens. Then this set is relatively closed inside `s`,
    and moreover in every closed ball of radius `u n / 3` inside it the map is well approximated by
    `f' z`. Using countably many closed balls to split `M n z` into small diameter subsets
    `K n z p`, one obtains the desired sets `t q` after reindexing.
    -/
  -- exclude the trivial case where `s` is empty
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · refine ⟨fun _ => ∅, fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> simp
  -- we will use countably many linear maps. Select these from all the derivatives since the
  -- space of linear maps is second-countable
  obtain ⟨T, T_count, hT⟩ :
    ∃ T : Set s,
      T.Countable ∧ ⋃ x ∈ T, ball (f' (x : E)) (r (f' x)) = ⋃ x : s, ball (f' x) (r (f' x)) :=
    TopologicalSpace.isOpen_iUnion_countable _ fun x => isOpen_ball
  -- fix a sequence `u` of positive reals tending to zero.
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  -- `M n z` is the set of points `x` such that `f y - f x` is close to `f' z (y - x)` for `y`
  -- in the ball of radius `u n` around `x`.
  let M : ℕ → T → Set E := fun n z =>
    {x | x ∈ s ∧ ∀ y ∈ s ∩ ball x (u n), ‖f y - f x - f' z (y - x)‖ ≤ r (f' z) * ‖y - x‖}
  -- As `f` is differentiable everywhere on `s`, the sets `M n z` cover `s` by design.
  have s_subset : ∀ x ∈ s, ∃ (n : ℕ) (z : T), x ∈ M n z := by
    intro x xs
    obtain ⟨z, zT, hz⟩ : ∃ z ∈ T, f' x ∈ ball (f' (z : E)) (r (f' z)) := by
      have : f' x ∈ ⋃ z ∈ T, ball (f' (z : E)) (r (f' z)) := by
        rw [hT]
        refine mem_iUnion.2 ⟨⟨x, xs⟩, ?_⟩
        simpa only [mem_ball, Subtype.coe_mk, dist_self] using! (rpos (f' x)).bot_lt
      rwa [mem_iUnion₂, bex_def] at this
    obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ‖f' x - f' z‖ + ε ≤ r (f' z) := by
      refine ⟨r (f' z) - ‖f' x - f' z‖, ?_, le_of_eq (by abel)⟩
      simpa only [sub_pos] using! mem_ball_iff_norm.mp hz
    obtain ⟨δ, δpos, hδ⟩ :
      ∃ (δ : ℝ), 0 < δ ∧ ball x δ ∩ s ⊆ {y | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
    obtain ⟨n, hn⟩ : ∃ n, u n < δ := ((tendsto_order.1 u_lim).2 _ δpos).exists
    refine ⟨n, ⟨z, zT⟩, ⟨xs, ?_⟩⟩
    intro y hy
    calc
      ‖f y - f x - (f' z) (y - x)‖ = ‖f y - f x - (f' x) (y - x) + (f' x - f' z) (y - x)‖ := by
        congr 1
        simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
        abel
      _ ≤ ‖f y - f x - (f' x) (y - x)‖ + ‖(f' x - f' z) (y - x)‖ := norm_add_le _ _
      _ ≤ ε * ‖y - x‖ + ‖f' x - f' z‖ * ‖y - x‖ := by
        refine add_le_add (hδ ?_) (ContinuousLinearMap.le_opNorm _ _)
        rw [inter_comm]
        exact inter_subset_inter_right _ (ball_subset_ball hn.le) hy
      _ ≤ r (f' z) * ‖y - x‖ := by
        rw [← add_mul, add_comm]
        gcongr
  -- the sets `M n z` are relatively closed in `s`, as all the conditions defining it are clearly
  -- closed
  have closure_M_subset : ∀ n z, s ∩ closure (M n z) ⊆ M n z := by
    rintro n z x ⟨xs, hx⟩
    refine ⟨xs, fun y hy => ?_⟩
    obtain ⟨a, aM, a_lim⟩ : ∃ a : ℕ → E, (∀ k, a k ∈ M n z) ∧ Tendsto a atTop (𝓝 x) :=
      mem_closure_iff_seq_limit.1 hx
    have L1 :
      Tendsto (fun k : ℕ => ‖f y - f (a k) - (f' z) (y - a k)‖) atTop
        (𝓝 ‖f y - f x - (f' z) (y - x)‖) := by
      apply Tendsto.norm
      have L : Tendsto (fun k => f (a k)) atTop (𝓝 (f x)) := by
        apply (hf' x xs).continuousWithinAt.tendsto.comp
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ a_lim
        exact Eventually.of_forall fun k => (aM k).1
      apply Tendsto.sub (tendsto_const_nhds.sub L)
      exact ((f' z).continuous.tendsto _).comp (tendsto_const_nhds.sub a_lim)
    have L2 : Tendsto (fun k : ℕ => (r (f' z) : ℝ) * ‖y - a k‖) atTop (𝓝 (r (f' z) * ‖y - x‖)) :=
      (tendsto_const_nhds.sub a_lim).norm.const_mul _
    have I : ∀ᶠ k in atTop, ‖f y - f (a k) - (f' z) (y - a k)‖ ≤ r (f' z) * ‖y - a k‖ := by
      have L : Tendsto (fun k => dist y (a k)) atTop (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist a_lim
      filter_upwards [(tendsto_order.1 L).2 _ hy.2]
      intro k hk
      exact (aM k).2 y ⟨hy.1, hk⟩
    exact le_of_tendsto_of_tendsto L1 L2 I
  -- choose a dense sequence `d p`
  rcases TopologicalSpace.exists_dense_seq E with ⟨d, hd⟩
  -- split `M n z` into subsets `K n z p` of small diameters by intersecting with the ball
  -- `closedBall (d p) (u n / 3)`.
  let K : ℕ → T → ℕ → Set E := fun n z p => closure (M n z) ∩ closedBall (d p) (u n / 3)
  -- on the sets `K n z p`, the map `f` is well approximated by `f' z` by design.
  have K_approx : ∀ (n) (z : T) (p), ApproximatesLinearOn f (f' z) (s ∩ K n z p) (r (f' z)) := by
    intro n z p x hx y hy
    have yM : y ∈ M n z := closure_M_subset _ _ ⟨hy.1, hy.2.1⟩
    refine yM.2 _ ⟨hx.1, ?_⟩
    calc
      dist x y ≤ dist x (d p) + dist y (d p) := dist_triangle_right _ _ _
      _ ≤ u n / 3 + u n / 3 := add_le_add hx.2.2 hy.2.2
      _ < u n := by linarith [u_pos n]
  -- the sets `K n z p` are also closed, again by design.
  have K_closed : ∀ (n) (z : T) (p), IsClosed (K n z p) := fun n z p =>
    isClosed_closure.inter isClosed_closedBall
  -- reindex the sets `K n z p`, to let them only depend on an integer parameter `q`.
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ × T × ℕ, Function.Surjective F := by
    have : Encodable T := T_count.toEncodable
    have : Nonempty T := by
      rcases hs with ⟨x, xs⟩
      rcases s_subset x xs with ⟨n, z, _⟩
      exact ⟨z⟩
    inhabit ↥T
    exact ⟨_, Encodable.surjective_decode_getD (ℕ × T × ℕ) default⟩
  -- these sets `t q = K n z p` will do
  refine
    ⟨fun q => K (F q).1 (F q).2.1 (F q).2.2, fun q => f' (F q).2.1, fun n => K_closed _ _ _,
      fun x xs => ?_, fun q => K_approx _ _ _, fun _ q => ⟨(F q).2.1, (F q).2.1.1.2, rfl⟩⟩
  -- the only fact that needs further checking is that they cover `s`.
  -- we already know that any point `x ∈ s` belongs to a set `M n z`.
  obtain ⟨n, z, hnz⟩ : ∃ (n : ℕ) (z : T), x ∈ M n z := s_subset x xs
  -- by density, it also belongs to a ball `closedBall (d p) (u n / 3)`.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, x ∈ closedBall (d p) (u n / 3) := by
    have : Set.Nonempty (ball x (u n / 3)) := by simp only [nonempty_ball]; linarith [u_pos n]
    obtain ⟨p, hp⟩ : ∃ p : ℕ, d p ∈ ball x (u n / 3) := hd.exists_mem_open isOpen_ball this
    exact ⟨p, (mem_ball'.1 hp).le⟩
  -- choose `q` for which `t q = K n z p`.
  obtain ⟨q, hq⟩ : ∃ q, F q = (n, z, p) := hF _
  -- then `x` belongs to `t q`.
  apply mem_iUnion.2 ⟨q, _⟩
  simp -zeta only [K, hq, mem_inter_iff, hp, and_true]
  exact subset_closure hnz

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

open scoped Function -- required for scoped `on` notation

/-- Assume that a function `f` has a derivative at every point of a set `s`. Then one may
partition `s` into countably many disjoint relatively measurable sets (i.e., intersections
of `s` with measurable sets `t n`) on which `f` is well approximated by linear maps `A n`. -/
/-
**exists_partition_approximatesLinearOn_of_hasFDerivWithinAt** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：exists_partition_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountabl
eTopology F] (f : E -> F) (s : Set E) (f' : E -> E ->L[Real] F) (hf' : forall x 
in s, HasFDerivWithinAt f (f' x) s x) (r : (E ->L[Real] F) -> Real>=0) (rpos : f
orall A, r A != 0) : exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] F), Pairw
ise (Disjoint on t) ∧ (forall n, MeasurableSet (t n)) ∧ (s subseteq ⋃ n, t n) ∧ 
(forall n, ApproximatesLinearOn f (A n) (s inter t n) (r (A n))) ∧ (s.Nonempty -
> forall n, exists y in s,
参数：f : E -> F；s : Set E；f' : E -> E ->L[Real] F；hf' : forall x in s, HasFDerivWi
thinAt f (f' x) s x；r : (E ->L[Real] F) -> Real>=0；rpos : forall A, r A != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt`：exists_cl
osed_cover_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
 (f : E -> F) (s : Set E) (f' : E -> E ->L[Real] F)…
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `ApproximatesLinearOn.mono_set`：mono_set (hst : s subseteq t) (hf : Appro
ximatesLinearOn f f' t c) : ApproximatesLinearOn f f' s c
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i

--- 原说明 ---
Assume that a function `f` has a derivative at every point of a set `s`. Then on
e may
partition `s` into countably many disjoint relatively measurable sets (i.e., int
ersections
of `s` with measurable sets `t n`) on which `f` is well approximated by linear m
aps `A n`.
-/
theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E → F) (s : Set E) (f' : E → E →L[ℝ] F) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (r : (E →L[ℝ] F) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] F),
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n, t n) ∧
            (∀ n, ApproximatesLinearOn f (A n) (s ∩ t n) (r (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) := by
  rcases exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' r rpos with
    ⟨t, A, t_closed, st, t_approx, ht⟩
  refine
    ⟨disjointed t, A, disjoint_disjointed _,
      MeasurableSet.disjointed fun n => (t_closed n).measurableSet, ?_, ?_, ht⟩
  · rw [iUnion_disjointed]; exact st
  · intro n; exact (t_approx n).mono_set (inter_subset_inter_right _ (disjointed_subset _ _))

namespace MeasureTheory

/-!
### Local lemmas

We check that a function which is well enough approximated by a linear map expands the volume
essentially like this linear map, and that its derivative (if it exists) is almost everywhere close
to the approximating linear map.
-/


/-- Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a given linear
map `A`. Then it expands the volume of any set by at most `m` for any `m > det A`. -/
/-
**MeasureTheory.addHaar_image_le_mul_of_det_lt** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：addHaar_image_le_mul_of_det_lt (A : E ->L[Real] E) {m : Real>=0} (hm : ENN
Real.ofReal |A.det| < m) : forallᶠ δ in 𝓝[>] (0 : Real>=0), forall (s : Set E) (
f : E -> E), ApproximatesLinearOn f A s δ -> μ (f '' s) <= m * μ s
参数：A : E ->L[Real] E；hm : ENNReal.ofReal |A.det| < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `tendsto_measure_cthickening_of_isCompact`：tendsto_measure_cthickening_of
_isCompact [MetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [ProperS
pace α] {μ : Measure α} [IsFin…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.add_closedBall_zero`：∀ {E : Type u_1} [inst : SeminormedAddCom
mGroup E] {δ : ℝ} {s : Set E},   IsCompact s → 0 ≤ δ → s + Metric.closedBall 0 δ
 = Metric.cthickeni…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.Measure.addHaar_image_continuousLinearMap`：addHaar_image_c
ontinuousLinearMap (f : E ->L[Real] E) (s : Set E) : μ (f '' s) = ENNReal.ofReal
 |LinearMap.det (f : E ->ₗ[Real] E)| * μ s
· 使用定理 `ENNReal.mul_lt_mul_left`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b < c → b 
* a < c * a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Metric.measure_closedBall_pos`：measure_closedBall_pos (x : X) {r : Real}
 (hr : 0 < r) : 0 < μ (closedBall x r)
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_closedBall_lt_top`：measure_closedBall_lt_top [Pseu
doMetricSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {
x : α} {r : Real} : μ (Metric…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 152 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a 
given linear
map `A`. Then it expands the volume of any set by at most `m` for any `m > det A
`.
-/
theorem addHaar_image_le_mul_of_det_lt (A : E →L[ℝ] E) {m : ℝ≥0}
    (hm : ENNReal.ofReal |A.det| < m) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → μ (f '' s) ≤ m * μ s := by
  apply nhdsWithin_le_nhds
  let d := ENNReal.ofReal |A.det|
  -- construct a small neighborhood of `A '' (closedBall 0 1)` with measure comparable to
  -- the determinant of `A`.
  obtain ⟨ε, hε, εpos⟩ :
    ∃ ε : ℝ, μ (closedBall 0 ε + A '' closedBall 0 1) < m * μ (closedBall 0 1) ∧ 0 < ε := by
    have HC : IsCompact (A '' closedBall 0 1) :=
      (ProperSpace.isCompact_closedBall _ _).image A.continuous
    have L0 :
      Tendsto (fun ε => μ (cthickening ε (A '' closedBall 0 1))) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact tendsto_measure_cthickening_of_isCompact HC
    have L1 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply L0.congr' _
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [← HC.add_closedBall_zero (le_of_lt hr), add_comm]
    have L2 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (d * μ (closedBall 0 1))) := by
      convert! L1
      exact (addHaar_image_continuousLinearMap _ _ _).symm
    have I : d * μ (closedBall 0 1) < m * μ (closedBall 0 1) := by
      gcongr; exacts [(measure_closedBall_pos μ _ zero_lt_one).ne', measure_closedBall_lt_top.ne]
    have H :
      ∀ᶠ b : ℝ in 𝓝[>] 0, μ (closedBall 0 b + A '' closedBall 0 1) < m * μ (closedBall 0 1) :=
      (tendsto_order.1 L2).2 _ I
    exact (H.and self_mem_nhdsWithin).exists
  have : Iio (.mk ε εpos.le) ∈ 𝓝 (0 : ℝ≥0) := by apply Iio_mem_nhds; exact εpos
  filter_upwards [this]
  -- fix a function `f` which is close enough to `A`.
  intro δ hδ s f hf
  simp only [mem_Iio, ← NNReal.coe_lt_coe, NNReal.coe_mk] at hδ
  -- This function expands the volume of any ball by at most `m`
  have I : ∀ x r, x ∈ s → 0 ≤ r → μ (f '' (s ∩ closedBall x r)) ≤ m * μ (closedBall x r) := by
    intro x r xs r0
    have K : f '' (s ∩ closedBall x r) ⊆ A '' closedBall 0 r + closedBall (f x) (ε * r) := by
      rintro y ⟨z, ⟨zs, zr⟩, rfl⟩
      rw [mem_closedBall_iff_norm] at zr
      apply Set.mem_add.2 ⟨A (z - x), _, f z - f x - A (z - x) + f x, _, _⟩
      · apply mem_image_of_mem
        simpa only [dist_eq_norm, mem_closedBall, mem_closedBall_zero_iff, sub_zero] using zr
      · rw [mem_closedBall_iff_norm, add_sub_cancel_right]
        calc
          ‖f z - f x - A (z - x)‖ ≤ δ * ‖z - x‖ := hf _ zs _ xs
          _ ≤ ε * r := by gcongr
      · simp only [map_sub]
        abel
    have :
      A '' closedBall 0 r + closedBall (f x) (ε * r) =
        {f x} + r • (A '' closedBall 0 1 + closedBall 0 ε) := by
      rw [smul_add, ← add_assoc, add_comm {f x}, add_assoc, smul_closedBall _ _ εpos.le, smul_zero,
        singleton_add_closedBall_zero, ← image_smul_set, _root_.smul_closedBall _ _ zero_le_one,
        smul_zero, Real.norm_eq_abs, abs_of_nonneg r0, mul_one, mul_comm]
    rw [this] at K
    calc
      μ (f '' (s ∩ closedBall x r)) ≤ μ ({f x} + r • (A '' closedBall 0 1 + closedBall 0 ε)) :=
        measure_mono K
      _ = ENNReal.ofReal (r ^ finrank ℝ E) * μ (A '' closedBall 0 1 + closedBall 0 ε) := by
        simp only [abs_of_nonneg r0, addHaar_smul, image_add_left, abs_pow, singleton_add,
          measure_preimage_add]
      _ ≤ ENNReal.ofReal (r ^ finrank ℝ E) * (m * μ (closedBall 0 1)) := by
        rw [add_comm]; gcongr
      _ = m * μ (closedBall x r) := by simp only [addHaar_closedBall' μ _ r0]; ring
  -- covering `s` by closed balls with total measure very close to `μ s`, one deduces that the
  -- measure of `f '' s` is at most `m * (μ s + a)` for any positive `a`.
  have J : ∀ᶠ a in 𝓝[>] (0 : ℝ≥0∞), μ (f '' s) ≤ m * (μ s + a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [mem_Ioi] at ha
    obtain ⟨t, r, t_count, ts, rpos, st, μt⟩ :
      ∃ (t : Set E) (r : E → ℝ),
        t.Countable ∧
          t ⊆ s ∧
            (∀ x : E, x ∈ t → 0 < r x) ∧
              (s ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧
                (∑' x : ↥t, μ (closedBall (↑x) (r ↑x))) ≤ μ s + a :=
      Besicovitch.exists_closedBall_covering_tsum_measure_le μ ha.ne' (fun _ => Ioi 0) s
        fun x _ δ δpos => ⟨δ / 2, by simp [half_pos δpos, δpos]⟩
    have : Encodable t := t_count.toEncodable
    calc
      μ (f '' s) ≤ μ (⋃ x : t, f '' (s ∩ closedBall x (r x))) := by
        rw [biUnion_eq_iUnion] at st
        apply measure_mono
        rw [← image_iUnion, ← inter_iUnion]
        exact Set.image_mono (subset_inter (Subset.refl _) st)
      _ ≤ ∑' x : t, μ (f '' (s ∩ closedBall x (r x))) := measure_iUnion_le _
      _ ≤ ∑' x : t, m * μ (closedBall x (r x)) :=
        (ENNReal.tsum_le_tsum fun x => I x (r x) (ts x.2) (rpos x x.2).le)
      _ ≤ m * (μ s + a) := by rw [ENNReal.tsum_mul_left]; gcongr
  -- taking the limit in `a`, one obtains the conclusion
  have L : Tendsto (fun a => (m : ℝ≥0∞) * (μ s + a)) (𝓝[>] 0) (𝓝 (m * (μ s + 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ENNReal.Tendsto.const_mul (tendsto_const_nhds.add tendsto_id)
    simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]
  rw [add_zero] at L
  exact ge_of_tendsto L J

/-- Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a given linear
map `A`. Then it expands the volume of any set by at least `m` for any `m < det A`. -/
/-
**MeasureTheory.mul_le_addHaar_image_of_lt_det** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：mul_le_addHaar_image_of_lt_det (A : E ->L[Real] E) {m : Real>=0} (hm : (m 
: Real>=0∞) < ENNReal.ofReal |A.det|) : forallᶠ δ in 𝓝[>] (0 : Real>=0), forall 
(s : Set E) (f : E -> E), ApproximatesLinearOn f A s δ -> (m : Real>=0∞) * μ s <
= μ (f '' s)
参数：A : E ->L[Real] E；hm : (m : Real>=0∞) < ENNReal.ofReal |A.det|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousLinearEquiv.det_coe_symm`：det_coe_symm {R : Type*} [Field R] {
M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M] (A : M ≃L[R] M) : 
(A.symm : M ->L[R] M).de…
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `Real.toNNReal_inv`：∀ {x : ℝ}, x⁻¹.toNNReal = x.toNNReal⁻¹
· 使用定理 `NNReal.inv_lt_inv`：inv_lt_inv {x y : Real>=0} (hx : x != 0) (h : x < y) 
: y⁻¹ < x⁻¹
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.addHaar_image_le_mul_of_det_lt`：addHaar_image_le_mul_of_de
t_lt (A : E ->L[Real] E) {m : Real>=0} (hm : ENNReal.ofReal |A.det| < m) : foral
lᶠ δ in 𝓝[>] (0 : Real>=0), forall…
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a 
given linear
map `A`. Then it expands the volume of any set by at least `m` for any `m < det 
A`.
-/
theorem mul_le_addHaar_image_of_lt_det (A : E →L[ℝ] E) {m : ℝ≥0}
    (hm : (m : ℝ≥0∞) < ENNReal.ofReal |A.det|) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → (m : ℝ≥0∞) * μ s ≤ μ (f '' s) := by
  apply nhdsWithin_le_nhds
  -- The assumption `hm` implies that `A` is invertible. If `f` is close enough to `A`, it is also
  -- invertible. One can then pass to the inverses, and deduce the estimate from
  -- `addHaar_image_le_mul_of_det_lt` applied to `f⁻¹` and `A⁻¹`.
  -- exclude first the trivial case where `m = 0`.
  rcases eq_zero_or_pos m with (rfl | mpos)
  · filter_upwards
    simp only [forall_const, zero_mul, imp_true_iff, zero_le, ENNReal.coe_zero]
  have hA : A.det ≠ 0 := by
    intro h; simp only [h, ENNReal.not_lt_zero, ENNReal.ofReal_zero, abs_zero] at hm
  -- let `B` be the continuous linear equiv version of `A`.
  let B := A.toContinuousLinearEquivOfDetNeZero hA
  -- the determinant of `B.symm` is bounded by `m⁻¹`
  have I : ENNReal.ofReal |(B.symm : E →L[ℝ] E).det| < (m⁻¹ : ℝ≥0) := by
    simp only [ENNReal.ofReal, abs_inv, Real.toNNReal_inv, ContinuousLinearEquiv.det_coe_symm,
      ENNReal.coe_lt_coe] at hm ⊢
    exact NNReal.inv_lt_inv mpos.ne' hm
  -- therefore, we may apply `addHaar_image_le_mul_of_det_lt` to `B.symm` and `m⁻¹`.
  obtain ⟨δ₀, δ₀pos, hδ₀⟩ :
    ∃ δ : ℝ≥0,
      0 < δ ∧
        ∀ (t : Set E) (g : E → E),
          ApproximatesLinearOn g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t := by
    have :
      ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0,
        ∀ (t : Set E) (g : E → E),
          ApproximatesLinearOn g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t :=
      addHaar_image_le_mul_of_det_lt μ B.symm I
    rcases (this.and self_mem_nhdsWithin).exists with ⟨δ₀, h, h'⟩
    exact ⟨δ₀, h', h⟩
  -- record smallness conditions for `δ` that will be needed to apply `hδ₀` below.
  have L1 : ∀ᶠ δ in 𝓝 (0 : ℝ≥0), Subsingleton E ∨ δ < ‖(B.symm : E →L[ℝ] E)‖₊⁻¹ := by
    by_cases h : Subsingleton E
    · simp only [h, true_or, eventually_const]
    simp only [h, false_or]
    apply Iio_mem_nhds
    simpa only [h, false_or, inv_pos] using B.subsingleton_or_nnnorm_symm_pos
  have L2 :
    ∀ᶠ δ in 𝓝 (0 : ℝ≥0), ‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - δ)⁻¹ * δ < δ₀ := by
    have :
      Tendsto (fun δ => ‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - δ)⁻¹ * δ) (𝓝 0)
        (𝓝 (‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - 0)⁻¹ * 0)) := by
      rcases eq_or_ne ‖(B.symm : E →L[ℝ] E)‖₊ 0 with (H | H)
      · simpa only [H, zero_mul] using tendsto_const_nhds
      refine Tendsto.mul (tendsto_const_nhds.mul ?_) tendsto_id
      refine (Tendsto.sub tendsto_const_nhds tendsto_id).inv₀ ?_
      simpa only [tsub_zero, inv_eq_zero, Ne] using H
    simp only [mul_zero] at this
    exact (tendsto_order.1 this).2 δ₀ δ₀pos
  -- let `δ` be small enough, and `f` approximated by `B` up to `δ`.
  filter_upwards [L1, L2]
  intro δ h1δ h2δ s f hf
  have hf' : ApproximatesLinearOn f (B : E →L[ℝ] E) s δ := by convert! hf
  let F := hf'.toPartialEquiv h1δ
  -- the condition to be checked can be reformulated in terms of the inverse maps
  suffices H : μ (F.symm '' F.target) ≤ (m⁻¹ : ℝ≥0) * μ F.target by
    change (m : ℝ≥0∞) * μ F.source ≤ μ F.target
    rwa [← F.symm_image_target_eq_source, mul_comm, ← ENNReal.le_div_iff_mul_le, div_eq_mul_inv,
      mul_comm, ← ENNReal.coe_inv mpos.ne']
    · apply Or.inl
      simpa only [ENNReal.coe_eq_zero, Ne] using mpos.ne'
    · simp
  -- as `f⁻¹` is well approximated by `B⁻¹`, the conclusion follows from `hδ₀`
  -- and our choice of `δ`.
  exact hδ₀ _ _ ((hf'.to_inv h1δ).mono_num h2δ.le)

/-- If a differentiable function `f` is approximated by a linear map `A` on a set `s`, up to `δ`,
then at almost every `x` in `s` one has `‖f' x - A‖ ≤ δ`. -/
/-
**MeasureTheory._root_.ApproximatesLinearOn.norm_fderiv_sub_le** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a differentiable function `f` is approximated by a linear map `A` on a set `s
`, up to `δ`,
then at almost every `x` in `s` one has `‖f' x - A‖ ≤ δ`.
-/
theorem _root_.ApproximatesLinearOn.norm_fderiv_sub_le {A : E →L[ℝ] E} {δ : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hs : MeasurableSet s) (f' : E → E →L[ℝ] E)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : ∀ᵐ x ∂μ.restrict s, ‖f' x - A‖₊ ≤ δ := by
  /- The conclusion will hold at the Lebesgue density points of `s` (which have full measure).
    At such a point `x`, for any `z` and any `ε > 0` one has for small `r`
    that `{x} + r • closedBall z ε` intersects `s`. At a point `y` in the intersection,
    `f y - f x` is close both to `f' x (r z)` (by differentiability) and to `A (r z)`
    (by linear approximation), so these two quantities are close, i.e., `(f' x - A) z` is small. -/
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs]
  -- start from a Lebesgue density point `x`, belonging to `s`.
  intro x hx xs
  -- consider an arbitrary vector `z`.
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  -- to show that `‖(f' x - A) z‖ ≤ δ ‖z‖`, it suffices to do it up to some error that vanishes
  -- asymptotically in terms of `ε > 0`.
  suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
    have :
      Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at this
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    filter_upwards [self_mem_nhdsWithin]
    exact H
  -- fix a positive `ε`.
  intro ε εpos
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` intersects `s`, as `x` is a
  -- density point
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
    ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` is included in the set where
  -- `f y - f x` is well approximated by `f' x (y - x)`.
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  -- fix a small positive `r` satisfying the above properties, as well as a corresponding `y`.
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
    ∃ r : ℝ,
      (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧ {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  -- write `y = x + r a` with `a ∈ closedBall z ε`.
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  -- use the approximation properties to control `(f' x - A) a`, and then `(f' x - A) z` as `z` is
  -- close to `a`.
  have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
          Pi.sub_apply, map_smul, smul_sub]
      _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ := norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
      congr 1
      simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
      abel
    _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr

/-!
### Measure zero of the image, over non-measurable sets

If a set has measure `0`, then its image under a differentiable map has measure zero. This doesn't
require the set to be measurable. In the same way, if `f` is differentiable on a set `s` with
non-invertible derivative everywhere, then `f '' s` has measure `0`, again without measurability
assumptions.
-/


/-- A differentiable function maps sets of measure zero to sets of measure zero. -/
/-
**MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (hf : Differe
ntiableOn Real f s) (hs : μ s = 0) : μ (f '' s) = 0
参数：hf : DifferentiableOn Real f s；hs : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `MeasureTheory.addHaar_image_le_mul_of_det_lt`：addHaar_image_le_mul_of_de
t_lt (A : E ->L[Real] E) {m : Real>=0} (hm : ENNReal.ofReal |A.det| < m) : foral
lᶠ δ in 𝓝[>] (0 : Real>=0), forall…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`：exists_parti
tion_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F] (f : 
E -> F) (s : Set E) (f' : E -> E ->L[Real] F) (h…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
A differentiable function maps sets of measure zero to sets of measure zero.
-/
theorem addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (hf : DifferentiableOn ℝ f s)
    (hs : μ s = 0) : μ (f '' s) = 0 := by
  rw [← nonpos_iff_eq_zero]
  have :
      ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ (t : Set E), ApproximatesLinearOn f A t δ →
          μ (f '' t) ≤ (Real.toNNReal |A.det| + 1 : ℝ≥0) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + 1
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, zero_lt_one, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  obtain ⟨t, A, _, _, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = fderivWithin ℝ f s y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderivWithin ℝ f s)
      (fun x xs => (hf x xs).hasFDerivWithinAt) δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact Set.image_mono (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (Real.toNNReal |(A n).det| + 1 : ℝ≥0) * μ (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2
      exact ht n
    _ ≤ ∑' n, ((Real.toNNReal |(A n).det| + 1 : ℝ≥0) : ℝ≥0∞) * 0 := by
      gcongr with n
      exact le_trans (measure_mono inter_subset_left) (le_of_eq hs)
    _ = 0 := by simp only [tsum_zero, mul_zero]

/-- A version of **Sard's lemma** in fixed dimension: given a differentiable function from `E`
to `E` and a set where the differential is not invertible, then the image of this set has
zero measure. Here, we give an auxiliary statement towards this result. -/
/-
**MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux (hf' : forall x in s
, HasFDerivWithinAt f (f' x) s x) (R : Real) (hs : s subseteq closedBall 0 R) (ε
 : Real>=0) (εpos : 0 < ε) (h'f' : forall x in s, (f' x).det = 0) : μ (f '' s) <
= ε * μ (closedBall 0 R)
参数：hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；R : Real；hs : s subseteq 
closedBall 0 R；ε : Real>=0；εpos : 0 < ε；h'f' : forall x in s, (f' x).det = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `MeasureTheory.addHaar_image_le_mul_of_det_lt`：addHaar_image_le_mul_of_de
t_lt (A : E ->L[Real] E) {m : Real>=0} (hm : ENNReal.ofReal |A.det| < m) : foral
lᶠ δ in 𝓝[>] (0 : Real>=0), forall…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`：exists_parti
tion_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F] (f : 
E -> F) (s : Set E) (f' : E -> E ->L[Real] F) (h…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
A version of **Sard's lemma** in fixed dimension: given a differentiable functio
n from `E`
to `E` and a set where the differential is not invertible, then the image of thi
s set has
zero measure. Here, we give an auxiliary statement towards this result.
-/
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (R : ℝ) (hs : s ⊆ closedBall 0 R) (ε : ℝ≥0)
    (εpos : 0 < ε) (h'f' : ∀ x ∈ s, (f' x).det = 0) : μ (f '' s) ≤ ε * μ (closedBall 0 R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's); · simp only [measure_empty, zero_le, image_empty]
  have :
      ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ (t : Set E), ApproximatesLinearOn f A t δ →
          μ (f '' t) ≤ (Real.toNNReal |A.det| + ε : ℝ≥0) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      rw [← image_iUnion, ← inter_iUnion]
      gcongr
      exact subset_inter Subset.rfl t_cover
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (Real.toNNReal |(A n).det| + ε : ℝ≥0) * μ (s ∩ t n) := by
      gcongr
      exact (hδ (A _)).2 _ (ht _)
    _ = ∑' n, ε * μ (s ∩ t n) := by
      congr with n
      rcases Af' h's n with ⟨y, ys, hy⟩
      simp only [hy, h'f' y ys, Real.toNNReal_zero, abs_zero, zero_add]
    _ ≤ ε * ∑' n, μ (closedBall 0 R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * μ (⋃ n, closedBall 0 R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ ≤ ε * μ (closedBall 0 R) := by grw [← inter_iUnion, inter_subset_left]

/-- A version of Sard lemma in fixed dimension: given a differentiable function from `E` to `E` and
a set where the differential is not invertible, then the image of this set has zero measure. -/
/-
**MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (hf' : forall x in s, Ha
sFDerivWithinAt f (f' x) s x) (h'f' : forall x in s, (f' x).det = 0) : μ (f '' s
) = 0
参数：hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；h'f' : forall x in s, (f'
 x).det = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux`：add
Haar_image_eq_zero_of_det_fderivWithin_eq_zero_aux (hf' : forall x in s, HasFDer
ivWithinAt f (f' x) s x) (R : Real) (hs : s subseteq clos…
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_closedBall_lt_top`：measure_closedBall_lt_top [Pseu
doMetricSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {
x : α} {r : Real} : μ (Metric…
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
A version of Sard lemma in fixed dimension: given a differentiable function from
 `E` to `E` and
a set where the differential is not invertible, then the image of this set has z
ero measure.
-/
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (h'f' : ∀ x ∈ s, (f' x).det = 0) :
    μ (f '' s) = 0 := by
  suffices H : ∀ R, μ (f '' (s ∩ closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero, ← iUnion_inter_closedBall_nat s 0]
    calc
      μ (f '' ⋃ n : ℕ, s ∩ closedBall 0 n) ≤ ∑' n : ℕ, μ (f '' (s ∩ closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ ≤ 0 := by simp only [H, tsum_zero, nonpos_iff_eq_zero]
  intro R
  have A : ∀ (ε : ℝ≥0), 0 < ε → μ (f '' (s ∩ closedBall 0 R)) ≤ ε * μ (closedBall 0 R) :=
    fun ε εpos =>
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux μ
      (fun x hx => (hf' x hx.1).mono inter_subset_left) R inter_subset_right ε εpos
      fun x hx => h'f' x hx.1
  have B : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R)) (𝓝[>] 0) (𝓝 0) := by
    have :
      Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R)) (𝓝 0)
        (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * μ (closedBall 0 R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  rw [← nonpos_iff_eq_zero]
  apply ge_of_tendsto B
  filter_upwards [self_mem_nhdsWithin]
  exact A

/-!
### Weak measurability statements

We show that the derivative of a function on a set is almost everywhere measurable, and that the
image `f '' s` is measurable if `f` is injective on `s`. The latter statement follows from the
Lusin-Souslin theorem.
-/


/-- The derivative of a function on a measurable set is almost everywhere measurable on this set
with respect to Lebesgue measure. Note that, in general, it is not genuinely measurable there,
as `f'` is not unique (but only on a set of measure `0`, as the argument shows). -/
/-
**MeasureTheory.aemeasurable_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：aemeasurable_fderivWithin (hs : MeasurableSet s) (hf' : forall x in s, Has
FDerivWithinAt f (f' x) s x) : AEMeasurable f' (μ.restrict s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aemeasurable_of_unif_approx`：aemeasurable_of_unif_approx {β} [Measurable
Space β] [PseudoMetricSpace β] [BorelSpace β] {μ : Measure α} {g : α -> β} (hf :
 forall ε > (0 : …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`：exists_parti
tion_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F] (f : 
E -> F) (s : Set E) (f' : E -> E ->L[Real] F) (h…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `exists_measurable_piecewise`：exists_measurable_piecewise {ι} [Countable 
ι] [Nonempty ι] (t : ι -> Set α) (t_meas : forall n, MeasurableSet (t n)) (g : ι
 -> α -> β) (hg :…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.ae_sum_iff`：ae_sum_iff [Countable ι] {μ : ι -> Mea
sure α} {p : α -> Prop} : (forallᵐ x ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p 
x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ApproximatesLinearOn.norm_fderiv_sub_le`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E}  
 {f : E → E} [inst_3 : Measur…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The derivative of a function on a measurable set is almost everywhere measurable
 on this set
with respect to Lebesgue measure. Note that, in general, it is not genuinely mea
surable there,
as `f'` is not unique (but only on a set of measure `0`, as the argument shows).
-/
theorem aemeasurable_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : AEMeasurable f' (μ.restrict s) := by
  /- It suffices to show that `f'` can be uniformly approximated by a measurable function.
    Fix `ε > 0`. Thanks to `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, one
    can find a countable measurable partition of `s` into sets `s ∩ t n` on which `f` is well
    approximated by linear maps `A n`. On almost all of `s ∩ t n`, it follows from
    `ApproximatesLinearOn.norm_fderiv_sub_le` that `f'` is uniformly approximated by `A n`, which
    gives the conclusion. -/
  -- fix a precision `ε`
  refine aemeasurable_of_unif_approx fun ε εpos => ?_
  let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
  have δpos : 0 < δ := εpos
  -- partition `s` into sets `s ∩ t n` on which `f` is approximated by linear maps `A n`.
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, _⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) δ) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' (fun _ => δ) fun _ =>
      δpos.ne'
  -- define a measurable function `g` which coincides with `A n` on `t n`.
  obtain ⟨g, g_meas, hg⟩ :
      ∃ g : E → E →L[ℝ] E, Measurable g ∧ ∀ (n : ℕ) (x : E), x ∈ t n → g x = A n :=
    exists_measurable_piecewise t t_meas (fun n _ => A n) (fun n => measurable_const) <|
      t_disj.mono fun i j h => by simp only [h.inter_eq, eqOn_empty]
  refine ⟨g, g_meas.aemeasurable, ?_⟩
  -- reduce to checking that `f'` and `g` are close on almost all of `s ∩ t n`, for all `n`.
  suffices H : ∀ᵐ x : E ∂sum fun n ↦ μ.restrict (s ∩ t n), dist (g x) (f' x) ≤ ε by
    have : μ.restrict s ≤ sum fun n => μ.restrict (s ∩ t n) := by
      have : s = ⋃ n, s ∩ t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
      conv_lhs => rw [this]
      exact restrict_iUnion_le
    exact ae_mono this H
  -- fix such an `n`.
  refine ae_sum_iff.2 fun n => ?_
  -- on almost all `s ∩ t n`, `f' x` is close to `A n` thanks to
  -- `ApproximatesLinearOn.norm_fderiv_sub_le`.
  have E₁ : ∀ᵐ x : E ∂μ.restrict (s ∩ t n), ‖f' x - A n‖₊ ≤ δ :=
    (ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
      (hf' x hx.1).mono inter_subset_left
  -- moreover, `g x` is equal to `A n` there.
  have E₂ : ∀ᵐ x : E ∂μ.restrict (s ∩ t n), g x = A n := by
    suffices H : ∀ᵐ x : E ∂μ.restrict (t n), g x = A n from
      ae_mono (restrict_mono inter_subset_right le_rfl) H
    filter_upwards [ae_restrict_mem (t_meas n)]
    exact hg n
  -- putting these two properties together gives the conclusion.
  filter_upwards [E₁, E₂] with x hx1 hx2
  rw [← nndist_eq_nnnorm] at hx1
  rw [hx2, dist_comm]
  exact hx1
/-
**MeasureTheory.aemeasurable_ofReal_abs_det_fderivWithin** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：aemeasurable_ofReal_abs_det_fderivWithin (hs : MeasurableSet s) (hf' : for
all x in s, HasFDerivWithinAt f (f' x) s x) : AEMeasurable (fun x => ENNReal.ofR
eal |(f' x).det|) (μ.restrict s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `ENNReal.measurable_ofReal`：measurable_ofReal : Measurable ENNReal.ofReal
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `continuous_abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G], …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.continuous_det`：ContinuousLinearMap.continuous_det :
 Continuous fun f : E ->L[𝕜] E => f.det
· 使用定理 `MeasureTheory.aemeasurable_fderivWithin`：aemeasurable_fderivWithin (hs :
 MeasurableSet s) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) : AEMeas
urable f' (μ.restrict s)
-/
theorem aemeasurable_ofReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => ENNReal.ofReal |(f' x).det|) (μ.restrict s) := by
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'
/-
**MeasureTheory.aemeasurable_toNNReal_abs_det_fderivWithin** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：aemeasurable_toNNReal_abs_det_fderivWithin (hs : MeasurableSet s) (hf' : f
orall x in s, HasFDerivWithinAt f (f' x) s x) : AEMeasurable (fun x => |(f' x).d
et|.toNNReal) (μ.restrict s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_real_toNNReal`：measurable_real_toNNReal : Measurable Real.toN
NReal
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `continuous_abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G], …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.continuous_det`：ContinuousLinearMap.continuous_det :
 Continuous fun f : E ->L[𝕜] E => f.det
· 使用定理 `MeasureTheory.aemeasurable_fderivWithin`：aemeasurable_fderivWithin (hs :
 MeasurableSet s) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) : AEMeas
urable f' (μ.restrict s)
-/
theorem aemeasurable_toNNReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => |(f' x).det|.toNNReal) (μ.restrict s) := by
  apply measurable_real_toNNReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'

/-- If a function is differentiable and injective on a measurable set,
then the image is measurable. -/
/-
**MeasureTheory.measurable_image_of_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measurable_image_of_fderivWithin (hs : MeasurableSet s) (hf' : forall x in
 s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : MeasurableSet (f '' s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.image_of_continuousOn_injOn`：MeasurableSet.image_of_contin
uousOn_injOn [OpensMeasurableSpace β] [tγ : TopologicalSpace γ] [PolishSpace γ] 
[MeasurableSpace γ] [BorelSpace…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x

--- 原说明 ---
If a function is differentiable and injective on a measurable set,
then the image is measurable.
-/
theorem measurable_image_of_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : MeasurableSet (f '' s) :=
  haveI : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
  hs.image_of_continuousOn_injOn (DifferentiableOn.continuousOn this) hf

/-- If a function is differentiable and injective on a null measurable set,
then the image is null measurable. -/
/-
**MeasureTheory.nullMeasurable_image_of_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：nullMeasurable_image_of_fderivWithin (hs : NullMeasurableSet s μ) (hf' : f
orall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : NullMeasurableS
et (f '' s) μ
参数：hs : NullMeasurableSet s μ；hf' : forall x in s, HasFDerivWithinAt f (f' x) s 
x；hf : InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq`：exists_m
easurable_subset_ae_eq (h : NullMeasurableSet s μ) : exists t subseteq s, Measur
ableSet t ∧ t =ᵐ[μ] s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `MeasureTheory.union_ae_eq_left_of_ae_eq_empty`：union_ae_eq_left_of_ae_eq
_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_ze
ro`：addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (hf : Different
iableOn Real f s) (hs : μ s = 0) : μ (f '' s) = 0
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_eq_set`：ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t)
 = 0 ∧ μ (t \ s) = 0
· 使用定理 `MeasureTheory.NullMeasurableSet.congr`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → s =ᵐ[μ] t → M…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.measurable_image_of_fderivWithin`：measurable_image_of_fder
ivWithin (hs : MeasurableSet s) (hf' : forall x in s, HasFDerivWithinAt f (f' x)
 s x) (hf : InjOn f s) : MeasurableS…
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If a function is differentiable and injective on a null measurable set,
then the image is null measurable.
-/
theorem nullMeasurable_image_of_fderivWithin (hs : NullMeasurableSet s μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    NullMeasurableSet (f '' s) μ := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : f '' s =ᵐ[μ] f '' t := by
    have : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this, image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      (fun x hx ↦ ?_) (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  apply NullMeasurableSet.congr _ A.symm
  apply MeasurableSet.nullMeasurableSet
  apply measurable_image_of_fderivWithin ht _ (hf.mono ts) (f' := f')
  intro x hx
  exact (hf' x (ts hx)).mono ts

/-- If a function is differentiable and injective on a measurable set `s`, then its restriction
to `s` is a measurable embedding. -/
/-
**MeasureTheory.measurableEmbedding_of_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：measurableEmbedding_of_fderivWithin (hs : MeasurableSet s) (hf' : forall x
 in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : MeasurableEmbedding (s
.domRestrict f)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.measurableEmbedding`：ContinuousOn.measurableEmbedding [Bore
lSpace β] [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ
] (hs : MeasurableSet …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x

--- 原说明 ---
If a function is differentiable and injective on a measurable set `s`, then its 
restriction
to `s` is a measurable embedding.
-/
theorem measurableEmbedding_of_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    MeasurableEmbedding (s.domRestrict f) :=
  haveI : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
  this.continuousOn.measurableEmbedding hs hf

/-!
### Proving the estimate for the measure of the image

We show the formula `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ = μ (f '' s)`,
in `lintegral_abs_det_fderiv_eq_addHaar_image`. For this, we show both inequalities in both
directions, first up to controlled errors and then letting these errors tend to `0`.
-/


/-
**MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv_aux1** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：addHaar_image_le_lintegral_abs_det_fderiv_aux1 (hs : MeasurableSet s) (hf'
 : forall x in s, HasFDerivWithinAt f (f' x) s x) {ε : Real>=0} (εpos : 0 < ε) :
 μ (f '' s) <= (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；εpos
 : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `MeasureTheory.addHaar_image_le_mul_of_det_lt`：addHaar_image_le_mul_of_de
t_lt (A : E ->L[Real] E) {m : Real>=0} (hm : ENNReal.ofReal |A.det| < m) : foral
lᶠ δ in 𝓝[>] (0 : Real>=0), forall…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.continuousAt_iff`：continuousAt_iff [PseudoMetricSpace β] {f : α -
> β} {a : α} : ContinuousAt f a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, di
st x a < δ ->…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearMap.continuous_det`：ContinuousLinearMap.continuous_det :
 Continuous fun f : E ->L[𝕜] E => f.det
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
### Proving the estimate for the measure of the image

We show the formula `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ = μ (f '' s)`,
in `lintegral_abs_det_fderiv_eq_addHaar_image`. For this, we show both inequalit
ies in both
directions, first up to controlled errors and then letting these errors tend to 
`0`.
-/
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux1 (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) {ε : ℝ≥0} (εpos : 0 < ε) :
    μ (f '' s) ≤ (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
  /- To bound `μ (f '' s)`, we cover `s` by sets where `f` is well-approximated by linear maps
    `A n` (and where `f'` is almost everywhere close to `A n`), and then use that `f` expands the
    measure of such a set by at most `(A n).det + ε`. -/
  have :
    ∀ A : E →L[ℝ] E,
      ∃ δ : ℝ≥0,
        0 < δ ∧
          (∀ B : E →L[ℝ] E, ‖B - A‖ ≤ δ → |B.det - A.det| ≤ ε) ∧
            ∀ (t : Set E) (g : E → E), ApproximatesLinearOn g A t δ →
              μ (g '' t) ≤ (ENNReal.ofReal |A.det| + ε) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ B, dist B A < δ' → dist B.det A.det < ↑ε := by
      refine continuousAt_iff.1 ?_ ε εpos
      exact ContinuousLinearMap.continuous_det.continuousAt
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      calc
        ‖B - A‖ ≤ (min δ δ'' : ℝ≥0) := hB
        _ ≤ δ'' := by simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
        _ < δ' := half_lt_self δ'pos
    · intro t g htg
      exact h t g (htg.mono_num (min_le_left _ _))
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact Set.image_mono (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ENNReal.ofReal |(A n).det| + ε) * μ (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2.2
      exact ht n
    _ = ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
    _ ≤ ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have I : |(A n).det| ≤ |(f' x).det| + ε :=
        calc
          |(A n).det| = |(f' x).det - ((f' x).det - (A n).det)| := by congr 1; abel
          _ ≤ |(f' x).det| + |(f' x).det - (A n).det| := abs_sub _ _
          _ ≤ |(f' x).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(A n).det| + ε ≤ ENNReal.ofReal (|(f' x).det| + ε) + ε := by gcongr
        _ = ENNReal.ofReal |(f' x).det| + 2 * ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, two_mul, add_assoc, NNReal.zero_le_coe,
            ENNReal.ofReal_coe_nnreal]
    _ = ∫⁻ x in ⋃ n, s ∩ t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      have M : ∀ n : ℕ, MeasurableSet (s ∩ t n) := fun n => hs.inter (t_meas n)
      rw [lintegral_iUnion M]
      exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
    _ = (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
      simp only [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
/-
**MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv_aux2** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：addHaar_image_le_lintegral_abs_det_fderiv_aux2 (hs : MeasurableSet s) (h's
 : μ s != ∞) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) : μ (f '' s) 
<= ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ
参数：hs : MeasurableSet s；h's : μ s != ∞；hf' : forall x in s, HasFDerivWithinAt f 
(f' x) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 32 条，此处仅展示前 30 条）
-/
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux2 (hs : MeasurableSet s) (h's : μ s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : ℝ≥0 => (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 ((∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * (0 : ℝ≥0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact addHaar_image_le_lintegral_abs_det_fderiv_aux1 μ hs hf' εpos
/-
**MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：addHaar_image_le_lintegral_abs_det_fderiv (hs : MeasurableSet s) (hf' : fo
rall x in s, HasFDerivWithinAt f (f' x) s x) : μ (f '' s) <= ∫⁻ x in s, ENNReal.
ofReal |(f' x).det| ∂μ
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv_aux2`：addHaar_im
age_le_lintegral_abs_det_fderiv_aux2 (hs : MeasurableSet s) (h's : μ s != ∞) (hf
' : forall x in s, HasFDerivWithinAt f (f' x) s x)…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
（共 36 条，此处仅展示前 30 条）
-/
theorem addHaar_image_le_lintegral_abs_det_fderiv (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets μ i
  have A : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    μ (f '' s) ≤ ∑' n, μ (f '' (s ∩ u n)) := by
      conv_lhs => rw [A, image_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        addHaar_image_le_lintegral_abs_det_fderiv_aux2 μ (hs.inter (u_meas n)) _ fun x hx =>
          (hf' x hx.1).mono inter_subset_left
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_rhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right
/-
**MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image_aux1** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_abs_det_fderiv_le_addHaar_image_aux1 (hs : MeasurableSet s) (hf'
 : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) {ε : Real>=0}
 (εpos : 0 < ε) : (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) <= μ (f '' s) + 2 
* ε * μ s
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s；εpos : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.continuousAt_iff`：continuousAt_iff [PseudoMetricSpace β] {f : α -
> β} {a : α} : ContinuousAt f a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, di
st x a < δ ->…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearMap.continuous_det`：ContinuousLinearMap.continuous_det :
 Continuous fun f : E ->L[𝕜] E => f.det
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
（共 112 条，此处仅展示前 30 条）
-/
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux1 (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) {ε : ℝ≥0} (εpos : 0 < ε) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) + 2 * ε * μ s := by
  /- To bound `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ`, we cover `s` by sets where `f` is
    well-approximated by linear maps `A n` (and where `f'` is almost everywhere close to `A n`),
    and then use that `f` expands the measure of such a set by at least `(A n).det - ε`. -/
  have :
    ∀ A : E →L[ℝ] E,
      ∃ δ : ℝ≥0,
        0 < δ ∧
          (∀ B : E →L[ℝ] E, ‖B - A‖ ≤ δ → |B.det - A.det| ≤ ε) ∧
            ∀ (t : Set E) (g : E → E), ApproximatesLinearOn g A t δ →
              ENNReal.ofReal |A.det| * μ t ≤ μ (g '' t) + ε * μ t := by
    intro A
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ B, dist B A < δ' → dist B.det A.det < ↑ε := by
      refine continuousAt_iff.1 ?_ ε εpos
      exact ContinuousLinearMap.continuous_det.continuousAt
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    have I'' : ∀ B : E →L[ℝ] E, ‖B - A‖ ≤ ↑δ'' → |B.det - A.det| ≤ ↑ε := by
      intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      exact hB.trans_lt (half_lt_self δ'pos)
    rcases eq_or_ne A.det 0 with (hA | hA)
    · refine ⟨δ'', half_pos δ'pos, I'', ?_⟩
      simp only [hA, forall_const, zero_mul, ENNReal.ofReal_zero, imp_true_iff,
        zero_le, abs_zero]
    let m : ℝ≥0 := Real.toNNReal |A.det| - ε
    have I : (m : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
      simp only [m, ENNReal.ofReal, ENNReal.coe_sub]
      apply ENNReal.sub_lt_self ENNReal.coe_ne_top
      · simpa only [abs_nonpos_iff, Real.toNNReal_eq_zero, ENNReal.coe_eq_zero, Ne] using hA
      · simp only [εpos.ne', ENNReal.coe_eq_zero, Ne, not_false_iff]
    rcases ((mul_le_addHaar_image_of_lt_det μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      apply I'' _ (hB.trans _)
      simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
    · intro t g htg
      rcases eq_or_ne (μ t) ∞ with (ht | ht)
      · simp only [ht, εpos.ne', ENNReal.mul_top, ENNReal.coe_eq_zero, le_top, Ne,
          not_false_iff, _root_.add_top]
      have := h t g (htg.mono_num (min_le_left _ _))
      rwa [ENNReal.coe_sub, ENNReal.sub_mul, tsub_le_iff_right] at this
      simp only [ht, imp_true_iff, Ne, not_false_iff]
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  have s_eq : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [s_eq]
      rw [lintegral_iUnion]
      · exact fun n => hs.inter (t_meas n)
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ ≤ ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have I : |(f' x).det| ≤ |(A n).det| + ε :=
        calc
          |(f' x).det| = |(A n).det + ((f' x).det - (A n).det)| := by congr 1; abel
          _ ≤ |(A n).det| + |(f' x).det - (A n).det| := abs_add_le _ _
          _ ≤ |(A n).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(f' x).det| ≤ ENNReal.ofReal (|(A n).det| + ε) :=
          ENNReal.ofReal_le_ofReal I
        _ = ENNReal.ofReal |(A n).det| + ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
    _ = ∑' n, (ENNReal.ofReal |(A n).det| * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
      simp only [setLIntegral_const, lintegral_add_right _ measurable_const]
    _ ≤ ∑' n, (μ (f '' (s ∩ t n)) + ε * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
      gcongr
      exact (hδ (A _)).2.2 _ _ (ht _)
    _ = μ (f '' s) + 2 * ε * μ s := by
      conv_rhs => rw [s_eq]
      rw [image_iUnion, measure_iUnion]; rotate_left
      · intro i j hij
        apply Disjoint.image _ hf inter_subset_left inter_subset_left
        exact Disjoint.mono inter_subset_right inter_subset_right (t_disj hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (t_meas i))
            (fun x hx => (hf' x hx.1).mono inter_subset_left)
            (hf.mono inter_subset_left)
      rw [measure_iUnion]; rotate_left
      · exact pairwise_disjoint_mono t_disj fun i => inter_subset_right
      · exact fun i => hs.inter (t_meas i)
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      congr 1
      ext1 i
      rw [mul_assoc, two_mul, add_assoc]
/-
**MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image_aux2** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_abs_det_fderiv_le_addHaar_image_aux2 (hs : MeasurableSet s) (h's
 : μ s != ∞) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f
 s) : (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) <= μ (f '' s)
参数：hs : MeasurableSet s；h's : μ s != ∞；hf' : forall x in s, HasFDerivWithinAt f 
(f' x) s x；hf : InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 32 条，此处仅展示前 30 条）
-/
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux2 (hs : MeasurableSet s) (h's : μ s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) := by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : ℝ≥0 => μ (f '' s) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 (μ (f '' s) + 2 * (0 : ℝ≥0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact lintegral_abs_det_fderiv_le_addHaar_image_aux1 μ hs hf' hf εpos
/-
**MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：lintegral_abs_det_fderiv_le_addHaar_image (hs : MeasurableSet s) (hf' : fo
rall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : (∫⁻ x in s, ENNR
eal.ofReal |(f' x).det| ∂μ) <= μ (f '' s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_iUnion`：lintegral_iUnion [Countable β] {s : β ->
 Set α} (hm : forall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s)) (f 
: α -> Real>=0∞) : ∫…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `pairwise_disjoint_mono`：pairwise_disjoint_mono [PartialOrder α] [OrderBo
t α] (hs : Pairwise (Disjoint on f)) (h : g <= f) : Pairwise (Disjoint on g)
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image_aux2`：lintegral_
abs_det_fderiv_le_addHaar_image_aux2 (hs : MeasurableSet s) (h's : μ s != ∞) (hf
' : forall x in s, HasFDerivWithinAt f (f' x) s x)…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
（共 40 条，此处仅展示前 30 条）
-/
theorem lintegral_abs_det_fderiv_le_addHaar_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) := by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets μ i
  have A : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right
    _ ≤ ∑' n, μ (f '' (s ∩ u n)) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        lintegral_abs_det_fderiv_le_addHaar_image_aux2 μ (hs.inter (u_meas n)) _
          (fun x hx => (hf' x hx.1).mono inter_subset_left) (hf.mono inter_subset_left)
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = μ (f '' s) := by
      conv_rhs => rw [A, image_iUnion]
      rw [measure_iUnion]
      · intro i j hij
        apply Disjoint.image _ hf inter_subset_left inter_subset_left
        exact
          Disjoint.mono inter_subset_right inter_subset_right
            (disjoint_disjointed _ hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (u_meas i))
            (fun x hx => (hf' x hx.1).mono inter_subset_left)
            (hf.mono inter_subset_left)

/-- Change of variable formula for differentiable functions, set version: if a function `f` is
injective and differentiable on a measurable set `s`, then the measure of `f '' s` is given by the
integral of `|(f' x).det|` on `s`.
Note that the measurability of `f '' s` is given by `measurable_image_of_fderivWithin`. -/
/-
**MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：lintegral_abs_det_fderiv_eq_addHaar_image (hs : MeasurableSet s) (hf' : fo
rall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : (∫⁻ x in s, ENNR
eal.ofReal |(f' x).det| ∂μ) = μ (f '' s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image`：lintegral_abs_d
et_fderiv_le_addHaar_image (hs : MeasurableSet s) (hf' : forall x in s, HasFDeri
vWithinAt f (f' x) s x) (hf : InjOn f s) : (∫…
· 使用定理 `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv`：addHaar_image_l
e_lintegral_abs_det_fderiv (hs : MeasurableSet s) (hf' : forall x in s, HasFDeri
vWithinAt f (f' x) s x) : μ (f '' s) <= ∫⁻ x …

--- 原说明 ---
Change of variable formula for differentiable functions, set version: if a funct
ion `f` is
injective and differentiable on a measurable set `s`, then the measure of `f '' 
s` is given by the
integral of `|(f' x).det|` on `s`.
Note that the measurability of `f '' s` is given by `measurable_image_of_fderivW
ithin`.
-/
theorem lintegral_abs_det_fderiv_eq_addHaar_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' s) :=
  le_antisymm (lintegral_abs_det_fderiv_le_addHaar_image μ hs hf' hf)
    (addHaar_image_le_lintegral_abs_det_fderiv μ hs hf')

/-- Change of variable formula for differentiable functions, set version: if a function `f` is
injective and differentiable on a null measurable set `s`, then the measure of `f '' s` is given
by the integral of `|(f' x).det|` on `s`.
Note that the null-measurability of `f '' s` is given by `nullMeasurable_image_of_fderivWithin`. -/
/-
**MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：lintegral_abs_det_fderiv_eq_addHaar_image (hs : MeasurableSet s) (hf' : fo
rall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : (∫⁻ x in s, ENNR
eal.ofReal |(f' x).det| ∂μ) = μ (f '' s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image`：lintegral_abs_d
et_fderiv_le_addHaar_image (hs : MeasurableSet s) (hf' : forall x in s, HasFDeri
vWithinAt f (f' x) s x) (hf : InjOn f s) : (∫…
· 使用定理 `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv`：addHaar_image_l
e_lintegral_abs_det_fderiv (hs : MeasurableSet s) (hf' : forall x in s, HasFDeri
vWithinAt f (f' x) s x) : μ (f '' s) <= ∫⁻ x …

--- 原说明 ---
Change of variable formula for differentiable functions, set version: if a funct
ion `f` is
injective and differentiable on a null measurable set `s`, then the measure of `
f '' s` is given
by the integral of `|(f' x).det|` on `s`.
Note that the null-measurability of `f '' s` is given by `nullMeasurable_image_o
f_fderivWithin`.
-/
theorem lintegral_abs_det_fderiv_eq_addHaar_image₀ (hs : NullMeasurableSet s μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' s) := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : μ (f '' s) = μ (f '' t) := by
    apply measure_congr
    have : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this, image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      (fun x hx ↦ ?_) (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  have B : (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ)
      = (∫⁻ x in t, ENNReal.ofReal |(f' x).det| ∂μ) :=
    setLIntegral_congr t_eq_s.symm
  rw [A, B, lintegral_abs_det_fderiv_eq_addHaar_image _ ht _ (hf.mono ts)]
  intro x hx
  exact (hf' x (ts hx)).mono ts

/-- Change of variable formula for differentiable functions, set version: if a function `f` is
injective and differentiable on a null measurable set `s`, then the pushforward of the measure with
density `|(f' x).det|` on `s` is the Lebesgue measure on the image set. -/
/-
**MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：map_withDensity_abs_det_fderiv_eq_addHaar (hs : NullMeasurableSet s μ) (hf
' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : Measure.ma
p f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) = μ.restri
ct (f '' s)
参数：hs : NullMeasurableSet s μ；hf' : forall x in s, HasFDerivWithinAt f (f' x) s 
x；hf : InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.aemeasurable₀`：ContinuousOn.aemeasurable₀ [TopologicalSpace
 α] [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [BorelSpac
e β] {f : α -> β…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `DifferentiableWithinAt.continuousWithinAt`：DifferentiableWithinAt.contin
uousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `AEMeasurable.mono_ac`：mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AE
Measurable f μ
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `AEMeasurable.nullMeasurableSet_preimage`：∀ {α : Type u_1} {β : Type u_2}
 {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}
   {f : α → β} {s : Set β}, A…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasureTheory.withDensity_apply₀`：withDensity_apply₀ (f : α -> Real>=0∞)
 {s : Set α} (hs : NullMeasurableSet s μ) : μ.withDensity f s = ∫⁻ a in s, f a ∂
μ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.restrict_restrict₀`：restrict_restrict₀ (hs : NullM
easurableSet s (μ.restrict t)) : (μ.restrict t).restrict s = μ.restrict (s inter
 t)
· 使用定理 `MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image₀`：lintegral_abs_
det_fderiv_eq_addHaar_image₀ (hs : NullMeasurableSet s μ) (hf' : forall x in s, 
HasFDerivWithinAt f (f' x) s x) (hf : InjOn f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.nullMeasurableSet_restrict`：nullMeasurableSet_restrict (hs
 : NullMeasurableSet s μ) {t : Set α} : NullMeasurableSet t (μ.restrict s) ↔ Nul
lMeasurableSet (t inter s) μ
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s

--- 原说明 ---
Change of variable formula for differentiable functions, set version: if a funct
ion `f` is
injective and differentiable on a null measurable set `s`, then the pushforward 
of the measure with
density `|(f' x).det|` on `s` is the Lebesgue measure on the image set.
-/
theorem map_withDensity_abs_det_fderiv_eq_addHaar (hs : NullMeasurableSet s μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) =
      μ.restrict (f '' s) := by
  have h'f : AEMeasurable f (μ.restrict s) := by
    apply ContinuousOn.aemeasurable₀ (fun x hx ↦ ?_) hs
    exact (hf' x hx).differentiableWithinAt.continuousWithinAt
  have h''f : AEMeasurable f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) := by
    apply h'f.mono_ac
    exact withDensity_absolutelyContinuous _ _
  apply Measure.ext fun t ht => ?_
  have h't : NullMeasurableSet (f ⁻¹' t) (μ.restrict s) := h'f.nullMeasurableSet_preimage ht
  rw [map_apply_of_aemeasurable h''f ht, withDensity_apply₀ _ h't,
    Measure.restrict_apply ht, restrict_restrict₀ h't,
    lintegral_abs_det_fderiv_eq_addHaar_image₀ μ ((nullMeasurableSet_restrict hs).1 h't)
      (fun x hx => (hf' x hx.2).mono inter_subset_right) (hf.mono inter_subset_right),
    image_preimage_inter]

/-- Change of variable formula for differentiable functions, set version: if a function `f` is
injective and differentiable on a measurable set `s`, then the pushforward of the measure with
density `|(f' x).det|` on `s` is the Lebesgue measure on the image set. This version is expressed
in terms of the restricted function `s.domRestrict f`.
For a version for the original function, see `map_withDensity_abs_det_fderiv_eq_addHaar`.
-/
/-
**MeasureTheory.restrict_map_withDensity_abs_det_fderiv_eq_addHaar** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：restrict_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s) 
(hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : Measure
.map (s.domRestrict f) (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x)
.det|)) = μ.restrict (f '' s)
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.measurable_piecewise`：ContinuousOn.measurable_piecewise {f 
g : α -> γ} {s : Set α} [forall j : α, Decidable (j in s)] (hf : ContinuousOn f 
s) (hg : ContinuousOn g…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `Set.piecewise_eqOn`：piecewise_eqOn (f g : α -> β) : EqOn (s.piecewise f 
g) f s
· 使用定理 `HasFDerivWithinAt.congr`：HasFDerivWithinAt.congr (h : HasFDerivWithinAt 
f f' s x) (hs : EqOn f₁ f s) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用定理 `MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar`：map_withDensity
_abs_det_fderiv_eq_addHaar (hs : NullMeasurableSet s μ) (hf' : forall x in s, Ha
sFDerivWithinAt f (f' x) s x) (hf : InjOn f s…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.InjOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α 
→ β}, Set.InjOn f₁ s → Set.EqOn f₁ f₂ s → Set.InjOn f₂ s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s

--- 原说明 ---
Change of variable formula for differentiable functions, set version: if a funct
ion `f` is
injective and differentiable on a measurable set `s`, then the pushforward of th
e measure with
density `|(f' x).det|` on `s` is the Lebesgue measure on the image set. This ver
sion is expressed
in terms of the restricted function `s.domRestrict f`.
For a version for the original function, see `map_withDensity_abs_det_fderiv_eq_
addHaar`.
-/
theorem restrict_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map (s.domRestrict f) (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (f '' s) := by
  obtain ⟨u, u_meas, uf⟩ : ∃ u, Measurable u ∧ EqOn u f s := by
    classical
    refine ⟨piecewise s f 0, ?_, piecewise_eqOn _ _ _⟩
    refine ContinuousOn.measurable_piecewise ?_ continuous_zero.continuousOn hs
    have : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
    exact this.continuousOn
  have u' : ∀ x ∈ s, HasFDerivWithinAt u (f' x) s x := fun x hx =>
    (hf' x hx).congr (fun y hy => uf hy) (uf hx)
  set F : s → E := u ∘ (↑) with hF
  have A :
    Measure.map F (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (u '' s) := by
    rw [hF, ← Measure.map_map u_meas measurable_subtype_coe, map_comap_subtype_coe hs,
      restrict_withDensity hs]
    exact map_withDensity_abs_det_fderiv_eq_addHaar μ hs.nullMeasurableSet u' (hf.congr uf.symm)
  rw [uf.image_eq] at A
  have : F = s.domRestrict f := by
    ext x
    exact uf x.2
  rwa [this] at A

/-! ### Change of variable formulas in integrals -/


/-- Change of variable formula for differentiable functions: if a function `f` is
injective and differentiable on a measurable set `s`, then the Lebesgue integral of a function
`g : E → ℝ≥0∞` on `f '' s` coincides with the integral of `|(f' x).det| * g ∘ f` on `s`.
Note that the measurability of `f '' s` is given by `measurable_image_of_fderivWithin`. -/
/-
**MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s) (hf
' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E -> Re
al>=0∞) : ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f
 x) ∂μ
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s；g : E -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_map_withDensity_abs_det_fderiv_eq_addHaar`：restri
ct_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s) (hf' : foral
l x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn …
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
· 使用定理 `MeasureTheory.measurableEmbedding_of_fderivWithin`：measurableEmbedding_o
f_fderivWithin (hs : MeasurableSet s) (hf' : forall x in s, HasFDerivWithinAt f 
(f' x) s x) (hf : InjOn f s) : Measurab…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul_non_measurabl
e₀`：setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ (μ : Measure α)
 {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasurable f (μ.restric…
· 使用定理 `MeasureTheory.aemeasurable_ofReal_abs_det_fderivWithin`：aemeasurable_ofR
eal_abs_det_fderivWithin (hs : MeasurableSet s) (hf' : forall x in s, HasFDerivW
ithinAt f (f' x) s x) : AEMeasurable (fun x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Change of variable formula for differentiable functions: if a function `f` is
injective and differentiable on a measurable set `s`, then the Lebesgue integral
 of a function
`g : E → ℝ≥0∞` on `f '' s` coincides with the integral of `|(f' x).det| * g ∘ f`
 on `s`.
Note that the measurability of `f '' s` is given by `measurable_image_of_fderivW
ithin`.
-/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).lintegral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map, map_comap_subtype_coe hs,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · simp only [Pi.mul_apply]
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact aemeasurable_ofReal_abs_det_fderivWithin μ hs hf'

/-- Integrability in the change of variable formula for differentiable functions: if a
function `f` is injective and differentiable on a measurable set `s`, then a function
`g : E → F` is integrable on `f '' s` if and only if `|(f' x).det| • g ∘ f` is
integrable on `s`. -/
/-
**MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (hs : MeasurableSe
t s) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g :
 E -> F) : IntegrableOn g (f '' s) μ ↔ IntegrableOn (fun x => |(f' x).det| • g (
f x)) s μ
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s；g : E -> F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_map_withDensity_abs_det_fderiv_eq_addHaar`：restri
ct_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s) (hf' : foral
l x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn …
· 使用定理 `MeasurableEmbedding.integrable_map_iff`：∀ {α : Type u_1} {δ : Type u_4} 
{ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : M
easurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.measurableEmbedding_of_fderivWithin`：measurableEmbedding_o
f_fderivWithin (hs : MeasurableSet s) (hf' : forall x in s, HasFDerivWithinAt f 
(f' x) s x) (hf : InjOn f s) : Measurab…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_coe_smul₀`：integrabl
e_withDensity_iff_integrable_coe_smul₀ {f : α -> Real>=0} (hf : AEMeasurable f μ
) {g : α -> E} : Integrable g (μ.withDensity fun x …
· 使用定理 `MeasureTheory.aemeasurable_toNNReal_abs_det_fderivWithin`：aemeasurable_t
oNNReal_abs_det_fderivWithin (hs : MeasurableSet s) (hf' : forall x in s, HasFDe
rivWithinAt f (f' x) s x) : AEMeasurable (fun …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Integrability in the change of variable formula for differentiable functions: if
 a
function `f` is injective and differentiable on a measurable set `s`, then a fun
ction
`g : E → F` is integrable on `f '' s` if and only if `|(f' x).det| • g ∘ f` is
integrable on `s`.
-/
theorem integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    IntegrableOn g (f '' s) μ ↔ IntegrableOn (fun x => |(f' x).det| • g (f x)) s μ := by
  rw [IntegrableOn, ← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).integrable_map_iff]
  simp only [Set.domRestrict_eq, ← Function.comp_assoc, ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_iff, map_comap_subtype_coe hs,
    restrict_withDensity hs, integrable_withDensity_iff_integrable_coe_smul₀]
  · simp_rw [IntegrableOn, Real.coe_toNNReal _ (abs_nonneg _), Function.comp_apply]
  · exact aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf'

/-- Change of variable formula for differentiable functions: if a function `f` is
injective and differentiable on a measurable set `s`, then the Bochner integral of a function
`g : E → F` on `f '' s` coincides with the integral of `|(f' x).det| • g ∘ f` on `s`. -/
/-
**MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_image_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s) (hf'
 : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E -> F) 
: ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ
参数：hs : MeasurableSet s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hf :
 InjOn f s；g : E -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_map_withDensity_abs_det_fderiv_eq_addHaar`：restri
ct_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s) (hf' : foral
l x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn …
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasureTheory.measurableEmbedding_of_fderivWithin`：measurableEmbedding_o
f_fderivWithin (hs : MeasurableSet s) (hf' : forall x in s, HasFDerivWithinAt f 
(f' x) s x) (hf : InjOn f s) : Measurab…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `setIntegral_withDensity_eq_setIntegral_smul₀`：setIntegral_withDensity_eq
_setIntegral_smul₀ {f : X -> Real>=0} {s : Set X} (hf : AEMeasurable f (μ.restri
ct s)) (g : X -> E) (hs : Measurab…
· 使用定理 `MeasureTheory.aemeasurable_toNNReal_abs_det_fderivWithin`：aemeasurable_t
oNNReal_abs_det_fderivWithin (hs : MeasurableSet s) (hf' : forall x in s, HasFDe
rivWithinAt f (f' x) s x) : AEMeasurable (fun …
· 使用定理 `NNReal.smul_def`：smul_def {M : Type*} [SMul Real M] (c : Real>=0) (x : M
) : c • x = (c : Real) • x
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
Change of variable formula for differentiable functions: if a function `f` is
injective and differentiable on a measurable set `s`, then the Bochner integral 
of a function
`g : E → F` on `f '' s` coincides with the integral of `|(f' x).det| • g ∘ f` on
 `s`.
-/
theorem integral_image_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).integral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map, map_comap_subtype_coe hs,
    setIntegral_withDensity_eq_setIntegral_smul₀
      (aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf') _ hs]
  congr with x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (abs_nonneg (f' x).det)]
/-
**MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_target_eq_integral_abs_det_fderiv_smul {f : OpenPartialHomeomorph
 E E} (hf' : forall x in f.source, HasFDerivAt f (f' x) x) (g : E -> F) : ∫ x in
 f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ
参数：hf' : forall x in f.source, HasFDerivAt f (f' x) x；g : E -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`：integral_i
mage_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s) (hf' : forall x in s
, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s)…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
-/
theorem integral_target_eq_integral_abs_det_fderiv_smul {f : OpenPartialHomeomorph E E}
    (hf' : ∀ x ∈ f.source, HasFDerivAt f (f' x) x) (g : E → F) :
    ∫ x in f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ := by
  have : f '' f.source = f.target := PartialEquiv.image_source_eq_target f.toPartialEquiv
  rw [← this]
  apply integral_image_eq_integral_abs_det_fderiv_smul μ f.open_source.measurableSet _ f.injOn
  intro x hx
  exact (hf' x hx).hasFDerivWithinAt

section withDensity

/-
**MeasureTheory._root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_int
egral_abs_det_fderiv_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul
    (hs : MeasurableSet s) (hf : MeasurableEmbedding f)
    {g : E → ℝ} (hg : ∀ᵐ x ∂μ, x ∈ f '' s → 0 ≤ g x) (hg_int : IntegrableOn g (f '' s) μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |(f' x).det| * g (f x) ∂μ) := by
  rw [Measure.comap_apply f hf.injective (fun t ht ↦ hf.measurableSet_image' ht) _ hs,
    withDensity_apply _ (hf.measurableSet_image' hs),
    ← ofReal_integral_eq_lintegral_ofReal hg_int
      ((ae_restrict_iff' (hf.measurableSet_image' hs)).mpr hg),
    integral_image_eq_integral_abs_det_fderiv_smul μ hs hf' hf.injective.injOn]
  simp_rw [smul_eq_mul]
/-
**MeasureTheory._root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_inte
gral_abs_det_fderiv_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul
    (hs : MeasurableSet s) (f : E ≃ᵐ E)
    {g : E → ℝ} (hg : ∀ᵐ x ∂μ, x ∈ f '' s → 0 ≤ g x) (hg_int : IntegrableOn g (f '' s) μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |(f' x).det| * g (f x) ∂μ) := by
  rw [MeasurableEquiv.map_symm,
    MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul μ hs
      f.measurableEmbedding hg hg_int hf']

end withDensity

end MeasureTheory

