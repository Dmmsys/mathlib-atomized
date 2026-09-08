/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `Convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map. This lemma and its versions are formulated using `RCLike`,
  so they work both for real and complex derivatives.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `‖f x‖ ≤ B x` from upper estimates on `f'` or `‖f'‖`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `‖f x‖ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `‖f x - f a‖ ≤ C * ‖x - a‖`; several versions deal with
  right derivative and derivative within `[a, b]` (`HasDerivWithinAt` or `derivWithin`).

* `Convex.is_const_of_fderivWithin_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` : a C^1 function over the reals is
  strictly differentiable. (This is a corollary of the mean value inequality.)
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open Metric Set Asymptotics ContinuousLinearMap Filter

open scoped Topology NNReal

/-! ### One-dimensional fencing inequalities -/


/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
/-
**image_le_of_liminf_slope_right_lt_deriv_boundary'** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : Real -> Real} {a
 b : Real} (hf : ContinuousOn f (Icc a b)) -- `hf'` actually says `liminf (f z -
 f x) / (z - x) ≤ f' x` (hf' : forall x in Ico a b, forall r, f' x < r -> exists
ᶠ z in 𝓝[>] x, slope f x z < r) {B B' : Real -> Real} (ha : f a <= B a) (hB : Co
ntinuousOn B (Icc a b)) (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (I
ci x) x) (bound : forall x in Ico a b, f x = B x -> f' x < B' x) : forall ⦃x⦄, x
 in Icc a b -> f x <= B x
参数：hf : ContinuousOn f (Icc a b)；f z - f x；z - x；hf' : forall x in Ico a b, fora
ll r, f' x < r -> existsᶠ z in 𝓝[>] x, slope f x z < r；ha : f a <= B a；hB : Cont
inuousOn B (Icc a b)；hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x
) x；bound : forall x in Ico a b, f x = B x -> f' x < B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ContinuousOn.preimage_isClosed_of_isClosed`：ContinuousOn.preimage_isClos
ed_of_isClosed {t : Set β} (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClo
sed t) : IsClosed (s inter f ⁻¹'…
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `OrderClosedTopology.isClosed_le'`：∀ {α : Type u_1} {inst : TopologicalSp
ace α} {inst_1 : Preorder α} [self : OrderClosedTopology α],   IsClosed {p | p.1
 ≤ p.2}
· 使用定理 `IsClosed.Icc_subset_of_forall_exists_gt`：IsClosed.Icc_subset_of_forall_e
xists_gt {a b : α} {s : Set α} (hs : IsClosed (s inter Icc a b)) (ha : a in s) (
hgt : forall x in s inter Ico…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
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
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `nhdsWithin_le_of_mem`：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s 
in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a
· 使用定理 `Icc_mem_nhdsGT_of_mem`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : LinearOrder α] [ClosedIciTopology α] {a b c : α},   b ∈ Set.Ico c a → Set.Ic
c c a ∈ nhd…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the derivat
ive.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`.
-/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  change Icc a b ⊆ { x | f x ≤ B x }
  set s := { x | f x ≤ B x } ∩ Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prodMk hB
  have : IsClosed s := by
    simp only [s, inter_comm]
    exact A.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  apply this.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxB : f x ≤ B x, xab⟩ y hy
  rcases hxB.lt_or_eq with hxB | hxB
  · -- If `f x < B x`, then all we need is continuity of both sides
    refine nonempty_of_mem (inter_mem ?_ (Ioc_mem_nhdsGT hy))
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x :=
      A x (Ico_subset_Icc_self xab) (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hxB)
    have : ∀ᶠ x in 𝓝[>] x, f x < B x := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) this
    exact this.mono fun y => le_of_lt
  · rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩
    specialize hf' x xab r hfr
    have HB : ∀ᶠ z in 𝓝[>] x, r < slope B x z :=
      (hasDerivWithinAt_iff_tendsto_slope' <| lt_irrefl x).1 (hB' x xab).Ioi_of_Ici
        (Ioi_mem_nhds hrB)
    obtain ⟨z, hfz, hzB, hz⟩ : ∃ z, slope f x z < r ∧ r < slope B x z ∧ z ∈ Ioc x y :=
      hf'.and_eventually (HB.and (Ioc_mem_nhdsGT hy)) |>.exists
    refine ⟨z, ?_, hz⟩
    have := (hfz.trans hzB).le
    rwa [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right (sub_pos.2 hz.1), hxB,
      sub_le_sub_iff_right] at this

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
/-
**image_le_of_liminf_slope_right_lt_deriv_boundary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : Real -> Real} {a 
b : Real} (hf : ContinuousOn f (Icc a b)) -- `hf'` actually says `liminf (f z - 
f x) / (z - x) ≤ f' x` (hf' : forall x in Ico a b, forall r, f' x < r -> existsᶠ
 z in 𝓝[>] x, slope f x z < r) {B B' : Real -> Real} (ha : f a <= B a) (hB : for
all x, HasDerivAt B (B' x) x) (bound : forall x in Ico a b, f x = B x -> f' x < 
B' x) : forall ⦃x⦄, x in Icc a b -> f x <= B x
参数：hf : ContinuousOn f (Icc a b)；f z - f x；z - x；hf' : forall x in Ico a b, fora
ll r, f' x < r -> existsᶠ z in 𝓝[>] x, slope f x z < r；ha : f a <= B a；hB : fora
ll x, HasDerivAt B (B' x) x；bound : forall x in Ico a b, f x = B x -> f' x < B' 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_le_of_liminf_slope_right_lt_deriv_boundary'`：image_le_of_liminf_sl
ope_right_lt_deriv_boundary' {f f' : Real -> Real} {a b : Real} (hf : Continuous
On f (Icc a b)) -- `hf'` actually says …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the derivat
ive.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`.
-/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
/-
**image_le_of_liminf_slope_right_le_deriv_boundary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_le_of_liminf_slope_right_le_deriv_boundary {f : Real -> Real} {a b :
 Real} (hf : ContinuousOn f (Icc a b)) {B B' : Real -> Real} (ha : f a <= B a) (
hB : ContinuousOn B (Icc a b)) (hB' : forall x in Ico a b, HasDerivWithinAt B (B
' x) (Ici x) x) -- `bound` actually says `liminf (f z - f x) / (z - x) ≤ B' x` (
bound : forall x in Ico a b, forall r, B' x < r -> existsᶠ z in 𝓝[>] x, slope f 
x z < r) : forall ⦃x⦄, x in Icc a b -> f x <= B x
参数：hf : ContinuousOn f (Icc a b)；ha : f a <= B a；hB : ContinuousOn B (Icc a b)；h
B' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x；f z - f x；z - x；bo
und : forall x in Ico a b, forall r, B' x < r -> existsᶠ z in 𝓝[>] x, slope f x 
z < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_le_of_liminf_slope_right_lt_deriv_boundary'`：image_le_of_liminf_sl
ope_right_lt_deriv_boundary' {f f' : Real -> Real} {a b : Real} (hf : Continuous
On f (Icc a b)) -- `hf'` actually says …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ContinuousOn.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousOn.mul`：ContinuousOn.mul (hf : ContinuousOn f s) (hg : Continu
ousOn g s) : ContinuousOn (f * g) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `HasDerivWithinAt.add`：HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s
 x) (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f + g) (f' + g') s x
· 使用定理 `HasDerivWithinAt.const_mul`：HasDerivWithinAt.const_mul (c : 𝔸) (hd : Has
DerivWithinAt d d' s x) : HasDerivWithinAt (fun y => c * d y) (c * d') s x
· 使用定理 `HasDerivWithinAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{f : 𝕜 → F} {f' …
· 使用定理 `hasDerivWithinAt_id`：hasDerivWithinAt_id : HasDerivWithinAt id 1 s x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_add_iff_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 :
 LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b : α},   a < a + b ↔
 0 < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousWithinAt.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace 
M] [inst_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : Topol
ogicalSpace X] {f …
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the derivat
ive.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`.
-/
theorem image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    -- `bound` actually says `liminf (f z - f x) / (z - x) ≤ B' x`
    (bound : ∀ x ∈ Ico a b, ∀ r, B' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  have Hr : ∀ x ∈ Icc a b, ∀ r > 0, f x ≤ B x + r * (x - a) := fun x hx r hr => by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zero]
    · exact hB.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro x hx
      exact (hB' x hx).add (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul r)
    · intro x _ _
      rw [mul_one]
      exact (lt_add_iff_pos_right _).2 hr
    exact hx
  intro x hx
  have : ContinuousWithinAt (fun r => B x + r * (x - a)) (Ioi 0) 0 := by fun_prop
  convert! continuousWithinAt_const.closure_le _ this (Hr x hx) using 1 <;> simp

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
/-
**image_le_of_deriv_right_lt_deriv_boundary'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_le_of_deriv_right_lt_deriv_boundary' {f f' : Real -> Real} {a b : Re
al} (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt
 f (f' x) (Ici x) x) {B B' : Real -> Real} (ha : f a <= B a) (hB : ContinuousOn 
B (Icc a b)) (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x) (b
ound : forall x in Ico a b, f x = B x -> f' x < B' x) : forall ⦃x⦄, x in Icc a b
 -> f x <= B x
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : f a <= B a；hB : ContinuousOn B (Icc a b)；hB' : forall x in 
Ico a b, HasDerivWithinAt B (B' x) (Ici x) x；bound : forall x in Ico a b, f x = 
B x -> f' x < B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_le_of_liminf_slope_right_lt_deriv_boundary'`：image_le_of_liminf_sl
ope_right_lt_deriv_boundary' {f f' : Real -> Real} {a b : Real} (hf : Continuous
On f (Icc a b)) -- `hf'` actually says …
· 使用定理 `HasDerivWithinAt.liminf_right_slope_le`：HasDerivWithinAt.liminf_right_sl
ope_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : f' < r) : existsᶠ z in 𝓝[>] 
x, slope f x z < r

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the derivat
ive.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`.
-/
theorem image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
/-
**image_le_of_deriv_right_lt_deriv_boundary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_le_of_deriv_right_lt_deriv_boundary {f f' : Real -> Real} {a b : Rea
l} (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt 
f (f' x) (Ici x) x) {B B' : Real -> Real} (ha : f a <= B a) (hB : forall x, HasD
erivAt B (B' x) x) (bound : forall x in Ico a b, f x = B x -> f' x < B' x) : for
all ⦃x⦄, x in Icc a b -> f x <= B x
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : f a <= B a；hB : forall x, HasDerivAt B (B' x) x；bound : for
all x in Ico a b, f x = B x -> f' x < B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_le_of_deriv_right_lt_deriv_boundary'`：image_le_of_deriv_right_lt_d
eriv_boundary' {f f' : Real -> Real} {a b : Real} (hf : ContinuousOn f (Icc a b)
) (hf' : forall x in Ico a b, Ha…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the derivat
ive.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`.
-/
theorem image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
/-
**image_le_of_deriv_right_le_deriv_boundary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_le_of_deriv_right_le_deriv_boundary {f f' : Real -> Real} {a b : Rea
l} (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt 
f (f' x) (Ici x) x) {B B' : Real -> Real} (ha : f a <= B a) (hB : ContinuousOn B
 (Icc a b)) (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x) (bo
und : forall x in Ico a b, f' x <= B' x) : forall ⦃x⦄, x in Icc a b -> f x <= B 
x
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : f a <= B a；hB : ContinuousOn B (Icc a b)；hB' : forall x in 
Ico a b, HasDerivWithinAt B (B' x) (Ici x) x；bound : forall x in Ico a b, f' x <
= B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_le_of_liminf_slope_right_le_deriv_boundary`：image_le_of_liminf_slo
pe_right_le_deriv_boundary {f : Real -> Real} {a b : Real} (hf : ContinuousOn f 
(Icc a b)) {B B' : Real -> Real} (ha :…
· 使用定理 `HasDerivWithinAt.liminf_right_slope_le`：HasDerivWithinAt.liminf_right_sl
ope_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : f' < r) : existsᶠ z in 𝓝[>] 
x, slope f x z < r
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the derivat
ive.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`.
-/
theorem image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f' x ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' fun x hx _ hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/


section

variable {f : ℝ → E} {a b : ℝ}

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(‖f z‖ - ‖f x‖) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. -/
/-
**image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*} [No
rmedAddCommGroup E] {f : Real -> E} {f' : Real -> Real} (hf : ContinuousOn f (Ic
c a b)) -- `hf'` actually says `liminf (‖f z‖ - ‖f x‖) / (z - x) ≤ f' x` (hf' : 
forall x in Ico a b, forall r, f' x < r -> existsᶠ z in 𝓝[>] x, slope (norm ∘ f)
 x z < r) {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : ContinuousOn B (Icc a 
b)) (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x) (bound : fo
rall x in Ico a b, ‖f x‖ =
参数：hf : ContinuousOn f (Icc a b)；‖f z‖ - ‖f x‖；z - x；hf' : forall x in Ico a b, 
forall r, f' x < r -> existsᶠ z in 𝓝[>] x, slope (norm ∘ f) x z < r；ha : ‖f a‖ <
= B a；hB : ContinuousOn B (Icc a b)；hB' : forall x in Ico a b, HasDerivWithinAt 
B (B' x) (Ici x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_le_of_liminf_slope_right_lt_deriv_boundary'`：image_le_of_liminf_sl
ope_right_lt_deriv_boundary' {f f' : Real -> Real} {a b : Real} (hf : Continuous
On f (Icc a b)) -- `hf'` actually says …
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the derivat
ive.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(‖f z‖ - ‖f x‖) / (z -
 x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`.
-/
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {f' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (‖f z‖ - ‖f x‖) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope (norm ∘ f) x z < r)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuousOn hf) hf' ha hB
    hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
/-
**image_norm_le_of_norm_deriv_right_lt_deriv_boundary'** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : Real -> E} (hf 
: ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x
) (Ici x) x) {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : ContinuousOn B (Icc
 a b)) (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x) (bound :
 forall x in Ico a b, ‖f x‖ = B x -> ‖f' x‖ < B' x) : forall ⦃x⦄, x in Icc a b -
> ‖f x‖ <= B x
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : ‖f a‖ <= B a；hB : ContinuousOn B (Icc a b)；hB' : forall x i
n Ico a b, HasDerivWithinAt B (B' x) (Ici x) x；bound : forall x in Ico a b, ‖f x
‖ = B x -> ‖f' x‖ < B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary`：image_norm_l
e_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*} [NormedAddCommGroup E
] {f : Real -> E} {f' : Real -> Real} (hf : Cont…
· 使用定理 `HasDerivWithinAt.liminf_right_slope_norm_le`：HasDerivWithinAt.liminf_rig
ht_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : ‖f'‖ < r) : exists
ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖…

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the norm of
 the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point o
f `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the a
ssumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
/-
**image_norm_le_of_norm_deriv_right_lt_deriv_boundary** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : Real -> E} (hf :
 ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x)
 (Ici x) x) {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : forall x, HasDerivAt
 B (B' x) x) (bound : forall x in Ico a b, ‖f x‖ = B x -> ‖f' x‖ < B' x) : foral
l ⦃x⦄, x in Icc a b -> ‖f x‖ <= B x
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : ‖f a‖ <= B a；hB : forall x, HasDerivAt B (B' x) x；bound : f
orall x in Ico a b, ‖f x‖ = B x -> ‖f' x‖ < B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_norm_le_of_norm_deriv_right_lt_deriv_boundary'`：image_norm_le_of_n
orm_deriv_right_lt_deriv_boundary' {f' : Real -> E} (hf : ContinuousOn f (Icc a 
b)) (hf' : forall x in Ico a b, HasDerivWi…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the norm of
 the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the a
ssumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
/-
**image_norm_le_of_norm_deriv_right_le_deriv_boundary'** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : Real -> E} (hf 
: ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x
) (Ici x) x) {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : ContinuousOn B (Icc
 a b)) (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x) (bound :
 forall x in Ico a b, ‖f' x‖ <= B' x) : forall ⦃x⦄, x in Icc a b -> ‖f x‖ <= B x
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : ‖f a‖ <= B a；hB : ContinuousOn B (Icc a b)；hB' : forall x i
n Ico a b, HasDerivWithinAt B (B' x) (Ici x) x；bound : forall x in Ico a b, ‖f' 
x‖ <= B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_le_of_liminf_slope_right_le_deriv_boundary`：image_le_of_liminf_slo
pe_right_le_deriv_boundary {f : Real -> Real} {a b : Real} (hf : ContinuousOn f 
(Icc a b)) {B B' : Real -> Real} (ha :…
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `HasDerivWithinAt.liminf_right_slope_norm_le`：HasDerivWithinAt.liminf_rig
ht_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : ‖f'‖ < r) : exists
ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the norm of
 the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point o
f `[a, b)`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the a
ssumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuousOn hf) ha hB hB'
    fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le ((bound x hx).trans_lt hr)

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
/-
**image_norm_le_of_norm_deriv_right_le_deriv_boundary** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : Real -> E} (hf :
 ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x)
 (Ici x) x) {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : forall x, HasDerivAt
 B (B' x) x) (bound : forall x in Ico a b, ‖f' x‖ <= B' x) : forall ⦃x⦄, x in Ic
c a b -> ‖f x‖ <= B x
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : ‖f a‖ <= B a；hB : forall x, HasDerivAt B (B' x) x；bound : f
orall x in Ico a b, ‖f' x‖ <= B' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `image_norm_le_of_norm_deriv_right_le_deriv_boundary'`：image_norm_le_of_n
orm_deriv_right_le_deriv_boundary' {f' : Real -> E} (hf : ContinuousOn f (Icc a 
b)) (hf' : forall x in Ico a b, HasDerivWi…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
General fencing theorem for continuous functions with an estimate on the norm of
 the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the a
ssumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `‖f x - f a‖ ≤ C * (x - a)`. -/
/-
**norm_image_sub_le_of_norm_deriv_right_le_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_image_sub_le_of_norm_deriv_right_le_segment {f' : Real -> E} {C : Rea
l} (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt 
f (f' x) (Ici x) x) (bound : forall x in Ico a b, ‖f' x‖ <= C) : forall x in Icc
 a b, ‖f x - f a‖ <= C * (x - a)
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；bound : forall x in Ico a b, ‖f' x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
· 使用定理 `HasDerivAt.sub`：HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f - g) (f' - g') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `image_norm_le_of_norm_deriv_right_le_deriv_boundary`：image_norm_le_of_no
rm_deriv_right_le_deriv_boundary {f' : Real -> E} (hf : ContinuousOn f (Icc a b)
) (hf' : forall x in Ico a b, HasDerivWit…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `‖f x - f a‖ ≤ C * (x - a)`.
-/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : ℝ → E} {C : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  let g x := f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub continuousOn_const
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simp [g, hf' x hx]
  let B x := C * (x - a)
  have hB : ∀ x, HasDerivAt B C x := by
    intro x
    simpa using! (hasDerivAt_const x C).mul ((hasDerivAt_id x).sub (hasDerivAt_const x a))
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound
  simp only [g, B]; rw [sub_self, norm_zero, sub_self, mul_zero]

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `HasDerivWithinAt`
version. -/
/-
**norm_image_sub_le_of_norm_deriv_le_segment'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_image_sub_le_of_norm_deriv_le_segment' {f' : Real -> E} {C : Real} (h
f : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) (bound : forall 
x in Ico a b, ‖f' x‖ <= C) : forall x in Icc a b, ‖f x - f a‖ <= C * (x - a)
参数：hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x；bound : foral
l x in Ico a b, ‖f' x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `norm_image_sub_le_of_norm_deriv_right_le_segment`：norm_image_sub_le_of_n
orm_deriv_right_le_segment {f' : Real -> E} {C : Real} (hf : ContinuousOn f (Icc
 a b)) (hf' : forall x in Ico a b, Has…
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Icc_mem_nhdsGE_of_mem`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : LinearOrder α] [ClosedIciTopology α] {a b c : α},   b ∈ Set.Ico c a → Set.Ic
c c a ∈ nhd…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `HasDerivWithinAt`
version.
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).continuousWithinAt)
      (fun x hx => ?_) bound
  exact (hf x <| Ico_subset_Icc_self hx).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `derivWithin`
version. -/
/-
**norm_image_sub_le_of_norm_deriv_le_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_image_sub_le_of_norm_deriv_le_segment {C : Real} (hf : Differentiable
On Real f (Icc a b)) (bound : forall x in Ico a b, ‖derivWithin f (Icc a b) x‖ <
= C) : forall x in Icc a b, ‖f x - f a‖ <= C * (x - a)
参数：hf : DifferentiableOn Real f (Icc a b)；bound : forall x in Ico a b, ‖derivWit
hin f (Icc a b) x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_image_sub_le_of_norm_deriv_le_segment'`：norm_image_sub_le_of_norm_d
eriv_le_segment' {f' : Real -> E} {C : Real} (hf : forall x in Icc a b, HasDeriv
WithinAt f (f' x) (Icc a b) x) (b…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `derivWithin`
version.
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : DifferentiableOn ℝ f (Icc a b))
    (bound : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ C) :
    ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' ?_ bound
  exact fun x hx => (hf x hx).hasDerivWithinAt

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `HasDerivWithinAt`
version. -/
/-
**norm_image_sub_le_of_norm_deriv_le_segment_01'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : Real -> E} {C : Real}
 (hf : forall x in Icc (0 : Real) 1, HasDerivWithinAt f (f' x) (Icc (0 : Real) 1
) x) (bound : forall x in Ico (0 : Real) 1, ‖f' x‖ <= C) : ‖f 1 - f 0‖ <= C
参数：hf : forall x in Icc (0 : Real) 1, HasDerivWithinAt f (f' x) (Icc (0 : Real) 
1) x；bound : forall x in Ico (0 : Real) 1, ‖f' x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_image_sub_le_of_norm_deriv_le_segment'`：norm_image_sub_le_of_norm_d
eriv_le_segment' {f' : Real -> E} {C : Real} (hf : forall x in Icc a b, HasDeriv
WithinAt f (f' x) (Icc a b) x) (b…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `HasDerivWithinAt`
version.
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) 1) x)
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖f' x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `derivWithin` version. -/
/-
**norm_image_sub_le_of_norm_deriv_le_segment_01** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_image_sub_le_of_norm_deriv_le_segment_01 {C : Real} (hf : Differentia
bleOn Real f (Icc (0 : Real) 1)) (bound : forall x in Ico (0 : Real) 1, ‖derivWi
thin f (Icc (0 : Real) 1) x‖ <= C) : ‖f 1 - f 0‖ <= C
参数：hf : DifferentiableOn Real f (Icc (0 : Real) 1)；bound : forall x in Ico (0 : 
Real) 1, ‖derivWithin f (Icc (0 : Real) 1) x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_image_sub_le_of_norm_deriv_le_segment`：norm_image_sub_le_of_norm_de
riv_le_segment {C : Real} (hf : DifferentiableOn Real f (Icc a b)) (bound : fora
ll x in Ico a b, ‖derivWithin f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `derivWithin` version.
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ}
    (hf : DifferentiableOn ℝ f (Icc (0 : ℝ) 1))
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖derivWithin f (Icc (0 : ℝ) 1) x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)
/-
**constant_of_has_deriv_right_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b)) (hderi
v : forall x in Ico a b, HasDerivWithinAt f 0 (Ici x) x) : forall x in Icc a b, 
f x = f a
参数：hcont : ContinuousOn f (Icc a b)；hderiv : forall x in Ico a b, HasDerivWithin
At f 0 (Ici x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `norm_image_sub_le_of_norm_deriv_right_le_segment`：norm_image_sub_le_of_n
orm_deriv_right_le_segment {f' : Real -> E} {C : Real} (hf : ContinuousOn f (Icc
 a b)) (hf' : forall x in Ico a b, Has…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt f 0 (Ici x) x) : ∀ x ∈ Icc a b, f x = f a := by
  have : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ 0 * (x - a) := fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv (fun _ _ => norm_zero.le) x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using this
/-
**constant_of_derivWithin_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constant_of_derivWithin_zero (hdiff : DifferentiableOn Real f (Icc a b)) (
hderiv : forall x in Ico a b, derivWithin f (Icc a b) x = 0) : forall x in Icc a
 b, f x = f a
参数：hdiff : DifferentiableOn Real f (Icc a b)；hderiv : forall x in Ico a b, deriv
Within f (Icc a b) x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `norm_image_sub_le_of_norm_deriv_le_segment`：norm_image_sub_le_of_norm_de
riv_le_segment {C : Real} (hf : DifferentiableOn Real f (Icc a b)) (bound : fora
ll x in Ico a b, ‖derivWithin f …
-/
theorem constant_of_derivWithin_zero (hdiff : DifferentiableOn ℝ f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, derivWithin f (Icc a b) x = 0) : ∀ x ∈ Icc a b, f x = f a := by
  have H : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ 0 := by
    simpa only [norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx

variable {f' g : ℝ → E}

/-- If two continuous functions on `[a, b]` have the same right derivative and are equal at `a`,
  then they are equal everywhere on `[a, b]`. -/
/-
**eq_of_has_deriv_right_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_has_deriv_right_eq (derivf : forall x in Ico a b, HasDerivWithinAt f
 (f' x) (Ici x) x) (derivg : forall x in Ico a b, HasDerivWithinAt g (f' x) (Ici
 x) x) (fcont : ContinuousOn f (Icc a b)) (gcont : ContinuousOn g (Icc a b)) (hi
 : f a = g a) : forall y in Icc a b, f y = g y
参数：derivf : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x；derivg : fo
rall x in Ico a b, HasDerivWithinAt g (f' x) (Ici x) x；fcont : ContinuousOn f (I
cc a b)；gcont : ContinuousOn g (Icc a b)；hi : f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `constant_of_has_deriv_right_zero`：constant_of_has_deriv_right_zero (hcon
t : ContinuousOn f (Icc a b)) (hderiv : forall x in Ico a b, HasDerivWithinAt f 
0 (Ici x) x) : forall …
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HasDerivWithinAt.sub`：HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s
 x) (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f - g) (f' - g') s x

--- 原说明 ---
If two continuous functions on `[a, b]` have the same right derivative and are e
qual at `a`,
  then they are equal everywhere on `[a, b]`.
-/
theorem eq_of_has_deriv_right_eq (derivf : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (derivg : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x) (fcont : ContinuousOn f (Icc a b))
    (gcont : ContinuousOn g (Icc a b)) (hi : f a = g a) : ∀ y ∈ Icc a b, f y = g y := by
  simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
    simpa only [sub_self] using! (derivf y hy).sub (derivg y hy)

/-- If two differentiable functions on `[a, b]` have the same derivative within `[a, b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`. -/
/-
**eq_of_derivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_derivWithin_eq (fdiff : DifferentiableOn Real f (Icc a b)) (gdiff : 
DifferentiableOn Real g (Icc a b)) (hderiv : EqOn (derivWithin f (Icc a b)) (der
ivWithin g (Icc a b)) (Ico a b)) (hi : f a = g a) : forall y in Icc a b, f y = g
 y
参数：fdiff : DifferentiableOn Real f (Icc a b)；gdiff : DifferentiableOn Real g (Ic
c a b)；hderiv : EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a 
b)；hi : f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `Set.mem_Icc_of_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ico b a → x ∈ Set.Icc b a
· 使用定理 `Icc_mem_nhdsGE_of_mem`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : LinearOrder α] [ClosedIciTopology α] {a b c : α},   b ∈ Set.Ico c a → Set.Ic
c c a ∈ nhd…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_of_has_deriv_right_eq`：eq_of_has_deriv_right_eq (derivf : forall x in
 Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (derivg : forall x in Ico a b, Ha
sDerivWithinAt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
If two differentiable functions on `[a, b]` have the same derivative within `[a,
 b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`.
-/
theorem eq_of_derivWithin_eq (fdiff : DifferentiableOn ℝ f (Icc a b))
    (gdiff : DifferentiableOn ℝ g (Icc a b))
    (hderiv : EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a b)) (hi : f a = g a) :
    ∀ y ∈ Icc a b, f y = g y := by
  have A : ∀ y ∈ Ico a b, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  have B : ∀ y ∈ Ico a b, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y := fun y hy =>
    (gdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  exact eq_of_has_deriv_right_eq A (fun y hy => (hderiv hy).symm ▸ B y hy) fdiff.continuousOn
    gdiff.continuousOn hi

end

/-!
### Vector-valued functions `f : E → G`

Theorems in this section work both for real and complex differentiable functions. We use assumptions
`[NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]` to
achieve this result. For the domain `E` we also assume `[NormedSpace ℝ E]` to have a notion
of a `Convex` set. -/

section

namespace Convex

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f g : E → G} {C : ℝ} {s : Set E} {x y : E} {f' g' : E → E →L[𝕜] G} {φ : E →L[𝕜] G}

/-
**Convex.** 是 Mathlib 中的一个实例，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : PathConnectedSpace 𝕜 := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `HasFDerivWithinAt`. -/
/-
**Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 
`Convex`。
形式化陈述：norm_image_sub_le_of_norm_hasFDerivWithin_le (hf : forall x in s, HasFDeri
vWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x‖ <= C) (hs : Convex Real s
) (xs : x in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖
参数：hf : forall x in s, HasFDerivWithinAt f (f' x) s x；bound : forall x in s, ‖f'
 x‖ <= C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.mapsTo_lineMap`：Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.comp_hasDerivWithinAt`：HasFDerivWithinAt.comp_hasDeriv
WithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x)) (hf : HasDerivWithinA
t f f' s x) (hst : MapsTo f s…
· 使用定理 `HasFDerivWithinAt.restrictScalars`：HasFDerivWithinAt.restrictScalars (h 
: HasFDerivWithinAt f f' s x) : HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x
· 使用定理 `AffineMap.hasDerivWithinAt_lineMap`：hasDerivWithinAt_lineMap : HasDerivW
ithinAt (lineMap a b) (b - a) s x
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `norm_image_sub_le_of_norm_deriv_le_segment_01'`：norm_image_sub_le_of_nor
m_deriv_le_segment_01' {f' : Real -> E} {C : Real} (hf : forall x in Icc (0 : Re
al) 1, HasDerivWithinAt f (f' x) (Ic…

--- 原说明 ---
The mean value theorem on a convex set: if the derivative of a function is bound
ed by `C`, then
the function is `C`-Lipschitz. Version with `HasFDerivWithinAt`.
-/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ G := .restrictScalars ℝ 𝕜 G
  /- By composition with `AffineMap.lineMap x y`, we reduce to a statement for functions defined
    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
    We just have to check the differentiability of the composition and bounds on its derivative,
    which is straightforward but tedious for lack of automation. -/
  set g := (AffineMap.lineMap x y : ℝ → E)
  have segm : MapsTo g (Icc 0 1 : Set ℝ) s := hs.mapsTo_lineMap xs ys
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t := fun t ht => by
    simpa using ((hf (g t) (segm ht)).restrictScalars ℝ).comp_hasDerivWithinAt _
      AffineMap.hasDerivWithinAt_lineMap segm
  have bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (g t) (y - x)‖ ≤ C * ‖y - x‖ := fun t ht =>
    le_of_opNorm_le _ (bound _ <| segm <| Ico_subset_Icc_self ht) _
  simpa [g] using norm_image_sub_le_of_norm_deriv_le_segment_01' hD bound

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `HasFDerivWithinAt` and
`LipschitzOnWith`. -/
/-
**Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 
`Convex`。
形式化陈述：lipschitzOnWith_of_nnnorm_hasFDerivWithin_le {C : Real>=0} (hf : forall x 
in s, HasFDerivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x‖₊ <= C) (hs 
: Convex Real s) : LipschitzOnWith C f s
参数：hf : forall x in s, HasFDerivWithinAt f (f' x) s x；bound : forall x in s, ‖f'
 x‖₊ <= C；hs : Convex Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lipschitzOnWith_iff_norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst :
 SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C 
: NNReal} {s : Set E}…
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`：norm_image_sub_le_o
f_norm_hasFDerivWithin_le (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (
bound : forall x in s, ‖f' x‖ <= C) (hs :…

--- 原说明 ---
The mean value theorem on a convex set: if the derivative of a function is bound
ed by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `HasFDerivWithinAt`
 and
`LipschitzOnWith`.
-/
theorem lipschitzOnWith_of_nnnorm_hasFDerivWithin_le {C : ℝ≥0}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C)
    (hs : Convex ℝ s) : LipschitzOnWith C f s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊`, `f` is
`K`-Lipschitz on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt` for a version that claims
existence of `K` instead of an explicit estimate. -/
/-
**Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt** 是
 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : 
Convex Real s) {f : E -> G} (hder : forallᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f'
 y) s y) (hcont : ContinuousWithinAt f' s x) (K : Real>=0) (hK : ‖f' x‖₊ < K) : 
exists t in 𝓝[s] x, LipschitzOnWith K f t
参数：hs : Convex Real s；hder : forallᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y
；hcont : ContinuousWithinAt f' s x；K : Real>=0；hK : ‖f' x‖₊ < K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `ContinuousWithinAt.nnnorm`：∀ {α : Type u_1} {E : Type u_4} [inst : Semin
ormedAddGroup E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α}   {a : α}
, ContinuousWit…
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`：lipschitzOnWith_of_
nnnorm_hasFDerivWithin_le {C : Real>=0} (hf : forall x in s, HasFDerivWithinAt f
 (f' x) s x) (bound : forall x in s, ‖f' …
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)

--- 原说明 ---
Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a 
function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Sup
pose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊
`, `f` is
`K`-Lipschitz on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt` for a version th
at claims
existence of `K` instead of an explicit estimate.
-/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : Convex ℝ s)
    {f : E → G} (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hcont : ContinuousWithinAt f' s x) (K : ℝ≥0) (hK : ‖f' x‖₊ < K) :
    ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨ε, ε0, hε⟩ : ∃ ε > 0,
      ball x ε ∩ s ⊆ { y | HasFDerivWithinAt f (f' y) s y ∧ ‖f' y‖₊ < K } :=
    mem_nhdsWithin_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine ⟨s ∩ ball x ε, inter_mem_nhdsWithin _ (ball_mem_nhds _ ε0), ?_⟩
  exact
    (hs.inter (convex_ball _ _)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun y hy => (hε hy).1.mono inter_subset_left) fun y hy => (hε hy).2.le

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊`, `f` is Lipschitz
on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt` for a version
with an explicit estimate on the Lipschitz constant. -/
/-
**Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt** 是 Mathlib 中的一个
定理，位于命名空间 `Convex`。
形式化陈述：exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex Real s
) {f : E -> G} (hder : forallᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y) (hco
nt : ContinuousWithinAt f' s x) : exists K, exists t in 𝓝[s] x, LipschitzOnWith 
K f t
参数：hs : Convex Real s；hder : forallᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y
；hcont : ContinuousWithinAt f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_
lt`：exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : Co
nvex Real s) {f : E -> G} (hder : forallᶠ y in 𝓝[s] x, HasFDeriv…
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal

--- 原说明 ---
Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a 
function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Sup
pose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊
`, `f` is Lipschitz
on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt` for
 a version
with an explicit estimate on the Lipschitz constant.
-/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex ℝ s) {f : E → G}
    (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <|
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt hder hcont

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderivWithin`. -/
/-
**Convex.norm_image_sub_le_of_norm_fderivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 `Co
nvex`。
形式化陈述：norm_image_sub_le_of_norm_fderivWithin_le (hf : DifferentiableOn 𝕜 f s) (b
ound : forall x in s, ‖fderivWithin 𝕜 f s x‖ <= C) (hs : Convex Real s) (xs : x 
in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖
参数：hf : DifferentiableOn 𝕜 f s；bound : forall x in s, ‖fderivWithin 𝕜 f s x‖ <= 
C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`：norm_image_sub_le_o
f_norm_hasFDerivWithin_le (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (
bound : forall x in s, ‖f' x‖ <= C) (hs :…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x

--- 原说明 ---
The mean value theorem on a convex set: if the derivative of a function within t
his set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderivWithin`.
-/
theorem norm_image_sub_le_of_norm_fderivWithin_le (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderivWithin` and
`LipschitzOnWith`. -/
/-
**Convex.lipschitzOnWith_of_nnnorm_fderivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 `Co
nvex`。
形式化陈述：lipschitzOnWith_of_nnnorm_fderivWithin_le {C : Real>=0} (hf : Differentiab
leOn 𝕜 f s) (bound : forall x in s, ‖fderivWithin 𝕜 f s x‖₊ <= C) (hs : Convex R
eal s) : LipschitzOnWith C f s
参数：hf : DifferentiableOn 𝕜 f s；bound : forall x in s, ‖fderivWithin 𝕜 f s x‖₊ <=
 C；hs : Convex Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`：lipschitzOnWith_of_
nnnorm_hasFDerivWithin_le {C : Real>=0} (hf : forall x in s, HasFDerivWithinAt f
 (f' x) s x) (bound : forall x in s, ‖f' …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x

--- 原说明 ---
The mean value theorem on a convex set: if the derivative of a function is bound
ed by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderivWithin` and
`LipschitzOnWith`.
-/
theorem lipschitzOnWith_of_nnnorm_fderivWithin_le {C : ℝ≥0} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
/-
**Convex.norm_image_sub_le_of_norm_fderiv_le** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：norm_image_sub_le_of_norm_fderiv_le (hf : forall x in s, DifferentiableAt 
𝕜 f x) (bound : forall x in s, ‖fderiv 𝕜 f x‖ <= C) (hs : Convex Real s) (xs : x
 in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖
参数：hf : forall x in s, DifferentiableAt 𝕜 f x；bound : forall x in s, ‖fderiv 𝕜 f
 x‖ <= C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`：norm_image_sub_le_o
f_norm_hasFDerivWithin_le (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (
bound : forall x in s, ‖f' x‖ <= C) (hs :…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x

--- 原说明 ---
The mean value theorem on a convex set: if the derivative of a function is bound
ed by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`.
-/
theorem norm_image_sub_le_of_norm_fderiv_le (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `LipschitzOnWith`. -/
/-
**Convex.lipschitzOnWith_of_nnnorm_fderiv_le** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：lipschitzOnWith_of_nnnorm_fderiv_le {C : Real>=0} (hf : forall x in s, Dif
ferentiableAt 𝕜 f x) (bound : forall x in s, ‖fderiv 𝕜 f x‖₊ <= C) (hs : Convex 
Real s) : LipschitzOnWith C f s
参数：hf : forall x in s, DifferentiableAt 𝕜 f x；bound : forall x in s, ‖fderiv 𝕜 f
 x‖₊ <= C；hs : Convex Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`：lipschitzOnWith_of_
nnnorm_hasFDerivWithin_le {C : Real>=0} (hf : forall x in s, HasFDerivWithinAt f
 (f' x) s x) (bound : forall x in s, ‖f' …
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x

--- 原说明 ---
The mean value theorem on a convex set: if the derivative of a function is bound
ed by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `Lipsc
hitzOnWith`.
-/
theorem lipschitzOnWith_of_nnnorm_fderiv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound

/-- The mean value theorem: if the derivative of a function is bounded by `C`, then the function is
`C`-Lipschitz. Version with `fderiv` and `LipschitzWith`. -/
/-
**Convex._root_.lipschitzWith_of_nnnorm_fderiv_le** 是 Mathlib 中的一个定理，位于命名空间 `Con
vex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mean value theorem: if the derivative of a function is bounded by `C`, then 
the function is
`C`-Lipschitz. Version with `fderiv` and `LipschitzWith`.
-/
theorem _root_.lipschitzWith_of_nnnorm_fderiv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → G}
    {C : ℝ≥0} (hf : Differentiable 𝕜 f)
    (bound : ∀ x, ‖fderiv 𝕜 f x‖₊ ≤ C) : LipschitzWith C f := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ ↦ hf x) (fun x _ ↦ bound x) convex_univ

/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`HasFDerivWithinAt`. -/
/-
**Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'** 是 Mathlib 中的一个定理，位于命名空间
 `Convex`。
形式化陈述：norm_image_sub_le_of_norm_hasFDerivWithin_le' (hf : forall x in s, HasFDer
ivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x - φ‖ <= C) (hs : Convex R
eal s) (xs : x in s) (ys : y in s) : ‖f y - f x - φ (y - x)‖ <= C * ‖y - x‖
参数：hf : forall x in s, HasFDerivWithinAt f (f' x) s x；bound : forall x in s, ‖f'
 x - φ‖ <= C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.sub`：HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s
 x
· 使用定理 `ContinuousLinearMap.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.Analysis.Calculus.MeanValue.0.Convex.norm_image_sub_le_
of_norm_hasFDerivWithin_le'._abel_1_1`：∀ {E : Type u_2} [inst : NormedAddCommGro
up E] {𝕜 : Type u_3} {G : Type u_1} [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 …
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`：norm_image_sub_le_o
f_norm_hasFDerivWithin_le (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (
bound : forall x in s, ‖f' x‖ <= C) (hs :…

--- 原说明 ---
Variant of the mean value inequality on a convex set, using a bound on the diffe
rence between
the derivative and a fixed linear map, rather than a bound on the derivative its
elf. Version with
`HasFDerivWithinAt`.
-/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x - φ‖ ≤ C)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ := by
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
    applies, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. Then, we just need to glue
    together the pieces, expressing back `f` in terms of `g`. -/
  let g y := f y - φ y
  have hg : ∀ x ∈ s, HasFDerivWithinAt g (f' x - φ) s x := fun x xs =>
    (hf x xs).sub φ.hasFDerivWithinAt
  calc
    ‖f y - f x - φ (y - x)‖ = ‖f y - f x - (φ y - φ x)‖ := by simp
    _ = ‖f y - φ y - (f x - φ x)‖ := by congr 1; abel
    _ = ‖g y - g x‖ := by simp [g]
    _ ≤ C * ‖y - x‖ := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg bound hs xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderivWithin`. -/
/-
**Convex.norm_image_sub_le_of_norm_fderivWithin_le'** 是 Mathlib 中的一个定理，位于命名空间 `C
onvex`。
形式化陈述：norm_image_sub_le_of_norm_fderivWithin_le' (hf : DifferentiableOn 𝕜 f s) (
bound : forall x in s, ‖fderivWithin 𝕜 f s x - φ‖ <= C) (hs : Convex Real s) (xs
 : x in s) (ys : y in s) : ‖f y - f x - φ (y - x)‖ <= C * ‖y - x‖
参数：hf : DifferentiableOn 𝕜 f s；bound : forall x in s, ‖fderivWithin 𝕜 f s x - φ‖
 <= C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`：norm_image_sub_le_
of_norm_hasFDerivWithin_le' (hf : forall x in s, HasFDerivWithinAt f (f' x) s x)
 (bound : forall x in s, ‖f' x - φ‖ <= C) …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x

--- 原说明 ---
Variant of the mean value inequality on a convex set. Version with `fderivWithin
`.
-/
theorem norm_image_sub_le_of_norm_fderivWithin_le' (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
/-
**Convex.norm_image_sub_le_of_norm_fderiv_le'** 是 Mathlib 中的一个定理，位于命名空间 `Convex`
。
形式化陈述：norm_image_sub_le_of_norm_fderiv_le' (hf : forall x in s, DifferentiableAt
 𝕜 f x) (bound : forall x in s, ‖fderiv 𝕜 f x - φ‖ <= C) (hs : Convex Real s) (x
s : x in s) (ys : y in s) : ‖f y - f x - φ (y - x)‖ <= C * ‖y - x‖
参数：hf : forall x in s, DifferentiableAt 𝕜 f x；bound : forall x in s, ‖fderiv 𝕜 f
 x - φ‖ <= C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`：norm_image_sub_le_
of_norm_hasFDerivWithin_le' (hf : forall x in s, HasFDerivWithinAt f (f' x) s x)
 (bound : forall x in s, ‖f' x - φ‖ <= C) …
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x

--- 原说明 ---
Variant of the mean value inequality on a convex set. Version with `fderiv`.
-/
theorem norm_image_sub_le_of_norm_fderiv_le' (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
/-
**Convex.is_const_of_fderivWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：is_const_of_fderivWithin_eq_zero (hs : Convex Real s) (hf : Differentiable
On 𝕜 f s) (hf' : forall x in s, fderivWithin 𝕜 f s x = 0) (hx : x in s) (hy : y 
in s) : f x = f y
参数：hs : Convex Real s；hf : DifferentiableOn 𝕜 f s；hf' : forall x in s, fderivWit
hin 𝕜 f s x = 0；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Convex.norm_image_sub_le_of_norm_fderivWithin_le`：norm_image_sub_le_of_n
orm_fderivWithin_le (hf : DifferentiableOn 𝕜 f s) (bound : forall x in s, ‖fderi
vWithin 𝕜 f s x‖ <= C) (hs : Convex Re…

--- 原说明 ---
If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set.
-/
theorem is_const_of_fderivWithin_eq_zero (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : ∀ x ∈ s, fderivWithin 𝕜 f s x = 0) (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  have bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ 0 := fun x hx => by
    simp only [hf' x hx, norm_zero, le_rfl]
  simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
    hs.norm_image_sub_le_of_norm_fderivWithin_le hf bound hx hy
/-
**Convex._root_.is_const_of_fderiv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.is_const_of_fderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → G}
    (hf : Differentiable 𝕜 f) (hf' : ∀ x, fderiv 𝕜 f x = 0)
    (x y : E) : f x = f y := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  exact convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
    (fun x _ => by rw [fderivWithin_univ]; exact hf' x) trivial trivial

/-- If two functions have equal Fréchet derivatives at every point of a convex set, and are equal at
one point in that set, then they are equal on that set. -/
/-
**Convex.eqOn_of_fderivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：eqOn_of_fderivWithin_eq (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDiffOn 𝕜 s) (hf' : s.EqOn (fderivWit
hin 𝕜 f s) (fderivWithin 𝕜 g s)) (hx : x in s) (hfgx : f x = g x) : s.EqOn f g
参数：hs : Convex Real s；hf : DifferentiableOn 𝕜 f s；hg : DifferentiableOn 𝕜 g s；hs
' : UniqueDiffOn 𝕜 s；hf' : s.EqOn (fderivWithin 𝕜 f s) (fderivWithin 𝕜 g s)；hx :
 x in s；hfgx : f x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.is_const_of_fderivWithin_eq_zero`：is_const_of_fderivWithin_eq_zer
o (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s) (hf' : forall x in s, fderi
vWithin 𝕜 f s x = 0) (hx : x …
· 使用定理 `DifferentiableOn.sub`：DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f - g) s
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_sub`：fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf 
: DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderiv
Within…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
If two functions have equal Fréchet derivatives at every point of a convex set, 
and are equal at
one point in that set, then they are equal on that set.
-/
theorem eqOn_of_fderivWithin_eq (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDiffOn 𝕜 s)
    (hf' : s.EqOn (fderivWithin 𝕜 f s) (fderivWithin 𝕜 g s)) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g := fun y hy => by
  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
  refine hs.is_const_of_fderivWithin_eq_zero (hf.sub hg) (fun z hz => ?_) hx hy
  rw [fderivWithin_sub (hs' _ hz) (hf _ hz) (hg _ hz), sub_eq_zero, hf' hz]

/-- If `f` has zero derivative on an open set, then `f` is locally constant on `s`. -/
-- TODO: change the spelling once we have `IsLocallyConstantOn`.
/-
**Convex._root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero
    (hs : IsOpen s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) (t : Set G) : IsOpen (s ∩ f ⁻¹' t) := by
  refine Metric.isOpen_iff.mpr fun y ⟨hy, hy'⟩ ↦ ?_
  obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp hs y hy
  refine ⟨r, hr, Set.subset_inter h fun x hx ↦ ?_⟩
  have := (convex_ball y r).is_const_of_fderivWithin_eq_zero (hf.mono h) ?_ hx (mem_ball_self hr)
  · simpa [this]
  · intro z hz
    simpa only [fderivWithin_of_isOpen Metric.isOpen_ball hz] using! hf' (h hz)
/-
**Convex._root_.isLocallyConstant_of_fderiv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `C
onvex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isLocallyConstant_of_fderiv_eq_zero (h₁ : Differentiable 𝕜 f)
    (h₂ : ∀ x, fderiv 𝕜 f x = 0) : IsLocallyConstant f := by
  simpa using!
    isOpen_univ.isOpen_inter_preimage_of_fderiv_eq_zero h₁.differentiableOn fun _ _ ↦ h₂ _

/-- If `f` has zero derivative on a connected open set, then `f` is constant on `s`. -/
/-
**Convex._root_.IsOpen.exists_is_const_of_fderiv_eq_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` has zero derivative on a connected open set, then `f` is constant on `s`.
-/
theorem _root_.IsOpen.exists_is_const_of_fderiv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) : ∃ a, ∀ x ∈ s, f x = a := by
  obtain (rfl | ⟨y, hy⟩) := s.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  · refine ⟨f y, fun x hx ↦ ?_⟩
    have h₁ := hs.isOpen_inter_preimage_of_fderiv_eq_zero hf hf' {f y}
    have h₂ := hf.continuousOn.comp_continuous continuous_subtype_val (fun x ↦ x.2)
    by_contra h₃
    obtain ⟨t, ht, ht'⟩ := (isClosed_singleton (x := f y)).preimage h₂
    have ht'' : ∀ a ∈ s, a ∈ t ↔ f a ≠ f y := by simpa [Set.ext_iff] using ht'
    obtain ⟨z, H₁, H₂, H₃⟩ := hs' _ _ h₁ ht (fun x h ↦ by simp [h, ht'', eq_or_ne]) ⟨y, by simpa⟩
      ⟨x, by simp [ht'' _ hx, hx, h₃]⟩
    exact (ht'' _ H₁).mp H₃ H₂.2
/-
**Convex._root_.IsOpen.is_const_of_fderiv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Con
vex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.is_const_of_fderiv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  obtain ⟨a, ha⟩ := hs.exists_is_const_of_fderiv_eq_zero hs' hf hf'
  rw [ha x hx, ha y hy]
/-
**Convex._root_.IsOpen.exists_eq_add_of_fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Con
vex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.exists_eq_add_of_fderiv_eq (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (fderiv 𝕜 f) (fderiv 𝕜 g)) : ∃ a, s.EqOn f (g · + a) := by
  simp_rw [Set.EqOn, ← sub_eq_iff_eq_add']
  refine hs.exists_is_const_of_fderiv_eq_zero hs' (hf.sub hg) fun x hx ↦ ?_
  rw [fderiv_fun_sub (hf.differentiableAt (hs.mem_nhds hx)) (hg.differentiableAt (hs.mem_nhds hx)),
    hf' hx, sub_self, Pi.zero_apply]

/-- If two functions have equal Fréchet derivatives at every point of a connected open set,
and are equal at one point in that set, then they are equal on that set. -/
/-
**Convex._root_.IsOpen.eqOn_of_fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two functions have equal Fréchet derivatives at every point of a connected op
en set,
and are equal at one point in that set, then they are equal on that set.
-/
theorem _root_.IsOpen.eqOn_of_fderiv_eq (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : ∀ x ∈ s, fderiv 𝕜 f x = fderiv 𝕜 g x) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g := by
  obtain ⟨a, ha⟩ := hs.exists_eq_add_of_fderiv_eq hs' hf hg hf'
  obtain rfl := left_eq_add.mp (hfgx.symm.trans (ha hx))
  simpa using ha
/-
**Convex._root_.eq_of_fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.eq_of_fderiv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : E → G}
    (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g)
    (hf' : ∀ x, fderiv 𝕜 f x = fderiv 𝕜 g x) (x : E) (hfgx : f x = g x) : f = g := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  suffices Set.univ.EqOn f g from funext fun x => this <| mem_univ x
  exact convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn
    uniqueDiffOn_univ (fun x _ => by simpa using hf' _) (mem_univ _) hfgx
/-
**Convex.isLittleO_pow_succ** 是 Mathlib 中的一个引理，位于命名空间 `Convex`。
形式化陈述：isLittleO_pow_succ {x₀ : E} {n : Nat} (hs : Convex Real s) (hx₀s : x₀ in s
) (hff' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] f
un x => ‖x - x₀‖ ^ n) : (fun x => f x - f x₀) =o[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ (n
 + 1)
参数：hs : Convex Real s；hx₀s : x₀ in s；hff' : forall x in s, HasFDerivWithinAt f (
f' x) s x；hf' : f' =o[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `Convex.eventually_nhdsWithin_segment`：Convex.eventually_nhdsWithin_segme
nt {E 𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E] [T
opologicalSpace E] [Locall…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `norm_sub_le_of_mem_segment`：norm_sub_le_of_mem_segment {x y z : E} (hy :
 y in segment Real x z) : ‖y - x‖ <= ‖z - x‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
（共 37 条，此处仅展示前 30 条）
-/
lemma isLittleO_pow_succ {x₀ : E} {n : ℕ} (hs : Convex ℝ s) (hx₀s : x₀ ∈ s)
    (hff' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] fun x ↦ ‖x - x₀‖ ^ n) :
    (fun x ↦ f x - f x₀) =o[𝓝[s] x₀] fun x ↦ ‖x - x₀‖ ^ (n + 1) := by
  rw [Asymptotics.isLittleO_iff] at hf' ⊢
  intro c hc
  simp_rw [norm_pow, pow_succ, ← mul_assoc, norm_norm]
  simp_rw [norm_pow, norm_norm] at hf'
  have : ∀ᶠ x in 𝓝[s] x₀, segment ℝ x₀ x ⊆ s ∧ ∀ y ∈ segment ℝ x₀ x, ‖f' y‖ ≤ c * ‖x - x₀‖ ^ n := by
    have h1 : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := eventually_mem_nhdsWithin
    filter_upwards [h1, hs.eventually_nhdsWithin_segment hx₀s (hf' hc)] with x hxs h
    refine ⟨hs.segment_subset hx₀s hxs, fun y hy ↦ (h y hy).trans ?_⟩
    gcongr
    exact norm_sub_le_of_mem_segment hy
  filter_upwards [this] with x ⟨h_segment, h⟩
  convert!
    (convex_segment x₀ x).norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun x ↦ f x - f x₀)
      (y := x) (x := x₀) (s := segment ℝ x₀ x) ?_ h
      (left_mem_segment ℝ x₀ x)
      (right_mem_segment ℝ x₀ x) using 1
  · simp
  · simp only [hasFDerivWithinAt_sub_const_iff]
    exact fun x hx ↦ (hff' x (h_segment hx)).mono h_segment
/-
**Convex.isLittleO_pow_succ_real** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：isLittleO_pow_succ_real {f f' : Real -> E} {x₀ : Real} {n : Nat} {s : Set 
Real} (hs : Convex Real s) (hx₀s : x₀ in s) (hff' : forall x in s, HasDerivWithi
nAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] fun x => (x - x₀) ^ n) : (fun x => f x -
 f x₀) =o[𝓝[s] x₀] fun x => (x - x₀) ^ (n + 1)
参数：hs : Convex Real s；hx₀s : x₀ in s；hff' : forall x in s, HasDerivWithinAt f (f
' x) s x；hf' : f' =o[𝓝[s] x₀] fun x => (x - x₀) ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `Convex.isLittleO_pow_succ`：isLittleO_pow_succ {x₀ : E} {n : Nat} (hs : C
onvex Real s) (hx₀s : x₀ in s) (hff' : forall x in s, HasFDerivWithinAt f (f' x)
 s x) (hf' : f'…
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem isLittleO_pow_succ_real {f f' : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s)
    (hff' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ n) :
    (fun x ↦ f x - f x₀) =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ (n + 1) := by
  have h := hs.isLittleO_pow_succ hx₀s hff' ?_ (n := n)
  · rw [Asymptotics.isLittleO_iff] at h ⊢
    simpa using h
  · rw [Asymptotics.isLittleO_iff] at hf' ⊢
    convert! hf' using 4 with c hc x
    simp

end Convex

namespace Convex

variable {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `HasDerivWithinAt`. -/
/-
**Convex.norm_image_sub_le_of_norm_hasDerivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 `
Convex`。
形式化陈述：norm_image_sub_le_of_norm_hasDerivWithin_le {C : Real} (hf : forall x in s
, HasDerivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x‖ <= C) (hs : Conv
ex Real s) (xs : x in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖
参数：hf : forall x in s, HasDerivWithinAt f (f' x) s x；bound : forall x in s, ‖f' 
x‖ <= C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`：norm_image_sub_le_o
f_norm_hasFDerivWithin_le (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (
bound : forall x in s, ‖f' x‖ <= C) (hs :…
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…

--- 原说明 ---
The mean value theorem on a convex set in dimension 1: if the derivative of a fu
nction is
bounded by `C`, then the function is `C`-Lipschitz. Version with `HasDerivWithin
At`.
-/
theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `HasDerivWithinAt` and `LipschitzOnWith`. -/
/-
**Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 `
Convex`。
形式化陈述：lipschitzOnWith_of_nnnorm_hasDerivWithin_le {C : Real>=0} (hs : Convex Rea
l s) (hf : forall x in s, HasDerivWithinAt f (f' x) s x) (bound : forall x in s,
 ‖f' x‖₊ <= C) : LipschitzOnWith C f s
参数：hs : Convex Real s；hf : forall x in s, HasDerivWithinAt f (f' x) s x；bound : 
forall x in s, ‖f' x‖₊ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`：lipschitzOnWith_of_
nnnorm_hasFDerivWithin_le {C : Real>=0} (hf : forall x in s, HasFDerivWithinAt f
 (f' x) s x) (bound : forall x in s, ‖f' …
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.nnnorm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u
_4} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [in
st_2 : NormedSpace 𝕜 E] (x : E),…

--- 原说明 ---
The mean value theorem on a convex set in dimension 1: if the derivative of a fu
nction is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `HasDerivWithinAt` and `LipschitzOnWith`.
-/
theorem lipschitzOnWith_of_nnnorm_hasDerivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `derivWithin` -/
/-
**Convex.norm_image_sub_le_of_norm_derivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 `Con
vex`。
形式化陈述：norm_image_sub_le_of_norm_derivWithin_le {C : Real} (hf : DifferentiableOn
 𝕜 f s) (bound : forall x in s, ‖derivWithin f s x‖ <= C) (hs : Convex Real s) (
xs : x in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖
参数：hf : DifferentiableOn 𝕜 f s；bound : forall x in s, ‖derivWithin f s x‖ <= C；h
s : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`：norm_image_sub_le_of
_norm_hasDerivWithin_le {C : Real} (hf : forall x in s, HasDerivWithinAt f (f' x
) s x) (bound : forall x in s, ‖f' x‖ <=…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
The mean value theorem on a convex set in dimension 1: if the derivative of a fu
nction within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `de
rivWithin`
-/
theorem norm_image_sub_le_of_norm_derivWithin_le {C : ℝ} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖derivWithin f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
    ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `derivWithin` and `LipschitzOnWith`. -/
/-
**Convex.lipschitzOnWith_of_nnnorm_derivWithin_le** 是 Mathlib 中的一个定理，位于命名空间 `Con
vex`。
形式化陈述：lipschitzOnWith_of_nnnorm_derivWithin_le {C : Real>=0} (hs : Convex Real s
) (hf : DifferentiableOn 𝕜 f s) (bound : forall x in s, ‖derivWithin f s x‖₊ <= 
C) : LipschitzOnWith C f s
参数：hs : Convex Real s；hf : DifferentiableOn 𝕜 f s；bound : forall x in s, ‖derivW
ithin f s x‖₊ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`：lipschitzOnWith_of_n
nnorm_hasDerivWithin_le {C : Real>=0} (hs : Convex Real s) (hf : forall x in s, 
HasDerivWithinAt f (f' x) s x) (bound : …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
The mean value theorem on a convex set in dimension 1: if the derivative of a fu
nction is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `derivWithin` and `LipschitzOnWith`.
-/
theorem lipschitzOnWith_of_nnnorm_derivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : DifferentiableOn 𝕜 f s) (bound : ∀ x ∈ s, ‖derivWithin f s x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
/-
**Convex.norm_image_sub_le_of_norm_deriv_le** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：norm_image_sub_le_of_norm_deriv_le {C : Real} (hf : forall x in s, Differe
ntiableAt 𝕜 f x) (bound : forall x in s, ‖deriv f x‖ <= C) (hs : Convex Real s) 
(xs : x in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖
参数：hf : forall x in s, DifferentiableAt 𝕜 f x；bound : forall x in s, ‖deriv f x‖
 <= C；hs : Convex Real s；xs : x in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`：norm_image_sub_le_of
_norm_hasDerivWithin_le {C : Real} (hf : forall x in s, HasDerivWithinAt f (f' x
) s x) (bound : forall x in s, ‖f' x‖ <=…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x

--- 原说明 ---
The mean value theorem on a convex set in dimension 1: if the derivative of a fu
nction is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`.
-/
theorem norm_image_sub_le_of_norm_deriv_le {C : ℝ} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `LipschitzOnWith`. -/
/-
**Convex.lipschitzOnWith_of_nnnorm_deriv_le** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：lipschitzOnWith_of_nnnorm_deriv_le {C : Real>=0} (hf : forall x in s, Diff
erentiableAt 𝕜 f x) (bound : forall x in s, ‖deriv f x‖₊ <= C) (hs : Convex Real
 s) : LipschitzOnWith C f s
参数：hf : forall x in s, DifferentiableAt 𝕜 f x；bound : forall x in s, ‖deriv f x‖
₊ <= C；hs : Convex Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`：lipschitzOnWith_of_n
nnorm_hasDerivWithin_le {C : Real>=0} (hs : Convex Real s) (hf : forall x in s, 
HasDerivWithinAt f (f' x) s x) (bound : …
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x

--- 原说明 ---
The mean value theorem on a convex set in dimension 1: if the derivative of a fu
nction is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `LipschitzOnWith`.
-/
theorem lipschitzOnWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound

/-- The mean value theorem set in dimension 1: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `deriv` and `LipschitzWith`. -/
/-
**Convex._root_.lipschitzWith_of_nnnorm_deriv_le** 是 Mathlib 中的一个定理，位于命名空间 `Conv
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mean value theorem set in dimension 1: if the derivative of a function is bo
unded by `C`,
then the function is `C`-Lipschitz. Version with `deriv` and `LipschitzWith`.
-/
theorem _root_.lipschitzWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : Differentiable 𝕜 f)
    (bound : ∀ x, ‖deriv f x‖₊ ≤ C) : LipschitzWith C f :=
  lipschitzOnWith_univ.1 <|
    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x

/-- If `f : 𝕜 → G`, `𝕜 = R` or `𝕜 = ℂ`, is differentiable everywhere and its derivative equal zero,
then it is a constant function. -/
/-
**Convex._root_.is_const_of_deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : 𝕜 → G`, `𝕜 = R` or `𝕜 = ℂ`, is differentiable everywhere and its derivat
ive equal zero,
then it is a constant function.
-/
theorem _root_.is_const_of_deriv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, deriv f x = 0)
    (x y : 𝕜) : f x = f y :=
  is_const_of_fderiv_eq_zero hf (fun z => by simp [← toSpanSingleton_deriv, hf']) _ _
/-
**Convex._root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero
    (hs : IsOpen s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) (t : Set G) : IsOpen (s ∩ f ⁻¹' t) :=
  hs.isOpen_inter_preimage_of_fderiv_eq_zero hf
    (fun x hx ↦ by simp [← toSpanSingleton_deriv, hf' hx]) t
/-
**Convex._root_.IsOpen.exists_is_const_of_deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.exists_is_const_of_deriv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) : ∃ a, ∀ x ∈ s, f x = a :=
  hs.exists_is_const_of_fderiv_eq_zero hs' hf (fun {x} hx ↦ by
    ext; simp [← toSpanSingleton_deriv, hf' hx])
/-
**Convex._root_.IsOpen.is_const_of_deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Conv
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.is_const_of_deriv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) {x y : 𝕜} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  hs.is_const_of_fderiv_eq_zero hs' hf (fun a ha ↦ by
    ext; simp [← toSpanSingleton_deriv, hf' ha]) hx hy
/-
**Convex._root_.IsOpen.exists_eq_add_of_deriv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Conv
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.exists_eq_add_of_deriv_eq {f g : 𝕜 → G} (hs : IsOpen s)
    (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (deriv f) (deriv g)) : ∃ a, s.EqOn f (g · + a) :=
  hs.exists_eq_add_of_fderiv_eq hs' hf hg (fun x hx ↦ by simp [← toSpanSingleton_deriv, hf' hx])
/-
**Convex._root_.IsOpen.eqOn_of_deriv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.eqOn_of_deriv_eq {f g : 𝕜 → G} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (deriv f) (deriv g)) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g :=
  hs.eqOn_of_fderiv_eq hs' hf hg (fun _ hx ↦ ContinuousLinearMap.ext_ring (hf' hx)) hx hfgx

end Convex

end

section RCLike

/-!
### Vector-valued functions `f : E → F`. Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] {f : G → H} {f' : G → G →L[𝕜] H} {x : G}

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
/-
**hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder : forallᶠ y in 𝓝 x,
 HasFDerivAt f (f' y) y) (hcont : ContinuousAt f' x) : HasStrictFDerivAt f (f' x
) x
参数：hder : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y；hcont : ContinuousAt f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasStrictFDerivAt_iff_isLittleO`：hasStrictFDerivAt_iff_isLittleO : HasSt
rictFDerivAt f f' x ↔ (fun p : E × E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x,
 x)] fun p : E × E =>…
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`：norm_image_sub_le_
of_norm_hasFDerivWithin_le' (hf : forall x in s, HasFDerivWithinAt f (f' x) s x)
 (bound : forall x in s, ‖f' x - φ‖ <= C) …
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `Set.prodMk_mem_set_prod_eq`：prodMk_mem_set_prod_eq : ((a, b) in s ×ˢ t) 
= (a in s ∧ b in t)
· 使用引理 `ball_prod_same`：ball_prod_same (x : α) (y : β) (r : Real) : ball x r ×ˢ 
ball y r = ball (x, y) r

--- 原说明 ---
Over the reals or the complexes, a continuously differentiable function is stric
tly
differentiable.
-/
theorem hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (hder : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictFDerivAt f (f' x) x := by
  -- turn little-o definition of strict_fderiv into an epsilon-delta statement
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  refine fun c hc => Metric.eventually_nhds_iff_ball.mpr ?_
  -- the correct ε is the modulus of continuity of f'
  rcases Metric.mem_nhds_iff.mp (inter_mem hder (hcont <| ball_mem_nhds _ hc)) with ⟨ε, ε0, hε⟩
  refine ⟨ε, ε0, ?_⟩
  -- simplify formulas involving the product E × E
  rintro ⟨a, b⟩ h
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at h
  -- exploit the choice of ε as the modulus of continuity of f'
  have hf' : ∀ x' ∈ ball x ε, ‖f' x' - f' x‖ ≤ c := fun x' H' => by
    rw [← dist_eq_norm]
    exact le_of_lt (hε H').2
  -- apply mean value theorem
  let : NormedSpace ℝ G := .restrictScalars ℝ 𝕜 G
  refine (convex_ball _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le' ?_ hf' h.2 h.1
  exact fun y hy => (hε hy).1.hasFDerivWithinAt

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
/-
**hasStrictDerivAt_of_hasDerivAt_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_of_hasDerivAt_of_continuousAt {f f' : 𝕜 -> G} {x : 𝕜} (hd
er : forallᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) : HasS
trictDerivAt f (f' x) x
参数：hder : forallᶠ y in 𝓝 x, HasDerivAt f (f' y) y；hcont : ContinuousAt f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt`：hasStrictFDerivAt_of_h
asFDerivAt_of_continuousAt (hder : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hc
ont : ContinuousAt f' x) : HasStrictFD…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…

--- 原说明 ---
Over the reals or the complexes, a continuously differentiable function is stric
tly
differentiable.
-/
theorem hasStrictDerivAt_of_hasDerivAt_of_continuousAt {f f' : 𝕜 → G} {x : 𝕜}
    (hder : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictDerivAt f (f' x) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder.mono fun _ hy => hy.hasFDerivAt) <|
    (smulRightL 𝕜 𝕜 G 1).continuous.continuousAt.comp hcont

end RCLike

