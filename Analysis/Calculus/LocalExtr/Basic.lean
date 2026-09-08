/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Local extrema of differentiable functions

## Main definitions

In a real normed space `E` we define `posTangentConeAt (s : Set E) (x : E)`.
This would be the same as `tangentConeAt ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below,
we also prove similar theorems for `min`, `extr` (if applicable),
and `fderiv`/`deriv` instead of `HasFDerivAt`/`HasDerivAt`.

* `IsLocalMaxOn.hasFDerivWithinAt_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `IsLocalMaxOn.hasFDerivWithinAt_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `IsLocalMax.hasFDerivAt_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `HasFDeriv*`/`HasDeriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, tangent cone, Fermat's Theorem
-/

public section


universe u v

open Filter Set

open scoped Topology Convex NNReal

section Module

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {f' : StrongDual ℝ E} {s : Set E} {a x y : E}

/-!
### Positive tangent cone
-/

/-
**posTangentConeAt_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posTangentConeAt_mono : Monotone fun s => posTangentConeAt s a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tangentConeAt_mono`：tangentConeAt_mono (h : s subseteq t) : tangentConeA
t 𝕜 s x subseteq tangentConeAt 𝕜 t x

--- 原说明 ---
### Positive tangent cone
-/
theorem posTangentConeAt_mono : Monotone fun s => posTangentConeAt s a := by
  intro s t hst
  exact tangentConeAt_mono hst
/-
**mem_posTangentConeAt_of_frequently_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_posTangentConeAt_of_frequently_mem (h : existsᶠ t : Real in 𝓝[>] 0, x 
+ t • y in s) : y in posTangentConeAt s x
参数：h : existsᶠ t : Real in 𝓝[>] 0, x + t • y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_tangentConeAt_of_add_smul_mem`：mem_tangentConeAt_of_add_smul_mem {α 
: Type*} {l : Filter α} [l.NeBot] {c : α -> 𝕜} (hc₀ : Tendsto c l (𝓝[!=] 0)) (hm
em : forallᶠ n in l, x …
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.frequently_iff_neBot`：frequently_iff_neBot {l : Filter α} {p : α 
-> Prop} : (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x})
· 使用定理 `Filter.frequently_map`：frequently_map {P : β -> Prop} : (existsᶠ b in ma
p m f, P b) ↔ existsᶠ a in f, P (m a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.map_coe_nhdsGT`：map_coe_nhdsGT (x : Real>=0) : (𝓝[>] x).map toRea
l = 𝓝[>] ↑x
· 使用定理 `NNReal.coe_zero`：↑0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mem_posTangentConeAt_of_frequently_mem (h : ∃ᶠ t : ℝ in 𝓝[>] 0, x + t • y ∈ s) :
    y ∈ posTangentConeAt s x := by
  rw [← NNReal.coe_zero, ← NNReal.map_coe_nhdsGT, frequently_map, frequently_iff_neBot] at h
  apply mem_tangentConeAt_of_add_smul_mem (l := 𝓝[>] (0 : ℝ≥0) ⊓ 𝓟 {t | x + (t : ℝ) • y ∈ s})
  · exact tendsto_id'.mpr <| inf_le_left.trans <| nhdsGT_le_nhdsNE _
  · simp [eventually_inf_principal, NNReal.smul_def]
/-
**sub_mem_posTangentConeAt_of_segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_mem_posTangentConeAt_of_segment_subset (h : segment Real x y subseteq 
s) : y - x in posTangentConeAt s x
参数：h : segment Real x y subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem_posTangentConeAt_of_openSegment_subset`：sub_mem_posTangentConeAt
_of_openSegment_subset (h : openSegment Real x y subseteq s) : y - x in tangentC
oneAt Real>=0 s x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `openSegment_subset_segment`：openSegment_subset_segment (x y : E) : openS
egment 𝕜 x y subseteq [x -[𝕜] y]
-/
theorem sub_mem_posTangentConeAt_of_segment_subset (h : segment ℝ x y ⊆ s) :
    y - x ∈ posTangentConeAt s x :=
  sub_mem_posTangentConeAt_of_openSegment_subset <| (openSegment_subset_segment ..).trans h

/-- If `[x -[ℝ] x + y] ⊆ s`, then `y` belongs to the positive tangent cone of `s`. -/
/-
**mem_posTangentConeAt_of_segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_posTangentConeAt_of_segment_subset (h : [x -[Real] x + y] subseteq s) 
: y in posTangentConeAt s x
参数：h : [x -[Real] x + y] subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_mem_posTangentConeAt_of_segment_subset`：sub_mem_posTangentConeAt_of_
segment_subset (h : segment Real x y subseteq s) : y - x in posTangentConeAt s x

--- 原说明 ---
If `[x -[ℝ] x + y] ⊆ s`, then `y` belongs to the positive tangent cone of `s`.
-/
theorem mem_posTangentConeAt_of_segment_subset (h : [x -[ℝ] x + y] ⊆ s) :
    y ∈ posTangentConeAt s x := by
  simpa using sub_mem_posTangentConeAt_of_segment_subset h
/-
**posTangentConeAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posTangentConeAt_univ : posTangentConeAt univ a = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tangentConeAt_univ`：tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instNeBotNhdsWithinComplSetSingletonOfNontrivial`：∀ {α : Type u_1} [inst
 : TopologicalSpace α] [inst_1 : LinearOrder α] [OrderTopology α] [DenselyOrdere
d α] (x : α)   [Nontrivial α], (nhdsWi…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
theorem posTangentConeAt_univ : posTangentConeAt univ a = univ := tangentConeAt_univ

/-!
### Fermat's Theorem (vector space)
-/

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
/-
**IsLocalMaxOn.hasFDerivWithinAt_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.hasFDerivWithinAt_nonpos (h : IsLocalMaxOn f s a) (hf : HasFD
erivWithinAt f f' s a) (hy : y in posTangentConeAt s a) : f' y <= 0
参数：h : IsLocalMaxOn f s a；hf : HasFDerivWithinAt f f' s a；hy : y in posTangentCo
neAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `HasFDerivWithinAt.lim`：HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f'
 s x) {α : Type*} {l : Filter α} {c : α -> 𝕜} {d : α -> E} {v : E} (dlim : Tends
to d l (𝓝 0…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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

--- 原说明 ---
If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` withi
n `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`.
-/
theorem IsLocalMaxOn.hasFDerivWithinAt_nonpos (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a) : f' y ≤ 0 := by
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
  suffices ∀ᶠ n in l, c n • (f (a + d n) - f a) ≤ 0 from
    le_of_tendsto (hf.lim hd₀ hd hcd) this
  replace hd : Tendsto (fun n => a + d n) l (𝓝[s] (a + 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add hd₀, hd⟩
  rw [add_zero] at hd
  refine hd.eventually h |>.mono fun n hn ↦ ?_
  exact mul_nonpos_of_nonneg_of_nonpos (c n).coe_nonneg (sub_nonpos.2 hn)

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
/-
**IsLocalMaxOn.fderivWithin_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.fderivWithin_nonpos (h : IsLocalMaxOn f s a) (hy : y in posTa
ngentConeAt s a) : (fderivWithin Real f s a : E -> Real) y <= 0
参数：h : IsLocalMaxOn f s a；hy : y in posTangentConeAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMaxOn.hasFDerivWithinAt_nonpos`：IsLocalMaxOn.hasFDerivWithinAt_no
npos (h : IsLocalMaxOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in posTa
ngentConeAt s a) : f' y <= …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent con
e
of `s` at `a`, then `f' y ≤ 0`.
-/
theorem IsLocalMaxOn.fderivWithin_nonpos (h : IsLocalMaxOn f s a)
    (hy : y ∈ posTangentConeAt s a) : (fderivWithin ℝ f s a : E → ℝ) y ≤ 0 := by
  classical
  exact
    if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
/-
**IsLocalMaxOn.hasFDerivWithinAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.hasFDerivWithinAt_eq_zero (h : IsLocalMaxOn f s a) (hf : HasF
DerivWithinAt f f' s a) (hy : y in posTangentConeAt s a) (hy' : -y in posTangent
ConeAt s a) : f' y = 0
参数：h : IsLocalMaxOn f s a；hf : HasFDerivWithinAt f f' s a；hy : y in posTangentCo
neAt s a；hy' : -y in posTangentConeAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsLocalMaxOn.hasFDerivWithinAt_nonpos`：IsLocalMaxOn.hasFDerivWithinAt_no
npos (h : IsLocalMaxOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in posTa
ngentConeAt s a) : f' y <= …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within 
`s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y 
≤ 0`.
-/
theorem IsLocalMaxOn.hasFDerivWithinAt_eq_zero (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 :=
  le_antisymm (h.hasFDerivWithinAt_nonpos hf hy) <| by simpa using h.hasFDerivWithinAt_nonpos hf hy'

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
/-
**IsLocalMaxOn.fderivWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.fderivWithin_eq_zero (h : IsLocalMaxOn f s a) (hy : y in posT
angentConeAt s a) (hy' : -y in posTangentConeAt s a) : (fderivWithin Real f s a 
: E -> Real) y = 0
参数：h : IsLocalMaxOn f s a；hy : y in posTangentConeAt s a；hy' : -y in posTangentC
oneAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMaxOn.hasFDerivWithinAt_eq_zero`：IsLocalMaxOn.hasFDerivWithinAt_e
q_zero (h : IsLocalMaxOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in pos
TangentConeAt s a) (hy' : -y…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0

--- 原说明 ---
If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positiv
e tangent cone
of `s` at `a`, then `f' y = 0`.
-/
theorem IsLocalMaxOn.fderivWithin_eq_zero (h : IsLocalMaxOn f s a)
    (hy : y ∈ posTangentConeAt s a) (hy' : -y ∈ posTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y = 0 := by
  classical
  exact if hf : DifferentiableWithinAt ℝ f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
/-
**IsLocalMinOn.hasFDerivWithinAt_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.hasFDerivWithinAt_nonneg (h : IsLocalMinOn f s a) (hf : HasFD
erivWithinAt f f' s a) (hy : y in posTangentConeAt s a) : 0 <= f' y
参数：h : IsLocalMinOn f s a；hf : HasFDerivWithinAt f f' s a；hy : y in posTangentCo
neAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLocalMaxOn.hasFDerivWithinAt_nonpos`：IsLocalMaxOn.hasFDerivWithinAt_no
npos (h : IsLocalMaxOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in posTa
ngentConeAt s a) : f' y <= …
· 使用定理 `IsLocalMinOn.neg`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α
] [inst_1 : AddCommGroup β] [inst_2 : PartialOrder β]   [IsOrderedAddMonoid β] {
f : α …
· 使用定理 `HasFDerivWithinAt.neg`：HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f'
 s x) : HasFDerivWithinAt (-f) (-f') s x

--- 原说明 ---
If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` withi
n `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`.
-/
theorem IsLocalMinOn.hasFDerivWithinAt_nonneg (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a) : 0 ≤ f' y := by
  simpa using h.neg.hasFDerivWithinAt_nonpos hf.neg hy

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
/-
**IsLocalMinOn.fderivWithin_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.fderivWithin_nonneg (h : IsLocalMinOn f s a) (hy : y in posTa
ngentConeAt s a) : (0 : Real) <= (fderivWithin Real f s a : E -> Real) y
参数：h : IsLocalMinOn f s a；hy : y in posTangentConeAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMinOn.hasFDerivWithinAt_nonneg`：IsLocalMinOn.hasFDerivWithinAt_no
nneg (h : IsLocalMinOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in posTa
ngentConeAt s a) : 0 <= f' …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent con
e
of `s` at `a`, then `0 ≤ f' y`.
-/
theorem IsLocalMinOn.fderivWithin_nonneg (h : IsLocalMinOn f s a)
    (hy : y ∈ posTangentConeAt s a) : (0 : ℝ) ≤ (fderivWithin ℝ f s a : E → ℝ) y := by
  classical
  exact
    if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
/-
**IsLocalMinOn.hasFDerivWithinAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.hasFDerivWithinAt_eq_zero (h : IsLocalMinOn f s a) (hf : HasF
DerivWithinAt f f' s a) (hy : y in posTangentConeAt s a) (hy' : -y in posTangent
ConeAt s a) : f' y = 0
参数：h : IsLocalMinOn f s a；hf : HasFDerivWithinAt f f' s a；hy : y in posTangentCo
neAt s a；hy' : -y in posTangentConeAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `IsLocalMaxOn.hasFDerivWithinAt_eq_zero`：IsLocalMaxOn.hasFDerivWithinAt_e
q_zero (h : IsLocalMaxOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in pos
TangentConeAt s a) (hy' : -y…
· 使用定理 `IsLocalMinOn.neg`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α
] [inst_1 : AddCommGroup β] [inst_2 : PartialOrder β]   [IsOrderedAddMonoid β] {
f : α …
· 使用定理 `HasFDerivWithinAt.neg`：HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f'
 s x) : HasFDerivWithinAt (-f) (-f') s x

--- 原说明 ---
If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within 
`s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y 
≤ 0`.
-/
theorem IsLocalMinOn.hasFDerivWithinAt_eq_zero (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 := by
  simpa using h.neg.hasFDerivWithinAt_eq_zero hf.neg hy hy'

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
/-
**IsLocalMinOn.fderivWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.fderivWithin_eq_zero (h : IsLocalMinOn f s a) (hy : y in posT
angentConeAt s a) (hy' : -y in posTangentConeAt s a) : (fderivWithin Real f s a 
: E -> Real) y = 0
参数：h : IsLocalMinOn f s a；hy : y in posTangentConeAt s a；hy' : -y in posTangentC
oneAt s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMinOn.hasFDerivWithinAt_eq_zero`：IsLocalMinOn.hasFDerivWithinAt_e
q_zero (h : IsLocalMinOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in pos
TangentConeAt s a) (hy' : -y…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0

--- 原说明 ---
If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positiv
e tangent cone
of `s` at `a`, then `f' y = 0`.
-/
theorem IsLocalMinOn.fderivWithin_eq_zero (h : IsLocalMinOn f s a)
    (hy : y ∈ posTangentConeAt s a) (hy' : -y ∈ posTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y = 0 := by
  classical
  exact if hf : DifferentiableWithinAt ℝ f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
/-
**IsLocalMin.hasFDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.hasFDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasFDerivAt f f'
 a) : f' = 0
参数：h : IsLocalMin f a；hf : HasFDerivAt f f' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsLocalMinOn.hasFDerivWithinAt_eq_zero`：IsLocalMinOn.hasFDerivWithinAt_e
q_zero (h : IsLocalMinOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y in pos
TangentConeAt s a) (hy' : -y…
· 使用定理 `IsLocalMin.on`：IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s
 a
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `posTangentConeAt_univ`：posTangentConeAt_univ : posTangentConeAt univ a =
 univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local minimum equals zer
o.
-/
theorem IsLocalMin.hasFDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasFDerivAt f f' a) : f' = 0 := by
  ext y
  apply (h.on univ).hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt <;>
      rw [posTangentConeAt_univ] <;>
    apply mem_univ

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
/-
**IsLocalMin.fderiv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a) : fderiv Real f a = 0
参数：h : IsLocalMin f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMin.hasFDerivAt_eq_zero`：IsLocalMin.hasFDerivAt_eq_zero (h : IsLo
calMin f a) (hf : HasFDerivAt f f' a) : f' = 0
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local minimum equals zer
o.
-/
theorem IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a) : fderiv ℝ f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
/-
**IsLocalMax.hasFDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.hasFDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasFDerivAt f f'
 a) : f' = 0
参数：h : IsLocalMax f a；hf : HasFDerivAt f f' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `IsLocalMin.hasFDerivAt_eq_zero`：IsLocalMin.hasFDerivAt_eq_zero (h : IsLo
calMin f a) (hf : HasFDerivAt f f' a) : f' = 0
· 使用定理 `IsLocalMax.neg`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : AddCommGroup β] [inst_2 : PartialOrder β]   [IsOrderedAddMonoid β] {f 
: α …
· 使用定理 `HasFDerivAt.neg`：HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt 
(-f) (-f') x

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local maximum equals zer
o.
-/
theorem IsLocalMax.hasFDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasFDerivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.hasFDerivAt_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
/-
**IsLocalMax.fderiv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a) : fderiv Real f a = 0
参数：h : IsLocalMax f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMax.hasFDerivAt_eq_zero`：IsLocalMax.hasFDerivAt_eq_zero (h : IsLo
calMax f a) (hf : HasFDerivAt f f' a) : f' = 0
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local maximum equals zer
o.
-/
theorem IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a) : fderiv ℝ f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
/-
**IsLocalExtr.hasFDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.hasFDerivAt_eq_zero (h : IsLocalExtr f a) : HasFDerivAt f f' a
 -> f' = 0
参数：h : IsLocalExtr f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.elim`：IsLocalExtr.elim {p : Prop} : IsLocalExtr f a -> (IsLo
calMin f a -> p) -> (IsLocalMax f a -> p) -> p
· 使用定理 `IsLocalMin.hasFDerivAt_eq_zero`：IsLocalMin.hasFDerivAt_eq_zero (h : IsLo
calMin f a) (hf : HasFDerivAt f f' a) : f' = 0
· 使用定理 `IsLocalMax.hasFDerivAt_eq_zero`：IsLocalMax.hasFDerivAt_eq_zero (h : IsLo
calMax f a) (hf : HasFDerivAt f f' a) : f' = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local extremum equals ze
ro.
-/
theorem IsLocalExtr.hasFDerivAt_eq_zero (h : IsLocalExtr f a) : HasFDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.hasFDerivAt_eq_zero IsLocalMax.hasFDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
/-
**IsLocalExtr.fderiv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.fderiv_eq_zero (h : IsLocalExtr f a) : fderiv Real f a = 0
参数：h : IsLocalExtr f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.elim`：IsLocalExtr.elim {p : Prop} : IsLocalExtr f a -> (IsLo
calMin f a -> p) -> (IsLocalMax f a -> p) -> p
· 使用定理 `IsLocalMin.fderiv_eq_zero`：IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a
) : fderiv Real f a = 0
· 使用定理 `IsLocalMax.fderiv_eq_zero`：IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a
) : fderiv Real f a = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local extremum equals ze
ro.
-/
theorem IsLocalExtr.fderiv_eq_zero (h : IsLocalExtr f a) : fderiv ℝ f a = 0 :=
  h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero

end Module

/-!
### Fermat's Theorem
-/

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {a b : ℝ}

/-
**one_mem_posTangentConeAt_iff_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_mem_posTangentConeAt_iff_mem_closure : 1 in posTangentConeAt s a ↔ a i
n closure (Ioi a inter s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
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
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_const_lt`：Filter.Tendsto.eventually_const_lt {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Filter.Tendsto f l (𝓝 v))
 : forallᶠ a in l, u < f…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `pos_of_mul_pos_right`：pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < 
a * b) (ha : 0 <= a) : 0 < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mem_posTangentConeAt_of_frequently_mem`：mem_posTangentConeAt_of_frequent
ly_mem (h : existsᶠ t : Real in 𝓝[>] 0, x + t • y in s) : y in posTangentConeAt 
s x
（共 38 条，此处仅展示前 30 条）
-/
lemma one_mem_posTangentConeAt_iff_mem_closure :
    1 ∈ posTangentConeAt s a ↔ a ∈ closure (Ioi a ∩ s) := by
  constructor
  · intro h
    rcases exists_fun_of_mem_tangentConeAt h with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
    have : Tendsto (a + d ·) l (𝓝 a) := by
      simpa only [add_zero] using tendsto_const_nhds.add hd₀
    apply mem_closure_of_tendsto this
    filter_upwards [hcd.eventually_const_lt one_pos, hd] with n hcdn hdn
    refine ⟨?_, hdn⟩
    simpa using pos_of_mul_pos_right hcdn
  · intro h
    apply mem_posTangentConeAt_of_frequently_mem
    rw [mem_closure_iff_frequently, ← map_add_left_nhds_zero, frequently_map] at h
    simpa [nhdsWithin, frequently_inf_principal] using h
/-
**one_mem_posTangentConeAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_mem_posTangentConeAt_iff_frequently : 1 in posTangentConeAt s a ↔ exis
tsᶠ x in 𝓝[>] a, x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_mem_posTangentConeAt_iff_mem_closure`：one_mem_posTangentConeAt_iff_m
em_closure : 1 in posTangentConeAt s a ↔ a in closure (Ioi a inter s)
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `frequently_nhdsWithin_iff`：frequently_nhdsWithin_iff {z : α} {s : Set α}
 {p : α -> Prop} : (existsᶠ x in 𝓝[s] z, p x) ↔ existsᶠ x in 𝓝 z, p x ∧ x in s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_mem_posTangentConeAt_iff_frequently :
    1 ∈ posTangentConeAt s a ↔ ∃ᶠ x in 𝓝[>] a, x ∈ s := by
  rw [one_mem_posTangentConeAt_iff_mem_closure, mem_closure_iff_frequently,
    frequently_nhdsWithin_iff, inter_comm]
  simp_rw [mem_inter_iff]

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
/-
**IsLocalMin.hasDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a
) : f' = 0
参数：h : IsLocalMin f a；hf : HasDerivAt f f' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `IsLocalMin.hasFDerivAt_eq_zero`：IsLocalMin.hasFDerivAt_eq_zero (h : IsLo
calMin f a) (hf : HasFDerivAt f f' a) : f' = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasDerivAt_iff_hasFDerivAt`：hasDerivAt_iff_hasFDerivAt {f' : F} : HasDer
ivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local minimum equals zer
o.
-/
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using DFunLike.congr_fun (h.hasFDerivAt_eq_zero (hasDerivAt_iff_hasFDerivAt.1 hf)) 1

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
/-
**IsLocalMin.deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.deriv_eq_zero (h : IsLocalMin f a) : deriv f a = 0
参数：h : IsLocalMin f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMin.hasDerivAt_eq_zero`：IsLocalMin.hasDerivAt_eq_zero (h : IsLoca
lMin f a) (hf : HasDerivAt f f' a) : f' = 0
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local minimum equals zer
o.
-/
theorem IsLocalMin.deriv_eq_zero (h : IsLocalMin f a) : deriv f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
/-
**IsLocalMax.hasDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.hasDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a
) : f' = 0
参数：h : IsLocalMax f a；hf : HasDerivAt f f' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `IsLocalMin.hasDerivAt_eq_zero`：IsLocalMin.hasDerivAt_eq_zero (h : IsLoca
lMin f a) (hf : HasDerivAt f f' a) : f' = 0
· 使用定理 `IsLocalMax.neg`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : AddCommGroup β] [inst_2 : PartialOrder β]   [IsOrderedAddMonoid β] {f 
: α …
· 使用定理 `HasDerivAt.neg`：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f)
 (-f') x

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local maximum equals zer
o.
-/
theorem IsLocalMax.hasDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.hasDerivAt_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
/-
**IsLocalMax.deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.deriv_eq_zero (h : IsLocalMax f a) : deriv f a = 0
参数：h : IsLocalMax f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMax.hasDerivAt_eq_zero`：IsLocalMax.hasDerivAt_eq_zero (h : IsLoca
lMax f a) (hf : HasDerivAt f f' a) : f' = 0
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local maximum equals zer
o.
-/
theorem IsLocalMax.deriv_eq_zero (h : IsLocalMax f a) : deriv f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
/-
**IsLocalExtr.hasDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.hasDerivAt_eq_zero (h : IsLocalExtr f a) : HasDerivAt f f' a -
> f' = 0
参数：h : IsLocalExtr f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.elim`：IsLocalExtr.elim {p : Prop} : IsLocalExtr f a -> (IsLo
calMin f a -> p) -> (IsLocalMax f a -> p) -> p
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsLocalMin.hasDerivAt_eq_zero`：IsLocalMin.hasDerivAt_eq_zero (h : IsLoca
lMin f a) (hf : HasDerivAt f f' a) : f' = 0
· 使用定理 `IsLocalMax.hasDerivAt_eq_zero`：IsLocalMax.hasDerivAt_eq_zero (h : IsLoca
lMax f a) (hf : HasDerivAt f f' a) : f' = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local extremum equals ze
ro.
-/
theorem IsLocalExtr.hasDerivAt_eq_zero (h : IsLocalExtr f a) : HasDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.hasDerivAt_eq_zero IsLocalMax.hasDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
/-
**IsLocalExtr.deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f a) : deriv f a = 0
参数：h : IsLocalExtr f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.elim`：IsLocalExtr.elim {p : Prop} : IsLocalExtr f a -> (IsLo
calMin f a -> p) -> (IsLocalMax f a -> p) -> p
· 使用定理 `IsLocalMin.deriv_eq_zero`：IsLocalMin.deriv_eq_zero (h : IsLocalMin f a) 
: deriv f a = 0
· 使用定理 `IsLocalMax.deriv_eq_zero`：IsLocalMax.deriv_eq_zero (h : IsLocalMax f a) 
: deriv f a = 0

--- 原说明 ---
**Fermat's Theorem**: the derivative of a function at a local extremum equals ze
ro.
-/
theorem IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f a) : deriv f a = 0 :=
  h.elim IsLocalMin.deriv_eq_zero IsLocalMax.deriv_eq_zero

end Real

