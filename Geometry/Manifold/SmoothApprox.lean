/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Patrick Massot
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Approximation of continuous functions by smooth functions

In this file, we deduce from the existence of smooth partitions of unity that any continuous map
from a real σ-compact finite dimensional manifold `M` to a real normed space `F` can be
approximated uniformly by smooth functions.

More precisely, we strengthen this result in three ways :
* instead of a single number `ε > 0`, one may prescribe the precision of the approximation using
  an arbitrary continuous positive function `ε : M → ℝ`. This allows, for example, a control
  on the asymptotic behaviour of the approximation (e.g, choosing a precision `ε` which vanishes
  at infinity yields that continuous functions vanishing at infinity can be approximated by
  smooth functions vanishing at infinity).
* if the original map `f` already has the desired regularity on some neighborhood of a closed
  set `M`, one can choose an approximation which stays equal to `f` on `S`. This allows
  for some additional control in a setting with iterated approximations.
* finally, one may prescribe the approximation to vanish wherever the original function vanishes.
  For example, this shows that continuous functions supported on some compact set `K` may be
  approximated uniformly by smooth function supported on the **same** compact `K`.
  (Compare with arguments based on convolution where one needs to thicken `K` a bit).

## Main results

* `Continuous.exists_contMDiff_approx_and_eqOn`: approximating a continuous function `f : M → F`
  by a `C^n` function `g : M → E`, with precision prescribed by a continuous positive `ε : M → ℝ`,
  while ensuring that `support g ⊆ support f` and that `g` coincides with `f` on some closed set `S`
  in the neighborhood of which `f` is already `C^n`.
* `Continuous.exists_contMDiff_approx`: a simpler version of the previous result when one does not
  care about prescribing points with `g x = f x`. One still gets `support g ⊆ support f` for free,
  so we put it in the conclusion.
* `Continuous.exists_contDiff_approx_and_eqOn`, `Continuous.exists_contDiff_approx`: specializations
  of the previous results when `M = E` is a normed space.

## Implementation notes

With minor work, we could strengthen the statements in the following ways:
- the precision function `ε : M → ℝ` may be assumed `LowerSemicontinuous` instead of `Continuous`,
- the condition `support g ⊆ support f`, which translates to `∀ x, f x = 0 → g x = 0`,
  may be strengthened to `∀ x, f x = h x → g x = h x` for some arbitrary smooth `h : M → F`.

This file depends on the manifold library, which may be annoying if you only need the normed space
statements. **Please do not let this refrain you from using them** if they apply naturally in your
context: if this is too much of a problem, you should complain on Zulip, so that we get more data
about the need for a non-manifold version of `SmoothPartitionOfUnity`.

## TODO

- More generally, all results should apply to approximating continuous sections of a smooth
  vector bundle by smooth sections.
- If needed, specialize to `M = U` an open subset of a normed space `E`
  (we currently do `M = E` only).

-/

public section

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section

section Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {f : M → F} {ε : M → ℝ}

/-
**Continuous.exists_contMDiff_approx_and_eqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_contMDiff_approx_and_eqOn (n : Nat∞) (f_cont : Continuou
s f) (ε_cont : Continuous ε) (ε_pos : forall x, 0 < ε x) {S U : Set M} (hS : IsC
losed S) (hU : U in 𝓝ˢ S) (hfU : CMDiff[U] n f) : exists g : C^n⟮I, M; 𝓘(Real, F
), F⟯, (forall x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧ support g subseteq supp
ort f
参数：n : Nat∞；f_cont : Continuous f；ε_cont : Continuous ε；ε_pos : forall x, 0 < ε 
x；hS : IsClosed S；hU : U in 𝓝ˢ S；hfU : CMDiff[U] n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `Convex.setOfPred_const_imp`：Convex.setOfPred_const_imp {P : Prop} (hs : 
Convex 𝕜 s) : Convex 𝕜 {x | P -> x in s}
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `exists_contMDiffMap_forall_mem_convex_of_local`：exists_contMDiffMap_fora
ll_mem_convex_of_local (ht : forall x, Convex Real (t x)) (Hloc : forall x : M, 
exists U in 𝓝 x, exists g : M -> F, …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `ContinuousAt.eventually_lt`：∀ {α : Type u} {β : Type v} [inst : Topologi
calSpace α] [inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [in
st_3 : Topologic…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dist_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], dist 0 = norm
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 41 条，此处仅展示前 30 条）
-/
theorem Continuous.exists_contMDiff_approx_and_eqOn (n : ℕ∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : ∀ x, 0 < ε x)
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S) (hfU : CMDiff[U] n f) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯,
      (∀ x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧ support g ⊆ support f := by
  have dist_f_f : ∀ x, dist (f x) (f x) < ε x := by simpa only [dist_self] using ε_pos
  let t : M → Set F := fun x ↦ {y | dist y (f x) < ε x ∧ (x ∈ S → y = f x) ∧ (f x = 0 → y = 0)}
  suffices ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x by
    rcases this with ⟨g, hg⟩
    exact ⟨g, fun x ↦ (hg x).1, fun x ↦ (hg x).2.1, fun x ↦ mt (hg x).2.2⟩
  have t_conv (x) : Convex ℝ (t x) := (convex_ball (f x) (ε x)).inter <|
    (convex_singleton _).setOfPred_const_imp.inter (convex_singleton _).setOfPred_const_imp
  apply exists_contMDiffMap_forall_mem_convex_of_local I t_conv
  intro x
  by_cases hx : x ∈ S
  · refine ⟨U, mem_nhdsSet_iff_forall.mp hU x hx, ?_⟩
    exact ⟨f, hfU, fun y _ ↦ ⟨dist_f_f y, fun _ ↦ rfl, id⟩⟩
  · have : ∀ᶠ y in 𝓝 x, y ∉ S ∧ dist (f x) (f y) < ε y := (hS.isOpen_compl.eventually_mem hx).and
      ((continuous_const.dist f_cont).continuousAt.eventually_lt ε_cont.continuousAt (dist_f_f x))
    have : ∀ᶠ y in 𝓝 x, (y ∉ S ∧ dist (f x) (f y) < ε y) ∧ (f y = 0 → f x = 0) := by
      by_cases hx' : f x = 0
      · simpa [hx'] using this
      · simpa [hx'] using this.and (f_cont.continuousAt.eventually_ne hx')
    exact ⟨_, this, (fun _ ↦ f x), contMDiffOn_const, fun y hy ↦ ⟨hy.1.2, by simp [hy.1.1], hy.2⟩⟩
/-
**Continuous.exists_contMDiff_approx** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_contMDiff_approx (n : Nat∞) (f_cont : Continuous f) (ε_c
ont : Continuous ε) (ε_pos : forall x, 0 < ε x) : exists g : C^n⟮I, M; 𝓘(Real, F
), F⟯, (forall x, dist (g x) (f x) < ε x) ∧ support g subseteq support f
参数：n : Nat∞；f_cont : Continuous f；ε_cont : Continuous ε；ε_pos : forall x, 0 < ε 
x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_contMDiff_approx_and_eqOn`：Continuous.exists_contMDiff
_approx_and_eqOn (n : Nat∞) (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_p
os : forall x, 0 < ε x) {S U : Se…
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `mem_nhdsSet_empty`：mem_nhdsSet_empty : s in 𝓝ˢ (∅ : Set X)
· 使用定理 `contMDiffOn_empty`：contMDiffOn_empty : ContMDiffOn I I' n f ∅
-/
theorem Continuous.exists_contMDiff_approx (n : ℕ∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : ∀ x, 0 < ε x) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (∀ x, dist (g x) (f x) < ε x) ∧ support g ⊆ support f := by
  obtain ⟨g, g_approx, -, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn I n ε_cont ε_pos
    isClosed_empty mem_nhdsSet_empty contMDiffOn_empty
  exact ⟨g, g_approx, g_supp⟩

end Manifold

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {f : E → F} {ε : E → ℝ}

/-
**Continuous.exists_contDiff_approx_and_eqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_contDiff_approx_and_eqOn (n : Nat∞) (f_cont : Continuous
 f) (ε_cont : Continuous ε) (ε_pos : forall x, 0 < ε x) {S U : Set E} (hS : IsCl
osed S) (hU : U in 𝓝ˢ S) (hfU : ContDiffOn Real n f U) : exists g : E -> F, Cont
Diff Real n g ∧ (forall x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧ support g subs
eteq support f
参数：n : Nat∞；f_cont : Continuous f；ε_cont : Continuous ε；ε_pos : forall x, 0 < ε 
x；hS : IsClosed S；hU : U in 𝓝ˢ S；hfU : ContDiffOn Real n f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_contMDiff_approx_and_eqOn`：Continuous.exists_contMDiff
_approx_and_eqOn (n : Nat∞) (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_p
os : forall x, 0 < ε x) {S U : Se…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
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
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContDiffOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `ContMDiff.contDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…
· 使用定理 `ContMDiffMap.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
-/
theorem Continuous.exists_contDiff_approx_and_eqOn (n : ℕ∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : ∀ x, 0 < ε x)
    {S U : Set E} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S) (hfU : ContDiffOn ℝ n f U) :
    ∃ g : E → F, ContDiff ℝ n g ∧
      (∀ x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧ support g ⊆ support f := by
  obtain ⟨g, g_approx, g_eqOn, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn 𝓘(ℝ, E) n
    ε_cont ε_pos hS hU hfU.contMDiffOn
  exact ⟨g, g.contMDiff.contDiff, g_approx, g_eqOn, g_supp⟩
/-
**Continuous.exists_contDiff_approx** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_contDiff_approx (n : Nat∞) (f_cont : Continuous f) (ε_co
nt : Continuous ε) (ε_pos : forall x, 0 < ε x) : exists g : E -> F, ContDiff Rea
l n g ∧ (forall x, dist (g x) (f x) < ε x) ∧ support g subseteq support f
参数：n : Nat∞；f_cont : Continuous f；ε_cont : Continuous ε；ε_pos : forall x, 0 < ε 
x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_contDiff_approx_and_eqOn`：Continuous.exists_contDiff_a
pprox_and_eqOn (n : Nat∞) (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos
 : forall x, 0 < ε x) {S U : Set…
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `mem_nhdsSet_empty`：mem_nhdsSet_empty : s in 𝓝ˢ (∅ : Set X)
· 使用定理 `contDiffOn_empty`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E :
 Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type
 uF} […
-/
theorem Continuous.exists_contDiff_approx (n : ℕ∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : ∀ x, 0 < ε x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ (∀ x, dist (g x) (f x) < ε x) ∧ support g ⊆ support f := by
  obtain ⟨g, g_contDiff, g_approx, -, g_supp⟩ := f_cont.exists_contDiff_approx_and_eqOn n
    ε_cont ε_pos isClosed_empty mem_nhdsSet_empty contDiffOn_empty
  exact ⟨g, g_contDiff, g_approx, g_supp⟩

end NormedSpace

