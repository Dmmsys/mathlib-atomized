/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Differentiability of sum of functions

We prove some `HasSumUniformlyOn` versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions we also prove an `iteratedDerivWithin`
version.

-/

public section

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

section UniformlyOn

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

/-
**HasSumUniformlyOn.of_norm_le_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSumUniformlyOn.of_norm_le_summable {f : α -> β -> F} (hu : Summable u) 
{s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : HasSumUniformlyOn f (
fun x => ∑' n, f n x) s
参数：hu : Summable u；hfu : forall n x, x in s -> ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…
-/
theorem HasSumUniformlyOn.of_norm_le_summable {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]
/-
**HasSumUniformlyOn.of_norm_le_summable_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSumUniformlyOn.of_norm_le_summable_eventually {ι : Type*} {f : ι -> β -
> F} {u : ι -> Real} (hu : Summable u) {s : Set β} (hfu : forallᶠ n in cofinite,
 forall x in s, ‖f n x‖ <= u n) : HasSumUniformlyOn f (fun x => ∑' n, f n x) s
参数：hu : Summable u；hfu : forallᶠ n in cofinite, forall x in s, ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `tendstoUniformlyOn_tsum_of_cofinite_eventually`：tendstoUniformlyOn_tsum_
of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real} (hu : Summa
ble u) {s : Set β} (hfu : forallᶠ n …
-/
theorem HasSumUniformlyOn.of_norm_le_summable_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]
/-
**SummableLocallyUniformlyOn.of_locally_bounded_eventually** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：SummableLocallyUniformlyOn.of_locally_bounded_eventually [TopologicalSpace
 β] [LocallyCompactSpace β] {f : α -> β -> F} {s : Set β} (hs : IsOpen s) (hu : 
forall K subseteq s, IsCompact K -> exists u : α -> Real, Summable u ∧ forallᶠ n
 in cofinite, forall k in K, ‖f n k‖ <= u n) : SummableLocallyUniformlyOn f s
参数：hs : IsOpen s；hu : forall K subseteq s, IsCompact K -> exists u : α -> Real, 
Summable u ∧ forallᶠ n in cofinite, forall k in K, ‖f n k‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSumLocallyUniformlyOn.summableLocallyUniformlyOn`：∀ {α : Type u_1} {β
 : Type u_2} {ι : Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α}
 {s : Set β}   [inst_1 : UniformSpace α] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`：∀ {α : Type u_1}
 {β : Type u_2} {ι : Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β →
 α} {s : Set β}   [inst_1 : UniformSpace α] …
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_isCompact`：tendstoLocallyUniformlyO
n_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) : TendstoLocallyU
niformlyOn F f p s ↔ forall K, K sub…
· 使用定理 `tendstoUniformlyOn_tsum_of_cofinite_eventually`：tendstoUniformlyOn_tsum_
of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real} (hu : Summa
ble u) {s : Set β} (hfu : forallᶠ n …
-/
lemma SummableLocallyUniformlyOn.of_locally_bounded_eventually [TopologicalSpace β]
    [LocallyCompactSpace β] {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧
    ∀ᶠ n in cofinite, ∀ k ∈ K, ‖f n k‖ ≤ u n) : SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := fun x ↦ ∑' n, f n x)
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2
/-
**SummableLocallyUniformlyOn_of_locally_bounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [Locall
yCompactSpace β] {f : α -> β -> F} {s : Set β} (hs : IsOpen s) (hu : forall K su
bseteq s, IsCompact K -> exists u : α -> Real, Summable u ∧ forall n, forall k i
n K, ‖f n k‖ <= u n) : SummableLocallyUniformlyOn f s
参数：hs : IsOpen s；hu : forall K subseteq s, IsCompact K -> exists u : α -> Real, 
Summable u ∧ forall n, forall k in K, ‖f n k‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SummableLocallyUniformlyOn.of_locally_bounded_eventually`：SummableLocall
yUniformlyOn.of_locally_bounded_eventually [TopologicalSpace β] [LocallyCompactS
pace β] {f : α -> β -> F} {s : Set β} (hs : Is…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n, ∀ k ∈ K, ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact ⟨u, hu1, by filter_upwards using hu2⟩

end UniformlyOn

variable {ι 𝕜 F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set 𝕜}

/-- The `derivWithin` of a sum whose derivative is absolutely and uniformly convergent sum on an
open set `s` is the sum of the derivatives of sequence of functions on the open set `s` -/
/-
**derivWithin_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_tsum {f : ι -> 𝕜 -> F} (hs : IsOpen s) {x : 𝕜} (hx : x in s) (
hf : forall y in s, Summable fun n => f n y) (h : SummableLocallyUniformlyOn (fu
n n => (derivWithin (fun z => f n z) s)) s) (hf2 : forall n r, r in s -> Differe
ntiableAt 𝕜 (f n) r) : derivWithin (fun z => ∑' n, f n z) s x = ∑' n, derivWithi
n (f n) s x
参数：hs : IsOpen s；hx : x in s；hf : forall y in s, Summable fun n => f n y；h : Sum
mableLocallyUniformlyOn (fun n => (derivWithin (fun z => f n z) s)) s；hf2 : fora
ll n r, r in s -> DifferentiableAt 𝕜 (f n) r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `hasDerivAt_of_tendstoLocallyUniformlyOn`：hasDerivAt_of_tendstoLocallyUni
formlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s) (hf' : TendstoLocallyUniformlyOn 
f' g' l s) (hf : forallᶠ n in…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `TendstoLocallyUniformlyOn.congr_right`：TendstoLocallyUniformlyOn.congr_r
ight {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p s) (hg : s.EqOn f g) : T
endstoLocallyUniformlyOn F …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`：∀ {α : Type u_1}
 {β : Type u_2} {ι : Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β →
 α} {s : Set β}   [inst_1 : UniformSpace α] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSumLocallyUniformlyOn.tsum_eqOn`：∀ {α : Type u_1} {β : Type u_2} {ι :
 Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [i
nst_1 : UniformSpace α] …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.fun_sum`：HasDerivAt.fun_sum (h : forall i in u, HasDerivAt (A
 i) (A' i) x) : HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `IsOpen.uniqueDiffWithinAt`：IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs
 : x in s) : UniqueDiffWithinAt 𝕜 s x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R

--- 原说明 ---
The `derivWithin` of a sum whose derivative is absolutely and uniformly converge
nt sum on an
open set `s` is the sum of the derivatives of sequence of functions on the open 
set `s`
-/
theorem derivWithin_tsum {f : ι → 𝕜 → F} (hs : IsOpen s) {x : 𝕜} (hx : x ∈ s)
    (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt 𝕜 (f n) r) :
    derivWithin (fun z ↦ ∑' n, f n z) s x = ∑' n, derivWithin (f n) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ (hf y hy).hasSum) hx
    (f' := fun n : Finset ι ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ (hg.tsum_eqOn hb).symm
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq ↦ ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

/-- If a sequence of functions `fₙ` is such that `∑ fₙ (z)` is summable for each `z` in an
open set `s`, and for each `1 ≤ k ≤ m`, the series of `k`-th iterated derivatives
`∑ (iteratedDerivWithin k fₙ s) (z)`
is summable locally uniformly on `s`, and each `fₙ` is `m`-times differentiable, then the `m`-th
iterated derivative of the sum is the sum of the `m`-th iterated derivatives. -/
/-
**iteratedDerivWithin_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_tsum {f : ι -> 𝕜 -> F} (m : Nat) (hs : IsOpen s) {x : 
𝕜} (hx : x in s) (hsum : forall t in s, Summable (fun n : ι => f n t)) (h : fora
ll k, 1 <= k -> k <= m -> SummableLocallyUniformlyOn (fun n => (iteratedDerivWit
hin k (fun z => f n z) s)) s) (hf2 : forall n k r, k <= m -> r in s -> Different
iableAt 𝕜 (iteratedDerivWithin k (fun z => f n z) s) r) : iteratedDerivWithin m 
(fun z => ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x
参数：m : Nat；hs : IsOpen s；hx : x in s；hsum : forall t in s, Summable (fun n : ι =
> f n t)；h : forall k, 1 <= k -> k <= m -> SummableLocallyUniformlyOn (fun n => 
(iteratedDerivWithin k (fun z => f n z) s)) s；hf2 : forall n k r, k <= m -> r in
 s -> DifferentiableAt 𝕜 (iteratedDerivWithin k (fun z => f n z) s) r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_tsum`：derivWithin_tsum {f : ι -> 𝕜 -> F} (hs : IsOpen s) {x 
: 𝕜} (hx : x in s) (hf : forall y in s, Summable fun n => f n y) (h : SummableLo
callyU…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用定理 `SummableLocallyUniformlyOn.summable`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {x : β} {s : Set β}   [inst
_1 : UniformSpace α] [ins…
· 使用定理 `SummableLocallyUniformlyOn_congr`：∀ {α : Type u_1} {β : Type u_2} {ι : T
ype u_3} [inst : AddCommMonoid α] {s : Set β} [inst_1 : UniformSpace α]   [inst_
2 : TopologicalSpace β…
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x

--- 原说明 ---
If a sequence of functions `fₙ` is such that `∑ fₙ (z)` is summable for each `z`
 in an
open set `s`, and for each `1 ≤ k ≤ m`, the series of `k`-th iterated derivative
s
`∑ (iteratedDerivWithin k fₙ s) (z)`
is summable locally uniformly on `s`, and each `fₙ` is `m`-times differentiable,
 then the `m`-th
iterated derivative of the sum is the sum of the `m`-th iterated derivatives.
-/
theorem iteratedDerivWithin_tsum {f : ι → 𝕜 → F} (m : ℕ) (hs : IsOpen s)
    {x : 𝕜} (hx : x ∈ s) (hsum : ∀ t ∈ s, Summable (fun n : ι ↦ f n t))
    (h : ∀ k, 1 ≤ k → k ≤ m → SummableLocallyUniformlyOn
      (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, k ≤ m → r ∈ s →
      DifferentiableAt 𝕜 (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _ _ (fun n r hr ↦ hf2 n m r (by lia) hr)]
    · exact derivWithin_congr (fun t ht ↦ hm ht (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he)) (hm hx (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by lia) (by lia)).summable hr).congr (fun _ ↦ by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht ↦ by rw [iteratedDerivWithin_succ]) (h (m + 1) (by lia) (by lia))
