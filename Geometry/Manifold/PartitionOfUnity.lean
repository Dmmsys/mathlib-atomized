/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.MetricSpace.PartitionOfUnity
public import Mathlib.Topology.ShrinkingLemma

/-!
# Smooth partition of unity

In this file we define two structures, `SmoothBumpCovering` and `SmoothPartitionOfUnity`. Both
structures describe coverings of a set by a locally finite family of supports of smooth functions
with some additional properties. The former structure is mostly useful as an intermediate step in
the construction of a smooth partition of unity but some proofs that traditionally deal with a
partition of unity can use a `SmoothBumpCovering` as well.

Given a real manifold `M` and its subset `s`, a `SmoothBumpCovering ι I M s` is a collection of
`SmoothBumpFunction`s `f i` indexed by `i : ι` such that

* the center of each `f i` belongs to `s`;
* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, there exists `i : ι` such that `f i =ᶠ[𝓝 x] 1`.

In the same settings, a `SmoothPartitionOfUnity ι I M s` is a collection of smooth nonnegative
functions `f i : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, `i : ι`, such that

* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, the sum `∑ᶠ i, f i x` equals one;
* for each `x`, the sum `∑ᶠ i, f i x` is less than or equal to one.

We say that `f : SmoothBumpCovering ι I M s` is *subordinate* to a map `U : M → Set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finite-dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → Set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `SmoothBumpCovering ι I M s`
subordinate to `U`. Then we use this fact to prove a similar statement about smooth partitions of
unity, see `SmoothPartitionOfUnity.exists_isSubordinate`.

Finally, we use existence of a partition of unity to prove lemma
`exists_contMDiffMap_forall_mem_convex_of_local` that allows us to construct a globally defined
smooth function from local functions.

## TODO

* Build a framework to transfer local definitions to global using partition of unity and use it
  to define, e.g., the integral of a differential form over a manifold. Lemma
  `exists_contMDiffMap_forall_mem_convex_of_local` is a first step in this direction.

## Tags

smooth bump function, partition of unity
-/

@[expose] public section

universe uι uE uH uM uF

open Bundle Function Filter Module Set
open scoped Topology Manifold ContDiff

noncomputable section

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type uH}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M]

/-!
### Covering by supports of smooth bump functions

In this section we define `SmoothBumpCovering ι I M s` to be a collection of
`SmoothBumpFunction`s such that their supports are a locally finite family of sets and for each
`x ∈ s` some function `f i` from the collection is equal to `1` in a neighborhood of `x`. A covering
of this type is useful to construct a smooth partition of unity and can be used instead of a
partition of unity in some proofs.

We prove that on a smooth finite-dimensional real manifold with `σ`-compact Hausdorff topology, for
any `U : M → Set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `SmoothBumpCovering ι I M s`
subordinate to `U`. -/

variable (ι M)

/-- We say that a collection of `SmoothBumpFunction`s is a `SmoothBumpCovering` of a set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `fun i ↦ support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite-dimensional real manifold which is a `σ`-compact Hausdorff topological space,
then for every covering `U : M → Set M`, `∀ x, U x ∈ 𝓝 x`, there exists a `SmoothBumpCovering`
subordinate to `U`, see `SmoothBumpCovering.exists_isSubordinate`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
/-
**SmoothBumpCovering** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：SmoothBumpCovering [FiniteDimensional Real E] (s : Set M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a collection of `SmoothBumpFunction`s is a `SmoothBumpCovering` of a
 set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `fun i ↦ support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite-dimensional real manifold which is a `σ`-compact Hausdorff to
pological space,
then for every covering `U : M → Set M`, `∀ x, U x ∈ 𝓝 x`, there exists a `Smoot
hBumpCovering`
subordinate to `U`, see `SmoothBumpCovering.exists_isSubordinate`.

This covering can be used, e.g., to construct a partition of unity and to prove 
the weak
Whitney embedding theorem.
-/
structure SmoothBumpCovering [FiniteDimensional ℝ E] (s : Set M := univ) where
  /-- The center point of each bump in the smooth covering. -/
  c : ι → M
  /-- A smooth bump function around `c i`. -/
  toFun : ∀ i, SmoothBumpFunction I (c i)
  /-- All the bump functions in the covering are centered at points in `s`. -/
  c_mem' : ∀ i, c i ∈ s
  /-- Around each point, there are only finitely many nonzero bump functions in the family. -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- Around each point in `s`, one of the bump functions is equal to `1`. -/
  eventuallyEq_one' : ∀ x ∈ s, ∃ i, toFun i =ᶠ[𝓝 x] 1

/-- We say that a collection of functions form a smooth partition of unity on a set `s` if

* all functions are infinitely smooth and nonnegative;
* the family `fun i ↦ support (f i)` is locally finite;
* for all `x ∈ s` the sum `∑ᶠ i, f i x` equals one;
* for all `x`, the sum `∑ᶠ i, f i x` is less than or equal to one. -/
/-
**SmoothPartitionOfUnity** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：SmoothPartitionOfUnity (s : Set M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a collection of functions form a smooth partition of unity on a set 
`s` if

* all functions are infinitely smooth and nonnegative;
* the family `fun i ↦ support (f i)` is locally finite;
* for all `x ∈ s` the sum `∑ᶠ i, f i x` equals one;
* for all `x`, the sum `∑ᶠ i, f i x` is less than or equal to one.
-/
structure SmoothPartitionOfUnity (s : Set M := univ) where
  /-- The family of functions forming the partition of unity. -/
  toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
  /-- Around each point, there are only finitely many nonzero functions in the family. -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- All the functions in the partition of unity are nonnegative. -/
  nonneg' : ∀ i x, 0 ≤ toFun i x
  /-- The functions in the partition of unity add up to `1` at any point of `s`. -/
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  /-- The functions in the partition of unity add up to at most `1` everywhere. -/
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1

variable {ι I M}

namespace SmoothPartitionOfUnity

variable {s : Set M} (f : SmoothPartitionOfUnity ι I M s) {n : ℕ∞}

/-
**SmoothPartitionOfUnity.** 是 Mathlib 中的一个实例，位于命名空间 `SmoothPartitionOfUnity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : Set M} : FunLike (SmoothPartitionOfUnity ι I M s) ι C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**SmoothPartitionOfUnity.locallyFinite** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartitio
nOfUnity`。
形式化陈述：∀ {ι : Type uι} {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {H : Type uH}   [inst_2 : TopologicalSpace H] {I : ModelWithCorners
 ℝ E H} {M : Type uM} [inst_3 : TopologicalSpace M]   [inst_4 : ChartedSpace H M
] {s : Set M} (f : SmoothPartitionOfUnity ι I M s),   LocallyFinite fun i => Fun
ction.support ⇑(f i)
参数：f : SmoothPartitionOfUnity ι I M s；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.locallyFinite'`：∀ {ι : Type uι} {E : Type uE} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : 
TopologicalSpace H] {I : Mo…
-/
protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'
/-
**SmoothPartitionOfUnity.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartitionOfUnit
y`。
形式化陈述：nonneg (i : ι) (x : M) : 0 <= f i x
参数：i : ι；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.nonneg'`：∀ {ι : Type uι} {E : Type uE} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Topolog
icalSpace H] {I : Mo…
-/
theorem nonneg (i : ι) (x : M) : 0 ≤ f i x :=
  f.nonneg' i x
/-
**SmoothPartitionOfUnity.sum_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartitionOf
Unity`。
形式化陈述：sum_eq_one {x} (hx : x in s) : ∑ᶠ i, f i x = 1
参数：hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.sum_eq_one'`：∀ {ι : Type uι} {E : Type uE} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Top
ologicalSpace H] {I : Mo…
-/
theorem sum_eq_one {x} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx
/-
**SmoothPartitionOfUnity.exists_pos_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPart
itionOfUnity`。
形式化陈述：exists_pos_of_mem {x} (hx : x in s) : exists i, 0 < f i x
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SmoothPartitionOfUnity.nonneg`：nonneg (i : ι) (x : M) : 0 <= f i x
· 使用定理 `SmoothPartitionOfUnity.sum_eq_one`：sum_eq_one {x} (hx : x in s) : ∑ᶠ i, 
f i x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exists_pos_of_mem {x} (hx : x ∈ s) : ∃ i, 0 < f i x := by
  by_contra! h
  have H : ∀ i, f i x = 0 := fun i ↦ le_antisymm (h i) (f.nonneg i x)
  have := f.sum_eq_one hx
  simp_rw [H] at this
  simpa
/-
**SmoothPartitionOfUnity.sum_le_one** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartitionOf
Unity`。
形式化陈述：sum_le_one (x : M) : ∑ᶠ i, f i x <= 1
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.sum_le_one'`：∀ {ι : Type uι} {E : Type uE} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Top
ologicalSpace H] {I : Mo…
-/
theorem sum_le_one (x : M) : ∑ᶠ i, f i x ≤ 1 :=
  f.sum_le_one' x

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
@[simps]
/-
**SmoothPartitionOfUnity.toPartitionOfUnity** 是 Mathlib 中的一个定义，位于命名空间 `SmoothPar
titionOfUnity`。
形式化陈述：toPartitionOfUnity : PartitionOfUnity ι M s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.locallyFinite'`：∀ {ι : Type uι} {E : Type uE} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : 
TopologicalSpace H] {I : Mo…
· 使用定理 `SmoothPartitionOfUnity.nonneg'`：∀ {ι : Type uι} {E : Type uE} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Topolog
icalSpace H] {I : Mo…
· 使用定理 `SmoothPartitionOfUnity.sum_eq_one'`：∀ {ι : Type uι} {E : Type uE} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Top
ologicalSpace H] {I : Mo…
· 使用定理 `SmoothPartitionOfUnity.sum_le_one'`：∀ {ι : Type uι} {E : Type uE} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Top
ologicalSpace H] {I : Mo…

--- 原说明 ---
Reinterpret a smooth partition of unity as a continuous partition of unity.
-/
def toPartitionOfUnity : PartitionOfUnity ι M s :=
  { f with toFun := fun i => f i }
/-
**SmoothPartitionOfUnity.contMDiff_sum** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartitio
nOfUnity`。
形式化陈述：contMDiff_sum : CMDiff ∞ fun x => ∑ᶠ i, f i x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_finsum`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : NontriviallyNo
rmedField 𝕜] {n : WithTop ℕ∞} {H : Type u_3}   [inst_1 : TopologicalSpace H] {E 
: Type…
· 使用定理 `ContMDiffMap.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `SmoothPartitionOfUnity.locallyFinite`：∀ {ι : Type uι} {E : Type uE} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : T
opologicalSpace H] {I : Mo…
-/
theorem contMDiff_sum : CMDiff ∞ fun x => ∑ᶠ i, f i x :=
  contMDiff_finsum (fun i => (f i).contMDiff) f.locallyFinite
/-
**SmoothPartitionOfUnity.le_one** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartitionOfUnit
y`。
形式化陈述：le_one (i : ι) (x : M) : f i x <= 1
参数：i : ι；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.le_one`：le_one (i : ι) (x : X) : f i x <= 1
-/
theorem le_one (i : ι) (x : M) : f i x ≤ 1 :=
  f.toPartitionOfUnity.le_one i x
/-
**SmoothPartitionOfUnity.sum_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartitionOf
Unity`。
形式化陈述：sum_nonneg (x : M) : 0 <= ∑ᶠ i, f i x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.sum_nonneg`：sum_nonneg (x : X) : 0 <= ∑ᶠ i, f i x
-/
theorem sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x :=
  f.toPartitionOfUnity.sum_nonneg x
/-
**SmoothPartitionOfUnity.finsum_smul_mem_convex** 是 Mathlib 中的一个定理，位于命名空间 `Smoot
hPartitionOfUnity`。
形式化陈述：finsum_smul_mem_convex {g : ι -> M -> F} {t : Set F} {x : M} (hx : x in s)
 (hg : forall i, f i x != 0 -> g i x in t) (ht : Convex Real t) : ∑ᶠ i, f i x • 
g i x in t
参数：hx : x in s；hg : forall i, f i x != 0 -> g i x in t；ht : Convex Real t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.finsum_mem`：Convex.finsum_mem {ι : Sort*} {w : ι -> R} {z : ι -> 
E} {s : Set E} (hs : Convex R s) (h₀ : forall i, 0 <= w i) (h₁ : ∑ᶠ i, w i = 1) 
(hz : f…
· 使用定理 `SmoothPartitionOfUnity.nonneg`：nonneg (i : ι) (x : M) : 0 <= f i x
· 使用定理 `SmoothPartitionOfUnity.sum_eq_one`：sum_eq_one {x} (hx : x in s) : ∑ᶠ i, 
f i x = 1
-/
theorem finsum_smul_mem_convex {g : ι → M → F} {t : Set F} {x : M} (hx : x ∈ s)
    (hg : ∀ i, f i x ≠ 0 → g i x ∈ t) (ht : Convex ℝ t) : ∑ᶠ i, f i x • g i x ∈ t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg
/-
**SmoothPartitionOfUnity.contMDiff_smul** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartiti
onOfUnity`。
形式化陈述：contMDiff_smul {g : M -> F} {i} (hg : forall x in tsupport (f i), CMDiffAt
 n g x) : CMDiff n fun x => f i x • g x
参数：hg : forall x in tsupport (f i), CMDiffAt n g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_of_tsupport`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `ContMDiffAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H
 : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddC
ommGro…
· 使用定理 `instContMDiffSMulModelWithCornersSelf`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {n : WithTop…
· 使用定理 `ContMDiffAt.of_le`：ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le :
 m <= n) : ContMDiffAt I I' m f x
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `ContMDiffMap.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `tsupport_smul_subset_left`：tsupport_smul_subset_left {M α} [Zero M] [Zer
o α] [SMulWithZero M α] (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x
) subseteq tsup…
-/
theorem contMDiff_smul {g : M → F} {i} (hg : ∀ x ∈ tsupport (f i), CMDiffAt n g x) :
    CMDiff n fun x ↦ f i x • g x :=
  contMDiff_of_tsupport fun x hx =>
    ((f i).contMDiff.contMDiffAt.of_le (mod_cast le_top)).smul <| hg x
      <| tsupport_smul_subset_left _ _ hx

/-- If `f` is a smooth partition of unity on a set `s : Set M` and `g : ι → M → F` is a family of
functions such that `g i` is $C^n$ smooth at every point of the topological support of `f i`, then
the sum `fun x ↦ ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
/-
**SmoothPartitionOfUnity.contMDiff_finsum_smul** 是 Mathlib 中的一个定理，位于命名空间 `Smooth
PartitionOfUnity`。
形式化陈述：contMDiff_finsum_smul {g : ι -> M -> F} (hg : forall (i), forall x in tsup
port (f i), CMDiffAt n (g i) x) : CMDiff n fun x => ∑ᶠ i, f i x • g i x
参数：hg : forall (i), forall x in tsupport (f i), CMDiffAt n (g i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_finsum`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : NontriviallyNo
rmedField 𝕜] {n : WithTop ℕ∞} {H : Type u_3}   [inst_1 : TopologicalSpace H] {E 
: Type…
· 使用定理 `SmoothPartitionOfUnity.contMDiff_smul`：contMDiff_smul {g : M -> F} {i} (
hg : forall x in tsupport (f i), CMDiffAt n g x) : CMDiff n fun x => f i x • g x
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `SmoothPartitionOfUnity.locallyFinite`：∀ {ι : Type uι} {E : Type uE} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : T
opologicalSpace H] {I : Mo…
· 使用引理 `Function.support_smul_subset_left`：support_smul_subset_left [Zero R] [Ze
ro M] [SMulWithZero R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq su
pport f

--- 原说明 ---
If `f` is a smooth partition of unity on a set `s : Set M` and `g : ι → M → F` i
s a family of
functions such that `g i` is $C^n$ smooth at every point of the topological supp
ort of `f i`, then
the sum `fun x ↦ ∑ᶠ i, f i x • g i x` is smooth on the whole manifold.
-/
theorem contMDiff_finsum_smul {g : ι → M → F}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), CMDiffAt n (g i) x) :
    CMDiff n fun x ↦ ∑ᶠ i, f i x • g i x :=
(contMDiff_finsum fun i ↦ f.contMDiff_smul (hg i)) <|
f.locallyFinite.subset fun _ ↦ support_smul_subset_left _ _
/-
**SmoothPartitionOfUnity.contMDiffAt_finsum** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPar
titionOfUnity`。
形式化陈述：contMDiffAt_finsum {x₀ : M} {g : ι -> M -> F} (hφ : forall i, x₀ in tsuppo
rt (f i) -> CMDiffAt n (g i) x₀) : CMDiffAt n (fun x => ∑ᶠ i, f i x • g i x) x₀
参数：hφ : forall i, x₀ in tsupport (f i) -> CMDiffAt n (g i) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_finsum`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : Nontrivially
NormedField 𝕜] {n : WithTop ℕ∞} {H : Type u_3}   [inst_1 : TopologicalSpace H] {
E : Type…
· 使用定理 `LocallyFinite.smul_left`：LocallyFinite.smul_left [Zero R] [Zero M] [SMul
WithZero R M] {s : ι -> X -> R} (h : LocallyFinite fun i => support <| s i) (f :
 ι -> X -> M)…
· 使用定理 `SmoothPartitionOfUnity.locallyFinite`：∀ {ι : Type uι} {E : Type uE} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : T
opologicalSpace H] {I : Mo…
· 使用定理 `ContMDiffAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H
 : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddC
ommGro…
· 使用定理 `instContMDiffSMulModelWithCornersSelf`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {n : WithTop…
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `ContMDiffMap.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `contMDiffAt_of_notMem`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `tsupport_smul_subset_left`：tsupport_smul_subset_left {M α} [Zero M] [Zer
o α] [SMulWithZero M α] (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x
) subseteq tsup…
-/
theorem contMDiffAt_finsum {x₀ : M} {g : ι → M → F}
    (hφ : ∀ i, x₀ ∈ tsupport (f i) → CMDiffAt n (g i) x₀) :
    CMDiffAt n (fun x ↦ ∑ᶠ i, f i x • g i x) x₀ := by
  refine _root_.contMDiffAt_finsum (f.locallyFinite.smul_left _) fun i ↦ ?_
  by_cases hx : x₀ ∈ tsupport (f i)
  · exact ContMDiffAt.smul ((f i).contMDiff.of_le (mod_cast le_top)).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (f i) (g i)) hx) n
/-
**SmoothPartitionOfUnity.contDiffAt_finsum** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPart
itionOfUnity`。
形式化陈述：contDiffAt_finsum {s : Set E} (f : SmoothPartitionOfUnity ι 𝓘(Real, E) E s
) {x₀ : E} {g : ι -> E -> F} (hφ : forall i, x₀ in tsupport (f i) -> ContDiffAt 
Real n (g i) x₀) : ContDiffAt Real n (fun x => ∑ᶠ i, f i x • g i x) x₀
参数：f : SmoothPartitionOfUnity ι 𝓘(Real, E) E s；hφ : forall i, x₀ in tsupport (f 
i) -> ContDiffAt Real n (g i) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.contMDiffAt_finsum`：contMDiffAt_finsum {x₀ : M} {
g : ι -> M -> F} (hφ : forall i, x₀ in tsupport (f i) -> CMDiffAt n (g i) x₀) : 
CMDiffAt n (fun x => ∑ᶠ i, f i …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem contDiffAt_finsum {s : Set E} (f : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s) {x₀ : E}
    {g : ι → E → F} (hφ : ∀ i, x₀ ∈ tsupport (f i) → ContDiffAt ℝ n (g i) x₀) :
    ContDiffAt ℝ n (fun x ↦ ∑ᶠ i, f i x • g i x) x₀ := by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact f.contMDiffAt_finsum hφ

section finsupport

variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)

/-- The support of a smooth partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ support f i`, i.e. `f i x₀ ≠ 0`. -/
/-
**SmoothPartitionOfUnity.finsupport** 是 Mathlib 中的一个定义，位于命名空间 `SmoothPartitionOf
Unity`。
形式化陈述：finsupport : Finset ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a smooth partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ support f i`, i.e. `f i x₀ ≠ 0`.
-/
def finsupport : Finset ι := ρ.toPartitionOfUnity.finsupport x₀

@[simp]
/-
**SmoothPartitionOfUnity.mem_finsupport** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartiti
onOfUnity`。
形式化陈述：mem_finsupport {i : ι} : i in ρ.finsupport x₀ ↔ i in support fun i => ρ i 
x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.mem_finsupport`：mem_finsupport (x₀ : X) {i} : i in ρ.fi
nsupport x₀ ↔ i in support fun i => ρ i x₀
-/
theorem mem_finsupport {i : ι} : i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i ↦ ρ i x₀ :=
  ρ.toPartitionOfUnity.mem_finsupport x₀

@[simp]
/-
**SmoothPartitionOfUnity.coe_finsupport** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartiti
onOfUnity`。
形式化陈述：coe_finsupport : (ρ.finsupport x₀ : Set ι) = support fun i => ρ i x₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.coe_finsupport`：coe_finsupport (x₀ : X) : (ρ.finsupport
 x₀ : Set ι) = support fun i => ρ i x₀
-/
theorem coe_finsupport : (ρ.finsupport x₀ : Set ι) = support fun i ↦ ρ i x₀ :=
  ρ.toPartitionOfUnity.coe_finsupport x₀
/-
**SmoothPartitionOfUnity.sum_finsupport** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartiti
onOfUnity`。
形式化陈述：sum_finsupport (hx₀ : x₀ in s) : ∑ i in ρ.finsupport x₀, ρ i x₀ = 1
参数：hx₀ : x₀ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.sum_finsupport`：sum_finsupport (hx₀ : x₀ in s) : ∑ i in
 ρ.finsupport x₀, ρ i x₀ = 1
-/
theorem sum_finsupport (hx₀ : x₀ ∈ s) : ∑ i ∈ ρ.finsupport x₀, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport hx₀
/-
**SmoothPartitionOfUnity.sum_finsupport'** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartit
ionOfUnity`。
形式化陈述：sum_finsupport' (hx₀ : x₀ in s) {I : Finset ι} (hI : ρ.finsupport x₀ subse
teq I) : ∑ i in I, ρ i x₀ = 1
参数：hx₀ : x₀ in s；hI : ρ.finsupport x₀ subseteq I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.sum_finsupport'`：sum_finsupport' (hx₀ : x₀ in s) {I : F
inset ι} (hI : ρ.finsupport x₀ subseteq I) : ∑ i in I, ρ i x₀ = 1
-/
theorem sum_finsupport' (hx₀ : x₀ ∈ s) {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) :
    ∑ i ∈ I, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport' hx₀ hI
/-
**SmoothPartitionOfUnity.sum_finsupport_smul_eq_finsum** 是 Mathlib 中的一个定理，位于命名空间
 `SmoothPartitionOfUnity`。
形式化陈述：sum_finsupport_smul_eq_finsum {A : Type*} [AddCommGroup A] [Module Real A]
 (φ : ι -> M -> A) : ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ 
i x₀
参数：φ : ι -> M -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.sum_finsupport_smul_eq_finsum`：sum_finsupport_smul_eq_f
insum {M : Type*} [AddCommMonoid M] [Module Real M] (φ : ι -> X -> M) : ∑ i in ρ
.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ…
-/
theorem sum_finsupport_smul_eq_finsum {A : Type*} [AddCommGroup A] [Module ℝ A] (φ : ι → M → A) :
    ∑ i ∈ ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ :=
  ρ.toPartitionOfUnity.sum_finsupport_smul_eq_finsum φ

end finsupport

section fintsupport -- smooth partitions of unity have locally finite `tsupport`
variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)

/-- The `tsupport`s of a smooth partition of unity are locally finite. -/
/-
**SmoothPartitionOfUnity.finite_tsupport** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPartit
ionOfUnity`。
形式化陈述：finite_tsupport : {i | x₀ in tsupport (ρ i)}.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.finite_tsupport`：finite_tsupport : {i | x₀ in tsupport 
(ρ i)}.Finite

--- 原说明 ---
The `tsupport`s of a smooth partition of unity are locally finite.
-/
theorem finite_tsupport : {i | x₀ ∈ tsupport (ρ i)}.Finite :=
  ρ.toPartitionOfUnity.finite_tsupport _

/-- The tsupport of a partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ tsupport f i`. -/
/-
**SmoothPartitionOfUnity.fintsupport** 是 Mathlib 中的一个定义，位于命名空间 `SmoothPartitionO
fUnity`。
形式化陈述：fintsupport (x : M) : Finset ι
参数：x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.finite_tsupport`：finite_tsupport : {i | x₀ in tsu
pport (ρ i)}.Finite

--- 原说明 ---
The tsupport of a partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ tsupport f i`.
-/
def fintsupport (x : M) : Finset ι :=
  (ρ.finite_tsupport x).toFinset
/-
**SmoothPartitionOfUnity.mem_fintsupport_iff** 是 Mathlib 中的一个定理，位于命名空间 `SmoothPa
rtitionOfUnity`。
形式化陈述：mem_fintsupport_iff (i : ι) : i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `SmoothPartitionOfUnity.finite_tsupport`：finite_tsupport : {i | x₀ in tsu
pport (ρ i)}.Finite
-/
theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x₀ ↔ x₀ ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _
/-
**SmoothPartitionOfUnity.eventually_fintsupport_subset** 是 Mathlib 中的一个定理，位于命名空间
 `SmoothPartitionOfUnity`。
形式化陈述：eventually_fintsupport_subset : forallᶠ y in 𝓝 x₀, ρ.fintsupport y subsete
q ρ.fintsupport x₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.eventually_fintsupport_subset`：eventually_fintsupport_s
ubset : forallᶠ y in 𝓝 x₀, ρ.fintsupport y subseteq ρ.fintsupport x₀
-/
theorem eventually_fintsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.fintsupport y ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_fintsupport_subset _
/-
**SmoothPartitionOfUnity.finsupport_subset_fintsupport** 是 Mathlib 中的一个定理，位于命名空间
 `SmoothPartitionOfUnity`。
形式化陈述：finsupport_subset_fintsupport : ρ.finsupport x₀ subseteq ρ.fintsupport x₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.finsupport_subset_fintsupport`：finsupport_subset_fintsu
pport : ρ.finsupport x₀ subseteq ρ.fintsupport x₀
-/
theorem finsupport_subset_fintsupport : ρ.finsupport x₀ ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.finsupport_subset_fintsupport x₀
/-
**SmoothPartitionOfUnity.eventually_finsupport_subset** 是 Mathlib 中的一个定理，位于命名空间 
`SmoothPartitionOfUnity`。
形式化陈述：eventually_finsupport_subset : forallᶠ y in 𝓝 x₀, ρ.finsupport y subseteq 
ρ.fintsupport x₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.eventually_finsupport_subset`：eventually_finsupport_sub
set : forallᶠ y in 𝓝 x₀, ρ.finsupport y subseteq ρ.fintsupport x₀
-/
theorem eventually_finsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.finsupport y ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_finsupport_subset x₀

end fintsupport

section IsSubordinate

/-- A smooth partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
/-
**SmoothPartitionOfUnity.IsSubordinate** 是 Mathlib 中的一个定义，位于命名空间 `SmoothPartitio
nOfUnity`。
形式化陈述：IsSubordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι -> Set M)
参数：f : SmoothPartitionOfUnity ι I M s；U : ι -> Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A smooth partition of unity `f i` is subordinate to a family of sets `U i` index
ed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`.
-/
def IsSubordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) :=
  ∀ i, tsupport (f i) ⊆ U i

variable {f}
variable {U : ι → Set M}

@[simp]
/-
**SmoothPartitionOfUnity.isSubordinate_toPartitionOfUnity** 是 Mathlib 中的一个定理，位于命
名空间 `SmoothPartitionOfUnity`。
形式化陈述：isSubordinate_toPartitionOfUnity : f.toPartitionOfUnity.IsSubordinate U ↔ 
f.IsSubordinate U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSubordinate_toPartitionOfUnity :
    f.toPartitionOfUnity.IsSubordinate U ↔ f.IsSubordinate U :=
  Iff.rfl

alias ⟨_, IsSubordinate.toPartitionOfUnity⟩ := isSubordinate_toPartitionOfUnity

/-- If `f` is a smooth partition of unity on a set `s : Set M` subordinate to a family of open sets
`U : ι → Set M` and `g : ι → M → F` is a family of functions such that `g i` is $C^n$ smooth on
`U i`, then the sum `fun x ↦ ∑ᶠ i, f i x • g i x` is $C^n$ smooth on the whole manifold. -/
/-
**SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul** 是 Mathlib 中的一个定理，
位于命名空间 `SmoothPartitionOfUnity.IsSubordinate`。
形式化陈述：∀ {ι : Type uι} {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {F : Type uF}   [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpa
ce ℝ F] {H : Type uH} [inst_4 : TopologicalSpace H]   {I : ModelWithCorners ℝ E 
H} {M : Type uM} [inst_5 : TopologicalSpace M] [inst_6 : ChartedSpace H M] {s : 
Set M}   {f : SmoothPartitionOfUnity ι I M s} {n : ℕ∞} {U : ι → Set M} {g : ι → 
M → F},   f.IsSubordinate U →     (∀ (i : ι), IsOpen (U i)) →       (∀ (i : ι), 
ContMDiffOn I (modelWithCornersSelf ℝ F) (↑n) (g i) (U i)) →         ContMDiff I
 (modelWithCornersSelf ℝ F) ↑n fun x => ∑ᶠ (i : ι), (f i) x • g i x
参数：∀ (i : ι), IsOpen (U i)；∀ (i : ι), ContMDiffOn I (modelWithCornersSelf ℝ F) (
↑n) (g i) (U i)；modelWithCornersSelf ℝ F；i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.contMDiff_finsum_smul`：contMDiff_finsum_smul {g :
 ι -> M -> F} (hg : forall (i), forall x in tsupport (f i), CMDiffAt n (g i) x) 
: CMDiff n fun x => ∑ᶠ i, f i x • …
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If `f` is a smooth partition of unity on a set `s : Set M` subordinate to a fami
ly of open sets
`U : ι → Set M` and `g : ι → M → F` is a family of functions such that `g i` is 
$C^n$ smooth on
`U i`, then the sum `fun x ↦ ∑ᶠ i, f i x • g i x` is $C^n$ smooth on the whole m
anifold.
-/
theorem IsSubordinate.contMDiff_finsum_smul {g : ι → M → F} (hf : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (hg : ∀ i, CMDiff[U i] n (g i)) :
    CMDiff n fun x ↦ ∑ᶠ i, f i x • g i x :=
f.contMDiff_finsum_smul fun i _ hx ↦ (hg i).contMDiffAt <| (ho i).mem_nhds (hf i hx)

end IsSubordinate

end SmoothPartitionOfUnity

namespace BumpCovering

-- Repeat variables to drop `[FiniteDimensional ℝ E]` and `[IsManifold I ∞ M]`
/-
**BumpCovering.contMDiff_toPartitionOfUnity** 是 Mathlib 中的一个定理，位于命名空间 `BumpCover
ing`。
形式化陈述：contMDiff_toPartitionOfUnity {E : Type uE} [NormedAddCommGroup E] [NormedS
pace Real E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H} 
{M : Type uM} [TopologicalSpace M] [ChartedSpace H M] {s : Set M} (f : BumpCover
ing ι M s) (hf : forall i, CMDiff ∞ (f i)) (i : ι) : CMDiff ∞ (f.toPartitionOfUn
ity i)
参数：f : BumpCovering ι M s；hf : forall i, CMDiff ∞ (f i)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mul`：ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDif
f n (f * g)
· 使用定理 `instContMDiffMulOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [ins
t_2 : NormedAddCommGro…
· 使用定理 `ContMDiffRing.toContMDiffMul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `contMDiff_finprod_cond`：contMDiff_finprod_cond (hc : forall i, p i -> CM
Diff n (f i)) (hf : LocallyFinite fun i => mulSupport (f i)) : CMDiff n fun x =>
 ∏ᶠ (i) (_ :…
· 使用定理 `ContMDiff.sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : 
Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddComm
Gro…
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Function.mulSupport_one_sub`：mulSupport_one_sub [AddGroup R] (f : ι -> R
) : mulSupport (fun x => 1 - f x) = support f
· 使用定理 `BumpCovering.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topologi
calSpace X] {s : Set X} (f : BumpCovering ι X s),   LocallyFinite fun i => Funct
ion.support ⇑(f …
-/
theorem contMDiff_toPartitionOfUnity {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M] {s : Set M} (f : BumpCovering ι M s)
    (hf : ∀ i, CMDiff ∞ (f i)) (i : ι) : CMDiff ∞ (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ => contMDiff_const.sub (hf j)) <| by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

variable {s : Set M}

/-- A `BumpCovering` such that all functions in this covering are smooth generates a smooth
partition of unity.

In our formalization, not every `f : BumpCovering ι M s` with smooth functions `f i` is a
`SmoothBumpCovering`; instead, a `SmoothBumpCovering` is a covering by supports of
`SmoothBumpFunction`s. So, we define `BumpCovering.toSmoothPartitionOfUnity`, then reuse it
in `SmoothBumpCovering.toSmoothPartitionOfUnity`. -/
/-
**BumpCovering.toSmoothPartitionOfUnity** 是 Mathlib 中的一个定义，位于命名空间 `BumpCovering`
。
形式化陈述：toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : forall i, CMDiff ∞
 (f i)) : SmoothPartitionOfUnity ι I M s
参数：f : BumpCovering ι M s；hf : forall i, CMDiff ∞ (f i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.contMDiff_toPartitionOfUnity`：contMDiff_toPartitionOfUnity 
{E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E] {H : Type uH} [Topolog
icalSpace H] {I : ModelWithCorn…
· 使用定理 `PartitionOfUnity.locallyFinite'`：∀ {ι : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity 
ι X s), LocallyFinite…
· 使用定理 `PartitionOfUnity.nonneg'`：∀ {ι : Type u_1} {X : Type u_2} [inst : Topolo
gicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity ι X s),
 0 ≤ self.toFu…
· 使用定理 `PartitionOfUnity.sum_eq_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : To
pologicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity ι X
 s), ∀ x ∈ s, ∑ᶠ (…
· 使用定理 `PartitionOfUnity.sum_le_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : To
pologicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity ι X
 s) (x : X), ∑ᶠ (i…

--- 原说明 ---
A `BumpCovering` such that all functions in this covering are smooth generates a
 smooth
partition of unity.

In our formalization, not every `f : BumpCovering ι M s` with smooth functions `
f i` is a
`SmoothBumpCovering`; instead, a `SmoothBumpCovering` is a covering by supports 
of
`SmoothBumpFunction`s. So, we define `BumpCovering.toSmoothPartitionOfUnity`, th
en reuse it
in `SmoothBumpCovering.toSmoothPartitionOfUnity`.
-/
def toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, CMDiff ∞ (f i)) :
    SmoothPartitionOfUnity ι I M s :=
  { f.toPartitionOfUnity with
    toFun := fun i => ⟨f.toPartitionOfUnity i, f.contMDiff_toPartitionOfUnity hf i⟩ }

@[simp]
/-
**BumpCovering.toSmoothPartitionOfUnity_toPartitionOfUnity** 是 Mathlib 中的一个定理，位于
命名空间 `BumpCovering`。
形式化陈述：toSmoothPartitionOfUnity_toPartitionOfUnity (f : BumpCovering ι M s) (hf :
 forall i, CMDiff ∞ (f i)) : (f.toSmoothPartitionOfUnity hf).toPartitionOfUnity 
= f.toPartitionOfUnity
参数：f : BumpCovering ι M s；hf : forall i, CMDiff ∞ (f i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSmoothPartitionOfUnity_toPartitionOfUnity (f : BumpCovering ι M s)
    (hf : ∀ i, CMDiff ∞ (f i)) :
    (f.toSmoothPartitionOfUnity hf).toPartitionOfUnity = f.toPartitionOfUnity :=
  rfl

@[simp]
/-
**BumpCovering.coe_toSmoothPartitionOfUnity** 是 Mathlib 中的一个定理，位于命名空间 `BumpCover
ing`。
形式化陈述：coe_toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : forall i, CMDi
ff ∞ (f i)) (i : ι) : ⇑(f.toSmoothPartitionOfUnity hf i) = f.toPartitionOfUnity 
i
参数：f : BumpCovering ι M s；hf : forall i, CMDiff ∞ (f i)；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, CMDiff ∞ (f i))
    (i : ι) : ⇑(f.toSmoothPartitionOfUnity hf i) = f.toPartitionOfUnity i :=
  rfl
/-
**BumpCovering.IsSubordinate.toSmoothPartitionOfUnity** 是 Mathlib 中的一个定理，位于命名空间 
`BumpCovering.IsSubordinate`。
形式化陈述：∀ {ι : Type uι} {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {H : Type uH}   [inst_2 : TopologicalSpace H] {I : ModelWithCorners
 ℝ E H} {M : Type uM} [inst_3 : TopologicalSpace M]   [inst_4 : ChartedSpace H M
] {s : Set M} {f : BumpCovering ι M s} {U : ι → Set M},   f.IsSubordinate U →   
  ∀ (hf : ∀ (i : ι), ContMDiff I (modelWithCornersSelf ℝ ℝ) ↑⊤ ⇑(f i)),       (f
.toSmoothPartitionOfUnity hf).IsSubordinate U
参数：hf : ∀ (i : ι), ContMDiff I (modelWithCornersSelf ℝ ℝ) ↑⊤ ⇑(f i)；f.toSmoothPa
rtitionOfUnity hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.IsSubordinate.toPartitionOfUnity`：∀ {ι : Type u} {X : Type 
v} [inst : TopologicalSpace X] {s : Set X} {f : BumpCovering ι X s} {U : ι → Set
 X},   f.IsSubordinate U → f.toPart…
-/
theorem IsSubordinate.toSmoothPartitionOfUnity {f : BumpCovering ι M s} {U : ι → Set M}
    (h : f.IsSubordinate U) (hf : ∀ i, CMDiff ∞ (f i)) :
    (f.toSmoothPartitionOfUnity hf).IsSubordinate U :=
  h.toPartitionOfUnity

end BumpCovering

namespace SmoothBumpCovering

variable [FiniteDimensional ℝ E]
variable {s : Set M} {U : M → Set M} (fs : SmoothBumpCovering ι I M s)

/-
**SmoothBumpCovering.** 是 Mathlib 中的一个实例，位于命名空间 `SmoothBumpCovering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (SmoothBumpCovering ι I M s) fun x => ∀ i : ι, SmoothBumpFunction I (x.c i) :=
  ⟨toFun⟩

/--
We say that `f : SmoothBumpCovering ι I M s` is *subordinate* to a map `U : M → Set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
/-
**SmoothBumpCovering.IsSubordinate** 是 Mathlib 中的一个定义，位于命名空间 `SmoothBumpCovering
`。
形式化陈述：IsSubordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M -> Set M
)
参数：f : SmoothBumpCovering ι I M s；U : M -> Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `f : SmoothBumpCovering ι I M s` is *subordinate* to a map `U : M → 
Set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more gener
al than
being subordinate to an open covering of `M`, because we make no assumption abou
t the way `U x`
depends on `x`.
-/
def IsSubordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M → Set M) :=
  ∀ i, tsupport (f i) ⊆ U (f.c i)
/-
**SmoothBumpCovering.IsSubordinate.support_subset** 是 Mathlib 中的一个定理，位于命名空间 `Smo
othBumpCovering.IsSubordinate`。
形式化陈述：∀ {ι : Type uι} {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {H : Type uH}   [inst_2 : TopologicalSpace H] {I : ModelWithCorners
 ℝ E H} {M : Type uM} [inst_3 : TopologicalSpace M]   [inst_4 : ChartedSpace H M
] [inst_5 : FiniteDimensional ℝ E] {s : Set M} {fs : SmoothBumpCovering ι I M s}
   {U : M → Set M}, fs.IsSubordinate U → ∀ (i : ι), Function.support ↑(fs.toFun 
i) ⊆ U (fs.c i)
参数：i : ι；fs.toFun i；fs.c i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem IsSubordinate.support_subset {fs : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : fs.IsSubordinate U) (i : ι) : support (fs i) ⊆ U (fs.c i) :=
  Subset.trans subset_closure (h i)

variable (I) in
/-- Let `M` be a smooth manifold modelled on a finite-dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → Set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
/-
**SmoothBumpCovering.exists_isSubordinate** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpC
overing`。
形式化陈述：exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s) (
hU : forall x in s, U x in 𝓝 x) : exists (ι : Type uM) (f : SmoothBumpCovering ι
 I M s), f.IsSubordinate U
参数：hs : IsClosed s；hU : forall x in s, U x in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.locallyCompactSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ChartedSpace.locallyCompactSpace`：ChartedSpace.locallyCompactSpace [Loca
llyCompactSpace H] : LocallyCompactSpace M
· 使用定理 `SmoothBumpFunction.nhds_basis_support`：nhds_basis_support {s : Set M} (h
s : s in 𝓝 c) : (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => tsupport f sub
seteq s) fun f => support f
· 使用定理 `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`：refinement_
of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocallyCompactSpace X] [
SigmaCompactSpace X] [T2Space X] {ι : X -> Type u…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `exists_subset_iUnion_closed_subset`：exists_subset_iUnion_closed_subset (
hs : IsClosed s) (uo : forall i, IsOpen (u i)) (uf : forall x in s, { i | x in u
 i }.Finite) (us : s sub…
· 使用定理 `NormalSpace.of_paracompactSpace_r1Space`：∀ {X : Type v} [inst : Topologi
calSpace X] [R1Space X] [ParacompactSpace X], NormalSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `paracompact_of_locallyCompact_sigmaCompact`：∀ {X : Type v} [inst : Topol
ogicalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] [T2Space X], 
  ParacompactSpace X
· 使用定理 `SmoothBumpFunction.isOpen_support`：isOpen_support : IsOpen (support f)
· 使用定理 `LocallyFinite.point_finite`：point_finite (hf : LocallyFinite f) (x : X) 
: { b | x in f b }.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SmoothBumpFunction.support_updateRIn`：support_updateRIn {r : Real} (hr :
 r in Ioo 0 f.rOut) : support (f.updateRIn r hr) = support f
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `SmoothBumpFunction.eventuallyEq_one_of_dist_lt`：eventuallyEq_one_of_dist
_lt (hs : x in (chartAt H c).source) (hd : dist (extChartAt I c x) (extChartAt I
 c c) < f.rIn) : f =ᶠ[𝓝 x] 1
· 使用定理 `SmoothBumpFunction.support_subset_source`：support_subset_source : suppor
t f subseteq (chartAt H c).source
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SmoothBumpFunction.exists_r_pos_lt_subset_ball`：exists_r_pos_lt_subset_b
all {s : Set M} (hsc : IsClosed s) (hs : s subseteq support f) : exists r in Ioo
 0 f.rOut, s subseteq (chartAt H c).…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Let `M` be a smooth manifold modelled on a finite-dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a
 closed set
in `M` and `U : M → Set M` be a collection of sets such that `U x ∈ 𝓝 x` for eve
ry `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`.
-/
theorem exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s)
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ (ι : Type uM) (f : SmoothBumpCovering ι I M s), f.IsSubordinate U := by
  -- First we deduce some missing instances
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Next we choose a covering by supports of smooth bump functions
  have hB := fun x hx => SmoothBumpFunction.nhds_basis_support (I := I) (hU x hx)
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs hB with
    ⟨ι, c, f, hf, hsub', hfin⟩
  choose hcs hfU using hf
  -- Then we use the shrinking lemma to get a covering by smaller open
  rcases exists_subset_iUnion_closed_subset hs (fun i => (f i).isOpen_support)
    (fun x _ => hfin.point_finite x) hsub' with ⟨V, hsV, hVc, hVf⟩
  choose r hrR hr using fun i => (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i)
  refine ⟨ι, ⟨c, fun i => (f i).updateRIn (r i) (hrR i), hcs, ?_, fun x hx => ?_⟩, fun i => ?_⟩
  · simpa only [SmoothBumpFunction.support_updateRIn]
  · refine (mem_iUnion.1 <| hsV hx).imp fun i hi => ?_
    exact ((f i).updateRIn _ _).eventuallyEq_one_of_dist_lt
      ((f i).support_subset_source <| hVf _ hi) (hr i hi).2
  · simpa only [SmoothBumpFunction.support_updateRIn, tsupport] using hfU i
/-
**SmoothBumpCovering.locallyFinite** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpCovering
`。
形式化陈述：∀ {ι : Type uι} {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {H : Type uH}   [inst_2 : TopologicalSpace H] {I : ModelWithCorners
 ℝ E H} {M : Type uM} [inst_3 : TopologicalSpace M]   [inst_4 : ChartedSpace H M
] [inst_5 : FiniteDimensional ℝ E] {s : Set M} (fs : SmoothBumpCovering ι I M s)
,   LocallyFinite fun i => Function.support ↑(fs.toFun i)
参数：fs : SmoothBumpCovering ι I M s；fs.toFun i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpCovering.locallyFinite'`：∀ {ι : Type uι} {E : Type uE} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Topo
logicalSpace H] {I : Mo…
-/
protected theorem locallyFinite : LocallyFinite fun i => support (fs i) :=
  fs.locallyFinite'
/-
**SmoothBumpCovering.point_finite** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpCovering`
。
形式化陈述：∀ {ι : Type uι} {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {H : Type uH}   [inst_2 : TopologicalSpace H] {I : ModelWithCorners
 ℝ E H} {M : Type uM} [inst_3 : TopologicalSpace M]   [inst_4 : ChartedSpace H M
] [inst_5 : FiniteDimensional ℝ E] {s : Set M} (fs : SmoothBumpCovering ι I M s)
 (x : M),   {i | ↑(fs.toFun i) x ≠ 0}.Finite
参数：fs : SmoothBumpCovering ι I M s；x : M；fs.toFun i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.point_finite`：point_finite (hf : LocallyFinite f) (x : X) 
: { b | x in f b }.Finite
· 使用定理 `SmoothBumpCovering.locallyFinite`：∀ {ι : Type uι} {E : Type uE} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Topol
ogicalSpace H] {I : Mo…
-/
protected theorem point_finite (x : M) : {i | fs i x ≠ 0}.Finite :=
  fs.locallyFinite.point_finite x

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
/-
**SmoothBumpCovering.ind** 是 Mathlib 中的一个定义，位于命名空间 `SmoothBumpCovering`。
形式化陈述：ind (x : M) (hx : x in s) : ι
参数：x : M；hx : x in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpCovering.eventuallyEq_one'`：∀ {ι : Type uι} {E : Type uE} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : T
opologicalSpace H] {I : Mo…

--- 原说明 ---
Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`.
-/
def ind (x : M) (hx : x ∈ s) : ι :=
  (fs.eventuallyEq_one' x hx).choose
/-
**SmoothBumpCovering.eventuallyEq_one** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpCover
ing`。
形式化陈述：eventuallyEq_one (x : M) (hx : x in s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1
参数：x : M；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SmoothBumpCovering.eventuallyEq_one'`：∀ {ι : Type uι} {E : Type uE} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : T
opologicalSpace H] {I : Mo…
-/
theorem eventuallyEq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
  (fs.eventuallyEq_one' x hx).choose_spec
/-
**SmoothBumpCovering.apply_ind** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpCovering`。
形式化陈述：apply_ind (x : M) (hx : x in s) : fs (fs.ind x hx) x = 1
参数：x : M；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `SmoothBumpCovering.eventuallyEq_one`：eventuallyEq_one (x : M) (hx : x in
 s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1
-/
theorem apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
  (fs.eventuallyEq_one x hx).eq_of_nhds
/-
**SmoothBumpCovering.mem_support_ind** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpCoveri
ng`。
形式化陈述：mem_support_ind (x : M) (hx : x in s) : x in support (fs <| fs.ind x hx)
参数：x : M；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SmoothBumpCovering.apply_ind`：apply_ind (x : M) (hx : x in s) : fs (fs.i
nd x hx) x = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs <| fs.ind x hx) := by
  simp [fs.apply_ind x hx]
/-
**SmoothBumpCovering.mem_chartAt_source_of_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Smo
othBumpCovering`。
形式化陈述：mem_chartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) : x in (char
tAt H (fs.c i)).source
参数：h : fs i x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpFunction.support_subset_source`：support_subset_source : suppor
t f subseteq (chartAt H c).source
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mem_chartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (chartAt H (fs.c i)).source :=
  (fs i).support_subset_source <| by simp [h]
/-
**SmoothBumpCovering.mem_extChartAt_source_of_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `
SmoothBumpCovering`。
形式化陈述：mem_extChartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) : x in (e
xtChartAt I (fs.c i)).source
参数：h : fs i x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `SmoothBumpCovering.mem_chartAt_source_of_eq_one`：mem_chartAt_source_of_e
q_one {i : ι} {x : M} (h : fs i x = 1) : x in (chartAt H (fs.c i)).source
-/
theorem mem_extChartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (extChartAt I (fs.c i)).source := by
  rw [extChartAt_source]; exact fs.mem_chartAt_source_of_eq_one h
/-
**SmoothBumpCovering.mem_chartAt_ind_source** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBum
pCovering`。
形式化陈述：mem_chartAt_ind_source (x : M) (hx : x in s) : x in (chartAt H (fs.c (fs.i
nd x hx))).source
参数：x : M；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpCovering.mem_chartAt_source_of_eq_one`：mem_chartAt_source_of_e
q_one {i : ι} {x : M} (h : fs i x = 1) : x in (chartAt H (fs.c i)).source
· 使用定理 `SmoothBumpCovering.apply_ind`：apply_ind (x : M) (hx : x in s) : fs (fs.i
nd x hx) x = 1
-/
theorem mem_chartAt_ind_source (x : M) (hx : x ∈ s) : x ∈ (chartAt H (fs.c (fs.ind x hx))).source :=
  fs.mem_chartAt_source_of_eq_one (fs.apply_ind x hx)
/-
**SmoothBumpCovering.mem_extChartAt_ind_source** 是 Mathlib 中的一个定理，位于命名空间 `Smooth
BumpCovering`。
形式化陈述：mem_extChartAt_ind_source (x : M) (hx : x in s) : x in (extChartAt I (fs.c
 (fs.ind x hx))).source
参数：x : M；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpCovering.mem_extChartAt_source_of_eq_one`：mem_extChartAt_sourc
e_of_eq_one {i : ι} {x : M} (h : fs i x = 1) : x in (extChartAt I (fs.c i)).sour
ce
· 使用定理 `SmoothBumpCovering.apply_ind`：apply_ind (x : M) (hx : x in s) : fs (fs.i
nd x hx) x = 1
-/
theorem mem_extChartAt_ind_source (x : M) (hx : x ∈ s) :
    x ∈ (extChartAt I (fs.c (fs.ind x hx))).source :=
  fs.mem_extChartAt_source_of_eq_one (fs.apply_ind x hx)

/-- The index type of a `SmoothBumpCovering` of a compact manifold is finite. -/
@[instance_reducible]
/-
**SmoothBumpCovering.fintype** 是 Mathlib 中的一个定义，位于命名空间 `SmoothBumpCovering`。
形式化陈述：{ι : Type uι} →   {E : Type uE} →     [inst : NormedAddCommGroup E] →     
  [inst_1 : NormedSpace ℝ E] →         {H : Type uH} →           [inst_2 : Topol
ogicalSpace H] →             {I : ModelWithCorners ℝ E H} →               {M : T
ype uM} →                 [inst_3 : TopologicalSpace M] →                   [ins
t_4 : ChartedSpace H M] →                     [inst_5 : FiniteDimensional ℝ E] →
                       {s : Set M} → SmoothBumpCovering ι I M s → [CompactSpace 
M] → Fintype ι
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpCovering.locallyFinite`：∀ {ι : Type uι} {E : Type uE} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Topol
ogicalSpace H] {I : Mo…

--- 原说明 ---
The index type of a `SmoothBumpCovering` of a compact manifold is finite.
-/
protected def fintype [CompactSpace M] : Fintype ι :=
  fs.locallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support

variable [T2Space M]
variable [IsManifold I ∞ M]

/-- Reinterpret a `SmoothBumpCovering` as a continuous `BumpCovering`. Note that not every
`f : BumpCovering ι M s` with smooth functions `f i` is a `SmoothBumpCovering`. -/
/-
**SmoothBumpCovering.toBumpCovering** 是 Mathlib 中的一个定义，位于命名空间 `SmoothBumpCoverin
g`。
形式化陈述：toBumpCovering : BumpCovering ι M s where toFun i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpCovering.locallyFinite`：∀ {ι : Type uι} {E : Type uE} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : Topol
ogicalSpace H] {I : Mo…
· 使用定理 `SmoothBumpCovering.eventuallyEq_one'`：∀ {ι : Type uι} {E : Type uE} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : T
opologicalSpace H] {I : Mo…

--- 原说明 ---
Reinterpret a `SmoothBumpCovering` as a continuous `BumpCovering`. Note that not
 every
`f : BumpCovering ι M s` with smooth functions `f i` is a `SmoothBumpCovering`.
-/
def toBumpCovering : BumpCovering ι M s where
  toFun i := ⟨fs i, (fs i).continuous⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'

@[simp]
/-
**SmoothBumpCovering.isSubordinate_toBumpCovering** 是 Mathlib 中的一个定理，位于命名空间 `Smo
othBumpCovering`。
形式化陈述：isSubordinate_toBumpCovering {f : SmoothBumpCovering ι I M s} {U : M -> Se
t M} : (f.toBumpCovering.IsSubordinate fun i => U (f.c i)) ↔ f.IsSubordinate U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSubordinate_toBumpCovering {f : SmoothBumpCovering ι I M s} {U : M → Set M} :
    (f.toBumpCovering.IsSubordinate fun i => U (f.c i)) ↔ f.IsSubordinate U :=
  Iff.rfl

alias ⟨_, IsSubordinate.toBumpCovering⟩ := isSubordinate_toBumpCovering

/-- Every `SmoothBumpCovering` defines a smooth partition of unity. -/
/-
**SmoothBumpCovering.toSmoothPartitionOfUnity** 是 Mathlib 中的一个定义，位于命名空间 `SmoothB
umpCovering`。
形式化陈述：toSmoothPartitionOfUnity : SmoothPartitionOfUnity ι I M s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `SmoothBumpCovering` defines a smooth partition of unity.
-/
def toSmoothPartitionOfUnity : SmoothPartitionOfUnity ι I M s :=
  fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).contMDiff
/-
**SmoothBumpCovering.toSmoothPartitionOfUnity_apply** 是 Mathlib 中的一个定理，位于命名空间 `S
moothBumpCovering`。
形式化陈述：toSmoothPartitionOfUnity_apply (i : ι) (x : M) : fs.toSmoothPartitionOfUni
ty i x = fs i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - fs j x)
参数：i : ι；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSmoothPartitionOfUnity_apply (i : ι) (x : M) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - fs j x) :=
  rfl

open scoped Classical in
/-
**SmoothBumpCovering.toSmoothPartitionOfUnity_eq_mul_prod** 是 Mathlib 中的一个定理，位于命
名空间 `SmoothBumpCovering`。
形式化陈述：toSmoothPartitionOfUnity_eq_mul_prod (i : ι) (x : M) (t : Finset ι) (ht : 
forall j, WellOrderingRel j i -> fs j x != 0 -> j in t) : fs.toSmoothPartitionOf
Unity i x = fs i x * ∏ j in t with WellOrderingRel j i, (1 - fs j x)
参数：i : ι；x : M；t : Finset ι；ht : forall j, WellOrderingRel j i -> fs j x != 0 ->
 j in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.toPartitionOfUnity_eq_mul_prod`：toPartitionOfUnity_eq_mul_p
rod (i : ι) (x : X) (t : Finset ι) (ht : forall j, WellOrderingRel j i -> f j x 
!= 0 -> j in t) : f.toPartitionOf…
-/
theorem toSmoothPartitionOfUnity_eq_mul_prod (i : ι) (x : M) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → fs j x ≠ 0 → j ∈ t) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ j ∈ t with WellOrderingRel j i, (1 - fs j x) :=
  fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod i x t ht

open scoped Classical in
/-
**SmoothBumpCovering.exists_finset_toSmoothPartitionOfUnity_eventuallyEq** 是 Mat
hlib 中的一个定理，位于命名空间 `SmoothBumpCovering`。
形式化陈述：exists_finset_toSmoothPartitionOfUnity_eventuallyEq (i : ι) (x : M) : exis
ts t : Finset ι, fs.toSmoothPartitionOfUnity i =ᶠ[𝓝 x] fs i * ∏ j in t with Well
OrderingRel j i, ((1 : M -> Real) - fs j)
参数：i : ι；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.coe_prod`：coe_prod [CommMonoid β] [ContinuousMul β] {ι : T
ype*} (s : Finset ι) (f : ι -> C(α, β)) : ⇑(∏ i in s, f i) = ∏ i in s, (f i : α 
-> β)
· 使用定理 `BumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq`：exists_finse
t_toPartitionOfUnity_eventuallyEq (i : ι) (x : X) : exists t : Finset ι, f.toPar
titionOfUnity i =ᶠ[𝓝 x] f i * ∏ j in t with Well…
-/
theorem exists_finset_toSmoothPartitionOfUnity_eventuallyEq (i : ι) (x : M) :
    ∃ t : Finset ι,
      fs.toSmoothPartitionOfUnity i =ᶠ[𝓝 x]
        fs i * ∏ j ∈ t with WellOrderingRel j i, ((1 : M → ℝ) - fs j) := by
  simpa using! fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq i x
/-
**SmoothBumpCovering.toSmoothPartitionOfUnity_zero_of_zero** 是 Mathlib 中的一个定理，位于
命名空间 `SmoothBumpCovering`。
形式化陈述：toSmoothPartitionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) : f
s.toSmoothPartitionOfUnity i x = 0
参数：h : fs i x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.toPartitionOfUnity_zero_of_zero`：toPartitionOfUnity_zero_of
_zero {i : ι} {x : X} (h : f i x = 0) : f.toPartitionOfUnity i x = 0
-/
theorem toSmoothPartitionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
    fs.toSmoothPartitionOfUnity i x = 0 :=
  fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h
/-
**SmoothBumpCovering.support_toSmoothPartitionOfUnity_subset** 是 Mathlib 中的一个定理，
位于命名空间 `SmoothBumpCovering`。
形式化陈述：support_toSmoothPartitionOfUnity_subset (i : ι) : support (fs.toSmoothPart
itionOfUnity i) subseteq support (fs i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.support_toPartitionOfUnity_subset`：support_toPartitionOfUni
ty_subset (i : ι) : support (f.toPartitionOfUnity i) subseteq support (f i)
-/
theorem support_toSmoothPartitionOfUnity_subset (i : ι) :
    support (fs.toSmoothPartitionOfUnity i) ⊆ support (fs i) :=
  fs.toBumpCovering.support_toPartitionOfUnity_subset i
/-
**SmoothBumpCovering.IsSubordinate.toSmoothPartitionOfUnity** 是 Mathlib 中的一个定理，位
于命名空间 `SmoothBumpCovering.IsSubordinate`。
形式化陈述：∀ {ι : Type uι} {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {H : Type uH}   [inst_2 : TopologicalSpace H] {I : ModelWithCorners
 ℝ E H} {M : Type uM} [inst_3 : TopologicalSpace M]   [inst_4 : ChartedSpace H M
] [inst_5 : FiniteDimensional ℝ E] {s : Set M} [inst_6 : T2Space M]   [inst_7 : 
IsManifold I (↑⊤) M] {f : SmoothBumpCovering ι I M s} {U : M → Set M},   f.IsSub
ordinate U → f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i)
参数：↑⊤；f.c i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.IsSubordinate.toPartitionOfUnity`：∀ {ι : Type u} {X : Type 
v} [inst : TopologicalSpace X] {s : Set X} {f : BumpCovering ι X s} {U : ι → Set
 X},   f.IsSubordinate U → f.toPart…
· 使用定理 `SmoothBumpCovering.IsSubordinate.toBumpCovering`：∀ {ι : Type uι} {E : Ty
pe uE} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   
[inst_2 : TopologicalSpace H] {I : Mo…
-/
theorem IsSubordinate.toSmoothPartitionOfUnity {f : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : f.IsSubordinate U) : f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i) :=
  h.toBumpCovering.toPartitionOfUnity
/-
**SmoothBumpCovering.sum_toSmoothPartitionOfUnity_eq** 是 Mathlib 中的一个定理，位于命名空间 `
SmoothBumpCovering`。
形式化陈述：sum_toSmoothPartitionOfUnity_eq (x : M) : ∑ᶠ i, fs.toSmoothPartitionOfUnit
y i x = 1 - ∏ᶠ i, (1 - fs i x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.sum_toPartitionOfUnity_eq`：sum_toPartitionOfUnity_eq (x : X
) : ∑ᶠ i, f.toPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - f i x)
-/
theorem sum_toSmoothPartitionOfUnity_eq (x : M) :
    ∑ᶠ i, fs.toSmoothPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
  fs.toBumpCovering.sum_toPartitionOfUnity_eq x

end SmoothBumpCovering

variable (I)
variable [FiniteDimensional ℝ E]
variable [IsManifold I ∞ M] {n : ℕ∞}

/-- Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite-dimensional manifold,
there exists an infinitely smooth function that is equal to `0` on `s` and to `1` on `t`.
See also `exists_contMDiff_zero_iff_one_iff_of_isClosed`, which ensures additionally that
`f` is equal to `0` exactly on `s` and to `1` exactly on `t`. -/
/-
**exists_contMDiffMap_zero_one_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_contMDiffMap_zero_one_of_isClosed [T2Space M] [SigmaCompactSpace M]
 {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) : exists 
f : C^n⟮I, M; 𝓘(Real), Real⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc 0 1
参数：hs : IsClosed s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `SmoothBumpCovering.exists_isSubordinate`：exists_isSubordinate [T2Space M
] [SigmaCompactSpace M] (hs : IsClosed s) (hU : forall x in s, U x in 𝓝 x) : exi
sts (ι : Type uM) (f : Smooth…
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `SmoothPartitionOfUnity.contMDiff_sum`：contMDiff_sum : CMDiff ∞ fun x => 
∑ᶠ i, f i x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SmoothBumpCovering.toSmoothPartitionOfUnity_zero_of_zero`：toSmoothPartit
ionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) : fs.toSmoothPartitionO
fUnity i x = 0
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `SmoothBumpCovering.IsSubordinate.support_subset`：∀ {ι : Type uι} {E : Ty
pe uE} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   
[inst_2 : TopologicalSpace H] {I : Mo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SmoothPartitionOfUnity.sum_eq_one`：sum_eq_one {x} (hx : x in s) : ∑ᶠ i, 
f i x = 1
· 使用定理 `SmoothPartitionOfUnity.sum_nonneg`：sum_nonneg (x : M) : 0 <= ∑ᶠ i, f i x
· 使用定理 `SmoothPartitionOfUnity.sum_le_one`：sum_le_one (x : M) : ∑ᶠ i, f i x <= 1

--- 原说明 ---
Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite-dimensiona
l manifold,
there exists an infinitely smooth function that is equal to `0` on `s` and to `1
` on `t`.
See also `exists_contMDiff_zero_iff_one_iff_of_isClosed`, which ensures addition
ally that
`f` is equal to `0` exactly on `s` and to `1` exactly on `t`.
-/
theorem exists_contMDiffMap_zero_one_of_isClosed [T2Space M] [SigmaCompactSpace M] {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc 0 1 := by
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  set g := f.toSmoothPartitionOfUnity
  refine
    ⟨⟨_, g.contMDiff_sum.of_le (by simp)⟩, fun x hx => ?_, fun x => g.sum_eq_one, fun x =>
      ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  suffices ∀ i, g i x = 0 by simp only [this, ContMDiffMap.coeFn_mk, finsum_zero, Pi.zero_apply]
  refine fun i => f.toSmoothPartitionOfUnity_zero_of_zero ?_
  exact notMem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)

/-- Given two disjoint closed sets `s, t` in a Hausdorff normal σ-compact finite-dimensional
manifold `M`, there exists a smooth function `f : M → [0,1]` that vanishes in a neighbourhood of `s`
and is equal to `1` in a neighbourhood of `t`. -/
/-
**exists_contMDiffMap_zero_one_nhds_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_contMDiffMap_zero_one_nhds_of_isClosed [T2Space M] [NormalSpace M] 
[SigmaCompactSpace M] {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Di
sjoint s t) : exists f : C^n⟮I, M; 𝓘(Real), Real⟯, (forallᶠ x in 𝓝ˢ s, f x = 0) 
∧ (forallᶠ x in 𝓝ˢ t, f x = 1) ∧ forall x, f x in Icc 0 1
参数：hs : IsClosed s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `normal_exists_closure_subset`：normal_exists_closure_subset [NormalSpace 
X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t) (hst : s subseteq t) : exists
 u, IsOpen u ∧ s s…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_compl_iff_disjoint_left`：subset_compl_iff_disjoint_left : s s
ubseteq tᶜ ↔ Disjoint t s
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `exists_contMDiffMap_zero_one_of_isClosed`：exists_contMDiffMap_zero_one_o
f_isClosed [T2Space M] [SigmaCompactSpace M] {s t : Set M} (hs : IsClosed s) (ht
 : IsClosed t) (hd : Disjoint …
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
Given two disjoint closed sets `s, t` in a Hausdorff normal σ-compact finite-dim
ensional
manifold `M`, there exists a smooth function `f : M → [0,1]` that vanishes in a 
neighbourhood of `s`
and is equal to `1` in a neighbourhood of `t`.
-/
theorem exists_contMDiffMap_zero_one_nhds_of_isClosed
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfu, hfv, hf⟩ := exists_contMDiffMap_zero_one_of_isClosed I isClosed_closure
    isClosed_closure (subset_compl_iff_disjoint_left.mp hvu) (n := n)
  refine ⟨f, ?_, ?_, hf⟩
  · exact eventually_of_mem (mem_of_superset (u_op.mem_nhdsSet.mpr hsu) subset_closure) hfu
  · exact eventually_of_mem (mem_of_superset (v_op.mem_nhdsSet.mpr htv) subset_closure) hfv

/-- Given two sets `s, t` in a Hausdorff normal σ-compact finite-dimensional manifold `M`
with `s` open and `s ⊆ interior t`, there is a smooth function `f : M → [0,1]` which is equal to `s`
in a neighbourhood of `s` and has support contained in `t`. -/
/-
**exists_contMDiffMap_one_nhds_of_subset_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_contMDiffMap_one_nhds_of_subset_interior [T2Space M] [NormalSpace M
] [SigmaCompactSpace M] {s t : Set M} (hs : IsClosed s) (hd : s subseteq interio
r t) : exists f : C^n⟮I, M; 𝓘(Real), Real⟯, (forallᶠ x in 𝓝ˢ s, f x = 1) ∧ (fora
ll x ∉ t, f x = 0) ∧ forall x, f x in Icc 0 1
参数：hs : IsClosed s；hd : s subseteq interior t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_contMDiffMap_zero_one_nhds_of_isClosed`：exists_contMDiffMap_zero_
one_nhds_of_isClosed [T2Space M] [NormalSpace M] [SigmaCompactSpace M] {s t : Se
t M} (hs : IsClosed s) (ht : IsClos…
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.subset_compl_iff_disjoint_left`：subset_compl_iff_disjoint_left : s s
ubseteq tᶜ ↔ Disjoint t s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.Eventually.self_of_nhdsSet`：Filter.Eventually.self_of_nhdsSet {p 
: X -> Prop} (h : forallᶠ x in 𝓝ˢ s, p x) : forall x in s, p x
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
Given two sets `s, t` in a Hausdorff normal σ-compact finite-dimensional manifol
d `M`
with `s` open and `s ⊆ interior t`, there is a smooth function `f : M → [0,1]` w
hich is equal to `s`
in a neighbourhood of `s` and has support contained in `t`.
-/
theorem exists_contMDiffMap_one_nhds_of_subset_interior
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x ∉ t, f x = 0) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  rcases exists_contMDiffMap_zero_one_nhds_of_isClosed I isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) (n := n) with ⟨f, h0, h1, hf⟩
  refine ⟨f, h1, fun x hx ↦ ?_, hf⟩
  exact h0.self_of_nhdsSet _ fun hx' ↦ hx <| interior_subset hx'

namespace SmoothPartitionOfUnity

/-- A `SmoothPartitionOfUnity` that consists of a single function, uniformly equal to one,
defined as an example for `Inhabited` instance. -/
/-
**SmoothPartitionOfUnity.single** 是 Mathlib 中的一个定义，位于命名空间 `SmoothPartitionOfUnit
y`。
形式化陈述：single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s
参数：i : ι；s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SmoothPartitionOfUnity` that consists of a single function, uniformly equal t
o one,
defined as an example for `Inhabited` instance.
-/
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    classical
    rcases eq_or_ne j i with (rfl | h)
    · simp only [contMDiff_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
    · simp only [contMDiff_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h,
        ContinuousMap.coe_zero]
/-
**SmoothPartitionOfUnity.** 是 Mathlib 中的一个实例，位于命名空间 `SmoothPartitionOfUnity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited ι] (s : Set M) : Inhabited (SmoothPartitionOfUnity ι I M s) :=
  ⟨single I default s⟩

variable [T2Space M] [SigmaCompactSpace M]

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `SmoothPartitionOfUnity ι M s` that is subordinate to `U`. -/
/-
**SmoothPartitionOfUnity.exists_isSubordinate** 是 Mathlib 中的一个定理，位于命名空间 `SmoothP
artitionOfUnity`。
形式化陈述：exists_isSubordinate {s : Set M} (hs : IsClosed s) (U : ι -> Set M) (ho : 
forall i, IsOpen (U i)) (hU : s subseteq ⋃ i, U i) : exists f : SmoothPartitionO
fUnity ι I M s, f.IsSubordinate U
参数：hs : IsClosed s；U : ι -> Set M；ho : forall i, IsOpen (U i)；hU : s subseteq ⋃ 
i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.locallyCompactSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ChartedSpace.locallyCompactSpace`：ChartedSpace.locallyCompactSpace [Loca
llyCompactSpace H] : LocallyCompactSpace M
· 使用定理 `BumpCovering.exists_isSubordinate_of_prop`：exists_isSubordinate_of_prop 
[NormalSpace X] [ParacompactSpace X] (p : (X -> Real) -> Prop) (h01 : forall s t
, IsClosed s -> IsClosed t -> D…
· 使用定理 `NormalSpace.of_paracompactSpace_r1Space`：∀ {X : Type v} [inst : Topologi
calSpace X] [R1Space X] [ParacompactSpace X], NormalSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `paracompact_of_locallyCompact_sigmaCompact`：∀ {X : Type v} [inst : Topol
ogicalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] [T2Space X], 
  ParacompactSpace X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `exists_contMDiffMap_zero_one_of_isClosed`：exists_contMDiffMap_zero_one_o
f_isClosed [T2Space M] [SigmaCompactSpace M] {s t : Set M} (hs : IsClosed s) (ht
 : IsClosed t) (hd : Disjoint …
· 使用定理 `ContMDiffMap.instContinuousMapClass`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContMDiffMap.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `BumpCovering.IsSubordinate.toSmoothPartitionOfUnity`：∀ {ι : Type uι} {E 
: Type uE} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH
}   [inst_2 : TopologicalSpace H] {I : Mo…

--- 原说明 ---
If `X` is a paracompact normal topological space and `U` is an open covering of 
a closed set
`s`, then there exists a `SmoothPartitionOfUnity ι M s` that is subordinate to `
U`.
-/
theorem exists_isSubordinate {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) : ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- porting note(https://github.com/leanprover-community/batteries/issues/116):
  -- split `rcases` into `have` + `rcases`
  have := BumpCovering.exists_isSubordinate_of_prop (ContMDiff I 𝓘(ℝ) ∞) ?_ hs U ho hU
  · rcases this with ⟨f, hf, hfU⟩
    exact ⟨f.toSmoothPartitionOfUnity hf, hfU.toSmoothPartitionOfUnity hf⟩
  · intro s t hs ht hd
    rcases exists_contMDiffMap_zero_one_of_isClosed I hs ht hd with ⟨f, hf⟩
    exact ⟨f, f.contMDiff, hf⟩
/-
**SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source_of_isClosed** 是 Mat
hlib 中的一个定理，位于命名空间 `SmoothPartitionOfUnity`。
形式化陈述：exists_isSubordinate_chartAt_source_of_isClosed {s : Set M} (hs : IsClosed
 s) : exists f : SmoothPartitionOfUnity s I M s, f.IsSubordinate (fun x => (char
tAt H (x : M)).source)
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.exists_isSubordinate`：exists_isSubordinate {s : S
et M} (hs : IsClosed s) (U : ι -> Set M) (ho : forall i, IsOpen (U i)) (hU : s s
ubseteq ⋃ i, U i) : exists f : Sm…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem exists_isSubordinate_chartAt_source_of_isClosed {s : Set M} (hs : IsClosed s) :
    ∃ f : SmoothPartitionOfUnity s I M s,
      f.IsSubordinate (fun x ↦ (chartAt H (x : M)).source) := by
  apply exists_isSubordinate _ hs _ (fun i ↦ (chartAt H _).open_source) (fun x hx ↦ ?_)
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)

variable (M)
/-
**SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source** 是 Mathlib 中的一个定理，
位于命名空间 `SmoothPartitionOfUnity`。
形式化陈述：exists_isSubordinate_chartAt_source : exists f : SmoothPartitionOfUnity M 
I M univ, f.IsSubordinate (fun x => (chartAt H x).source)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.exists_isSubordinate`：exists_isSubordinate {s : S
et M} (hs : IsClosed s) (U : ι -> Set M) (ho : forall i, IsOpen (U i)) (hU : s s
ubseteq ⋃ i, U i) : exists f : Sm…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem exists_isSubordinate_chartAt_source :
    ∃ f : SmoothPartitionOfUnity M I M univ, f.IsSubordinate (fun x ↦ (chartAt H x).source) := by
  apply exists_isSubordinate _ isClosed_univ _ (fun i ↦ (chartAt H _).open_source) (fun x _ ↦ ?_)
  exact mem_iUnion_of_mem x (mem_chart_source H x)

end SmoothPartitionOfUnity

variable [SigmaCompactSpace M] [T2Space M] {t : M → Set F} {n : ℕ∞}

/-- Let `V` be a vector bundle over a σ-compact Hausdorff finite-dimensional topological manifold
`M`. Let `t : M → Set (V x)` be a family of convex sets in the fibers of `V`.
Suppose that for each point `x₀ : M` there exists a neighborhood `U_x₀` of `x₀` and a local
section `s_loc : M → V x` such that `s_loc` is $C^n$ smooth on `U_x₀` (when viewed as a map to
the total space of the bundle) and `s_loc y ∈ t y` for all `y ∈ U_x₀`.
Then there exists a global $C^n$ smooth section `s : Cₛ^n⟮I_M; F_fiber, V⟯` such that
`s x ∈ t x` for all `x : M`.
-/
/-
**exists_contMDiffSection_forall_mem_convex_of_local** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：exists_contMDiffSection_forall_mem_convex_of_local {F_fiber : Type*} [Norm
edAddCommGroup F_fiber] [NormedSpace Real F_fiber] (V : M -> Type*) [forall x, A
ddCommGroup (V x)] [forall x, TopologicalSpace (V x)] [forall x, Module Real (V 
x)] [TopologicalSpace (TotalSpace F_fiber V)] [FiberBundle F_fiber V] [VectorBun
dle Real F_fiber V] (t : forall x, Set (V x)) (ht_conv : forall x, Convex Real (
t x)) (Hloc : forall x₀ : M, exists U_x₀ in 𝓝 x₀, exists (s_loc : (x : M) -> V x
), (CMDiff[U_x₀] n (T% s_l
参数：V : M -> Type*；V x；V x；V x；TotalSpace F_fiber V；t : forall x, Set (V x)；ht_co
nv : forall x, Convex Real (t x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SmoothPartitionOfUnity.exists_isSubordinate`：exists_isSubordinate {s : S
et M} (hs : IsClosed s) (U : ι -> Set M) (ho : forall i, IsOpen (U i)) (hU : s s
ubseteq ⋃ i, U i) : exists f : Sm…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用引理 `ContMDiffOn.smul_section_of_tsupport`：ContMDiffOn.smul_section_of_tsuppo
rt {s : Π (x : M), V x} {ψ : M -> 𝕜} (hψ : CMDiff[u] n ψ) (ht : IsOpen u) (ht' :
 tsupport ψ subseteq u) (h…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `ContMDiffMap.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用引理 `ContMDiff.finsum_section_of_locallyFinite`：ContMDiff.finsum_section_of_l
ocallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0}) (ht' : forall i,
 CMDiff n (T% (t i ·))) : CMDif…
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `SmoothPartitionOfUnity.locallyFinite`：∀ {ι : Type uι} {E : Type uE} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH}   [inst_2 : T
opologicalSpace H] {I : Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] (
f : ι → M), Function.support f = {x | f x ≠ 0}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用引理 `left_ne_zero_of_smul`：left_ne_zero_of_smul : a • b != 0 -> a != 0
· 使用定理 `Convex.finsum_mem`：Convex.finsum_mem {ι : Sort*} {w : ι -> R} {z : ι -> 
E} {s : Set E} (hs : Convex R s) (h₀ : forall i, 0 <= w i) (h₁ : ∑ᶠ i, w i = 1) 
(hz : f…
· 使用定理 `SmoothPartitionOfUnity.nonneg`：nonneg (i : ι) (x : M) : 0 <= f i x
· 使用定理 `SmoothPartitionOfUnity.sum_eq_one`：sum_eq_one {x} (hx : x in s) : ∑ᶠ i, 
f i x = 1
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Let `V` be a vector bundle over a σ-compact Hausdorff finite-dimensional topolog
ical manifold
`M`. Let `t : M → Set (V x)` be a family of convex sets in the fibers of `V`.
Suppose that for each point `x₀ : M` there exists a neighborhood `U_x₀` of `x₀` 
and a local
section `s_loc : M → V x` such that `s_loc` is $C^n$ smooth on `U_x₀` (when view
ed as a map to
the total space of the bundle) and `s_loc y ∈ t y` for all `y ∈ U_x₀`.
Then there exists a global $C^n$ smooth section `s : Cₛ^n⟮I_M; F_fiber, V⟯` such
 that
`s x ∈ t x` for all `x : M`.
-/
theorem exists_contMDiffSection_forall_mem_convex_of_local
    {F_fiber : Type*} [NormedAddCommGroup F_fiber] [NormedSpace ℝ F_fiber]
    (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, Module ℝ (V x)]
    [TopologicalSpace (TotalSpace F_fiber V)] [FiberBundle F_fiber V] [VectorBundle ℝ F_fiber V]
    (t : ∀ x, Set (V x)) (ht_conv : ∀ x, Convex ℝ (t x))
    (Hloc :
      ∀ x₀ : M, ∃ U_x₀ ∈ 𝓝 x₀, ∃ (s_loc : (x : M) → V x),
        (CMDiff[U_x₀] n (T% s_loc)) ∧ (∀ y ∈ U_x₀, s_loc y ∈ t y)) :
    ∃ s : Cₛ^n⟮I; F_fiber, V⟯, ∀ x : M, s x ∈ t x := by
  choose W h_nhds s_loc s_smooth h_mem_t using Hloc
  -- Construct an open cover from the interiors of the given neighborhoods.
  let U (x : M) : Set M := interior (W x)
  have hU_covers_univ : univ ⊆ ⋃ x, U x := by
    intro x_pt _
    simp only [mem_iUnion]
    exact ⟨x_pt, mem_interior_iff_mem_nhds.mpr (h_nhds x_pt)⟩
  -- Obtain a smooth partition of unity subordinate to this open cover.
  obtain ⟨ρ, hρU⟩ : ∃ ρ : SmoothPartitionOfUnity M I M univ, ρ.IsSubordinate U :=
    SmoothPartitionOfUnity.exists_isSubordinate
      I isClosed_univ U (fun x ↦ isOpen_interior) hU_covers_univ
  -- Define the global section `s` by taking a weighted sum of the local sections.
  let s x : V x := ∑ᶠ j, (ρ j x) • s_loc j x
  -- Prove that `s`, when viewed as a map to the total space, is smooth.
  have (j : M) : CMDiff n (T% (fun x ↦ (ρ j x) • (s_loc j x))) := by
    refine ContMDiffOn.smul_section_of_tsupport ?_ isOpen_interior (hρU j)
      ((s_smooth j).mono interior_subset)
    exact ((ρ j).contMDiff).of_le (sup_eq_left.mp rfl) |>.contMDiffOn
  have hs : CMDiff n (T% s) := by
    apply ContMDiff.finsum_section_of_locallyFinite ?_ this
    -- Future: can grind do this?
    apply ρ.locallyFinite.subset fun i x hx ↦ ?_
    rw [support]
    rw [mem_ofPred_eq] at hx ⊢
    exact left_ne_zero_of_smul hx
  -- Construct the smooth section and prove it lies in the convex sets `t x`.
  refine ⟨⟨s, hs⟩, fun x ↦ ?_⟩
  apply (ht_conv x).finsum_mem (ρ.nonneg · x) (ρ.sum_eq_one (mem_univ x))
  intro j h_ρjx_ne_zero
  have h_x_in_tsupport_ρj : x ∈ tsupport (ρ j) := subset_closure (mem_support.mpr h_ρjx_ne_zero)
  have h_x_in_Umap_j : x ∈ W j := interior_subset (hρU j h_x_in_tsupport_ρj)
  exact h_mem_t j x h_x_in_Umap_j

/-- Let `M` be a σ-compact Hausdorff finite-dimensional topological manifold. Let `t : M → Set F`
be a family of convex sets. Suppose that for each point `x : M` there exists a neighborhood
`U ∈ 𝓝 x` and a function `g : M → F` such that `g` is $C^n$ smooth on `U` and `g y ∈ t y` for all
`y ∈ U`. Then there exists a $C^n$ smooth function `g : C^n⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x`
for all `x`.

This is a special case of `exists_contMDiffSection_forall_mem_convex_of_local` where `V` is the
trivial bundle. See also `exists_contMDiffMap_mem_convex_of_local_const`. -/
/-
**exists_contMDiffMap_forall_mem_convex_of_local** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_contMDiffMap_forall_mem_convex_of_local (ht : forall x, Convex Real
 (t x)) (Hloc : forall x : M, exists U in 𝓝 x, exists g : M -> F, CMDiff[U] n g 
∧ forall y in U, g y in t y) : exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, forall x, g 
x in t x
参数：ht : forall x, Convex Real (t x)；Hloc : forall x : M, exists U in 𝓝 x, exists
 g : M -> F, CMDiff[U] n g ∧ forall y in U, g y in t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_contMDiffSection_forall_mem_convex_of_local`：exists_contMDiffSect
ion_forall_mem_convex_of_local {F_fiber : Type*} [NormedAddCommGroup F_fiber] [N
ormedSpace Real F_fiber] (V : M -> Type*…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.contMDiffWithinAt_section`：contMDiffWithinAt_section {s : forall 
x, E x} {a : Set B} {x₀ : B} : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x =
> TotalSpace.mk' F x (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.contMDiffAt_section`：contMDiffAt_section {s : forall x, E x} (x₀ 
: B) : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀
 ↔ ContMDiffAt I…
· 使用定理 `ContMDiffSection.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…

--- 原说明 ---
Let `M` be a σ-compact Hausdorff finite-dimensional topological manifold. Let `t
 : M → Set F`
be a family of convex sets. Suppose that for each point `x : M` there exists a n
eighborhood
`U ∈ 𝓝 x` and a function `g : M → F` such that `g` is $C^n$ smooth on `U` and `g
 y ∈ t y` for all
`y ∈ U`. Then there exists a $C^n$ smooth function `g : C^n⟮I, M; 𝓘(ℝ, F), F⟯` s
uch that `g x ∈ t x`
for all `x`.

This is a special case of `exists_contMDiffSection_forall_mem_convex_of_local` w
here `V` is the
trivial bundle. See also `exists_contMDiffMap_mem_convex_of_local_const`.
-/
theorem exists_contMDiffMap_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, CMDiff[U] n g ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  let ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (fun _ ↦ F) t ht
    (fun x₀ ↦ let ⟨U, hU, g, hgs, hgt⟩ := Hloc x₀
      ⟨U, hU, g, fun y hy ↦ Bundle.contMDiffWithinAt_section |>.mpr <| hgs y hy, hgt⟩)
  ⟨⟨s, (Bundle.contMDiffAt_section _ |>.mp <| s.contMDiff ·)⟩, hs⟩

/-- Let `M` be a σ-compact Hausdorff finite-dimensional topological manifold. Let `t : M → Set F` be
a family of convex sets. Suppose that for each point `x : M` there exists a vector `c : F` such that
for all `y` in a neighborhood of `x` we have `c ∈ t y`. Then there exists a smooth function
`g : C^n⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x` for all `x`. See also
`exists_contMDiffMap_forall_mem_convex_of_local`. -/
/-
**exists_contMDiffMap_forall_mem_convex_of_local_const** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：exists_contMDiffMap_forall_mem_convex_of_local_const (ht : forall x, Conve
x Real (t x)) (Hloc : forall x : M, exists c : F, forallᶠ y in 𝓝 x, c in t y) : 
exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, forall x, g x in t x
参数：ht : forall x, Convex Real (t x)；Hloc : forall x : M, exists c : F, forallᶠ y
 in 𝓝 x, c in t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_contMDiffMap_forall_mem_convex_of_local`：exists_contMDiffMap_fora
ll_mem_convex_of_local (ht : forall x, Convex Real (t x)) (Hloc : forall x : M, 
exists U in 𝓝 x, exists g : M -> F, …
· 使用定理 `contMDiffOn_const`：contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => 
c) s

--- 原说明 ---
Let `M` be a σ-compact Hausdorff finite-dimensional topological manifold. Let `t
 : M → Set F` be
a family of convex sets. Suppose that for each point `x : M` there exists a vect
or `c : F` such that
for all `y` in a neighborhood of `x` we have `c ∈ t y`. Then there exists a smoo
th function
`g : C^n⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x` for all `x`. See also
`exists_contMDiffMap_forall_mem_convex_of_local`.
-/
theorem exists_contMDiffMap_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ c : F, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  exists_contMDiffMap_forall_mem_convex_of_local I ht fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, contMDiffOn_const, fun _ => id⟩

/-- Let `M` be a smooth σ-compact manifold with extended distance. Let `K : ι → Set M` be a locally
finite family of closed sets, let `U : ι → Set M` be a family of open sets such that `K i ⊆ U i` for
all `i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and
`x ∈ K i`, we have `Metric.closedEBall x (δ x) ⊆ U i`. -/
/-
**Metric.exists_contMDiffMap_forall_closedEBall_subset** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Metric.exists_contMDiffMap_forall_closedEBall_subset {M : Type*} [EMetricS
pace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι -> Se
t M} {U : ι -> Set M} (hK : forall i, IsClosed (K i)) (hU : forall i, IsOpen (U 
i)) (hKU : forall i, K i subseteq U i) (hfin : LocallyFinite K) : exists δ : C^n
⟮I, M; 𝓘(Real, Real), Real⟯, (forall x, 0 < δ x) ∧ forall i, forall x in K i, Me
tric.closedEBall x (ENNReal.ofReal (δ x)) subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_contMDiffMap_forall_mem_convex_of_local_const`：exists_contMDiffMa
p_forall_mem_convex_of_local_const (ht : forall x, Convex Real (t x)) (Hloc : fo
rall x : M, exists c : F, forallᶠ y in 𝓝 x…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Metric.exists_forall_closedEBall_subset_aux₂`：exists_forall_closedEBall_
subset_aux₂ (y : X) : Convex Real (Ioi (0 : Real) inter ENNReal.ofReal ⁻¹' ⋂ (i)
 (_ : y in K i), { r | closedEBall…
· 使用定理 `Metric.exists_forall_closedEBall_subset_aux₁`：exists_forall_closedEBall_
subset_aux₁ (hK : forall i, IsClosed (K i)) (hU : forall i, IsOpen (U i)) (hKU :
 forall i, K i subseteq U i) (hfin…

--- 原说明 ---
Let `M` be a smooth σ-compact manifold with extended distance. Let `K : ι → Set 
M` be a locally
finite family of closed sets, let `U : ι → Set M` be a family of open sets such 
that `K i ⊆ U i` for
all `i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that fo
r any `i` and
`x ∈ K i`, we have `Metric.closedEBall x (δ x) ⊆ U i`.
-/
theorem Metric.exists_contMDiffMap_forall_closedEBall_subset
    {M : Type*} [EMetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^n⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ i, ∀ x ∈ K i, Metric.closedEBall x (ENNReal.ofReal (δ x)) ⊆ U i := by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_comm ι M]
    using! exists_contMDiffMap_forall_mem_convex_of_local_const I
      Metric.exists_forall_closedEBall_subset_aux₂
      (Metric.exists_forall_closedEBall_subset_aux₁ hK hU hKU hfin)

@[deprecated (since := "2026-01-24")]
alias Emetric.exists_contMDiffMap_forall_closedBall_subset :=
  Metric.exists_contMDiffMap_forall_closedEBall_subset

/-- Let `M` be a smooth σ-compact manifold with a metric. Let `K : ι → Set M` be a locally finite
family of closed sets, let `U : ι → Set M` be a family of open sets such that `K i ⊆ U i` for all
`i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and `x ∈ K i`,
we have `Metric.closedBall x (δ x) ⊆ U i`. -/
/-
**Metric.exists_contMDiffMap_forall_closedBall_subset** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Metric.exists_contMDiffMap_forall_closedBall_subset {M : Type*} [MetricSpa
ce M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι -> Set 
M} {U : ι -> Set M} (hK : forall i, IsClosed (K i)) (hU : forall i, IsOpen (U i)
) (hKU : forall i, K i subseteq U i) (hfin : LocallyFinite K) : exists δ : C^n⟮I
, M; 𝓘(Real, Real), Real⟯, (forall x, 0 < δ x) ∧ forall i, forall x in K i, Metr
ic.closedBall x (δ x) subseteq U i
参数：hK : forall i, IsClosed (K i)；hU : forall i, IsOpen (U i)；hKU : forall i, K i
 subseteq U i；hfin : LocallyFinite K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_contMDiffMap_forall_closedEBall_subset`：Metric.exists_cont
MDiffMap_forall_closedEBall_subset {M : Type*} [EMetricSpace M] [ChartedSpace H 
M] [IsManifold I ∞ M] [SigmaCompactSpace M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedEBall_ofReal`：Metric.closedEBall_ofReal {x : α} {ε : Real} 
(h : 0 <= ε) : closedEBall x (.ofReal ε) = closedBall x ε
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Let `M` be a smooth σ-compact manifold with a metric. Let `K : ι → Set M` be a l
ocally finite
family of closed sets, let `U : ι → Set M` be a family of open sets such that `K
 i ⊆ U i` for all
`i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for an
y `i` and `x ∈ K i`,
we have `Metric.closedBall x (δ x) ⊆ U i`.
-/
theorem Metric.exists_contMDiffMap_forall_closedBall_subset
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^n⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ i, ∀ x ∈ K i, Metric.closedBall x (δ x) ⊆ U i := by
  rcases Metric.exists_contMDiffMap_forall_closedEBall_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.closedEBall_ofReal (hδ0 _).le]
  exact hδ i x hx
/-
**IsOpen.exists_contMDiff_support_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.exists_contMDiff_support_eq_aux {s : Set H} (hs : IsOpen s) : exist
s f : H -> Real, f.support = s ∧ CMDiff n f ∧ Set.range f subseteq Set.Icc 0 1
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `IsOpen.exists_contDiff_support_eq`：IsOpen.exists_contDiff_support_eq {n 
: Nat∞} {s : Set E} (hs : IsOpen s) : exists f : E -> Real, f.support = s ∧ Cont
Diff Real n f ∧ Set.ran…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support_comp_eq_preimage`：∀ {ι : Type u_1} {κ : Type u_2} {M : 
Type u_3} [inst : Zero M] (g : κ → M) (f : ι → κ),   Function.support (g ∘ f) = 
f ⁻¹' Function.support …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.symm_comp_self`：symm_comp_self : I.symm ∘ I = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiff.comp_contMDiff`：ContDiff.comp_contMDiff {g : F -> F'} {f : M ->
 F} (hg : ContDiff 𝕜 n g) (hf : ContMDiff I 𝓘(𝕜, F) n f) : ContMDiff I 𝓘(𝕜, F') 
n (g ∘ f)
· 使用定理 `ModelWithCorners.contMDiff`：ModelWithCorners.contMDiff : ContMDiff I 𝓘(𝕜
, E) n I
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
lemma IsOpen.exists_contMDiff_support_eq_aux {s : Set H} (hs : IsOpen s) :
    ∃ f : H → ℝ, f.support = s ∧ CMDiff n f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  rcases h's.exists_contDiff_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    simp only [ModelWithCorners.symm_comp_self, preimage_id_eq, id_eq]
  · exact f_diff.comp_contMDiff I.contMDiff
  · exact Subset.trans (range_comp_subset_range _ _) f_range

/-- Given an open set in a finite-dimensional real manifold, there exists a nonnegative smooth
function with support equal to `s`. -/
/-
**IsOpen.exists_contMDiff_support_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.exists_contMDiff_support_eq {s : Set M} (hs : IsOpen s) : exists f 
: M -> Real, f.support = s ∧ CMDiff n f ∧ forall x, 0 <= f x
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`：exists_isSub
ordinate_chartAt_source : exists f : SmoothPartitionOfUnity M I M univ, f.IsSubo
rdinate (fun x => (chartAt H x).source)
· 使用引理 `IsOpen.exists_contMDiff_support_eq_aux`：IsOpen.exists_contMDiff_support_
eq_aux {s : Set H} (hs : IsOpen s) : exists f : H -> Real, f.support = s ∧ CMDif
f n f ∧ Set.range f subseteq…
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage_symm`：isOpen_inter_preimage_
symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target inter e.symm ⁻¹' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `SmoothPartitionOfUnity.nonneg`：nonneg (i : ι) (x : M) : 0 <= f i x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_eq_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {s : Set ι},   Function.support f = s ↔ (∀ x ∈ s, f x ≠ 0) ∧ ∀ x ∉ 
s, f x = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `SmoothPartitionOfUnity.exists_pos_of_mem`：exists_pos_of_mem {x} (hx : x 
in s) : exists i, 0 < f i x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Given an open set in a finite-dimensional real manifold, there exists a nonnegat
ive smooth
function with support equal to `s`.
-/
theorem IsOpen.exists_contMDiff_support_eq {s : Set M} (hs : IsOpen s) :
    ∃ f : M → ℝ, f.support = s ∧ CMDiff n f ∧ ∀ x, 0 ≤ f x := by
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  have A : ∀ (c : M), ∃ g : H → ℝ,
      g.support = (chartAt H c).target ∩ (chartAt H c).symm ⁻¹' s ∧
      CMDiff n g ∧ Set.range g ⊆ Set.Icc 0 1 := by
    intro i
    apply IsOpen.exists_contMDiff_support_eq_aux
    exact OpenPartialHomeomorph.isOpen_inter_preimage_symm _ hs
  choose g g_supp g_diff hg using A
  have h'g : ∀ c x, 0 ≤ g c x := fun c x ↦ (hg c (mem_range_self (f := g c) x)).1
  have h''g : ∀ c x, 0 ≤ f c x * g c (chartAt H c x) :=
    fun c x ↦ mul_nonneg (f.nonneg c x) (h'g c _)
  refine ⟨fun x ↦ ∑ᶠ c, f c x * g c (chartAt H c x), ?_, ?_, ?_⟩
  · refine support_eq_iff.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · apply ne_of_gt
      have B : ∃ c, 0 < f c x * g c (chartAt H c x) := by
        obtain ⟨c, hc⟩ : ∃ c, 0 < f c x := f.exists_pos_of_mem (mem_univ x)
        refine ⟨c, mul_pos hc ?_⟩
        apply lt_of_le_of_ne (h'g _ _) (Ne.symm _)
        rw [← mem_support, g_supp, ← mem_preimage, preimage_inter]
        have Hx : x ∈ tsupport (f c) := subset_tsupport _ (ne_of_gt hc)
        simp [(chartAt H c).left_inv (hf c Hx), hx, (chartAt H c).map_source (hf c Hx)]
      apply finsum_pos (fun c ↦ h''g c x) B
      apply (f.locallyFinite.point_finite x).subset
      apply compl_subset_compl.2
      rintro c (hc : f c x = 0)
      simpa only [mul_eq_zero] using! Or.inl hc
    · apply finsum_eq_zero_of_forall_eq_zero
      intro c
      by_cases Hx : x ∈ tsupport (f c)
      · suffices g c (chartAt H c x) = 0 by simp only [this, mul_zero]
        rw [← notMem_support, g_supp, ← mem_preimage, preimage_inter]
        contrapose hx
        simp only [mem_inter_iff, mem_preimage, (chartAt H c).left_inv (hf c Hx)] at hx
        exact hx.2
      · have : x ∉ support (f c) := by contrapose Hx; exact subset_tsupport _ Hx
        rw [notMem_support] at this
        simp [this]
  · apply SmoothPartitionOfUnity.contMDiff_finsum_smul
    intro c x hx
    apply (g_diff c (chartAt H c x)).comp
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _)
      (hf c hx)
  · intro x
    apply finsum_nonneg (fun c ↦ h''g c x)

/-- Given an open set `s` containing a closed set `t` in a finite-dimensional real manifold, there
exists a smooth function with support equal to `s`, taking values in `[0,1]`, and equal to `1`
exactly on `t`. -/
/-
**exists_contMDiff_support_eq_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_contMDiff_support_eq_eq_one_iff {s t : Set M} (hs : IsOpen s) (ht :
 IsClosed t) (h : t subseteq s) : exists f : M -> Real, CMDiff n f ∧ range f sub
seteq Icc 0 1 ∧ support f = s ∧ (forall x, x in t ↔ f x = 1)
参数：hs : IsOpen s；ht : IsClosed t；h : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.exists_contMDiff_support_eq`：IsOpen.exists_contMDiff_support_eq {
s : Set M} (hs : IsOpen s) : exists f : M -> Real, f.support = s ∧ CMDiff n f ∧ 
forall x, 0 <= f x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
Given an open set `s` containing a closed set `t` in a finite-dimensional real m
anifold, there
exists a smooth function with support equal to `s`, taking values in `[0,1]`, an
d equal to `1`
exactly on `t`.
-/
theorem exists_contMDiff_support_eq_eq_one_iff
    {s t : Set M} (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, CMDiff n f ∧ range f ⊆ Icc 0 1 ∧ support f = s ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  /- Take `f` with support equal to `s`, and `g` with support equal to `tᶜ`. Then `f / (f + g)`
  satisfies the conclusion of the theorem. -/
  rcases hs.exists_contMDiff_support_eq I with ⟨f, f_supp, f_diff, f_pos⟩
  rcases ht.isOpen_compl.exists_contMDiff_support_eq I with ⟨g, g_supp, g_diff, g_pos⟩
  have A : ∀ x, 0 < f x + g x := by
    intro x
    by_cases xs : x ∈ support f
    · have : 0 < f x := lt_of_le_of_ne (f_pos x) (Ne.symm xs)
      linarith [g_pos x]
    · have : 0 < g x := by
        apply lt_of_le_of_ne (g_pos x) (Ne.symm ?_)
        rw [← mem_support, g_supp]
        contrapose xs
        exact h.trans f_supp.symm.subset (by simpa using xs)
      linarith [f_pos x]
  refine ⟨fun x ↦ f x / (f x + g x), ?_, ?_, ?_, ?_⟩
  -- show that `f / (f + g)` is smooth
  · exact f_diff.div₀ (f_diff.add g_diff) (fun x ↦ ne_of_gt (A x))
  -- show that the range is included in `[0, 1]`
  · refine range_subset_iff.2 (fun x ↦ ⟨div_nonneg (f_pos x) (A x).le, ?_⟩)
    apply div_le_one_of_le₀ _ (A x).le
    simpa only [le_add_iff_nonneg_right] using g_pos x
  -- show that the support is `s`
  · have B : support (fun x ↦ f x + g x) = univ := eq_univ_of_forall (fun x ↦ (A x).ne')
    simp only [support_div, f_supp, B, inter_univ]
  -- show that the function equals one exactly on `t`
  · intro x
    simp [div_eq_one_iff_eq (A x).ne', left_eq_add, ← notMem_support, g_supp]

/-- Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite-dimensional manifold,
there exists an infinitely smooth function that is equal to `0` exactly on `s` and to `1`
exactly on `t`. See also `exists_contMDiffMap_zero_one_of_isClosed` for a
slightly weaker version. -/
/-
**exists_contMDiff_zero_iff_one_iff_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_contMDiff_zero_iff_one_iff_of_isClosed {s t : Set M} (hs : IsClosed
 s) (ht : IsClosed t) (hd : Disjoint s t) : exists f : M -> Real, CMDiff n f ∧ r
ange f subseteq Icc 0 1 ∧ (forall x, x in s ↔ f x = 0) ∧ (forall x, x in t ↔ f x
 = 1)
参数：hs : IsClosed s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_contMDiff_support_eq_eq_one_iff`：exists_contMDiff_support_eq_eq_o
ne_iff {s t : Set M} (hs : IsOpen s) (ht : IsClosed t) (h : t subseteq s) : exis
ts f : M -> Real, CMDiff n f…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite-dimensiona
l manifold,
there exists an infinitely smooth function that is equal to `0` exactly on `s` a
nd to `1`
exactly on `t`. See also `exists_contMDiffMap_zero_one_of_isClosed` for a
slightly weaker version.
-/
theorem exists_contMDiff_zero_iff_one_iff_of_isClosed {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : M → ℝ, CMDiff n f ∧ range f ⊆ Icc 0 1 ∧ (∀ x, x ∈ s ↔ f x = 0)
      ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  rcases exists_contMDiff_support_eq_eq_one_iff I hs.isOpen_compl ht hd.subset_compl_left with
    ⟨f, f_diff, f_range, fs, ft⟩
  refine ⟨f, f_diff, f_range, ?_, ft⟩
  simp [← notMem_support, fs]
