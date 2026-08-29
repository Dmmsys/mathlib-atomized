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

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace Real F] {H : Type uH}
  [TopologicalSpace H] (I : ModelWithCorners Real E H) {M : Type uM} [TopologicalSpace M]
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

/--
Definition of `SmoothBumpCovering` / `SmoothBumpCovering` 的定义

English:
structure SmoothBumpCovering
  parameters: [FiniteDimensional Real E] (s : Set M := univ)
  axioms and operations (5):
    - c : ι -> M
    - toFun : forall i, SmoothBumpFunction I (c i)
    - c_mem' : forall i, c i in s
    - locallyFinite' : LocallyFinite fun i => support (toFun i)
    - eventuallyEq_one' : forall x in s, exists i, toFun i =ᶠ[𝓝 x] 1

中文:
结构 光滑凸覆盖
  参数: [有限维 实数 E] (s : 集合 M := univ)
  公理与运算 (5 个):
    - c : ι -> M
    - toFun : 对任意 i, 光滑凸函数 I (c i)
    - c_mem' : 对任意 i, c i in s
    - locallyFinite' : 局部有限 fun i => support (toFun i)
    - eventuallyEq_one' : 对任意 x in s, 存在 i, toFun i =ᶠ[𝓝 x] 1
-/
structure SmoothBumpCovering [FiniteDimensional Real E] (s : Set M := univ) where
  /-- The center point of each bump in the smooth covering. -/
  c : ι -> M
  /-- A smooth bump function around `c i`. -/
  toFun : forall i, SmoothBumpFunction I (c i)
  /-- All the bump functions in the covering are centered at points in `s`. -/
  c_mem' : forall i, c i in s
  /-- Around each point, there are only finitely many nonzero bump functions in the family. -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- Around each point in `s`, one of the bump functions is equal to `1`. -/
  eventuallyEq_one' : forall x in s, exists i, toFun i =ᶠ[𝓝 x] 1

/--
Definition of `SmoothPartitionOfUnity` / `SmoothPartitionOfUnity` 的定义

English:
structure SmoothPartitionOfUnity
  parameters: (s : Set M := univ)
  axioms and operations (5):
    - toFun : ι -> C^∞⟮I, M; 𝓘(Real), Real⟯
    - locallyFinite' : LocallyFinite fun i => support (toFun i)
    - nonneg' : forall i x, 0 <= toFun i x
    - sum_eq_one' : forall x in s, ∑ᶠ i, toFun i x = 1
    - sum_le_one' : forall x, ∑ᶠ i, toFun i x <= 1

中文:
结构 光滑单位分解
  参数: (s : 集合 M := univ)
  公理与运算 (5 个):
    - toFun : ι -> C^∞⟮I, M; 𝓘(实数), 实数⟯
    - locallyFinite' : 局部有限 fun i => support (toFun i)
    - nonneg' : 对任意 i x, 0 <= toFun i x
    - sum_eq_one' : 对任意 x in s, ∑ᶠ i, toFun i x = 1
    - sum_le_one' : 对任意 x, ∑ᶠ i, toFun i x <= 1
-/
structure SmoothPartitionOfUnity (s : Set M := univ) where
  /-- The family of functions forming the partition of unity. -/
  toFun : ι -> C^∞⟮I, M; 𝓘(Real), Real⟯
  /-- Around each point, there are only finitely many nonzero functions in the family. -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- All the functions in the partition of unity are nonnegative. -/
  nonneg' : forall i x, 0 <= toFun i x
  /-- The functions in the partition of unity add up to `1` at any point of `s`. -/
  sum_eq_one' : forall x in s, ∑ᶠ i, toFun i x = 1
  /-- The functions in the partition of unity add up to at most `1` everywhere. -/
  sum_le_one' : forall x, ∑ᶠ i, toFun i x <= 1

variable {ι I M}

namespace SmoothPartitionOfUnity

variable {s : Set M} (f : SmoothPartitionOfUnity ι I M s) {n : Nat∞}

instance {s : Set M} : FunLike (SmoothPartitionOfUnity ι I M s) ι C^∞⟮I, M; 𝓘(Real), Real⟯ where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/--
theorem `locallyFinite` / 定理 `locallyFinite`

English:
theorem locallyFinite
  statement: LocallyFinite fun i => support (f i)
  proof: f.locallyFinite'

中文:
定理 locallyFinite
  结论: 局部有限 fun i => support (f i)
  证明: f.locallyFinite'
-/
protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (i : ι) (x : M)
  statement: 0 <= f i x
  proof: f.nonneg' i x

中文:
定理 nonneg
  条件: (i : ι) (x : M)
  结论: 0 <= f i x
  证明: f.nonneg' i x

Depends on / 依赖: f.nonneg, nonneg
-/
theorem nonneg (i : ι) (x : M) : 0 <= f i x :=
  f.nonneg' i x

/--
theorem `sum_eq_one` / 定理 `sum_eq_one`

English:
theorem sum_eq_one
  given: {x} (hx : x in s)
  statement: ∑ᶠ i, f i x = 1
  proof: f.sum_eq_one' x hx

中文:
定理 sum_eq_one
  条件: {x} (hx : x in s)
  结论: ∑ᶠ i, f i x = 1
  证明: f.sum_eq_one' x hx

Depends on / 依赖: f.sum_eq_one, sum_eq_one
-/
theorem sum_eq_one {x} (hx : x in s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx

/--
theorem `exists_pos_of_mem` / 定理 `exists_pos_of_mem`

English:
theorem exists_pos_of_mem
  given: {x} (hx : x in s)
  statement: exists i, 0 < f i x
  proof: by
  by_contra! h
  have H : forall i, f i x = 0 := fun i => le_antisymm (h i) (f.nonneg i x)
  have := f.sum_eq_one hx
  simp_rw [H] at this
  simpa

中文:
定理 存在_pos_of_mem
  条件: {x} (hx : x in s)
  结论: 存在 i, 0 < f i x
  证明: by
  by_contra! h
  have H : forall i, f i x = 0 := fun i => le_antisymm (h i) (f.nonneg i x)
  have := f.sum_eq_one hx
  simp_rw [H] at this
  simpa

Depends on / 依赖: f.nonneg, f.sum_eq_one, le_antisymm, nonneg, simp_rw, sum_eq_one
-/
theorem exists_pos_of_mem {x} (hx : x in s) : exists i, 0 < f i x := by
  by_contra! h
  have H : forall i, f i x = 0 := fun i => le_antisymm (h i) (f.nonneg i x)
  have := f.sum_eq_one hx
  simp_rw [H] at this
  simpa

/--
theorem `sum_le_one` / 定理 `sum_le_one`

English:
theorem sum_le_one
  given: (x : M)
  statement: ∑ᶠ i, f i x <= 1
  proof: f.sum_le_one' x

中文:
定理 sum_le_one
  条件: (x : M)
  结论: ∑ᶠ i, f i x <= 1
  证明: f.sum_le_one' x

Depends on / 依赖: f.sum_le_one, sum_le_one
-/
theorem sum_le_one (x : M) : ∑ᶠ i, f i x <= 1 :=
  f.sum_le_one' x

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
@[simps]
/--
Definition of `toPartitionOfUnity` / `toPartitionOfUnity` 的定义

English:
definition toPartitionOfUnity
  signature: : PartitionOfUnity ι M s
  body: { f with toFun := fun i => f i }

中文:
定义 toPartitionOfUnity
  签名: : 单位分解 ι M s
  定义体: { f with toFun := fun i => f i }
-/
def toPartitionOfUnity : PartitionOfUnity ι M s :=
  { f with toFun := fun i => f i }

/--
theorem `contMDiff_sum` / 定理 `contMDiff_sum`

English:
theorem contMDiff_sum
  statement: CMDiff ∞ fun x => ∑ᶠ i, f i x
  proof: contMDiff_finsum (fun i => (f i).contMDiff) f.locallyFinite

中文:
定理 contMDiff_sum
  结论: CMDiff ∞ fun x => ∑ᶠ i, f i x
  证明: contMDiff_finsum (fun i => (f i).contMDiff) f.locallyFinite

Depends on / 依赖: contMDiff, contMDiff_finsum, f.locallyFinite, locallyFinite
-/
theorem contMDiff_sum : CMDiff ∞ fun x => ∑ᶠ i, f i x :=
  contMDiff_finsum (fun i => (f i).contMDiff) f.locallyFinite

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: (i : ι) (x : M)
  statement: f i x <= 1
  proof: f.toPartitionOfUnity.le_one i x

中文:
定理 le_one
  条件: (i : ι) (x : M)
  结论: f i x <= 1
  证明: f.toPartitionOfUnity.le_one i x

Depends on / 依赖: f.toPartitionOfUnity.le_one, le_one, toPartitionOfUnity
-/
theorem le_one (i : ι) (x : M) : f i x <= 1 :=
  f.toPartitionOfUnity.le_one i x

/--
theorem `sum_nonneg` / 定理 `sum_nonneg`

English:
theorem sum_nonneg
  given: (x : M)
  statement: 0 <= ∑ᶠ i, f i x
  proof: f.toPartitionOfUnity.sum_nonneg x

中文:
定理 sum_nonneg
  条件: (x : M)
  结论: 0 <= ∑ᶠ i, f i x
  证明: f.toPartitionOfUnity.sum_nonneg x

Depends on / 依赖: f.toPartitionOfUnity.sum_nonneg, sum_nonneg, toPartitionOfUnity
-/
theorem sum_nonneg (x : M) : 0 <= ∑ᶠ i, f i x :=
  f.toPartitionOfUnity.sum_nonneg x

/--
theorem `finsum_smul_mem_convex` / 定理 `finsum_smul_mem_convex`

English:
theorem finsum_smul_mem_convex
  statement: {g : ι -> M -> F} {t : Set F} {x : M} (hx : x in s)
  proof: ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

中文:
定理 finsum_smul_mem_convex
  结论: {g : ι -> M -> F} {t : 集合 F} {x : M} (hx : x in s)
  证明: ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

Depends on / 依赖: f.nonneg, f.sum_eq_one, finsum_mem, ht.finsum_mem, nonneg, sum_eq_one
-/
theorem finsum_smul_mem_convex {g : ι -> M -> F} {t : Set F} {x : M} (hx : x in s)
    (hg : forall i, f i x != 0 -> g i x in t) (ht : Convex Real t) : ∑ᶠ i, f i x • g i x in t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

/--
theorem `contMDiff_smul` / 定理 `contMDiff_smul`

English:
theorem contMDiff_smul
  given: {g : M -> F} {i} (hg : forall x in tsupport (f i), CMDiffAt n g x)
  proof: contMDiff_of_tsupport fun x hx =>
((f i).contMDiff.contMDiffAt.of_le (mod_cast le_top)).smul hg x
 tsupport_smul_subset_left _ _ hx

中文:
定理 contMDiff_smul
  条件: {g : M -> F} {i} (hg : 对任意 x in tsupport (f i), CMDiffAt n g x)
  证明: contMDiff_of_tsupport fun x hx =>
((f i).contMDiff.contMDiffAt.of_le (mod_cast le_top)).smul hg x
 tsupport_smul_subset_left _ _ hx

Depends on / 依赖: contMDiff, contMDiff.contMDiffAt.of_le, contMDiffAt, contMDiff_of_tsupport, le_top, mod_cast, of_le, tsupport_smul_subset_left
-/
theorem contMDiff_smul {g : M -> F} {i} (hg : forall x in tsupport (f i), CMDiffAt n g x) :
    CMDiff n fun x => f i x • g x :=
  contMDiff_of_tsupport fun x hx =>
((f i).contMDiff.contMDiffAt.of_le (mod_cast le_top)).smul hg x
 tsupport_smul_subset_left _ _ hx

/--
theorem `contMDiff_finsum_smul` / 定理 `contMDiff_finsum_smul`

English:
theorem contMDiff_finsum_smul
  statement: {g : ι -> M -> F}
  proof: (contMDiff_finsum fun i => f.contMDiff_smul (hg i))
f.locallyFinite.subset fun _ => support_smul_subset_left _ _

中文:
定理 contMDiff_finsum_smul
  结论: {g : ι -> M -> F}
  证明: (contMDiff_finsum fun i => f.contMDiff_smul (hg i))
f.locallyFinite.subset fun _ => support_smul_subset_left _ _

Depends on / 依赖: contMDiff_finsum, contMDiff_smul, f.contMDiff_smul, f.locallyFinite.subset, locallyFinite, subset, support_smul_subset_left
-/
theorem contMDiff_finsum_smul {g : ι -> M -> F}
    (hg : forall (i), forall x in tsupport (f i), CMDiffAt n (g i) x) :
    CMDiff n fun x => ∑ᶠ i, f i x • g i x :=
(contMDiff_finsum fun i => f.contMDiff_smul (hg i))
f.locallyFinite.subset fun _ => support_smul_subset_left _ _

/--
theorem `contMDiffAt_finsum` / 定理 `contMDiffAt_finsum`

English:
theorem contMDiffAt_finsum
  statement: {x₀ : M} {g : ι -> M -> F}
  proof: by
  refine _root_.contMDiffAt_finsum (f.locallyFinite.smul_left _) fun i => ?_
  by_cases hx : x₀ in tsupport (f i)
  · exact ContMDiffAt.smul ((f i).contMDiff.of_le (mod_cast le_top)).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (f 

中文:
定理 contMDiffAt_finsum
  结论: {x₀ : M} {g : ι -> M -> F}
  证明: by
  refine _root_.contMDiffAt_finsum (f.locallyFinite.smul_left _) fun i => ?_
  by_cases hx : x₀ in tsupport (f i)
  · exact ContMDiffAt.smul ((f i).contMDiff.of_le (mod_cast le_top)).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (f 

Depends on / 依赖: ContMDiffAt, ContMDiffAt.smul, _root_, _root_.contMDiffAt_finsum, compl_subset_compl, compl_subset_compl.mpr, contMDiff, contMDiff.of_le, contMDiffAt, contMDiffAt_finsum, contMDiffAt_of_notMem, f.locallyFinite.smul_left, le_top, locallyFinite, mod_cast, of_le, smul_left, tsupport, tsupport_smul_subset_left
-/
theorem contMDiffAt_finsum {x₀ : M} {g : ι -> M -> F}
    (hφ : forall i, x₀ in tsupport (f i) -> CMDiffAt n (g i) x₀) :
    CMDiffAt n (fun x => ∑ᶠ i, f i x • g i x) x₀ := by
  refine _root_.contMDiffAt_finsum (f.locallyFinite.smul_left _) fun i => ?_
  by_cases hx : x₀ in tsupport (f i)
  · exact ContMDiffAt.smul ((f i).contMDiff.of_le (mod_cast le_top)).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (f i) (g i)) hx) n

/--
theorem `contDiffAt_finsum` / 定理 `contDiffAt_finsum`

English:
theorem contDiffAt_finsum
  statement: {s : Set E} (f : SmoothPartitionOfUnity ι 𝓘(Real, E) E s) {x₀ : E}
  proof: by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact f.contMDiffAt_finsum hφ

中文:
定理 contDiffAt_finsum
  结论: {s : 集合 E} (f : 光滑单位分解 ι 𝓘(实数, E) E s) {x₀ : E}
  证明: by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact f.contMDiffAt_finsum hφ

Depends on / 依赖: contMDiffAt_finsum, contMDiffAt_iff_contDiffAt, f.contMDiffAt_finsum
-/
theorem contDiffAt_finsum {s : Set E} (f : SmoothPartitionOfUnity ι 𝓘(Real, E) E s) {x₀ : E}
    {g : ι -> E -> F} (hφ : forall i, x₀ in tsupport (f i) -> ContDiffAt Real n (g i) x₀) :
    ContDiffAt Real n (fun x => ∑ᶠ i, f i x • g i x) x₀ := by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact f.contMDiffAt_finsum hφ

section finsupport

variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)

/--
Definition of `finsupport` / `finsupport` 的定义

English:
definition finsupport
  signature: : Finset ι
  body: ρ.toPartitionOfUnity.finsupport x₀

@[simp]

中文:
定义 finsupport
  签名: : 有限集 ι
  定义体: ρ.toPartitionOfUnity.finsupport x₀

@[simp]

Depends on / 依赖: finsupport, toPartitionOfUnity, toPartitionOfUnity.finsupport
-/
def finsupport : Finset ι := ρ.toPartitionOfUnity.finsupport x₀

@[simp]
/--
theorem `mem_finsupport` / 定理 `mem_finsupport`

English:
theorem mem_finsupport
  given: {i : ι}
  statement: i in ρ.finsupport x₀ ↔ i in support fun i => ρ i x₀
  proof: ρ.toPartitionOfUnity.mem_finsupport x₀

@[simp]

中文:
定理 mem_finsupport
  条件: {i : ι}
  结论: i in ρ.finsupport x₀ ↔ i in support fun i => ρ i x₀
  证明: ρ.toPartitionOfUnity.mem_finsupport x₀

@[simp]

Depends on / 依赖: mem_finsupport, toPartitionOfUnity, toPartitionOfUnity.mem_finsupport
-/
theorem mem_finsupport {i : ι} : i in ρ.finsupport x₀ ↔ i in support fun i => ρ i x₀ :=
  ρ.toPartitionOfUnity.mem_finsupport x₀

@[simp]
/--
theorem `coe_finsupport` / 定理 `coe_finsupport`

English:
theorem coe_finsupport
  statement: (ρ.finsupport x₀ : Set ι) = support fun i => ρ i x₀
  proof: ρ.toPartitionOfUnity.coe_finsupport x₀

中文:
定理 coe_finsupport
  结论: (ρ.finsupport x₀ : 集合 ι) = support fun i => ρ i x₀
  证明: ρ.toPartitionOfUnity.coe_finsupport x₀

Depends on / 依赖: coe_finsupport, toPartitionOfUnity, toPartitionOfUnity.coe_finsupport
-/
theorem coe_finsupport : (ρ.finsupport x₀ : Set ι) = support fun i => ρ i x₀ :=
  ρ.toPartitionOfUnity.coe_finsupport x₀

/--
theorem `sum_finsupport` / 定理 `sum_finsupport`

English:
theorem sum_finsupport
  given: (hx₀ : x₀ in s)
  statement: ∑ i in ρ.finsupport x₀, ρ i x₀ = 1
  proof: ρ.toPartitionOfUnity.sum_finsupport hx₀

中文:
定理 sum_finsupport
  条件: (hx₀ : x₀ in s)
  结论: ∑ i in ρ.finsupport x₀, ρ i x₀ = 1
  证明: ρ.toPartitionOfUnity.sum_finsupport hx₀

Depends on / 依赖: sum_finsupport, toPartitionOfUnity, toPartitionOfUnity.sum_finsupport
-/
theorem sum_finsupport (hx₀ : x₀ in s) : ∑ i in ρ.finsupport x₀, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport hx₀

/--
theorem `sum_finsupport'` / 定理 `sum_finsupport'`

English:
theorem sum_finsupport'
  given: (hx₀ : x₀ in s) {I : Finset ι} (hI : ρ.finsupport x₀ subseteq I)
  proof: ρ.toPartitionOfUnity.sum_finsupport' hx₀ hI

中文:
定理 sum_finsupport'
  条件: (hx₀ : x₀ in s) {I : 有限集 ι} (hI : ρ.finsupport x₀ subseteq I)
  证明: ρ.toPartitionOfUnity.sum_finsupport' hx₀ hI

Depends on / 依赖: sum_finsupport, toPartitionOfUnity, toPartitionOfUnity.sum_finsupport
-/
theorem sum_finsupport' (hx₀ : x₀ in s) {I : Finset ι} (hI : ρ.finsupport x₀ subseteq I) :
    ∑ i in I, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport' hx₀ hI

/--
theorem `sum_finsupport_smul_eq_finsum` / 定理 `sum_finsupport_smul_eq_finsum`

English:
theorem sum_finsupport_smul_eq_finsum
  given: {A : Type*} [AddCommGroup A] [Module Real A] (φ : ι -> M -> A)
  proof: ρ.toPartitionOfUnity.sum_finsupport_smul_eq_finsum φ

中文:
定理 sum_finsupport_smul_eq_finsum
  条件: {A : 类型} [加法交换群 A] [模 实数 A] (φ : ι -> M -> A)
  证明: ρ.toPartitionOfUnity.sum_finsupport_smul_eq_finsum φ

Depends on / 依赖: sum_finsupport_smul_eq_finsum, toPartitionOfUnity, toPartitionOfUnity.sum_finsupport_smul_eq_finsum
-/
theorem sum_finsupport_smul_eq_finsum {A : Type*} [AddCommGroup A] [Module Real A] (φ : ι -> M -> A) :
    ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ :=
  ρ.toPartitionOfUnity.sum_finsupport_smul_eq_finsum φ

end finsupport

section fintsupport -- smooth partitions of unity have locally finite `tsupport`
variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)

/--
theorem `finite_tsupport` / 定理 `finite_tsupport`

English:
theorem finite_tsupport
  statement: {i | x₀ in tsupport (ρ i)}.Finite
  proof: ρ.toPartitionOfUnity.finite_tsupport _

中文:
定理 finite_tsupport
  结论: {i | x₀ in tsupport (ρ i)}.有限
  证明: ρ.toPartitionOfUnity.finite_tsupport _

Depends on / 依赖: finite_tsupport, toPartitionOfUnity, toPartitionOfUnity.finite_tsupport
-/
theorem finite_tsupport : {i | x₀ in tsupport (ρ i)}.Finite :=
  ρ.toPartitionOfUnity.finite_tsupport _

/--
Definition of `fintsupport` / `fintsupport` 的定义

English:
definition fintsupport
  signature: (x : M)
  body: (ρ.finite_tsupport x).toFinset

中文:
定义 fintsupport
  签名: (x : M)
  定义体: (ρ.finite_tsupport x).toFinset

Depends on / 依赖: finite_tsupport, toFinset
-/
def fintsupport (x : M) : Finset ι :=
  (ρ.finite_tsupport x).toFinset

/--
theorem `mem_fintsupport_iff` / 定理 `mem_fintsupport_iff`

English:
theorem mem_fintsupport_iff
  given: (i : ι)
  statement: i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
  proof: Finite.mem_toFinset _

中文:
定理 mem_fintsupport_iff
  条件: (i : ι)
  结论: i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
  证明: Finite.mem_toFinset _

Depends on / 依赖: Finite, Finite.mem_toFinset, mem_toFinset
-/
theorem mem_fintsupport_iff (i : ι) : i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i) :=
  Finite.mem_toFinset _

/--
theorem `eventually_fintsupport_subset` / 定理 `eventually_fintsupport_subset`

English:
theorem eventually_fintsupport_subset
  statement: forallᶠ y in 𝓝 x₀, ρ.fintsupport y subseteq ρ.fintsupport x₀
  proof: ρ.toPartitionOfUnity.eventually_fintsupport_subset _

中文:
定理 eventually_fintsupport_subset
  结论: 对任意ᶠ y in 𝓝 x₀, ρ.fintsupport y subseteq ρ.fintsupport x₀
  证明: ρ.toPartitionOfUnity.eventually_fintsupport_subset _

Depends on / 依赖: eventually_fintsupport_subset, toPartitionOfUnity, toPartitionOfUnity.eventually_fintsupport_subset
-/
theorem eventually_fintsupport_subset : forallᶠ y in 𝓝 x₀, ρ.fintsupport y subseteq ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_fintsupport_subset _

/--
theorem `finsupport_subset_fintsupport` / 定理 `finsupport_subset_fintsupport`

English:
theorem finsupport_subset_fintsupport
  statement: ρ.finsupport x₀ subseteq ρ.fintsupport x₀
  proof: ρ.toPartitionOfUnity.finsupport_subset_fintsupport x₀

中文:
定理 finsupport_subset_fintsupport
  结论: ρ.finsupport x₀ subseteq ρ.fintsupport x₀
  证明: ρ.toPartitionOfUnity.finsupport_subset_fintsupport x₀

Depends on / 依赖: finsupport_subset_fintsupport, toPartitionOfUnity, toPartitionOfUnity.finsupport_subset_fintsupport
-/
theorem finsupport_subset_fintsupport : ρ.finsupport x₀ subseteq ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.finsupport_subset_fintsupport x₀

/--
theorem `eventually_finsupport_subset` / 定理 `eventually_finsupport_subset`

English:
theorem eventually_finsupport_subset
  statement: forallᶠ y in 𝓝 x₀, ρ.finsupport y subseteq ρ.fintsupport x₀
  proof: ρ.toPartitionOfUnity.eventually_finsupport_subset x₀

中文:
定理 eventually_finsupport_subset
  结论: 对任意ᶠ y in 𝓝 x₀, ρ.finsupport y subseteq ρ.fintsupport x₀
  证明: ρ.toPartitionOfUnity.eventually_finsupport_subset x₀

Depends on / 依赖: eventually_finsupport_subset, toPartitionOfUnity, toPartitionOfUnity.eventually_finsupport_subset
-/
theorem eventually_finsupport_subset : forallᶠ y in 𝓝 x₀, ρ.finsupport y subseteq ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_finsupport_subset x₀

end fintsupport

section IsSubordinate

/--
Definition of `IsSubordinate` / `IsSubordinate` 的定义

English:
definition IsSubordinate
  signature: (f : SmoothPartitionOfUnity ι I M s) (U : ι -> Set M)
  body: forall i, tsupport (f i) subseteq U i

中文:
定义 IsSubordinate
  签名: (f : 光滑单位分解 ι I M s) (U : ι -> 集合 M)
  定义体: forall i, tsupport (f i) subseteq U i

Depends on / 依赖: subseteq, tsupport
-/
def IsSubordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι -> Set M) :=
  forall i, tsupport (f i) subseteq U i

variable {f}
variable {U : ι -> Set M}

@[simp]
/--
theorem `isSubordinate_toPartitionOfUnity` / 定理 `isSubordinate_toPartitionOfUnity`

English:
theorem isSubordinate_toPartitionOfUnity
  proof: Iff.rfl

alias ⟨_, IsSubordinate.toPartitionOfUnity⟩ := isSubordinate_toPartitionOfUnity

中文:
定理 isSubordinate_toPartitionOfUnity
  证明: Iff.rfl

alias ⟨_, IsSubordinate.toPartitionOfUnity⟩ := isSubordinate_toPartitionOfUnity

Depends on / 依赖: Iff.rfl
-/
theorem isSubordinate_toPartitionOfUnity :
    f.toPartitionOfUnity.IsSubordinate U ↔ f.IsSubordinate U :=
  Iff.rfl

alias ⟨_, IsSubordinate.toPartitionOfUnity⟩ := isSubordinate_toPartitionOfUnity

/--
theorem `IsSubordinate.contMDiff_finsum_smul` / 定理 `IsSubordinate.contMDiff_finsum_smul`

English:
theorem IsSubordinate.contMDiff_finsum_smul
  statement: {g : ι -> M -> F} (hf : f.IsSubordinate U)
  proof: f.contMDiff_finsum_smul fun i _ hx => (hg i).contMDiffAt (ho i).mem_nhds (hf i hx)

中文:
定理 IsSubordinate.contMDiff_finsum_smul
  结论: {g : ι -> M -> F} (hf : f.IsSubordinate U)
  证明: f.contMDiff_finsum_smul fun i _ hx => (hg i).contMDiffAt (ho i).mem_nhds (hf i hx)

Depends on / 依赖: contMDiffAt, contMDiff_finsum_smul, f.contMDiff_finsum_smul, mem_nhds
-/
theorem IsSubordinate.contMDiff_finsum_smul {g : ι -> M -> F} (hf : f.IsSubordinate U)
    (ho : forall i, IsOpen (U i)) (hg : forall i, CMDiff[U i] n (g i)) :
    CMDiff n fun x => ∑ᶠ i, f i x • g i x :=
f.contMDiff_finsum_smul fun i _ hx => (hg i).contMDiffAt (ho i).mem_nhds (hf i hx)

end IsSubordinate

end SmoothPartitionOfUnity

namespace BumpCovering

-- Repeat variables to drop `[FiniteDimensional ℝ E]` and `[IsManifold I ∞ M]`
/--
theorem `contMDiff_toPartitionOfUnity` / 定理 `contMDiff_toPartitionOfUnity`

English:
theorem contMDiff_toPartitionOfUnity
  statement: {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: (hf i).mul (contMDiff_finprod_cond fun j _ => contMDiff_const.sub (hf j)) by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

中文:
定理 contMDiff_toPartitionOfUnity
  结论: {E : 类型uE} [赋范交换加群 E] [赋范空间 实数 E]
  证明: (hf i).mul (contMDiff_finprod_cond fun j _ => contMDiff_const.sub (hf j)) by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

Depends on / 依赖: contMDiff_const, contMDiff_const.sub, contMDiff_finprod_cond, f.locallyFinite, locallyFinite, mulSupport_one_sub
-/
theorem contMDiff_toPartitionOfUnity {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H} {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M] {s : Set M} (f : BumpCovering ι M s)
    (hf : forall i, CMDiff ∞ (f i)) (i : ι) : CMDiff ∞ (f.toPartitionOfUnity i) :=
(hf i).mul (contMDiff_finprod_cond fun j _ => contMDiff_const.sub (hf j)) by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

variable {s : Set M}

/--
Definition of `toSmoothPartitionOfUnity` / `toSmoothPartitionOfUnity` 的定义

English:
definition toSmoothPartitionOfUnity
  signature: (f : BumpCovering ι M s) (hf : forall i, CMDiff ∞ (f i))
  body: { f.toPartitionOfUnity with
    toFun := fun i => ⟨f.toPartitionOfUnity i, f.contMDiff_toPartitionOfUnity hf i⟩ }

@[simp]

中文:
定义 toSmoothPartitionOfUnity
  签名: (f : BumpCovering ι M s) (hf : 对任意 i, CMDiff ∞ (f i))
  定义体: { f.toPartitionOfUnity with
    toFun := fun i => ⟨f.toPartitionOfUnity i, f.contMDiff_toPartitionOfUnity hf i⟩ }

@[simp]

Depends on / 依赖: contMDiff_toPartitionOfUnity, f.contMDiff_toPartitionOfUnity, f.toPartitionOfUnity, toPartitionOfUnity
-/
def toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : forall i, CMDiff ∞ (f i)) :
    SmoothPartitionOfUnity ι I M s :=
  { f.toPartitionOfUnity with
    toFun := fun i => ⟨f.toPartitionOfUnity i, f.contMDiff_toPartitionOfUnity hf i⟩ }

@[simp]
/--
theorem `toSmoothPartitionOfUnity_toPartitionOfUnity` / 定理 `toSmoothPartitionOfUnity_toPartitionOfUnity`

English:
theorem toSmoothPartitionOfUnity_toPartitionOfUnity
  statement: (f : BumpCovering ι M s)
  proof: rfl

@[simp]

中文:
定理 toSmoothPartitionOfUnity_toPartitionOfUnity
  结论: (f : BumpCovering ι M s)
  证明: rfl

@[simp]
-/
theorem toSmoothPartitionOfUnity_toPartitionOfUnity (f : BumpCovering ι M s)
    (hf : forall i, CMDiff ∞ (f i)) :
    (f.toSmoothPartitionOfUnity hf).toPartitionOfUnity = f.toPartitionOfUnity :=
  rfl

@[simp]
/--
theorem `coe_toSmoothPartitionOfUnity` / 定理 `coe_toSmoothPartitionOfUnity`

English:
theorem coe_toSmoothPartitionOfUnity
  statement: (f : BumpCovering ι M s) (hf : forall i, CMDiff ∞ (f i))
  proof: rfl

中文:
定理 coe_toSmoothPartitionOfUnity
  结论: (f : BumpCovering ι M s) (hf : 对任意 i, CMDiff ∞ (f i))
  证明: rfl
-/
theorem coe_toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : forall i, CMDiff ∞ (f i))
    (i : ι) : ⇑(f.toSmoothPartitionOfUnity hf i) = f.toPartitionOfUnity i :=
  rfl

/--
theorem `IsSubordinate.toSmoothPartitionOfUnity` / 定理 `IsSubordinate.toSmoothPartitionOfUnity`

English:
theorem IsSubordinate.toSmoothPartitionOfUnity
  statement: {f : BumpCovering ι M s} {U : ι -> Set M}
  proof: h.toPartitionOfUnity

中文:
定理 IsSubordinate.toSmoothPartitionOfUnity
  结论: {f : BumpCovering ι M s} {U : ι -> 集合 M}
  证明: h.toPartitionOfUnity

Depends on / 依赖: h.toPartitionOfUnity, toPartitionOfUnity
-/
theorem IsSubordinate.toSmoothPartitionOfUnity {f : BumpCovering ι M s} {U : ι -> Set M}
    (h : f.IsSubordinate U) (hf : forall i, CMDiff ∞ (f i)) :
    (f.toSmoothPartitionOfUnity hf).IsSubordinate U :=
  h.toPartitionOfUnity

end BumpCovering

namespace SmoothBumpCovering

variable [FiniteDimensional Real E]
variable {s : Set M} {U : M -> Set M} (fs : SmoothBumpCovering ι I M s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (SmoothBumpCovering ι I M s) fun x => forall i
  body: ⟨toFun⟩

中文:
实例 :
  签名: CoeFun (光滑凸覆盖 ι I M s) fun x => 对任意 i
  定义体: ⟨toFun⟩
-/
instance : CoeFun (SmoothBumpCovering ι I M s) fun x => forall i : ι, SmoothBumpFunction I (x.c i) :=
  ⟨toFun⟩

/--
Definition of `IsSubordinate` / `IsSubordinate` 的定义

English:
definition IsSubordinate
  signature: {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M -> Set M)
  body: forall i, tsupport (f i) subseteq U (f.c i)

中文:
定义 IsSubordinate
  签名: {s : 集合 M} (f : 光滑凸覆盖 ι I M s) (U : M -> 集合 M)
  定义体: forall i, tsupport (f i) subseteq U (f.c i)

Depends on / 依赖: subseteq, tsupport
-/
def IsSubordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M -> Set M) :=
  forall i, tsupport (f i) subseteq U (f.c i)

/--
theorem `IsSubordinate.support_subset` / 定理 `IsSubordinate.support_subset`

English:
theorem IsSubordinate.support_subset
  statement: {fs : SmoothBumpCovering ι I M s} {U : M -> Set M}
  proof: Subset.trans subset_closure (h i)

中文:
定理 IsSubordinate.support_subset
  结论: {fs : 光滑凸覆盖 ι I M s} {U : M -> 集合 M}
  证明: Subset.trans subset_closure (h i)

Depends on / 依赖: Subset, Subset.trans, subset_closure
-/
theorem IsSubordinate.support_subset {fs : SmoothBumpCovering ι I M s} {U : M -> Set M}
    (h : fs.IsSubordinate U) (i : ι) : support (fs i) subseteq U (fs.c i) :=
  Subset.trans subset_closure (h i)

variable (I) in
/--
theorem `exists_isSubordinate` / 定理 `exists_isSubordinate`

English:
theorem exists_isSubordinate
  statement: [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s)
  proof: by
  -- First we deduce some missing instances
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Next we choose a covering by supports of smooth bump functions
  have hB := fun x hx => SmoothBumpFunction.nhds_basis_sup

中文:
定理 存在_isSubordinate
  结论: [T2空间 M] [SigmaCompact空间 M] (hs : 是闭集 s)
  证明: by
  -- First we deduce some missing instances
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Next we choose a covering by supports of smooth bump functions
  have hB := fun x hx => SmoothBumpFunction.nhds_basis_sup
-/
theorem exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s)
    (hU : forall x in s, U x in 𝓝 x) :
    exists (ι : Type uM) (f : SmoothBumpCovering ι I M s), f.IsSubordinate U := by
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

/--
theorem `locallyFinite` / 定理 `locallyFinite`

English:
theorem locallyFinite
  statement: LocallyFinite fun i => support (fs i)
  proof: fs.locallyFinite'

中文:
定理 locallyFinite
  结论: 局部有限 fun i => support (fs i)
  证明: fs.locallyFinite'
-/
protected theorem locallyFinite : LocallyFinite fun i => support (fs i) :=
  fs.locallyFinite'

/--
theorem `point_finite` / 定理 `point_finite`

English:
theorem point_finite
  given: (x : M)
  statement: {i | fs i x != 0}.Finite
  proof: fs.locallyFinite.point_finite x

中文:
定理 point_finite
  条件: (x : M)
  结论: {i | fs i x != 0}.有限
  证明: fs.locallyFinite.point_finite x
-/
protected theorem point_finite (x : M) : {i | fs i x != 0}.Finite :=
  fs.locallyFinite.point_finite x

/--
Definition of `ind` / `ind` 的定义

English:
definition ind
  signature: (x : M) (hx : x in s)
  body: (fs.eventuallyEq_one' x hx).choose

中文:
定义 ind
  签名: (x : M) (hx : x in s)
  定义体: (fs.eventuallyEq_one' x hx).choose

Depends on / 依赖: eventuallyEq_one, fs.eventuallyEq_one
-/
def ind (x : M) (hx : x in s) : ι :=
  (fs.eventuallyEq_one' x hx).choose

/--
theorem `eventuallyEq_one` / 定理 `eventuallyEq_one`

English:
theorem eventuallyEq_one
  given: (x : M) (hx : x in s)
  statement: fs (fs.ind x hx) =ᶠ[𝓝 x] 1
  proof: (fs.eventuallyEq_one' x hx).choose_spec

中文:
定理 eventuallyEq_one
  条件: (x : M) (hx : x in s)
  结论: fs (fs.ind x hx) =ᶠ[𝓝 x] 1
  证明: (fs.eventuallyEq_one' x hx).choose_spec

Depends on / 依赖: choose_spec, eventuallyEq_one, fs.eventuallyEq_one
-/
theorem eventuallyEq_one (x : M) (hx : x in s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
  (fs.eventuallyEq_one' x hx).choose_spec

/--
theorem `apply_ind` / 定理 `apply_ind`

English:
theorem apply_ind
  given: (x : M) (hx : x in s)
  statement: fs (fs.ind x hx) x = 1
  proof: (fs.eventuallyEq_one x hx).eq_of_nhds

中文:
定理 apply_ind
  条件: (x : M) (hx : x in s)
  结论: fs (fs.ind x hx) x = 1
  证明: (fs.eventuallyEq_one x hx).eq_of_nhds

Depends on / 依赖: eq_of_nhds, eventuallyEq_one, fs.eventuallyEq_one
-/
theorem apply_ind (x : M) (hx : x in s) : fs (fs.ind x hx) x = 1 :=
  (fs.eventuallyEq_one x hx).eq_of_nhds

/--
theorem `mem_support_ind` / 定理 `mem_support_ind`

English:
theorem mem_support_ind
  given: (x : M) (hx : x in s)
  statement: x in support (fs <| fs.ind x hx)
  proof: by
  simp [fs.apply_ind x hx]

中文:
定理 mem_support_ind
  条件: (x : M) (hx : x in s)
  结论: x in support (fs <| fs.ind x hx)
  证明: by
  simp [fs.apply_ind x hx]

Depends on / 依赖: apply_ind, fs.apply_ind
-/
theorem mem_support_ind (x : M) (hx : x in s) : x in support (fs <| fs.ind x hx) := by
  simp [fs.apply_ind x hx]

/--
theorem `mem_chartAt_source_of_eq_one` / 定理 `mem_chartAt_source_of_eq_one`

English:
theorem mem_chartAt_source_of_eq_one
  given: {i : ι} {x : M} (h : fs i x = 1)
  proof: (fs i).support_subset_source by simp [h]

中文:
定理 mem_chartAt_source_of_eq_one
  条件: {i : ι} {x : M} (h : fs i x = 1)
  证明: (fs i).support_subset_source by simp [h]

Depends on / 依赖: support_subset_source
-/
theorem mem_chartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x in (chartAt H (fs.c i)).source :=
(fs i).support_subset_source by simp [h]

/--
theorem `mem_extChartAt_source_of_eq_one` / 定理 `mem_extChartAt_source_of_eq_one`

English:
theorem mem_extChartAt_source_of_eq_one
  given: {i : ι} {x : M} (h : fs i x = 1)
  proof: by
  rw [extChartAt_source]; exact fs.mem_chartAt_source_of_eq_one h

中文:
定理 mem_extChartAt_source_of_eq_one
  条件: {i : ι} {x : M} (h : fs i x = 1)
  证明: by
  rw [extChartAt_source]; exact fs.mem_chartAt_source_of_eq_one h

Depends on / 依赖: extChartAt_source, fs.mem_chartAt_source_of_eq_one, mem_chartAt_source_of_eq_one
-/
theorem mem_extChartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x in (extChartAt I (fs.c i)).source := by
  rw [extChartAt_source]; exact fs.mem_chartAt_source_of_eq_one h

/--
theorem `mem_chartAt_ind_source` / 定理 `mem_chartAt_ind_source`

English:
theorem mem_chartAt_ind_source
  given: (x : M) (hx : x in s)
  statement: x in (chartAt H (fs.c (fs.ind x hx))).source
  proof: fs.mem_chartAt_source_of_eq_one (fs.apply_ind x hx)

中文:
定理 mem_chartAt_ind_source
  条件: (x : M) (hx : x in s)
  结论: x in (chartAt H (fs.c (fs.ind x hx))).source
  证明: fs.mem_chartAt_source_of_eq_one (fs.apply_ind x hx)

Depends on / 依赖: apply_ind, fs.apply_ind, fs.mem_chartAt_source_of_eq_one, mem_chartAt_source_of_eq_one
-/
theorem mem_chartAt_ind_source (x : M) (hx : x in s) : x in (chartAt H (fs.c (fs.ind x hx))).source :=
  fs.mem_chartAt_source_of_eq_one (fs.apply_ind x hx)

/--
theorem `mem_extChartAt_ind_source` / 定理 `mem_extChartAt_ind_source`

English:
theorem mem_extChartAt_ind_source
  given: (x : M) (hx : x in s)
  proof: fs.mem_extChartAt_source_of_eq_one (fs.apply_ind x hx)

中文:
定理 mem_extChartAt_ind_source
  条件: (x : M) (hx : x in s)
  证明: fs.mem_extChartAt_source_of_eq_one (fs.apply_ind x hx)

Depends on / 依赖: apply_ind, fs.apply_ind, fs.mem_extChartAt_source_of_eq_one, mem_extChartAt_source_of_eq_one
-/
theorem mem_extChartAt_ind_source (x : M) (hx : x in s) :
    x in (extChartAt I (fs.c (fs.ind x hx))).source :=
  fs.mem_extChartAt_source_of_eq_one (fs.apply_ind x hx)

/-- The index type of a `SmoothBumpCovering` of a compact manifold is finite. -/
@[instance_reducible]
/--
Definition of `fintype` / `fintype` 的定义

English:
definition fintype
  signature: [CompactSpace M]
  body: fs.locallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support

中文:
定义 fintype
  签名: [紧空间 M]
  定义体: fs.locallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support
-/
protected def fintype [CompactSpace M] : Fintype ι :=
  fs.locallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support

variable [T2Space M]
variable [IsManifold I ∞ M]

/--
Definition of `toBumpCovering` / `toBumpCovering` 的定义

English:
definition toBumpCovering
  signature: : BumpCovering ι M s where
  body: ⟨fs i, (fs i).continuous⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'

@[simp]

中文:
定义 toBumpCovering
  签名: : BumpCovering ι M s where
  定义体: ⟨fs i, (fs i).continuous⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'

@[simp]

Depends on / 依赖: continuous
-/
def toBumpCovering : BumpCovering ι M s where
  toFun i := ⟨fs i, (fs i).continuous⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'

@[simp]
/--
theorem `isSubordinate_toBumpCovering` / 定理 `isSubordinate_toBumpCovering`

English:
theorem isSubordinate_toBumpCovering
  given: {f : SmoothBumpCovering ι I M s} {U : M -> Set M}
  proof: Iff.rfl

alias ⟨_, IsSubordinate.toBumpCovering⟩ := isSubordinate_toBumpCovering

中文:
定理 isSubordinate_toBumpCovering
  条件: {f : 光滑凸覆盖 ι I M s} {U : M -> 集合 M}
  证明: Iff.rfl

alias ⟨_, IsSubordinate.toBumpCovering⟩ := isSubordinate_toBumpCovering

Depends on / 依赖: Iff.rfl
-/
theorem isSubordinate_toBumpCovering {f : SmoothBumpCovering ι I M s} {U : M -> Set M} :
    (f.toBumpCovering.IsSubordinate fun i => U (f.c i)) ↔ f.IsSubordinate U :=
  Iff.rfl

alias ⟨_, IsSubordinate.toBumpCovering⟩ := isSubordinate_toBumpCovering

/--
Definition of `toSmoothPartitionOfUnity` / `toSmoothPartitionOfUnity` 的定义

English:
definition toSmoothPartitionOfUnity
  signature: : SmoothPartitionOfUnity ι I M s
  body: fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).contMDiff

中文:
定义 toSmoothPartitionOfUnity
  签名: : 光滑单位分解 ι I M s
  定义体: fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).contMDiff

Depends on / 依赖: contMDiff, fs.toBumpCovering.toSmoothPartitionOfUnity, toBumpCovering, toSmoothPartitionOfUnity
-/
def toSmoothPartitionOfUnity : SmoothPartitionOfUnity ι I M s :=
  fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).contMDiff

/--
theorem `toSmoothPartitionOfUnity_apply` / 定理 `toSmoothPartitionOfUnity_apply`

English:
theorem toSmoothPartitionOfUnity_apply
  given: (i : ι) (x : M)
  proof: rfl

中文:
定理 toSmoothPartitionOfUnity_apply
  条件: (i : ι) (x : M)
  证明: rfl
-/
theorem toSmoothPartitionOfUnity_apply (i : ι) (x : M) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - fs j x) :=
  rfl

open scoped Classical in
/--
theorem `toSmoothPartitionOfUnity_eq_mul_prod` / 定理 `toSmoothPartitionOfUnity_eq_mul_prod`

English:
theorem toSmoothPartitionOfUnity_eq_mul_prod
  statement: (i : ι) (x : M) (t : Finset ι)
  proof: fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod i x t ht

中文:
定理 toSmoothPartitionOfUnity_eq_mul_prod
  结论: (i : ι) (x : M) (t : 有限集 ι)
  证明: fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod i x t ht

Depends on / 依赖: fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod, toBumpCovering, toPartitionOfUnity_eq_mul_prod
-/
theorem toSmoothPartitionOfUnity_eq_mul_prod (i : ι) (x : M) (t : Finset ι)
    (ht : forall j, WellOrderingRel j i -> fs j x != 0 -> j in t) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ j in t with WellOrderingRel j i, (1 - fs j x) :=
  fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod i x t ht

open scoped Classical in
/--
theorem `exists_finset_toSmoothPartitionOfUnity_eventuallyEq` / 定理 `exists_finset_toSmoothPartitionOfUnity_eventuallyEq`

English:
theorem exists_finset_toSmoothPartitionOfUnity_eventuallyEq
  given: (i : ι) (x : M)
  proof: by
  simpa using! fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq i x

中文:
定理 存在_finset_toSmoothPartitionOfUnity_eventuallyEq
  条件: (i : ι) (x : M)
  证明: by
  simpa using! fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq i x

Depends on / 依赖: exists_finset_toPartitionOfUnity_eventuallyEq, fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq, toBumpCovering
-/
theorem exists_finset_toSmoothPartitionOfUnity_eventuallyEq (i : ι) (x : M) :
    exists t : Finset ι,
      fs.toSmoothPartitionOfUnity i =ᶠ[𝓝 x]
        fs i * ∏ j in t with WellOrderingRel j i, ((1 : M -> Real) - fs j) := by
  simpa using! fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq i x

/--
theorem `toSmoothPartitionOfUnity_zero_of_zero` / 定理 `toSmoothPartitionOfUnity_zero_of_zero`

English:
theorem toSmoothPartitionOfUnity_zero_of_zero
  given: {i : ι} {x : M} (h : fs i x = 0)
  proof: fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h

中文:
定理 toSmoothPartitionOfUnity_zero_of_zero
  条件: {i : ι} {x : M} (h : fs i x = 0)
  证明: fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h

Depends on / 依赖: fs.toBumpCovering.toPartitionOfUnity_zero_of_zero, toBumpCovering, toPartitionOfUnity_zero_of_zero
-/
theorem toSmoothPartitionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
    fs.toSmoothPartitionOfUnity i x = 0 :=
  fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h

/--
theorem `support_toSmoothPartitionOfUnity_subset` / 定理 `support_toSmoothPartitionOfUnity_subset`

English:
theorem support_toSmoothPartitionOfUnity_subset
  given: (i : ι)
  proof: fs.toBumpCovering.support_toPartitionOfUnity_subset i

中文:
定理 support_toSmoothPartitionOfUnity_subset
  条件: (i : ι)
  证明: fs.toBumpCovering.support_toPartitionOfUnity_subset i

Depends on / 依赖: fs.toBumpCovering.support_toPartitionOfUnity_subset, support_toPartitionOfUnity_subset, toBumpCovering
-/
theorem support_toSmoothPartitionOfUnity_subset (i : ι) :
    support (fs.toSmoothPartitionOfUnity i) subseteq support (fs i) :=
  fs.toBumpCovering.support_toPartitionOfUnity_subset i

/--
theorem `IsSubordinate.toSmoothPartitionOfUnity` / 定理 `IsSubordinate.toSmoothPartitionOfUnity`

English:
theorem IsSubordinate.toSmoothPartitionOfUnity
  statement: {f : SmoothBumpCovering ι I M s} {U : M -> Set M}
  proof: h.toBumpCovering.toPartitionOfUnity

中文:
定理 IsSubordinate.toSmoothPartitionOfUnity
  结论: {f : 光滑凸覆盖 ι I M s} {U : M -> 集合 M}
  证明: h.toBumpCovering.toPartitionOfUnity
-/
theorem IsSubordinate.toSmoothPartitionOfUnity {f : SmoothBumpCovering ι I M s} {U : M -> Set M}
    (h : f.IsSubordinate U) : f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i) :=
  h.toBumpCovering.toPartitionOfUnity

/--
theorem `sum_toSmoothPartitionOfUnity_eq` / 定理 `sum_toSmoothPartitionOfUnity_eq`

English:
theorem sum_toSmoothPartitionOfUnity_eq
  given: (x : M)
  proof: fs.toBumpCovering.sum_toPartitionOfUnity_eq x

中文:
定理 sum_toSmoothPartitionOfUnity_eq
  条件: (x : M)
  证明: fs.toBumpCovering.sum_toPartitionOfUnity_eq x

Depends on / 依赖: fs.toBumpCovering.sum_toPartitionOfUnity_eq, sum_toPartitionOfUnity_eq, toBumpCovering
-/
theorem sum_toSmoothPartitionOfUnity_eq (x : M) :
    ∑ᶠ i, fs.toSmoothPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
  fs.toBumpCovering.sum_toPartitionOfUnity_eq x

end SmoothBumpCovering

variable (I)
variable [FiniteDimensional Real E]
variable [IsManifold I ∞ M] {n : Nat∞}

/--
theorem `exists_contMDiffMap_zero_one_of_isClosed` / 定理 `exists_contMDiffMap_zero_one_of_isClosed`

English:
theorem exists_contMDiffMap_zero_one_of_isClosed
  statement: [T2Space M] [SigmaCompactSpace M] {s t : Set M}
  proof: by
  have : forall x in t, sᶜ in 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  set g := f.toSmoothPartitionOfUnity
  refine
    ⟨⟨_, g.contMDiff_sum.of_le (by simp)⟩, fun x hx => ?_, fun x => g.sum_eq

中文:
定理 存在_contMDiffMap_zero_one_of_isClosed
  结论: [T2空间 M] [SigmaCompact空间 M] {s t : 集合 M}
  证明: by
  have : forall x in t, sᶜ in 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  set g := f.toSmoothPartitionOfUnity
  refine
    ⟨⟨_, g.contMDiff_sum.of_le (by simp)⟩, fun x hx => ?_, fun x => g.sum_eq

Depends on / 依赖: ContMDiffMap, ContMDiffMap.coeFn_mk, Pi.zero_apply, SmoothBumpCovering, SmoothBumpCovering.exists_isSubordinate, coeFn_mk, contMDiff_sum, disjoint_right, exists_isSubordinate, f.toSmoothPartitionOfUnity, f.toSmoothPartitionOfUnity_zero_of_zero, finsum_zero, g.contMDiff_sum.of_le, g.sum_eq_one, g.sum_le_one, g.sum_nonneg, hs.isOpen_compl.mem_nhds, isOpen_compl, mem_nhds, of_le
-/
theorem exists_contMDiffMap_zero_one_of_isClosed [T2Space M] [SigmaCompactSpace M] {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : C^n⟮I, M; 𝓘(Real), Real⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc 0 1 := by
  have : forall x in t, sᶜ in 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  set g := f.toSmoothPartitionOfUnity
  refine
    ⟨⟨_, g.contMDiff_sum.of_le (by simp)⟩, fun x hx => ?_, fun x => g.sum_eq_one, fun x =>
      ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  suffices forall i, g i x = 0 by simp only [this, ContMDiffMap.coeFn_mk, finsum_zero, Pi.zero_apply]
  refine fun i => f.toSmoothPartitionOfUnity_zero_of_zero ?_
  exact notMem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)

/--
theorem `exists_contMDiffMap_zero_one_nhds_of_isClosed` / 定理 `exists_contMDiffMap_zero_one_nhds_of_isClosed`

English:
theorem exists_contMDiffMap_zero_one_nhds_of_isClosed
  proof: by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfu, hfv, hf⟩ := exists_contMD

中文:
定理 存在_contMDiffMap_zero_one_nhds_of_isClosed
  证明: by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfu, hfv, hf⟩ := exists_contMD

Depends on / 依赖: eventually_of_mem, exists_contMDiffMap_zero_one_of_isClosed, hd.symm, ht.isOpen_compl, isClosed_closure, isClosed_closure.isOpen_compl, isOpen_compl, mem_nhdsSet, mem_of_superset, normal_exists_closure_subset, subset_c, subset_compl_comm, subset_compl_comm.mp, subset_compl_iff_disjoint_left, subset_compl_iff_disjoint_left.mp, subset_compl_iff_disjoint_left.mpr, u_op, u_op.mem_nhdsSet.mpr, v_op
-/
theorem exists_contMDiffMap_zero_one_nhds_of_isClosed
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : C^n⟮I, M; 𝓘(Real), Real⟯, (forallᶠ x in 𝓝ˢ s, f x = 0) ∧ (forallᶠ x in 𝓝ˢ t, f x = 1) ∧
      forall x, f x in Icc 0 1 := by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfu, hfv, hf⟩ := exists_contMDiffMap_zero_one_of_isClosed I isClosed_closure
    isClosed_closure (subset_compl_iff_disjoint_left.mp hvu) (n := n)
  refine ⟨f, ?_, ?_, hf⟩
  · exact eventually_of_mem (mem_of_superset (u_op.mem_nhdsSet.mpr hsu) subset_closure) hfu
  · exact eventually_of_mem (mem_of_superset (v_op.mem_nhdsSet.mpr htv) subset_closure) hfv

/--
theorem `exists_contMDiffMap_one_nhds_of_subset_interior` / 定理 `exists_contMDiffMap_one_nhds_of_subset_interior`

English:
theorem exists_contMDiffMap_one_nhds_of_subset_interior
  proof: by
  rcases exists_contMDiffMap_zero_one_nhds_of_isClosed I isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) (n := n) with ⟨f, h0, h1, hf⟩
  refine ⟨f, h1, fun x hx => ?_, hf⟩
exact h0.self_of_nhdsSet _ fun hx' => hx interior_subset hx'

中文:
定理 存在_contMDiffMap_one_nhds_of_subset_interior
  证明: by
  rcases exists_contMDiffMap_zero_one_nhds_of_isClosed I isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) (n := n) with ⟨f, h0, h1, hf⟩
  refine ⟨f, h1, fun x hx => ?_, hf⟩
exact h0.self_of_nhdsSet _ fun hx' => hx interior_subset hx'

Depends on / 依赖: compl_compl, exists_contMDiffMap_zero_one_nhds_of_isClosed, h0.self_of_nhdsSet, interior_subset, isClosed_compl, isOpen_interior, isOpen_interior.isClosed_compl, self_of_nhdsSet, subset_compl_iff_disjoint_left
-/
theorem exists_contMDiffMap_one_nhds_of_subset_interior
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (hd : s subseteq interior t) :
    exists f : C^n⟮I, M; 𝓘(Real), Real⟯, (forallᶠ x in 𝓝ˢ s, f x = 1) ∧ (forall x ∉ t, f x = 0) ∧
      forall x, f x in Icc 0 1 := by
  rcases exists_contMDiffMap_zero_one_nhds_of_isClosed I isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) (n := n) with ⟨f, h0, h1, hf⟩
  refine ⟨f, h1, fun x hx => ?_, hf⟩
exact h0.self_of_nhdsSet _ fun hx' => hx interior_subset hx'

namespace SmoothPartitionOfUnity

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (i : ι) (s : Set M)
  body: (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    classical
    rcases eq_or_ne j i with (rfl | h)
    · simp only [contMDiff_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
    · simp only [contMDiff_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h,
     

中文:
定义 single
  签名: (i : ι) (s : 集合 M)
  定义体: (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    classical
    rcases eq_or_ne j i with (rfl | h)
    · simp only [contMDiff_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
    · simp only [contMDiff_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h,
     

Depends on / 依赖: BumpCovering, BumpCovering.coe_single, BumpCovering.single, ContinuousMap, ContinuousMap.coe_one, ContinuousMap.coe_zero, Pi.single_eq_of_ne, Pi.single_eq_same, classical, coe_one, coe_single, coe_zero, contMDiff_one, contMDiff_zero, eq_or_ne, single, single_eq_of_ne, single_eq_same, toSmoothPartitionOfUnity
-/
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    classical
    rcases eq_or_ne j i with (rfl | h)
    · simp only [contMDiff_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
    · simp only [contMDiff_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h,
        ContinuousMap.coe_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: ι] (s
  body: ⟨single I default s⟩

中文:
实例 [可居
  签名: ι] (s
  定义体: ⟨single I default s⟩

Depends on / 依赖: single
-/
instance [Inhabited ι] (s : Set M) : Inhabited (SmoothPartitionOfUnity ι I M s) :=
  ⟨single I default s⟩

variable [T2Space M] [SigmaCompactSpace M]

/--
theorem `exists_isSubordinate` / 定理 `exists_isSubordinate`

English:
theorem exists_isSubordinate
  statement: {s : Set M} (hs : IsClosed s) (U : ι -> Set M) (ho : forall i, IsOpen (U i))
  proof: by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- porting note(https://github.com/leanprover-community/batteries/issues/116):
  -- split `rcases` into `have` + `rcases`
  have := BumpCovering.exists_isSubordinate_of

中文:
定理 存在_isSubordinate
  结论: {s : 集合 M} (hs : 是闭集 s) (U : ι -> 集合 M) (ho : 对任意 i, 是开集 (U i))
  证明: by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- porting note(https://github.com/leanprover-community/batteries/issues/116):
  -- split `rcases` into `have` + `rcases`
  have := BumpCovering.exists_isSubordinate_of

Depends on / 依赖: ChartedSpace, ChartedSpace.locallyCompactSpace, I.locallyCompactSpace, LocallyCompactSpace, locallyCompactSpace
-/
theorem exists_isSubordinate {s : Set M} (hs : IsClosed s) (U : ι -> Set M) (ho : forall i, IsOpen (U i))
    (hU : s subseteq ⋃ i, U i) : exists f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- porting note(https://github.com/leanprover-community/batteries/issues/116):
  -- split `rcases` into `have` + `rcases`
  have := BumpCovering.exists_isSubordinate_of_prop (ContMDiff I 𝓘(Real) ∞) ?_ hs U ho hU
  · rcases this with ⟨f, hf, hfU⟩
    exact ⟨f.toSmoothPartitionOfUnity hf, hfU.toSmoothPartitionOfUnity hf⟩
  · intro s t hs ht hd
    rcases exists_contMDiffMap_zero_one_of_isClosed I hs ht hd with ⟨f, hf⟩
    exact ⟨f, f.contMDiff, hf⟩

/--
theorem `exists_isSubordinate_chartAt_source_of_isClosed` / 定理 `exists_isSubordinate_chartAt_source_of_isClosed`

English:
theorem exists_isSubordinate_chartAt_source_of_isClosed
  given: {s : Set M} (hs : IsClosed s)
  proof: by
  apply exists_isSubordinate _ hs _ (fun i => (chartAt H _).open_source) (fun x hx => ?_)
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)

中文:
定理 存在_isSubordinate_chartAt_source_of_isClosed
  条件: {s : 集合 M} (hs : 是闭集 s)
  证明: by
  apply exists_isSubordinate _ hs _ (fun i => (chartAt H _).open_source) (fun x hx => ?_)
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)

Depends on / 依赖: chartAt, exists_isSubordinate, mem_chart_source, mem_iUnion_of_mem, open_source
-/
theorem exists_isSubordinate_chartAt_source_of_isClosed {s : Set M} (hs : IsClosed s) :
    exists f : SmoothPartitionOfUnity s I M s,
      f.IsSubordinate (fun x => (chartAt H (x : M)).source) := by
  apply exists_isSubordinate _ hs _ (fun i => (chartAt H _).open_source) (fun x hx => ?_)
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)

variable (M)
/--
theorem `exists_isSubordinate_chartAt_source` / 定理 `exists_isSubordinate_chartAt_source`

English:
theorem exists_isSubordinate_chartAt_source
  proof: by
  apply exists_isSubordinate _ isClosed_univ _ (fun i => (chartAt H _).open_source) (fun x _ => ?_)
  exact mem_iUnion_of_mem x (mem_chart_source H x)

中文:
定理 存在_isSubordinate_chartAt_source
  证明: by
  apply exists_isSubordinate _ isClosed_univ _ (fun i => (chartAt H _).open_source) (fun x _ => ?_)
  exact mem_iUnion_of_mem x (mem_chart_source H x)

Depends on / 依赖: chartAt, exists_isSubordinate, isClosed_univ, mem_chart_source, mem_iUnion_of_mem, open_source
-/
theorem exists_isSubordinate_chartAt_source :
    exists f : SmoothPartitionOfUnity M I M univ, f.IsSubordinate (fun x => (chartAt H x).source) := by
  apply exists_isSubordinate _ isClosed_univ _ (fun i => (chartAt H _).open_source) (fun x _ => ?_)
  exact mem_iUnion_of_mem x (mem_chart_source H x)

end SmoothPartitionOfUnity

variable [SigmaCompactSpace M] [T2Space M] {t : M -> Set F} {n : Nat∞}

/--
theorem `exists_contMDiffSection_forall_mem_convex_of_local` / 定理 `exists_contMDiffSection_forall_mem_convex_of_local`

English:
theorem exists_contMDiffSection_forall_mem_convex_of_local
  proof: by
  choose W h_nhds s_loc s_smooth h_mem_t using Hloc
  -- Construct an open cover from the interiors of the given neighborhoods.
  let U (x : M) : Set M := interior (W x)
  have hU_covers_univ : univ subseteq ⋃ x, U x := by
    intro x_pt _
    simp only [mem_iUnion]
    exact ⟨x_pt, mem_interior_

中文:
定理 存在_contMDiffSection_对任意_mem_convex_of_local
  证明: by
  choose W h_nhds s_loc s_smooth h_mem_t using Hloc
  -- Construct an open cover from the interiors of the given neighborhoods.
  let U (x : M) : Set M := interior (W x)
  have hU_covers_univ : univ subseteq ⋃ x, U x := by
    intro x_pt _
    simp only [mem_iUnion]
    exact ⟨x_pt, mem_interior_

Depends on / 依赖: h_mem_t, h_nhds, s_loc, s_smooth
-/
theorem exists_contMDiffSection_forall_mem_convex_of_local
    {F_fiber : Type*} [NormedAddCommGroup F_fiber] [NormedSpace Real F_fiber]
    (V : M -> Type*) [forall x, AddCommGroup (V x)] [forall x, TopologicalSpace (V x)] [forall x, Module Real (V x)]
    [TopologicalSpace (TotalSpace F_fiber V)] [FiberBundle F_fiber V] [VectorBundle Real F_fiber V]
    (t : forall x, Set (V x)) (ht_conv : forall x, Convex Real (t x))
    (Hloc :
      forall x₀ : M, exists U_x₀ in 𝓝 x₀, exists (s_loc : (x : M) -> V x),
        (CMDiff[U_x₀] n (T% s_loc)) ∧ (forall y in U_x₀, s_loc y in t y)) :
    exists s : Cₛ^n⟮I; F_fiber, V⟯, forall x : M, s x in t x := by
  choose W h_nhds s_loc s_smooth h_mem_t using Hloc
  -- Construct an open cover from the interiors of the given neighborhoods.
  let U (x : M) : Set M := interior (W x)
  have hU_covers_univ : univ subseteq ⋃ x, U x := by
    intro x_pt _
    simp only [mem_iUnion]
    exact ⟨x_pt, mem_interior_iff_mem_nhds.mpr (h_nhds x_pt)⟩
  -- Obtain a smooth partition of unity subordinate to this open cover.
  obtain ⟨ρ, hρU⟩ : exists ρ : SmoothPartitionOfUnity M I M univ, ρ.IsSubordinate U :=
    SmoothPartitionOfUnity.exists_isSubordinate
      I isClosed_univ U (fun x => isOpen_interior) hU_covers_univ
  -- Define the global section `s` by taking a weighted sum of the local sections.
  let s x : V x := ∑ᶠ j, (ρ j x) • s_loc j x
  -- Prove that `s`, when viewed as a map to the total space, is smooth.
  have (j : M) : CMDiff n (T% (fun x => (ρ j x) • (s_loc j x))) := by
    refine ContMDiffOn.smul_section_of_tsupport ?_ isOpen_interior (hρU j)
      ((s_smooth j).mono interior_subset)
.contMDiffOn exact ((ρ j).contMDiff).of_le (sup_eq_left.mp rfl)
  have hs : CMDiff n (T% s) := by
    apply ContMDiff.finsum_section_of_locallyFinite ?_ this
    -- Future: can grind do this?
    apply ρ.locallyFinite.subset fun i x hx => ?_
    rw [support]
    rw [mem_ofPred_eq] at hx ⊢
    exact left_ne_zero_of_smul hx
  -- Construct the smooth section and prove it lies in the convex sets `t x`.
  refine ⟨⟨s, hs⟩, fun x => ?_⟩
  apply (ht_conv x).finsum_mem (ρ.nonneg · x) (ρ.sum_eq_one (mem_univ x))
  intro j h_ρjx_ne_zero
  have h_x_in_tsupport_ρj : x in tsupport (ρ j) := subset_closure (mem_support.mpr h_ρjx_ne_zero)
  have h_x_in_Umap_j : x in W j := interior_subset (hρU j h_x_in_tsupport_ρj)
  exact h_mem_t j x h_x_in_Umap_j

/--
theorem `exists_contMDiffMap_forall_mem_convex_of_local` / 定理 `exists_contMDiffMap_forall_mem_convex_of_local`

English:
theorem exists_contMDiffMap_forall_mem_convex_of_local
  statement: (ht : forall x, Convex Real (t x))
  proof: let ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (fun _ => F) t ht
    (fun x₀ => let ⟨U, hU, g, hgs, hgt⟩ := Hloc x₀
.mpr hgs y hy, hgt⟩) ⟨U, hU, g, fun y hy => Bundle.contMDiffWithinAt_section
  ⟨⟨s, (Bundle.contMDiffAt_section _ |>.mp <| s.contMDiff ·)⟩, hs⟩

中文:
定理 存在_contMDiffMap_对任意_mem_convex_of_local
  结论: (ht : 对任意 x, 凸 实数 (t x))
  证明: let ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (fun _ => F) t ht
    (fun x₀ => let ⟨U, hU, g, hgs, hgt⟩ := Hloc x₀
.mpr hgs y hy, hgt⟩) ⟨U, hU, g, fun y hy => Bundle.contMDiffWithinAt_section
  ⟨⟨s, (Bundle.contMDiffAt_section _ |>.mp <| s.contMDiff ·)⟩, hs⟩

Depends on / 依赖: Bundle, Bundle.contMDiffAt_section, Bundle.contMDiffWithinAt_section, contMDiff, contMDiffAt_section, contMDiffWithinAt_section, exists_contMDiffSection_forall_mem_convex_of_local, s.contMDiff
-/
theorem exists_contMDiffMap_forall_mem_convex_of_local (ht : forall x, Convex Real (t x))
    (Hloc : forall x : M, exists U in 𝓝 x, exists g : M -> F, CMDiff[U] n g ∧ forall y in U, g y in t y) :
    exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, forall x, g x in t x :=
  let ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (fun _ => F) t ht
    (fun x₀ => let ⟨U, hU, g, hgs, hgt⟩ := Hloc x₀
.mpr hgs y hy, hgt⟩) ⟨U, hU, g, fun y hy => Bundle.contMDiffWithinAt_section
  ⟨⟨s, (Bundle.contMDiffAt_section _ |>.mp <| s.contMDiff ·)⟩, hs⟩

/--
theorem `exists_contMDiffMap_forall_mem_convex_of_local_const` / 定理 `exists_contMDiffMap_forall_mem_convex_of_local_const`

English:
theorem exists_contMDiffMap_forall_mem_convex_of_local_const
  statement: (ht : forall x, Convex Real (t x))
  proof: exists_contMDiffMap_forall_mem_convex_of_local I ht fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, contMDiffOn_const, fun _ => id⟩

中文:
定理 存在_contMDiffMap_对任意_mem_convex_of_local_const
  结论: (ht : 对任意 x, 凸 实数 (t x))
  证明: exists_contMDiffMap_forall_mem_convex_of_local I ht fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, contMDiffOn_const, fun _ => id⟩

Depends on / 依赖: contMDiffOn_const, exists_contMDiffMap_forall_mem_convex_of_local
-/
theorem exists_contMDiffMap_forall_mem_convex_of_local_const (ht : forall x, Convex Real (t x))
    (Hloc : forall x : M, exists c : F, forallᶠ y in 𝓝 x, c in t y) : exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, forall x, g x in t x :=
  exists_contMDiffMap_forall_mem_convex_of_local I ht fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, contMDiffOn_const, fun _ => id⟩

/--
theorem `Metric.exists_contMDiffMap_forall_closedEBall_subset` / 定理 `Metric.exists_contMDiffMap_forall_closedEBall_subset`

English:
theorem Metric.exists_contMDiffMap_forall_closedEBall_subset
  proof: by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_comm ι M]
    using! exists_contMDiffMap_forall_mem_convex_of_local_const I
      Metric.exists_forall_closedEBall_subset_aux₂
      (Metric.exists_forall_closedEBall_subset_aux₁ hK hU hKU hfin)

@[deprecated (since := "20

中文:
定理 Metric.存在_contMDiffMap_对任意_closedEBall_subset
  证明: by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_comm ι M]
    using! exists_contMDiffMap_forall_mem_convex_of_local_const I
      Metric.exists_forall_closedEBall_subset_aux₂
      (Metric.exists_forall_closedEBall_subset_aux₁ hK hU hKU hfin)

@[deprecated (since := "20

Depends on / 依赖: Metric, Metric.exists_forall_closedEBall_subset_aux, exists_contMDiffMap_forall_mem_convex_of_local_const, forall_and, forall_comm, mem_iInter, mem_inter_iff, mem_preimage
-/
theorem Metric.exists_contMDiffMap_forall_closedEBall_subset
    {M : Type*} [EMetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι -> Set M} {U : ι -> Set M}
    (hK : forall i, IsClosed (K i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i)
    (hfin : LocallyFinite K) :
    exists δ : C^n⟮I, M; 𝓘(Real, Real), Real⟯,
      (forall x, 0 < δ x) ∧ forall i, forall x in K i, Metric.closedEBall x (ENNReal.ofReal (δ x)) subseteq U i := by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_comm ι M]
    using! exists_contMDiffMap_forall_mem_convex_of_local_const I
      Metric.exists_forall_closedEBall_subset_aux₂
      (Metric.exists_forall_closedEBall_subset_aux₁ hK hU hKU hfin)

@[deprecated (since := "2026-01-24")]
alias Emetric.exists_contMDiffMap_forall_closedBall_subset :=
  Metric.exists_contMDiffMap_forall_closedEBall_subset

/--
theorem `Metric.exists_contMDiffMap_forall_closedBall_subset` / 定理 `Metric.exists_contMDiffMap_forall_closedBall_subset`

English:
theorem Metric.exists_contMDiffMap_forall_closedBall_subset
  proof: by
  rcases Metric.exists_contMDiffMap_forall_closedEBall_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.closedEBall_ofReal (hδ0 _).le]
  exact hδ i x hx

中文:
定理 Metric.存在_contMDiffMap_对任意_closedBall_subset
  证明: by
  rcases Metric.exists_contMDiffMap_forall_closedEBall_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.closedEBall_ofReal (hδ0 _).le]
  exact hδ i x hx

Depends on / 依赖: Metric, Metric.closedEBall_ofReal, Metric.exists_contMDiffMap_forall_closedEBall_subset, closedEBall_ofReal, exists_contMDiffMap_forall_closedEBall_subset
-/
theorem Metric.exists_contMDiffMap_forall_closedBall_subset
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι -> Set M} {U : ι -> Set M}
    (hK : forall i, IsClosed (K i)) (hU : forall i, IsOpen (U i)) (hKU : forall i, K i subseteq U i)
    (hfin : LocallyFinite K) :
    exists δ : C^n⟮I, M; 𝓘(Real, Real), Real⟯,
      (forall x, 0 < δ x) ∧ forall i, forall x in K i, Metric.closedBall x (δ x) subseteq U i := by
  rcases Metric.exists_contMDiffMap_forall_closedEBall_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.closedEBall_ofReal (hδ0 _).le]
  exact hδ i x hx

/--
lemma `IsOpen.exists_contMDiff_support_eq_aux` / 引理 `IsOpen.exists_contMDiff_support_eq_aux`

English:
lemma IsOpen.exists_contMDiff_support_eq_aux
  given: {s : Set H} (hs : IsOpen s)
  proof: by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  rcases h's.exists_contDiff_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    simp only [ModelWithCorners.symm_comp_self, preimage_i

中文:
引理 是开集.存在_contMDiff_support_eq_aux
  条件: {s : 集合 H} (hs : 是开集 s)
  证明: by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  rcases h's.exists_contDiff_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    simp only [ModelWithCorners.symm_comp_self, preimage_i

Depends on / 依赖: I.contMDiff, I.continuous_symm.isOpen_preimage, I.symm, IsOpen, ModelWithCorners, ModelWithCorners.symm_comp_self, Subset, Subset.trans, comp_contMDiff, contMDiff, continuous_symm, exists_contDiff_support_eq, f_diff, f_diff.comp_contMDiff, f_range, f_supp, id_eq, isOpen_preimage, preimage_comp, preimage_id_eq
-/
lemma IsOpen.exists_contMDiff_support_eq_aux {s : Set H} (hs : IsOpen s) :
    exists f : H -> Real, f.support = s ∧ CMDiff n f ∧ Set.range f subseteq Set.Icc 0 1 := by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  rcases h's.exists_contDiff_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    simp only [ModelWithCorners.symm_comp_self, preimage_id_eq, id_eq]
  · exact f_diff.comp_contMDiff I.contMDiff
  · exact Subset.trans (range_comp_subset_range _ _) f_range

/--
theorem `IsOpen.exists_contMDiff_support_eq` / 定理 `IsOpen.exists_contMDiff_support_eq`

English:
theorem IsOpen.exists_contMDiff_support_eq
  given: {s : Set M} (hs : IsOpen s)
  proof: by
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  have A : forall (c : M), exists g : H -> Real,
      g.support = (chartAt H c).target inter (chartAt H c).symm ⁻¹' s ∧
      CMDiff n g ∧ Set.range g subseteq Set.Icc 0 1 := by
    intro i
    apply IsOpen.exis

中文:
定理 是开集.存在_contMDiff_support_eq
  条件: {s : 集合 M} (hs : 是开集 s)
  证明: by
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  have A : forall (c : M), exists g : H -> Real,
      g.support = (chartAt H c).target inter (chartAt H c).symm ⁻¹' s ∧
      CMDiff n g ∧ Set.range g subseteq Set.Icc 0 1 := by
    intro i
    apply IsOpen.exis

Depends on / 依赖: CMDiff, IsOpen, IsOpen.exists_contMDiff_support_eq_aux, OpenPartialHomeomorph, OpenPartialHomeomorph.isOpen_inter_preimage_symm, Set.Icc, Set.range, SmoothPartitionOfUnity, SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source, chartAt, exists_contMDiff_support_eq_aux, exists_isSubordinate_chartAt_source, g.support, g_diff, g_supp, isOpen_inter_preimage_symm, mem_range_self, subseteq, support, target
-/
theorem IsOpen.exists_contMDiff_support_eq {s : Set M} (hs : IsOpen s) :
    exists f : M -> Real, f.support = s ∧ CMDiff n f ∧ forall x, 0 <= f x := by
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  have A : forall (c : M), exists g : H -> Real,
      g.support = (chartAt H c).target inter (chartAt H c).symm ⁻¹' s ∧
      CMDiff n g ∧ Set.range g subseteq Set.Icc 0 1 := by
    intro i
    apply IsOpen.exists_contMDiff_support_eq_aux
    exact OpenPartialHomeomorph.isOpen_inter_preimage_symm _ hs
  choose g g_supp g_diff hg using A
  have h'g : forall c x, 0 <= g c x := fun c x => (hg c (mem_range_self (f := g c) x)).1
  have h''g : forall c x, 0 <= f c x * g c (chartAt H c x) :=
    fun c x => mul_nonneg (f.nonneg c x) (h'g c _)
  refine ⟨fun x => ∑ᶠ c, f c x * g c (chartAt H c x), ?_, ?_, ?_⟩
  · refine support_eq_iff.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · apply ne_of_gt
      have B : exists c, 0 < f c x * g c (chartAt H c x) := by
        obtain ⟨c, hc⟩ : exists c, 0 < f c x := f.exists_pos_of_mem (mem_univ x)
        refine ⟨c, mul_pos hc ?_⟩
        apply lt_of_le_of_ne (h'g _ _) (Ne.symm _)
        rw [← mem_support]; rw [g_supp]; rw [← mem_preimage]; rw [preimage_inter]
        have Hx : x in tsupport (f c) := subset_tsupport _ (ne_of_gt hc)
        simp [(chartAt H c).left_inv (hf c Hx), hx, (chartAt H c).map_source (hf c Hx)]
      apply finsum_pos (fun c => h''g c x) B
      apply (f.locallyFinite.point_finite x).subset
      apply compl_subset_compl.2
      rintro c (hc : f c x = 0)
      simpa only [mul_eq_zero] using! Or.inl hc
    · apply finsum_eq_zero_of_forall_eq_zero
      intro c
      by_cases Hx : x in tsupport (f c)
      · suffices g c (chartAt H c x) = 0 by simp only [this, mul_zero]
        rw [← notMem_support]; rw [g_supp]; rw [← mem_preimage]; rw [preimage_inter]
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
    apply finsum_nonneg (fun c => h''g c x)

/--
theorem `exists_contMDiff_support_eq_eq_one_iff` / 定理 `exists_contMDiff_support_eq_eq_one_iff`

English:
theorem exists_contMDiff_support_eq_eq_one_iff
  proof: by
  /- Take `f` with support equal to `s`, and `g` with support equal to `tᶜ`. Then `f / (f + g)`
  satisfies the conclusion of the theorem. -/
  rcases hs.exists_contMDiff_support_eq I with ⟨f, f_supp, f_diff, f_pos⟩
  rcases ht.isOpen_compl.exists_contMDiff_support_eq I with ⟨g, g_supp, g_diff, g

中文:
定理 存在_contMDiff_support_eq_eq_one_iff
  证明: by
  /- Take `f` with support equal to `s`, and `g` with support equal to `tᶜ`. Then `f / (f + g)`
  satisfies the conclusion of the theorem. -/
  rcases hs.exists_contMDiff_support_eq I with ⟨f, f_supp, f_diff, f_pos⟩
  rcases ht.isOpen_compl.exists_contMDiff_support_eq I with ⟨g, g_supp, g_diff, g
-/
theorem exists_contMDiff_support_eq_eq_one_iff
    {s t : Set M} (hs : IsOpen s) (ht : IsClosed t) (h : t subseteq s) :
    exists f : M -> Real, CMDiff n f ∧ range f subseteq Icc 0 1 ∧ support f = s ∧ (forall x, x in t ↔ f x = 1) := by
  /- Take `f` with support equal to `s`, and `g` with support equal to `tᶜ`. Then `f / (f + g)`
  satisfies the conclusion of the theorem. -/
  rcases hs.exists_contMDiff_support_eq I with ⟨f, f_supp, f_diff, f_pos⟩
  rcases ht.isOpen_compl.exists_contMDiff_support_eq I with ⟨g, g_supp, g_diff, g_pos⟩
  have A : forall x, 0 < f x + g x := by
    intro x
    by_cases xs : x in support f
    · have : 0 < f x := lt_of_le_of_ne (f_pos x) (Ne.symm xs)
      linarith [g_pos x]
    · have : 0 < g x := by
        apply lt_of_le_of_ne (g_pos x) (Ne.symm ?_)
        rw [← mem_support]; rw [g_supp]
        contrapose xs
        exact h.trans f_supp.symm.subset (by simpa using xs)
      linarith [f_pos x]
  refine ⟨fun x => f x / (f x + g x), ?_, ?_, ?_, ?_⟩
  -- show that `f / (f + g)` is smooth
  · exact f_diff.div₀ (f_diff.add g_diff) (fun x => ne_of_gt (A x))
  -- show that the range is included in `[0, 1]`
  · refine range_subset_iff.2 (fun x => ⟨div_nonneg (f_pos x) (A x).le, ?_⟩)
    apply div_le_one_of_le₀ _ (A x).le
    simpa only [le_add_iff_nonneg_right] using g_pos x
  -- show that the support is `s`
  · have B : support (fun x => f x + g x) = univ := eq_univ_of_forall (fun x => (A x).ne')
    simp only [support_div, f_supp, B, inter_univ]
  -- show that the function equals one exactly on `t`
  · intro x
    simp [div_eq_one_iff_eq (A x).ne', left_eq_add, ← notMem_support, g_supp]

/--
theorem `exists_contMDiff_zero_iff_one_iff_of_isClosed` / 定理 `exists_contMDiff_zero_iff_one_iff_of_isClosed`

English:
theorem exists_contMDiff_zero_iff_one_iff_of_isClosed
  statement: {s t : Set M}
  proof: by
  rcases exists_contMDiff_support_eq_eq_one_iff I hs.isOpen_compl ht hd.subset_compl_left with
    ⟨f, f_diff, f_range, fs, ft⟩
  refine ⟨f, f_diff, f_range, ?_, ft⟩
  simp [← notMem_support, fs]

中文:
定理 存在_contMDiff_zero_iff_one_iff_of_isClosed
  结论: {s t : 集合 M}
  证明: by
  rcases exists_contMDiff_support_eq_eq_one_iff I hs.isOpen_compl ht hd.subset_compl_left with
    ⟨f, f_diff, f_range, fs, ft⟩
  refine ⟨f, f_diff, f_range, ?_, ft⟩
  simp [← notMem_support, fs]

Depends on / 依赖: exists_contMDiff_support_eq_eq_one_iff, f_diff, f_range, hd.subset_compl_left, hs.isOpen_compl, isOpen_compl, notMem_support, subset_compl_left
-/
theorem exists_contMDiff_zero_iff_one_iff_of_isClosed {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : M -> Real, CMDiff n f ∧ range f subseteq Icc 0 1 ∧ (forall x, x in s ↔ f x = 0)
      ∧ (forall x, x in t ↔ f x = 1) := by
  rcases exists_contMDiff_support_eq_eq_one_iff I hs.isOpen_compl ht hd.subset_compl_left with
    ⟨f, f_diff, f_range, fs, ft⟩
  refine ⟨f, f_diff, f_range, ?_, ft⟩
  simp [← notMem_support, fs]
