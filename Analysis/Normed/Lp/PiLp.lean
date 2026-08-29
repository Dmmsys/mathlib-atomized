/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Jireh Loreaux
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `L^p` distance on finite products of metric spaces

Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `Π i, α i`
is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$,
whereas for `p = 0` it is the cardinality of the set ${i | d (x_i, y_i) ≠ 0}$. For `p = ∞` the
distance is the supremum of the distances.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Π-type, named
`PiLp p α`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology, bornology and uniform structure on `PiLp p α` are (defeq to) the
product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

If you wish to endow a type synonym of `Π i, α i` with the `L^p` distance, you can use
`pseudoMetricSpaceToPi` and the declarations below that one.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is `lp`, the `L^p` norm on a product of (possibly
infinitely many) normed spaces, where the norm is
$$
\left(\sum ‖f (x)‖^p \right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, and some functions
have infinite `L^p` norm. These subtleties are not present in the case of finitely many metric
spaces, hence it is worth devoting a file to this specific case which is particularly well behaved.

Another related construction is `MeasureTheory.Lp`, the `L^p` norm on the space of functions from
a measure space to a normed space, where the norm is
$$
\left(\int ‖f (x)‖^p dμ\right)^{1/p}.
$$
This has all the same subtleties as `lp`, and the further subtlety that this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm).
The construction `PiLp` corresponds to the special case of `MeasureTheory.Lp` in which the basis
is a finite space equipped with the counting measure.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `PseudoEMetricSpace` and `PseudoMetricSpace`.

## TODO

TODO: the results about uniformity and bornology in the `Aux` section should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/

@[expose] public section

open Module Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal WithLp

noncomputable section

/--
Definition of `PiLp` / `PiLp` 的定义

English:
abbreviation PiLp
  signature: (p : Real>=0∞) {ι : Type*} (α : ι -> Type*)
  body: WithLp p (forall i : ι, α i)

中文:
缩写 PiLp
  签名: (p : 实数>=0∞) {ι : 类型} (α : ι -> 类型)
  定义体: WithLp p (forall i : ι, α i)

Depends on / 依赖: WithLp
-/
abbrev PiLp (p : Real>=0∞) {ι : Type*} (α : ι -> Type*) : Type _ :=
  WithLp p (forall i : ι, α i)

/-The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithLp.equiv`. -/
instance (p : Real>=0∞) {ι : Type*} (α : ι -> Type*) : CoeFun (PiLp p α) (fun _ => (i : ι) -> α i) where
  coe := ofLp

instance (p : Real>=0∞) {ι : Type*} (α : ι -> Type*) [forall i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨toLp p fun _ => default⟩

@[ext]
/--
theorem `PiLp.ext` / 定理 `PiLp.ext`

English:
theorem PiLp.ext
  statement: {p : Real>=0∞} {ι : Type*} {α : ι -> Type*} {x y : PiLp p α}
  proof: ofLp_injective p funext h

中文:
定理 PiLp.ext
  结论: {p : 实数>=0∞} {ι : 类型} {α : ι -> 类型} {x y : PiLp p α}
  证明: ofLp_injective p funext h
-/
protected theorem PiLp.ext {p : Real>=0∞} {ι : Type*} {α : ι -> Type*} {x y : PiLp p α}
(h : forall i, x i = y i) : x = y := ofLp_injective p funext h

namespace PiLp

variable (p : Real>=0∞) (𝕜 : Type*) {ι : Type*} (α : ι -> Type*) (β : ι -> Type*)
section
/- Register simplification lemmas for the applications of `PiLp` elements, as the usual lemmas
for Pi types will not trigger. -/
variable {𝕜 p α}
variable [Semiring 𝕜] [forall i, SeminormedAddCommGroup (β i)]
variable [forall i, Module 𝕜 (β i)] (c : 𝕜)
variable (x y : PiLp p β) (i : ι)

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  statement: (0 : PiLp p β) i = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  结论: (0 : PiLp p β) i = 0
  证明: rfl

@[simp]
-/
theorem zero_apply : (0 : PiLp p β) i = 0 :=
  rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  statement: (x + y) i = x i + y i
  proof: rfl

@[simp]

中文:
定理 add_apply
  结论: (x + y) i = x i + y i
  证明: rfl

@[simp]
-/
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  statement: (x - y) i = x i - y i
  proof: rfl

@[simp]

中文:
定理 sub_apply
  结论: (x - y) i = x i - y i
  证明: rfl

@[simp]
-/
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  statement: (c • x) i = c • x i
  proof: rfl

@[simp]

中文:
定理 smul_apply
  结论: (c • x) i = c • x i
  证明: rfl

@[simp]
-/
theorem smul_apply : (c • x) i = c • x i :=
  rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  statement: (-x) i = -x i
  proof: rfl

中文:
定理 neg_apply
  结论: (-x) i = -x i
  证明: rfl
-/
theorem neg_apply : (-x) i = -x i :=
  rfl

variable (p) in
/-- The projection on the `i`-th coordinate of `WithLp p (∀ i, α i)`, as a linear map. -/
@[simps!]
/--
Definition of `projₗ` / `projₗ` 的定义

English:
definition projₗ
  signature: (i : ι)
  body: (LinearMap.proj i : (forall i, β i) ->ₗ[𝕜] β i) ∘ₗ (WithLp.linearEquiv p 𝕜 (forall i, β i)).toLinearMap

中文:
定义 projₗ
  签名: (i : ι)
  定义体: (LinearMap.proj i : (forall i, β i) ->ₗ[𝕜] β i) ∘ₗ (WithLp.linearEquiv p 𝕜 (forall i, β i)).toLinearMap

Depends on / 依赖: LinearMap, LinearMap.proj, WithLp, WithLp.linearEquiv, linearEquiv, toLinearMap
-/
def projₗ (i : ι) : PiLp p β ->ₗ[𝕜] β i :=
  (LinearMap.proj i : (forall i, β i) ->ₗ[𝕜] β i) ∘ₗ (WithLp.linearEquiv p 𝕜 (forall i, β i)).toLinearMap

end

/--
lemma `toLp_apply` / 引理 `toLp_apply`

English:
lemma toLp_apply
  given: (x : forall i, α i) (i : ι)
  statement: toLp p x i = x i
  proof: rfl

中文:
引理 toLp_apply
  条件: (x : 对任意 i, α i) (i : ι)
  结论: toLp p x i = x i
  证明: rfl
-/
lemma toLp_apply (x : forall i, α i) (i : ι) : toLp p x i = x i := rfl

section Single
variable [DecidableEq ι]
variable {β}

section Zero
variable [forall i, Zero (β i)]

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (i : ι) (a : β i)
  body: toLp p (Pi.single i a)

@[simp]

中文:
定义 single
  签名: (i : ι) (a : β i)
  定义体: toLp p (Pi.single i a)

@[simp]

Depends on / 依赖: Pi.single, single
-/
def single (i : ι) (a : β i) : PiLp p β := toLp p (Pi.single i a)

@[simp]
/--
lemma `ofLp_single` / 引理 `ofLp_single`

English:
lemma ofLp_single
  given: (i : ι) (a : β i)
  statement: ofLp (single p i a) = Pi.single i a
  proof: rfl

@[simp]

中文:
引理 ofLp_single
  条件: (i : ι) (a : β i)
  结论: ofLp (single p i a) = Pi.single i a
  证明: rfl

@[simp]
-/
lemma ofLp_single (i : ι) (a : β i) : ofLp (single p i a) = Pi.single i a := rfl

@[simp]
/--
lemma `toLp_single` / 引理 `toLp_single`

English:
lemma toLp_single
  given: (i : ι) (a : β i)
  statement: toLp p (Pi.single i a) = single p i a
  proof: rfl

@[simp]

中文:
引理 toLp_single
  条件: (i : ι) (a : β i)
  结论: toLp p (Pi.single i a) = single p i a
  证明: rfl

@[simp]
-/
lemma toLp_single (i : ι) (a : β i) : toLp p (Pi.single i a) = single p i a := rfl

@[simp]
/--
lemma `single_eq_same` / 引理 `single_eq_same`

English:
lemma single_eq_same
  given: (i : ι) (a : β i)
  statement: single p i a i = a
  proof: by
  rw [ofLp_single]; rw [Pi.single_eq_same]

@[simp]

中文:
引理 single_eq_same
  条件: (i : ι) (a : β i)
  结论: single p i a i = a
  证明: by
  rw [ofLp_single]; rw [Pi.single_eq_same]

@[simp]

Depends on / 依赖: Pi.single_eq_same, ofLp_single, single_eq_same
-/
lemma single_eq_same (i : ι) (a : β i) : single p i a i = a := by
  rw [ofLp_single]; rw [Pi.single_eq_same]

@[simp]
/--
lemma `single_eq_of_ne` / 引理 `single_eq_of_ne`

English:
lemma single_eq_of_ne
  given: {i i' : ι} (h : i' != i) (a : β i)
  statement: single p i a i' = 0
  proof: by
  rw [ofLp_single]; rw [Pi.single_eq_of_ne h]

中文:
引理 single_eq_of_ne
  条件: {i i' : ι} (h : i' != i) (a : β i)
  结论: single p i a i' = 0
  证明: by
  rw [ofLp_single]; rw [Pi.single_eq_of_ne h]

Depends on / 依赖: Pi.single_eq_of_ne, ofLp_single, single_eq_of_ne
-/
lemma single_eq_of_ne {i i' : ι} (h : i' != i) (a : β i) : single p i a i' = 0 := by
  rw [ofLp_single]; rw [Pi.single_eq_of_ne h]

/-- Changing the hypothesis direction in `PiLp.single_eq_of_ne` for for ease of use by simp. -/
@[simp]
/--
lemma `single_eq_of_ne'` / 引理 `single_eq_of_ne'`

English:
lemma single_eq_of_ne'
  given: {i i' : ι} (h : i != i') (a : β i)
  statement: single p i a i' = 0
  proof: by
  rw [ofLp_single]; rw [Pi.single_eq_of_ne' h]

中文:
引理 single_eq_of_ne'
  条件: {i i' : ι} (h : i != i') (a : β i)
  结论: single p i a i' = 0
  证明: by
  rw [ofLp_single]; rw [Pi.single_eq_of_ne' h]

Depends on / 依赖: Pi.single_eq_of_ne, ofLp_single, single_eq_of_ne
-/
lemma single_eq_of_ne' {i i' : ι} (h : i != i') (a : β i) : single p i a i' = 0 := by
  rw [ofLp_single]; rw [Pi.single_eq_of_ne' h]

end Zero

@[simp]
/--
lemma `single_apply` / 引理 `single_apply`

English:
lemma single_apply
  given: [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι)
  proof: by
  rw [← toLp_single]; rw [PiLp.toLp_apply]; rw [← Pi.single_apply i a j]

中文:
引理 single_apply
  条件: [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι)
  证明: by
  rw [← toLp_single]; rw [PiLp.toLp_apply]; rw [← Pi.single_apply i a j]

Depends on / 依赖: Pi.single_apply, PiLp.toLp_apply, single_apply, toLp_apply, toLp_single
-/
lemma single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) :
    (single p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0 := by
  rw [← toLp_single]; rw [PiLp.toLp_apply]; rw [← Pi.single_apply i a j]

section AddCommGroup
variable [forall i, AddCommGroup (β i)]

@[simp]
/--
theorem `single_eq_zero_iff` / 定理 `single_eq_zero_iff`

English:
theorem single_eq_zero_iff
  given: (p : Real>=0∞) (i : ι) {a : β i}
  proof: (toLp_eq_zero p).trans Pi.single_eq_zero_iff

中文:
定理 single_eq_zero_iff
  条件: (p : 实数>=0∞) (i : ι) {a : β i}
  证明: (toLp_eq_zero p).trans Pi.single_eq_zero_iff

Depends on / 依赖: Pi.single_eq_zero_iff, single_eq_zero_iff, toLp_eq_zero
-/
theorem single_eq_zero_iff (p : Real>=0∞) (i : ι) {a : β i} :
    single p i a = 0 ↔ a = 0 :=
  (toLp_eq_zero p).trans Pi.single_eq_zero_iff

/--
lemma `single_add` / 引理 `single_add`

English:
lemma single_add
  given: (p : Real>=0∞) (i : ι) {a b : β i}
  proof: by
  simp_rw [← toLp_single, Pi.single_add, toLp_add]

中文:
引理 single_add
  条件: (p : 实数>=0∞) (i : ι) {a b : β i}
  证明: by
  simp_rw [← toLp_single, Pi.single_add, toLp_add]

Depends on / 依赖: Pi.single_add, simp_rw, single_add, toLp_add, toLp_single
-/
lemma single_add (p : Real>=0∞) (i : ι) {a b : β i} :
    single p i (a + b) = single p i a + single p i b := by
  simp_rw [← toLp_single, Pi.single_add, toLp_add]

/--
lemma `single_sub` / 引理 `single_sub`

English:
lemma single_sub
  given: (p : Real>=0∞) (i : ι) {a b : β i}
  proof: by
  simp_rw [← toLp_single, Pi.single_sub, toLp_sub]

中文:
引理 single_sub
  条件: (p : 实数>=0∞) (i : ι) {a b : β i}
  证明: by
  simp_rw [← toLp_single, Pi.single_sub, toLp_sub]

Depends on / 依赖: Pi.single_sub, simp_rw, single_sub, toLp_single, toLp_sub
-/
lemma single_sub (p : Real>=0∞) (i : ι) {a b : β i} :
    single p i (a - b) = single p i a - single p i b := by
  simp_rw [← toLp_single, Pi.single_sub, toLp_sub]

/--
lemma `single_neg` / 引理 `single_neg`

English:
lemma single_neg
  given: (p : Real>=0∞) (i : ι) {a : β i}
  proof: by
  simp_rw [← toLp_single, Pi.single_neg, toLp_neg]

中文:
引理 single_neg
  条件: (p : 实数>=0∞) (i : ι) {a : β i}
  证明: by
  simp_rw [← toLp_single, Pi.single_neg, toLp_neg]

Depends on / 依赖: Pi.single_neg, simp_rw, single_neg, toLp_neg, toLp_single
-/
lemma single_neg (p : Real>=0∞) (i : ι) {a : β i} :
    single p i (-a) = -single p i a := by
  simp_rw [← toLp_single, Pi.single_neg, toLp_neg]

end AddCommGroup

section LinearIndependent

/--
theorem `linearIndependent_single` / 定理 `linearIndependent_single`

English:
theorem linearIndependent_single
  statement: [Semiring 𝕜] {η : Type*} {ιs : η -> Type*}
  proof: by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun ji : Σ j, ιs j => Pi.single ji.1 (v ji.1 ji.2)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single v hs

中文:
定理 linearIndependent_single
  结论: [Semiring 𝕜] {η : 类型} {ιs : η -> 类型}
  证明: by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun ji : Σ j, ιs j => Pi.single ji.1 (v ji.1 ji.2)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single v hs

Depends on / 依赖: LinearIndependent, LinearMap, LinearMap.linearIndependent_iff_of_injOn, Pi.linearIndependent_single, Pi.single, WithLp, WithLp.linearEquiv, linearEquiv, linearIndependent_iff_of_injOn, linearIndependent_single, single, symm.toLinearMap, toLinearMap
-/
theorem linearIndependent_single [Semiring 𝕜] {η : Type*} {ιs : η -> Type*}
    {Ms : η -> Type*} [forall i, AddCommGroup (Ms i)] [forall i, Module 𝕜 (Ms i)] [DecidableEq η]
    (v : forall j, ιs j -> Ms j) (hs : forall i, LinearIndependent 𝕜 (v i)) :
    LinearIndependent 𝕜 fun ji : Σ j, ιs j => single p ji.1 (v ji.1 ji.2) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun ji : Σ j, ιs j => Pi.single ji.1 (v ji.1 ji.2)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single v hs

/--
theorem `linearIndependent_single_one` / 定理 `linearIndependent_single_one`

English:
theorem linearIndependent_single_one
  given: [Ring 𝕜]
  proof: by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι => Pi.single i (1 : 𝕜)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_one ι 𝕜

中文:
定理 linearIndependent_single_one
  条件: [Ring 𝕜]
  证明: by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι => Pi.single i (1 : 𝕜)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_one ι 𝕜

Depends on / 依赖: LinearIndependent, LinearMap, LinearMap.linearIndependent_iff_of_injOn, Pi.linearIndependent_single_one, Pi.single, WithLp, WithLp.linearEquiv, linearEquiv, linearIndependent_iff_of_injOn, linearIndependent_single_one, single, symm.toLinearMap, toLinearMap
-/
theorem linearIndependent_single_one [Ring 𝕜] :
    LinearIndependent 𝕜 (fun i : ι => single p i (1 : 𝕜)) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι => Pi.single i (1 : 𝕜)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_one ι 𝕜

/--
theorem `linearIndependent_single_of_ne_zero` / 定理 `linearIndependent_single_of_ne_zero`

English:
theorem linearIndependent_single_of_ne_zero
  statement: [Ring 𝕜] [IsDomain 𝕜] {M : Type*}
  proof: by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι => Pi.single i (v i)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_of_ne_zero hv

中文:
定理 linearIndependent_single_of_ne_zero
  结论: [Ring 𝕜] [IsDomain 𝕜] {M : 类型}
  证明: by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι => Pi.single i (v i)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_of_ne_zero hv

Depends on / 依赖: LinearIndependent, LinearMap, LinearMap.linearIndependent_iff_of_injOn, Pi.linearIndependent_single_of_ne_zero, Pi.single, WithLp, WithLp.linearEquiv, linearEquiv, linearIndependent_iff_of_injOn, linearIndependent_single_of_ne_zero, single, symm.toLinearMap, toLinearMap
-/
theorem linearIndependent_single_of_ne_zero [Ring 𝕜] [IsDomain 𝕜] {M : Type*}
    [AddCommGroup M] [Module 𝕜 M] [IsTorsionFree 𝕜 M] {v : ι -> M} (hv : forall i, v i != 0) :
    LinearIndependent 𝕜 fun i : ι => single p i (v i) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι => Pi.single i (v i)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_of_ne_zero hv

end LinearIndependent

end Single

section DistNorm

variable [Fintype ι]

/-!
### Definition of `edist`, `dist` and `norm` on `PiLp`

In this section we define the `edist`, `dist` and `norm` functions on `PiLp p α` without assuming
`[Fact (1 ≤ p)]` or metric properties of the spaces `α i`. This allows us to provide the rewrite
lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.to_real`.
-/


section EDist

variable [forall i, EDist (β i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EDist (PiLp p β)
  body: if p = 0 then {i | edist (f i) (g i) != 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, edist (f i) (g i) else (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

中文:
实例 :
  签名: EDist (PiLp p β)
  定义体: if p = 0 then {i | edist (f i) (g i) != 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, edist (f i) (g i) else (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

Depends on / 依赖: p.toReal, toFinite, toFinite.toFinset.card, toFinset, toReal
-/
instance : EDist (PiLp p β) where
  edist f g :=
    if p = 0 then {i | edist (f i) (g i) != 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, edist (f i) (g i) else (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {β}

/--
theorem `edist_eq_card` / 定理 `edist_eq_card`

English:
theorem edist_eq_card
  given: (f g : PiLp 0 β)
  proof: if_pos rfl

中文:
定理 edist_eq_card
  条件: (f g : PiLp 0 β)
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem edist_eq_card (f g : PiLp 0 β) :
    edist f g = {i | edist (f i) (g i) != 0}.toFinite.toFinset.card :=
  if_pos rfl

/--
theorem `edist_eq_sum` / 定理 `edist_eq_sum`

English:
theorem edist_eq_sum
  given: {p : Real>=0∞} (hp : 0 < p.toReal) (f g : PiLp p β)
  proof: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

中文:
定理 edist_eq_sum
  条件: {p : 实数>=0∞} (hp : 0 < p.to实数) (f g : PiLp p β)
  证明: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff.mp, if_neg, toReal_pos_iff
-/
theorem edist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g : PiLp p β) :
    edist f g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

/--
theorem `edist_eq_iSup` / 定理 `edist_eq_iSup`

English:
theorem edist_eq_iSup
  given: (f g : PiLp ∞ β)
  statement: edist f g = ⨆ i, edist (f i) (g i)
  proof: rfl

中文:
定理 edist_eq_iSup
  条件: (f g : PiLp ∞ β)
  结论: edist f g = ⨆ i, edist (f i) (g i)
  证明: rfl
-/
theorem edist_eq_iSup (f g : PiLp ∞ β) : edist f g = ⨆ i, edist (f i) (g i) := rfl

end EDist

section EDistProp

variable {β}
variable [forall i, PseudoEMetricSpace (β i)]

/--
theorem `edist_self` / 定理 `edist_self`

English:
theorem edist_self
  given: (f : PiLp p β)
  statement: edist f f = 0
  proof: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_iSup]
  · simp [edist_eq_sum h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

中文:
定理 edist_self
  条件: (f : PiLp p β)
  结论: edist f f = 0
  证明: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_iSup]
  · simp [edist_eq_sum h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]
-/
protected theorem edist_self (f : PiLp p β) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_iSup]
  · simp [edist_eq_sum h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/--
theorem `edist_comm` / 定理 `edist_comm`

English:
theorem edist_comm
  given: (f g : PiLp p β)
  statement: edist f g = edist g f
  proof: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, edist_comm]
  · simp only [edist_eq_iSup, edist_comm]
  · simp only [edist_eq_sum h, edist_comm]

中文:
定理 edist_comm
  条件: (f g : PiLp p β)
  结论: edist f g = edist g f
  证明: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, edist_comm]
  · simp only [edist_eq_iSup, edist_comm]
  · simp only [edist_eq_sum h, edist_comm]
-/
protected theorem edist_comm (f g : PiLp p β) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, edist_comm]
  · simp only [edist_eq_iSup, edist_comm]
  · simp only [edist_eq_sum h, edist_comm]

end EDistProp

section Dist

variable [forall i, Dist (α i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist (PiLp p α)
  body: if p = 0 then {i | dist (f i) (g i) != 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, dist (f i) (g i) else (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

中文:
实例 :
  签名: Dist (PiLp p α)
  定义体: if p = 0 then {i | dist (f i) (g i) != 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, dist (f i) (g i) else (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

Depends on / 依赖: p.toReal, toFinite, toFinite.toFinset.card, toFinset, toReal
-/
instance : Dist (PiLp p α) where
  dist f g :=
    if p = 0 then {i | dist (f i) (g i) != 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, dist (f i) (g i) else (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {α}

/--
theorem `dist_eq_card` / 定理 `dist_eq_card`

English:
theorem dist_eq_card
  given: (f g : PiLp 0 α)
  proof: if_pos rfl

中文:
定理 dist_eq_card
  条件: (f g : PiLp 0 α)
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem dist_eq_card (f g : PiLp 0 α) :
    dist f g = {i | dist (f i) (g i) != 0}.toFinite.toFinset.card :=
  if_pos rfl

/--
theorem `dist_eq_sum` / 定理 `dist_eq_sum`

English:
theorem dist_eq_sum
  given: {p : Real>=0∞} (hp : 0 < p.toReal) (f g : PiLp p α)
  proof: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

中文:
定理 dist_eq_sum
  条件: {p : 实数>=0∞} (hp : 0 < p.to实数) (f g : PiLp p α)
  证明: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff.mp, if_neg, toReal_pos_iff
-/
theorem dist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g : PiLp p α) :
    dist f g = (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

/--
theorem `dist_eq_iSup` / 定理 `dist_eq_iSup`

English:
theorem dist_eq_iSup
  given: (f g : PiLp ∞ α)
  statement: dist f g = ⨆ i, dist (f i) (g i)
  proof: rfl

中文:
定理 dist_eq_iSup
  条件: (f g : PiLp ∞ α)
  结论: dist f g = ⨆ i, dist (f i) (g i)
  证明: rfl
-/
theorem dist_eq_iSup (f g : PiLp ∞ α) : dist f g = ⨆ i, dist (f i) (g i) := rfl

end Dist

section Norm

variable [forall i, Norm (β i)]

/--
Instance `instNorm` / 实例 `instNorm`

English:
instance instNorm
  signature: : Norm (PiLp p β) where
  body: if p = 0 then {i | ‖f i‖ != 0}.toFinite.toFinset.card
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

中文:
实例 instNorm
  签名: : Norm (PiLp p β) where
  定义体: if p = 0 then {i | ‖f i‖ != 0}.toFinite.toFinset.card
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

Depends on / 依赖: p.toReal, toFinite, toFinite.toFinset.card, toFinset, toReal
-/
instance instNorm : Norm (PiLp p β) where
  norm f :=
    if p = 0 then {i | ‖f i‖ != 0}.toFinite.toFinset.card
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p β}

/--
theorem `norm_eq_card` / 定理 `norm_eq_card`

English:
theorem norm_eq_card
  given: (f : PiLp 0 β)
  statement: ‖f‖ = {i | ‖f i‖ != 0}.toFinite.toFinset.card
  proof: if_pos rfl

中文:
定理 norm_eq_card
  条件: (f : PiLp 0 β)
  结论: ‖f‖ = {i | ‖f i‖ != 0}.toFinite.toFinset.card
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem norm_eq_card (f : PiLp 0 β) : ‖f‖ = {i | ‖f i‖ != 0}.toFinite.toFinset.card :=
  if_pos rfl

/--
theorem `norm_eq_ciSup` / 定理 `norm_eq_ciSup`

English:
theorem norm_eq_ciSup
  given: (f : PiLp ∞ β)
  statement: ‖f‖ = ⨆ i, ‖f i‖
  proof: rfl

中文:
定理 norm_eq_ciSup
  条件: (f : PiLp ∞ β)
  结论: ‖f‖ = ⨆ i, ‖f i‖
  证明: rfl
-/
theorem norm_eq_ciSup (f : PiLp ∞ β) : ‖f‖ = ⨆ i, ‖f i‖ := rfl

/--
theorem `norm_eq_sum` / 定理 `norm_eq_sum`

English:
theorem norm_eq_sum
  given: (hp : 0 < p.toReal) (f : PiLp p β)
  proof: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

中文:
定理 norm_eq_sum
  条件: (hp : 0 < p.to实数) (f : PiLp p β)
  证明: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff.mp, if_neg, toReal_pos_iff
-/
theorem norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) :
    ‖f‖ = (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `PiLp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.

TODO: the results about uniformity and bornology should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/


variable [Fact (1 <= p)] [forall i, PseudoMetricSpace (α i)] [forall i, PseudoEMetricSpace (β i)]
variable [Fintype ι]

/-- Endowing the space `PiLp p β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
@[instance_reducible]
/--
Definition of `pseudoEmetricAux` / `pseudoEmetricAux` 的定义

English:
definition pseudoEmetricAux
  signature: : PseudoEMetricSpace (PiLp p β) where
  body: PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [ciSup_of_empty, ENNReal.bot_eq_zero, add_zero, nonpos_iff_eq_zero]
      -- Porting note: `le_i

中文:
定义 pseudoEmetricAux
  签名: : PseudoEMetricSpace (PiLp p β) where
  定义体: PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [ciSup_of_empty, ENNReal.bot_eq_zero, add_zero, nonpos_iff_eq_zero]
      -- Porting note: `le_i

Depends on / 依赖: PiLp.edist_self, edist_self
-/
def pseudoEmetricAux : PseudoEMetricSpace (PiLp p β) where
  edist_self := PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [ciSup_of_empty, ENNReal.bot_eq_zero, add_zero, nonpos_iff_eq_zero]
      -- Porting note: `le_iSup` needed some help
      refine
iSup_le fun i => (edist_triangle _ (g i) _).trans add_le_add
            (le_iSup (fun k => edist (f k) (g k)) i) (le_iSup (fun k => edist (g k) (h k)) i)
    · simp only [edist_eq_sum (zero_lt_one.trans_le hp)]
      calc
        (∑ i, edist (f i) (h i) ^ p.toReal) ^ (1 / p.toReal) <=
            (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          apply edist_triangle
        _ <=
            (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) +
              (∑ i, edist (g i) (h i) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.Lp_add_le _ _ _ hp

attribute [local instance] PiLp.pseudoEmetricAux

set_option backward.isDefEq.respectTransparency false in
/--
theorem `iSup_edist_ne_top_aux` / 定理 `iSup_edist_ne_top_aux`

English:
theorem iSup_edist_ne_top_aux
  statement: {ι : Type*} [Finite ι] {α : ι -> Type*}
  proof: by
  cases nonempty_fintype ι
  obtain ⟨M, hM⟩ := Finite.exists_le fun i => (⟨dist (f i) (g i), dist_nonneg⟩ : Real>=0)
  refine ne_of_lt ((iSup_le fun i => ?_).trans_lt (@ENNReal.coe_lt_top M))
  simp only [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_eq_coe_nnreal dist_nonneg]
  exact mod_c

中文:
定理 iSup_edist_ne_top_aux
  结论: {ι : 类型} [Finite ι] {α : ι -> 类型}
  证明: by
  cases nonempty_fintype ι
  obtain ⟨M, hM⟩ := Finite.exists_le fun i => (⟨dist (f i) (g i), dist_nonneg⟩ : Real>=0)
  refine ne_of_lt ((iSup_le fun i => ?_).trans_lt (@ENNReal.coe_lt_top M))
  simp only [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_eq_coe_nnreal dist_nonneg]
  exact mod_c

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.ofReal_eq_coe_nnreal, Finite, Finite.exists_le, PseudoMetricSpace, PseudoMetricSpace.edist_dist, coe_lt_top, dist_nonneg, edist_dist, exists_le, iSup_le, mod_cast, ne_of_lt, nonempty_fintype, ofReal_eq_coe_nnreal, trans_lt
-/
theorem iSup_edist_ne_top_aux {ι : Type*} [Finite ι] {α : ι -> Type*}
    [forall i, PseudoMetricSpace (α i)] (f g : PiLp ∞ α) : (⨆ i, edist (f i) (g i)) != ⊤ := by
  cases nonempty_fintype ι
  obtain ⟨M, hM⟩ := Finite.exists_le fun i => (⟨dist (f i) (g i), dist_nonneg⟩ : Real>=0)
  refine ne_of_lt ((iSup_le fun i => ?_).trans_lt (@ENNReal.coe_lt_top M))
  simp only [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_eq_coe_nnreal dist_nonneg]
  exact mod_cast hM i

/--
Definition of `pseudoMetricAux` / `pseudoMetricAux` 的定义

English:
abbreviation pseudoMetricAux
  signature: : PseudoMetricSpace (PiLp p α)
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp only [dist, top_ne_zero, ↓reduceIte]
        exact Real.iSup_nonneg fun i => dist_nonneg
      · simp only [dist]
        split_ifs with hp
        · linarith
        · exact Rea

中文:
缩写 pseudoMetricAux
  签名: : PseudoMetricSpace (PiLp p α)
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp only [dist, top_ne_zero, ↓reduceIte]
        exact Real.iSup_nonneg fun i => dist_nonneg
      · simp only [dist]
        split_ifs with hp
        · linarith
        · exact Rea

Depends on / 依赖: ENNReal, ENNReal.eq_o, Fintype, Fintype.sum_nonneg, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, Real.iSup_nonneg, dichotomy, dist_eq_iSup, dist_nonneg, edist_eq_iSup, eq_o, iSup_nonneg, isEmpty_or_nonempty, p.dichotomy, p.toReal, reduceIte, rpow_nonneg, split_ifs, sum_nonneg
-/
abbrev pseudoMetricAux : PseudoMetricSpace (PiLp p α) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp only [dist, top_ne_zero, ↓reduceIte]
        exact Real.iSup_nonneg fun i => dist_nonneg
      · simp only [dist]
        split_ifs with hp
        · linarith
        · exact Real.iSup_nonneg fun i => dist_nonneg
        · exact rpow_nonneg (Fintype.sum_nonneg fun i => by positivity) (1 / p.toReal))
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [edist_eq_iSup, dist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp
      · refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
have : BddAbove .range fun i => dist (f i) (g i) := Finite.bddAbove_range _
        simp [ciSup_le_iff this]
    · have : 0 < p.toReal := by rw [ENNReal.toReal_pos_iff_ne_top]; rintro rfl; norm_num at h
      simp only [edist_eq_sum, edist_dist, dist_eq_sum, this]
      rw [← ENNReal.ofReal_rpow_of_nonneg (by simp [Finset.sum_nonneg]; rw [Real.rpow_nonneg]) (by simp)]
      simp [Real.rpow_nonneg, ENNReal.ofReal_sum_of_nonneg, ← ENNReal.ofReal_rpow_of_nonneg]

attribute [local instance] PiLp.pseudoMetricAux

variable {p β} in
/--
theorem `edist_apply_le_edist_aux` / 定理 `edist_apply_le_edist_aux`

English:
theorem edist_apply_le_edist_aux
  given: (x y : PiLp p β) (i : ι)
  proof: by
  rcases p.dichotomy with (rfl | h)
  · simpa only [edist_eq_iSup] using le_iSup (fun i => edist (x i) (y i)) i
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_sum (zero_lt_one.trans_le h)]
    calc
      edist (x i) (y i) = (edis

中文:
定理 edist_apply_le_edist_aux
  条件: (x y : PiLp p β) (i : ι)
  证明: by
  rcases p.dichotomy with (rfl | h)
  · simpa only [edist_eq_iSup] using le_iSup (fun i => edist (x i) (y i)) i
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_sum (zero_lt_one.trans_le h)]
    calc
      edist (x i) (y i) = (edis
-/
private theorem edist_apply_le_edist_aux (x y : PiLp p β) (i : ι) :
    edist (x i) (y i) <= edist x y := by
  rcases p.dichotomy with (rfl | h)
  · simpa only [edist_eq_iSup] using le_iSup (fun i => edist (x i) (y i)) i
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_sum (zero_lt_one.trans_le h)]
    calc
      edist (x i) (y i) = (edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        simp [← ENNReal.rpow_mul, cancel, -one_div]
      _ <= (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr
        exact Finset.single_le_sum (fun i _ => (bot_le : (0 : Real>=0∞) <= _)) (Finset.mem_univ i)

/--
lemma `lipschitzWith_ofLp_aux` / 引理 `lipschitzWith_ofLp_aux`

English:
lemma lipschitzWith_ofLp_aux
  statement: LipschitzWith 1 (@ofLp p (forall i, β i))
  proof: .of_edist_le fun x y => by
    simp_rw [edist_pi_def, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
    exact edist_apply_le_edist_aux _ _

中文:
引理 lipschitzWith_ofLp_aux
  结论: LipschitzWith 1 (@ofLp p (对任意 i, β i))
  证明: .of_edist_le fun x y => by
    simp_rw [edist_pi_def, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
    exact edist_apply_le_edist_aux _ _
-/
private lemma lipschitzWith_ofLp_aux : LipschitzWith 1 (@ofLp p (forall i, β i)) :=
  .of_edist_le fun x y => by
    simp_rw [edist_pi_def, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
    exact edist_apply_le_edist_aux _ _

/--
lemma `antilipschitzWith_ofLp_aux` / 引理 `antilipschitzWith_ofLp_aux`

English:
lemma antilipschitzWith_ofLp_aux
  proof: by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp only [edist_eq_iSup, ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      ENNReal.coe_one, one_mul, iSup_le_iff]
    -- Porting note: `Finset.le_sup` needed some help
    exact fun i => Finset.le_sup (f := fun i => edist (x i) (y i

中文:
引理 antilipschitzWith_ofLp_aux
  证明: by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp only [edist_eq_iSup, ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      ENNReal.coe_one, one_mul, iSup_le_iff]
    -- Porting note: `Finset.le_sup` needed some help
    exact fun i => Finset.le_sup (f := fun i => edist (x i) (y i
-/
private lemma antilipschitzWith_ofLp_aux :
    AntilipschitzWith ((Fintype.card ι : Real>=0) ^ (1 / p).toReal) (@ofLp p (forall i, β i)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp only [edist_eq_iSup, ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      ENNReal.coe_one, one_mul, iSup_le_iff]
    -- Porting note: `Finset.le_sup` needed some help
    exact fun i => Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
  · have pos : 0 < p.toReal := zero_lt_one.trans_le h
    have nonneg : 0 <= 1 / p.toReal := one_div_nonneg.2 (le_of_lt pos)
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [edist_eq_sum pos]; rw [ENNReal.toReal_div 1 p]
    simp only [edist, ENNReal.toReal_one]
    calc
      (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) <=
          (∑ _i, edist (ofLp x) (ofLp y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr with i
        exact Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
      _ =
          ((Fintype.card ι : Real>=0) ^ (1 / p.toReal) : Real>=0) *
            edist (ofLp x) (ofLp y) := by
        simp only [nsmul_eq_mul, Finset.card_univ, ENNReal.rpow_one, Finset.sum_const,
          ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel]
        have : (Fintype.card ι : Real>=0∞) = (Fintype.card ι : Real>=0) :=
          (ENNReal.coe_natCast (Fintype.card ι)).symm
        rw [this]; rw [ENNReal.coe_rpow_of_nonneg _ nonneg]

/--
lemma `isUniformInducing_ofLp_aux` / 引理 `isUniformInducing_ofLp_aux`

English:
lemma isUniformInducing_ofLp_aux
  statement: IsUniformInducing (@ofLp p (forall i, β i))
  proof: (antilipschitzWith_ofLp_aux p β).isUniformInducing
      (lipschitzWith_ofLp_aux p β).uniformContinuous

中文:
引理 isUniformInducing_ofLp_aux
  结论: IsUniformInducing (@ofLp p (对任意 i, β i))
  证明: (antilipschitzWith_ofLp_aux p β).isUniformInducing
      (lipschitzWith_ofLp_aux p β).uniformContinuous
-/
private lemma isUniformInducing_ofLp_aux : IsUniformInducing (@ofLp p (forall i, β i)) :=
    (antilipschitzWith_ofLp_aux p β).isUniformInducing
      (lipschitzWith_ofLp_aux p β).uniformContinuous

set_option backward.privateInPublic true in
/--
lemma `uniformity_aux` / 引理 `uniformity_aux`

English:
lemma uniformity_aux
  statement: 𝓤 (PiLp p β) = 𝓤[UniformSpace.comap ofLp inferInstance]
  proof: by
  rw [← (isUniformInducing_ofLp_aux p β).comap_uniformity]
  rfl

中文:
引理 uniformity_aux
  结论: 𝓤 (PiLp p β) = 𝓤[UniformSpace.comap ofLp inferInstance]
  证明: by
  rw [← (isUniformInducing_ofLp_aux p β).comap_uniformity]
  rfl
-/
private lemma uniformity_aux : 𝓤 (PiLp p β) = 𝓤[UniformSpace.comap ofLp inferInstance] := by
  rw [← (isUniformInducing_ofLp_aux p β).comap_uniformity]
  rfl

/--
Instance `bornology` / 实例 `bornology`

English:
instance bornology
  signature: (p : Real>=0∞) (β : ι -> Type*) [forall i, Bornology (β i)]
  body: Bornology.induced ofLp

中文:
实例 bornology
  签名: (p : 实数>=0∞) (β : ι -> 类型) [对任意 i, Bornology (β i)]
  定义体: Bornology.induced ofLp

Depends on / 依赖: Bornology, Bornology.induced, induced
-/
instance bornology (p : Real>=0∞) (β : ι -> Type*) [forall i, Bornology (β i)] :
    Bornology (PiLp p β) := Bornology.induced ofLp

set_option backward.privateInPublic true in
/--
lemma `cobounded_aux` / 引理 `cobounded_aux`

English:
lemma cobounded_aux
  statement: @cobounded _ PseudoMetricSpace.toBornology = cobounded (PiLp p α)
  proof: le_antisymm (antilipschitzWith_ofLp_aux p α).tendsto_cobounded.le_comap
    (lipschitzWith_ofLp_aux p α).comap_cobounded_le

中文:
引理 cobounded_aux
  结论: @cobounded _ PseudoMetricSpace.toBornology = cobounded (PiLp p α)
  证明: le_antisymm (antilipschitzWith_ofLp_aux p α).tendsto_cobounded.le_comap
    (lipschitzWith_ofLp_aux p α).comap_cobounded_le
-/
private lemma cobounded_aux : @cobounded _ PseudoMetricSpace.toBornology = cobounded (PiLp p α) :=
  le_antisymm (antilipschitzWith_ofLp_aux p α).tendsto_cobounded.le_comap
    (lipschitzWith_ofLp_aux p α).comap_cobounded_le

end Aux


/--
Instance `topologicalSpace` / 实例 `topologicalSpace`

English:
instance topologicalSpace
  signature: [forall i, TopologicalSpace (β i)]
  body: Pi.topologicalSpace.induced ofLp

@[fun_prop, continuity]

中文:
实例 topologicalSpace
  签名: [对任意 i, TopologicalSpace (β i)]
  定义体: Pi.topologicalSpace.induced ofLp

@[fun_prop, continuity]

Depends on / 依赖: Pi.topologicalSpace.induced, induced, topologicalSpace
-/
instance topologicalSpace [forall i, TopologicalSpace (β i)] : TopologicalSpace (PiLp p β) :=
  Pi.topologicalSpace.induced ofLp

@[fun_prop, continuity]
/--
theorem `continuous_ofLp` / 定理 `continuous_ofLp`

English:
theorem continuous_ofLp
  given: [forall i, TopologicalSpace (β i)]
  statement: Continuous (@ofLp p (forall i, β i))
  proof: continuous_induced_dom

@[fun_prop, continuity]

中文:
定理 continuous_ofLp
  条件: [对任意 i, TopologicalSpace (β i)]
  结论: Continuous (@ofLp p (对任意 i, β i))
  证明: continuous_induced_dom

@[fun_prop, continuity]

Depends on / 依赖: continuous_induced_dom
-/
theorem continuous_ofLp [forall i, TopologicalSpace (β i)] : Continuous (@ofLp p (forall i, β i)) :=
  continuous_induced_dom

@[fun_prop, continuity]
/--
lemma `continuous_apply` / 引理 `continuous_apply`

English:
lemma continuous_apply
  given: [forall i, TopologicalSpace (β i)] (i : ι)
  proof: (continuous_apply i).comp (continuous_ofLp p β)

@[fun_prop, continuity]

中文:
引理 continuous_apply
  条件: [对任意 i, TopologicalSpace (β i)] (i : ι)
  证明: (continuous_apply i).comp (continuous_ofLp p β)

@[fun_prop, continuity]
-/
protected lemma continuous_apply [forall i, TopologicalSpace (β i)] (i : ι) :
    Continuous (fun f : PiLp p β => f i) := (continuous_apply i).comp (continuous_ofLp p β)

@[fun_prop, continuity]
/--
theorem `continuous_toLp` / 定理 `continuous_toLp`

English:
theorem continuous_toLp
  given: [forall i, TopologicalSpace (β i)]
  statement: Continuous (@toLp p (forall i, β i))
  proof: continuous_induced_rng.2 continuous_id

中文:
定理 continuous_toLp
  条件: [对任意 i, TopologicalSpace (β i)]
  结论: Continuous (@toLp p (对任意 i, β i))
  证明: continuous_induced_rng.2 continuous_id

Depends on / 依赖: continuous_id, continuous_induced_rng
-/
theorem continuous_toLp [forall i, TopologicalSpace (β i)] : Continuous (@toLp p (forall i, β i)) :=
  continuous_induced_rng.2 continuous_id

/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: [forall i, TopologicalSpace (β i)]
  body: WithLp.equiv p (Π i, β i)

@[simp]

中文:
定义 homeomorph
  签名: [对任意 i, TopologicalSpace (β i)]
  定义体: WithLp.equiv p (Π i, β i)

@[simp]

Depends on / 依赖: WithLp, WithLp.equiv
-/
def homeomorph [forall i, TopologicalSpace (β i)] : PiLp p β ≃ₜ (Π i, β i) where
  toEquiv := WithLp.equiv p (Π i, β i)

@[simp]
/--
lemma `toEquiv_homeomorph` / 引理 `toEquiv_homeomorph`

English:
lemma toEquiv_homeomorph
  given: [forall i, TopologicalSpace (β i)]
  proof: rfl

中文:
引理 toEquiv_homeomorph
  条件: [对任意 i, TopologicalSpace (β i)]
  证明: rfl
-/
lemma toEquiv_homeomorph [forall i, TopologicalSpace (β i)] :
    (homeomorph p β).toEquiv = WithLp.equiv p (Π i, β i) := rfl

/--
lemma `isOpenMap_apply` / 引理 `isOpenMap_apply`

English:
lemma isOpenMap_apply
  given: [forall i, TopologicalSpace (β i)] (i : ι)
  proof: (isOpenMap_eval i).comp (homeomorph p β).isOpenMap

中文:
引理 isOpenMap_apply
  条件: [对任意 i, TopologicalSpace (β i)] (i : ι)
  证明: (isOpenMap_eval i).comp (homeomorph p β).isOpenMap

Depends on / 依赖: homeomorph, isOpenMap, isOpenMap_eval
-/
lemma isOpenMap_apply [forall i, TopologicalSpace (β i)] (i : ι) :
    IsOpenMap (fun f : PiLp p β => f i) := (isOpenMap_eval i).comp (homeomorph p β).isOpenMap

/--
Instance `instProdT0Space` / 实例 `instProdT0Space`

English:
instance instProdT0Space
  signature: [forall i, TopologicalSpace (β i)] [forall i, T0Space (β i)]
  body: (homeomorph p β).symm.t0Space

中文:
实例 instProdT0Space
  签名: [对任意 i, TopologicalSpace (β i)] [对任意 i, T0Space (β i)]
  定义体: (homeomorph p β).symm.t0Space

Depends on / 依赖: homeomorph, symm.t0Space, t0Space
-/
instance instProdT0Space [forall i, TopologicalSpace (β i)] [forall i, T0Space (β i)] :
    T0Space (PiLp p β) :=
  (homeomorph p β).symm.t0Space

/--
Instance `secondCountableTopology` / 实例 `secondCountableTopology`

English:
instance secondCountableTopology
  signature: [Countable ι] [forall i, TopologicalSpace (β i)]
  body: (homeomorph p β).secondCountableTopology

中文:
实例 secondCountableTopology
  签名: [Countable ι] [对任意 i, TopologicalSpace (β i)]
  定义体: (homeomorph p β).secondCountableTopology

Depends on / 依赖: homeomorph, secondCountableTopology
-/
instance secondCountableTopology [Countable ι] [forall i, TopologicalSpace (β i)]
    [forall i, SecondCountableTopology (β i)] : SecondCountableTopology (PiLp p β) :=
  (homeomorph p β).secondCountableTopology

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: [forall i, UniformSpace (β i)]
  body: (Pi.uniformSpace β).comap ofLp

@[fun_prop]

中文:
实例 uniformSpace
  签名: [对任意 i, UniformSpace (β i)]
  定义体: (Pi.uniformSpace β).comap ofLp

@[fun_prop]

Depends on / 依赖: Pi.uniformSpace, uniformSpace
-/
instance uniformSpace [forall i, UniformSpace (β i)] : UniformSpace (PiLp p β) :=
  (Pi.uniformSpace β).comap ofLp

@[fun_prop]
/--
lemma `uniformContinuous_ofLp` / 引理 `uniformContinuous_ofLp`

English:
lemma uniformContinuous_ofLp
  given: [forall i, UniformSpace (β i)]
  proof: uniformContinuous_comap

@[fun_prop]

中文:
引理 uniformContinuous_ofLp
  条件: [对任意 i, UniformSpace (β i)]
  证明: uniformContinuous_comap

@[fun_prop]

Depends on / 依赖: uniformContinuous_comap
-/
lemma uniformContinuous_ofLp [forall i, UniformSpace (β i)] :
    UniformContinuous (@ofLp p (forall i, β i)) :=
  uniformContinuous_comap

@[fun_prop]
/--
lemma `uniformContinuous_toLp` / 引理 `uniformContinuous_toLp`

English:
lemma uniformContinuous_toLp
  given: [forall i, UniformSpace (β i)]
  proof: uniformContinuous_comap' uniformContinuous_id

中文:
引理 uniformContinuous_toLp
  条件: [对任意 i, UniformSpace (β i)]
  证明: uniformContinuous_comap' uniformContinuous_id

Depends on / 依赖: uniformContinuous_comap, uniformContinuous_id
-/
lemma uniformContinuous_toLp [forall i, UniformSpace (β i)] :
    UniformContinuous (@toLp p (forall i, β i)) :=
  uniformContinuous_comap' uniformContinuous_id

/--
Definition of `uniformEquiv` / `uniformEquiv` 的定义

English:
definition uniformEquiv
  signature: [forall i, UniformSpace (β i)]
  body: WithLp.equiv p (Π i, β i)
  uniformContinuous_toFun := uniformContinuous_ofLp p β
  uniformContinuous_invFun := uniformContinuous_toLp p β

@[simp]

中文:
定义 uniformEquiv
  签名: [对任意 i, UniformSpace (β i)]
  定义体: WithLp.equiv p (Π i, β i)
  uniformContinuous_toFun := uniformContinuous_ofLp p β
  uniformContinuous_invFun := uniformContinuous_toLp p β

@[simp]

Depends on / 依赖: WithLp, WithLp.equiv
-/
def uniformEquiv [forall i, UniformSpace (β i)] : PiLp p β ≃ᵤ (Π i, β i) where
  toEquiv := WithLp.equiv p (Π i, β i)
  uniformContinuous_toFun := uniformContinuous_ofLp p β
  uniformContinuous_invFun := uniformContinuous_toLp p β

@[simp]
/--
lemma `toHomeomorph_uniformEquiv` / 引理 `toHomeomorph_uniformEquiv`

English:
lemma toHomeomorph_uniformEquiv
  given: [forall i, UniformSpace (β i)]
  proof: rfl

@[simp]

中文:
引理 toHomeomorph_uniformEquiv
  条件: [对任意 i, UniformSpace (β i)]
  证明: rfl

@[simp]
-/
lemma toHomeomorph_uniformEquiv [forall i, UniformSpace (β i)] :
    (uniformEquiv p β).toHomeomorph = homeomorph p β := rfl

@[simp]
/--
lemma `toEquiv_uniformEquiv` / 引理 `toEquiv_uniformEquiv`

English:
lemma toEquiv_uniformEquiv
  given: [forall i, UniformSpace (β i)]
  proof: rfl

中文:
引理 toEquiv_uniformEquiv
  条件: [对任意 i, UniformSpace (β i)]
  证明: rfl
-/
lemma toEquiv_uniformEquiv [forall i, UniformSpace (β i)] :
    (uniformEquiv p β).toEquiv = WithLp.equiv p (Π i, β i) := rfl

/--
Instance `completeSpace` / 实例 `completeSpace`

English:
instance completeSpace
  signature: [forall i, UniformSpace (β i)] [forall i, CompleteSpace (β i)]
  body: (uniformEquiv p β).completeSpace_iff.2 inferInstance

中文:
实例 completeSpace
  签名: [对任意 i, UniformSpace (β i)] [对任意 i, CompleteSpace (β i)]
  定义体: (uniformEquiv p β).completeSpace_iff.2 inferInstance

Depends on / 依赖: completeSpace_iff, uniformEquiv
-/
instance completeSpace [forall i, UniformSpace (β i)] [forall i, CompleteSpace (β i)] :
    CompleteSpace (PiLp p β) :=
  (uniformEquiv p β).completeSpace_iff.2 inferInstance

section Fintype
variable [hp : Fact (1 <= p)]
variable [Fintype ι]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, PseudoEMetricSpace (β i)] : PseudoEMetricSpace (PiLp p β)
  body: (pseudoEmetricAux p β).replaceUniformity (uniformity_aux p β).symm

中文:
实例 [forall
  签名: i, PseudoEMetricSpace (β i)] : PseudoEMetricSpace (PiLp p β)
  定义体: (pseudoEmetricAux p β).replaceUniformity (uniformity_aux p β).symm

Depends on / 依赖: pseudoEmetricAux, replaceUniformity, uniformity_aux
-/
instance [forall i, PseudoEMetricSpace (β i)] : PseudoEMetricSpace (PiLp p β) :=
  (pseudoEmetricAux p β).replaceUniformity (uniformity_aux p β).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, EMetricSpace (α i)] : EMetricSpace (PiLp p α)
  body: EMetricSpace.ofT0PseudoEMetricSpace (PiLp p α)

中文:
实例 [forall
  签名: i, EMetricSpace (α i)] : EMetricSpace (PiLp p α)
  定义体: EMetricSpace.ofT0PseudoEMetricSpace (PiLp p α)

Depends on / 依赖: EMetricSpace, EMetricSpace.ofT0PseudoEMetricSpace, ofT0PseudoEMetricSpace
-/
instance [forall i, EMetricSpace (α i)] : EMetricSpace (PiLp p α) :=
  EMetricSpace.ofT0PseudoEMetricSpace (PiLp p α)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β)
  body: ((pseudoMetricAux p β).replaceUniformity (uniformity_aux p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (cobounded_aux p β).symm sᶜ

中文:
实例 [forall
  签名: i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β)
  定义体: ((pseudoMetricAux p β).replaceUniformity (uniformity_aux p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (cobounded_aux p β).symm sᶜ

Depends on / 依赖: Filter, Filter.ext_iff, cobounded_aux, ext_iff, pseudoMetricAux, replaceBornology, replaceUniformity, uniformity_aux
-/
instance [forall i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) :=
  ((pseudoMetricAux p β).replaceUniformity (uniformity_aux p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (cobounded_aux p β).symm sᶜ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, MetricSpace (α i)] : MetricSpace (PiLp p α)
  body: MetricSpace.ofT0PseudoMetricSpace _

中文:
实例 [forall
  签名: i, MetricSpace (α i)] : MetricSpace (PiLp p α)
  定义体: MetricSpace.ofT0PseudoMetricSpace _

Depends on / 依赖: MetricSpace, MetricSpace.ofT0PseudoMetricSpace, ofT0PseudoMetricSpace
-/
instance [forall i, MetricSpace (α i)] : MetricSpace (PiLp p α) :=
  MetricSpace.ofT0PseudoMetricSpace _

/--
theorem `nndist_eq_sum` / 定理 `nndist_eq_sum`

English:
theorem nndist_eq_sum
  statement: {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*} [forall i, PseudoMetricSpace (β i)]
  proof: NNReal.eq by
    push_cast
    exact dist_eq_sum (p.toReal_pos_iff_ne_top.mpr hp) _ _

中文:
定理 nndist_eq_sum
  结论: {p : 实数>=0∞} [Fact (1 <= p)] {β : ι -> 类型} [对任意 i, PseudoMetricSpace (β i)]
  证明: NNReal.eq by
    push_cast
    exact dist_eq_sum (p.toReal_pos_iff_ne_top.mpr hp) _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_sum, p.toReal_pos_iff_ne_top.mpr, toReal_pos_iff_ne_top
-/
theorem nndist_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*} [forall i, PseudoMetricSpace (β i)]
    (hp : p != ∞) (x y : PiLp p β) :
    nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) :=
NNReal.eq by
    push_cast
    exact dist_eq_sum (p.toReal_pos_iff_ne_top.mpr hp) _ _

/--
theorem `nndist_eq_iSup` / 定理 `nndist_eq_iSup`

English:
theorem nndist_eq_iSup
  given: {β : ι -> Type*} [forall i, PseudoMetricSpace (β i)] (x y : PiLp ∞ β)
  proof: NNReal.eq by
    push_cast
    exact dist_eq_iSup _ _

中文:
定理 nndist_eq_iSup
  条件: {β : ι -> 类型} [对任意 i, PseudoMetricSpace (β i)] (x y : PiLp ∞ β)
  证明: NNReal.eq by
    push_cast
    exact dist_eq_iSup _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_iSup
-/
theorem nndist_eq_iSup {β : ι -> Type*} [forall i, PseudoMetricSpace (β i)] (x y : PiLp ∞ β) :
    nndist x y = ⨆ i, nndist (x i) (y i) :=
NNReal.eq by
    push_cast
    exact dist_eq_iSup _ _

section
variable {β p}

/--
theorem `edist_apply_le` / 定理 `edist_apply_le`

English:
theorem edist_apply_le
  given: [forall i, PseudoEMetricSpace (β i)] (x y : PiLp p β) (i : ι)
  proof: edist_apply_le_edist_aux x y i

中文:
定理 edist_apply_le
  条件: [对任意 i, PseudoEMetricSpace (β i)] (x y : PiLp p β) (i : ι)
  证明: edist_apply_le_edist_aux x y i

Depends on / 依赖: edist_apply_le_edist_aux
-/
theorem edist_apply_le [forall i, PseudoEMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    edist (x i) (y i) <= edist x y :=
  edist_apply_le_edist_aux x y i

/--
theorem `nndist_apply_le` / 定理 `nndist_apply_le`

English:
theorem nndist_apply_le
  given: [forall i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι)
  proof: by
  simpa [← coe_nnreal_ennreal_nndist] using edist_apply_le x y i

中文:
定理 nndist_apply_le
  条件: [对任意 i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι)
  证明: by
  simpa [← coe_nnreal_ennreal_nndist] using edist_apply_le x y i

Depends on / 依赖: coe_nnreal_ennreal_nndist, edist_apply_le
-/
theorem nndist_apply_le [forall i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    nndist (x i) (y i) <= nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_apply_le x y i

/--
theorem `dist_apply_le` / 定理 `dist_apply_le`

English:
theorem dist_apply_le
  given: [forall i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι)
  proof: nndist_apply_le x y i

中文:
定理 dist_apply_le
  条件: [对任意 i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι)
  证明: nndist_apply_le x y i

Depends on / 依赖: nndist_apply_le
-/
theorem dist_apply_le [forall i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    dist (x i) (y i) <= dist x y :=
  nndist_apply_le x y i

end

/--
lemma `lipschitzWith_ofLp` / 引理 `lipschitzWith_ofLp`

English:
lemma lipschitzWith_ofLp
  given: [forall i, PseudoEMetricSpace (β i)]
  proof: lipschitzWith_ofLp_aux p β

中文:
引理 lipschitzWith_ofLp
  条件: [对任意 i, PseudoEMetricSpace (β i)]
  证明: lipschitzWith_ofLp_aux p β

Depends on / 依赖: lipschitzWith_ofLp_aux
-/
lemma lipschitzWith_ofLp [forall i, PseudoEMetricSpace (β i)] :
    LipschitzWith 1 (@ofLp p (forall i, β i)) :=
  lipschitzWith_ofLp_aux p β

/--
lemma `antilipschitzWith_toLp` / 引理 `antilipschitzWith_toLp`

English:
lemma antilipschitzWith_toLp
  given: [forall i, PseudoEMetricSpace (β i)]
  proof: (lipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

中文:
引理 antilipschitzWith_toLp
  条件: [对任意 i, PseudoEMetricSpace (β i)]
  证明: (lipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

Depends on / 依赖: lipschitzWith_ofLp, ofLp_toLp, to_rightInverse
-/
lemma antilipschitzWith_toLp [forall i, PseudoEMetricSpace (β i)] :
    AntilipschitzWith 1 (@toLp p (forall i, β i)) :=
  (lipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

/--
theorem `antilipschitzWith_ofLp` / 定理 `antilipschitzWith_ofLp`

English:
theorem antilipschitzWith_ofLp
  given: [forall i, PseudoEMetricSpace (β i)]
  proof: antilipschitzWith_ofLp_aux p β

中文:
定理 antilipschitzWith_ofLp
  条件: [对任意 i, PseudoEMetricSpace (β i)]
  证明: antilipschitzWith_ofLp_aux p β

Depends on / 依赖: antilipschitzWith_ofLp_aux
-/
theorem antilipschitzWith_ofLp [forall i, PseudoEMetricSpace (β i)] :
    AntilipschitzWith ((Fintype.card ι : Real>=0) ^ (1 / p).toReal) (@ofLp p (forall i, β i)) :=
  antilipschitzWith_ofLp_aux p β

/--
lemma `lipschitzWith_toLp` / 引理 `lipschitzWith_toLp`

English:
lemma lipschitzWith_toLp
  given: [forall i, PseudoEMetricSpace (β i)]
  proof: (antilipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

中文:
引理 lipschitzWith_toLp
  条件: [对任意 i, PseudoEMetricSpace (β i)]
  证明: (antilipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

Depends on / 依赖: antilipschitzWith_ofLp, ofLp_toLp, to_rightInverse
-/
lemma lipschitzWith_toLp [forall i, PseudoEMetricSpace (β i)] :
    LipschitzWith ((Fintype.card ι : Real>=0) ^ (1 / p).toReal) (@toLp p (forall i, β i)) :=
  (antilipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

/--
lemma `isometry_ofLp_infty` / 引理 `isometry_ofLp_infty`

English:
lemma isometry_ofLp_infty
  given: [forall i, PseudoEMetricSpace (β i)]
  proof: fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using lipschitzWith_ofLp ∞ β x y)
    (by simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
      one_mul] using antilipschitzWith_ofLp ∞ β x y)

中文:
引理 isometry_ofLp_infty
  条件: [对任意 i, PseudoEMetricSpace (β i)]
  证明: fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using lipschitzWith_ofLp ∞ β x y)
    (by simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
      one_mul] using antilipschitzWith_ofLp ∞ β x y)

Depends on / 依赖: ENNReal, ENNReal.coe_one, ENNReal.div_top, ENNReal.toReal_zero, NNReal, NNReal.rpow_zero, antilipschitzWith_ofLp, coe_one, div_top, le_antisymm, lipschitzWith_ofLp, one_mul, rpow_zero, toReal_zero
-/
lemma isometry_ofLp_infty [forall i, PseudoEMetricSpace (β i)] :
    Isometry (@ofLp ∞ (forall i, β i)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using lipschitzWith_ofLp ∞ β x y)
    (by simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
      one_mul] using antilipschitzWith_ofLp ∞ β x y)

/--
Instance `seminormedAddCommGroup` / 实例 `seminormedAddCommGroup`

English:
instance seminormedAddCommGroup
  signature: [forall i, SeminormedAddCommGroup (β i)]
  body: fun x y => by
    rcases p.dichotomy with (rfl | h)
    · simp only [dist_eq_iSup, norm_eq_ciSup, dist_eq_norm, add_apply, neg_apply, norm_neg_add]
    · have : p != ∞ := by
        intro hp
        rw [hp]; rw [ENNReal.toReal_top] at h
        linarith
      simp only [dist_eq_sum (zero_lt_one.tran

中文:
实例 seminormedAddCommGroup
  签名: [对任意 i, SeminormedAddCommGroup (β i)]
  定义体: fun x y => by
    rcases p.dichotomy with (rfl | h)
    · simp only [dist_eq_iSup, norm_eq_ciSup, dist_eq_norm, add_apply, neg_apply, norm_neg_add]
    · have : p != ∞ := by
        intro hp
        rw [hp]; rw [ENNReal.toReal_top] at h
        linarith
      simp only [dist_eq_sum (zero_lt_one.tran

Depends on / 依赖: ENNReal, ENNReal.toReal_top, add_apply, dichotomy, dist_eq_iSup, dist_eq_norm, dist_eq_sum, neg_apply, norm_eq_ciSup, norm_eq_sum, norm_neg_add, p.dichotomy, toReal_top, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
instance seminormedAddCommGroup [forall i, SeminormedAddCommGroup (β i)] :
    SeminormedAddCommGroup (PiLp p β) where
  dist_eq := fun x y => by
    rcases p.dichotomy with (rfl | h)
    · simp only [dist_eq_iSup, norm_eq_ciSup, dist_eq_norm, add_apply, neg_apply, norm_neg_add]
    · have : p != ∞ := by
        intro hp
        rw [hp]; rw [ENNReal.toReal_top] at h
        linarith
      simp only [dist_eq_sum (zero_lt_one.trans_le h), norm_eq_sum (zero_lt_one.trans_le h),
        dist_eq_norm, add_apply, neg_apply, norm_neg_add]

omit [Fintype ι] in
/--
lemma `isUniformInducing_toLp` / 引理 `isUniformInducing_toLp`

English:
lemma isUniformInducing_toLp
  given: [Finite ι] [forall i, PseudoEMetricSpace (β i)]
  proof: have := Fintype.ofFinite ι
  (antilipschitzWith_toLp p β).isUniformInducing
    (lipschitzWith_toLp p β).uniformContinuous

中文:
引理 isUniformInducing_toLp
  条件: [Finite ι] [对任意 i, PseudoEMetricSpace (β i)]
  证明: have := Fintype.ofFinite ι
  (antilipschitzWith_toLp p β).isUniformInducing
    (lipschitzWith_toLp p β).uniformContinuous

Depends on / 依赖: Fintype, Fintype.ofFinite, antilipschitzWith_toLp, isUniformInducing, lipschitzWith_toLp, ofFinite, uniformContinuous
-/
lemma isUniformInducing_toLp [Finite ι] [forall i, PseudoEMetricSpace (β i)] :
    IsUniformInducing (@toLp p (Π i, β i)) :=
  have := Fintype.ofFinite ι
  (antilipschitzWith_toLp p β).isUniformInducing
    (lipschitzWith_toLp p β).uniformContinuous

section
variable {β p}

/--
theorem `enorm_apply_le` / 定理 `enorm_apply_le`

English:
theorem enorm_apply_le
  given: [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι)
  proof: by
  simpa using edist_apply_le x 0 i

中文:
定理 enorm_apply_le
  条件: [对任意 i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι)
  证明: by
  simpa using edist_apply_le x 0 i

Depends on / 依赖: edist_apply_le
-/
theorem enorm_apply_le [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖ₑ <= ‖x‖ₑ := by
  simpa using edist_apply_le x 0 i

/--
theorem `nnnorm_apply_le` / 定理 `nnnorm_apply_le`

English:
theorem nnnorm_apply_le
  given: [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι)
  proof: by
  simpa using nndist_apply_le x 0 i

中文:
定理 nnnorm_apply_le
  条件: [对任意 i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι)
  证明: by
  simpa using nndist_apply_le x 0 i

Depends on / 依赖: nndist_apply_le
-/
theorem nnnorm_apply_le [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖₊ <= ‖x‖₊ := by
  simpa using nndist_apply_le x 0 i

/--
theorem `norm_apply_le` / 定理 `norm_apply_le`

English:
theorem norm_apply_le
  given: [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι)
  proof: by
  simpa using dist_apply_le x 0 i

中文:
定理 norm_apply_le
  条件: [对任意 i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι)
  证明: by
  simpa using dist_apply_le x 0 i

Depends on / 依赖: dist_apply_le
-/
theorem norm_apply_le [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖ <= ‖x‖ := by
  simpa using dist_apply_le x 0 i

end

/--
Instance `normedAddCommGroup` / 实例 `normedAddCommGroup`

English:
instance normedAddCommGroup
  signature: [forall i, NormedAddCommGroup (α i)]
  body: { PiLp.seminormedAddCommGroup p α with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 normedAddCommGroup
  签名: [对任意 i, NormedAddCommGroup (α i)]
  定义体: { PiLp.seminormedAddCommGroup p α with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: PiLp.seminormedAddCommGroup, eq_of_dist_eq_zero, seminormedAddCommGroup
-/
instance normedAddCommGroup [forall i, NormedAddCommGroup (α i)] : NormedAddCommGroup (PiLp p α) :=
  { PiLp.seminormedAddCommGroup p α with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/--
theorem `nnnorm_eq_sum` / 定理 `nnnorm_eq_sum`

English:
theorem nnnorm_eq_sum
  statement: {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*} (hp : p != ∞)
  proof: by
  ext
  simp [NNReal.coe_sum, norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]

中文:
定理 nnnorm_eq_sum
  结论: {p : 实数>=0∞} [Fact (1 <= p)] {β : ι -> 类型} (hp : p != ∞)
  证明: by
  ext
  simp [NNReal.coe_sum, norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]

Depends on / 依赖: NNReal, NNReal.coe_sum, coe_sum, norm_eq_sum, p.toReal_pos_iff_ne_top.mpr, toReal_pos_iff_ne_top
-/
theorem nnnorm_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*} (hp : p != ∞)
    [forall i, SeminormedAddCommGroup (β i)] (f : PiLp p β) :
    ‖f‖₊ = (∑ i, ‖f i‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [NNReal.coe_sum, norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]

section Linfty
variable {β}
variable [forall i, SeminormedAddCommGroup (β i)]

/--
theorem `nnnorm_eq_ciSup` / 定理 `nnnorm_eq_ciSup`

English:
theorem nnnorm_eq_ciSup
  given: (f : PiLp ∞ β)
  statement: ‖f‖₊ = ⨆ i, ‖f i‖₊
  proof: by
  ext
  simp [NNReal.coe_iSup, norm_eq_ciSup]

中文:
定理 nnnorm_eq_ciSup
  条件: (f : PiLp ∞ β)
  结论: ‖f‖₊ = ⨆ i, ‖f i‖₊
  证明: by
  ext
  simp [NNReal.coe_iSup, norm_eq_ciSup]

Depends on / 依赖: NNReal, NNReal.coe_iSup, coe_iSup, norm_eq_ciSup
-/
theorem nnnorm_eq_ciSup (f : PiLp ∞ β) : ‖f‖₊ = ⨆ i, ‖f i‖₊ := by
  ext
  simp [NNReal.coe_iSup, norm_eq_ciSup]

/--
lemma `nnnorm_ofLp` / 引理 `nnnorm_ofLp`

English:
lemma nnnorm_ofLp
  given: (f : PiLp ∞ β)
  statement: ‖ofLp f‖₊ = ‖f‖₊
  proof: by
  rw [nnnorm_eq_ciSup]; rw [Pi.nnnorm_def]; rw [Finset.sup_univ_eq_ciSup]

中文:
引理 nnnorm_ofLp
  条件: (f : PiLp ∞ β)
  结论: ‖ofLp f‖₊ = ‖f‖₊
  证明: by
  rw [nnnorm_eq_ciSup]; rw [Pi.nnnorm_def]; rw [Finset.sup_univ_eq_ciSup]
-/
@[simp] lemma nnnorm_ofLp (f : PiLp ∞ β) : ‖ofLp f‖₊ = ‖f‖₊ := by
  rw [nnnorm_eq_ciSup]; rw [Pi.nnnorm_def]; rw [Finset.sup_univ_eq_ciSup]

/--
lemma `nnnorm_toLp` / 引理 `nnnorm_toLp`

English:
lemma nnnorm_toLp
  given: (f : forall i, β i)
  statement: ‖toLp ∞ f‖₊ = ‖f‖₊
  proof: (nnnorm_ofLp _).symm

中文:
引理 nnnorm_toLp
  条件: (f : 对任意 i, β i)
  结论: ‖toLp ∞ f‖₊ = ‖f‖₊
  证明: (nnnorm_ofLp _).symm
-/
@[simp] lemma nnnorm_toLp (f : forall i, β i) : ‖toLp ∞ f‖₊ = ‖f‖₊ := (nnnorm_ofLp _).symm

/--
lemma `norm_ofLp` / 引理 `norm_ofLp`

English:
lemma norm_ofLp
  given: (f : PiLp ∞ β)
  statement: ‖ofLp f‖ = ‖f‖
  proof: congr_arg NNReal.toReal nnnorm_ofLp f

中文:
引理 norm_ofLp
  条件: (f : PiLp ∞ β)
  结论: ‖ofLp f‖ = ‖f‖
  证明: congr_arg NNReal.toReal nnnorm_ofLp f
-/
@[simp] lemma norm_ofLp (f : PiLp ∞ β) : ‖ofLp f‖ = ‖f‖ := congr_arg NNReal.toReal nnnorm_ofLp f
/--
lemma `norm_toLp` / 引理 `norm_toLp`

English:
lemma norm_toLp
  given: (f : forall i, β i)
  statement: ‖toLp ∞ f‖ = ‖f‖
  proof: (norm_ofLp _).symm

中文:
引理 norm_toLp
  条件: (f : 对任意 i, β i)
  结论: ‖toLp ∞ f‖ = ‖f‖
  证明: (norm_ofLp _).symm
-/
@[simp] lemma norm_toLp (f : forall i, β i) : ‖toLp ∞ f‖ = ‖f‖ := (norm_ofLp _).symm

end Linfty

/--
theorem `norm_eq_of_nat` / 定理 `norm_eq_of_nat`

English:
theorem norm_eq_of_nat
  statement: {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*}
  proof: by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    norm_eq_sum this]

中文:
定理 norm_eq_of_nat
  结论: {p : 实数>=0∞} [Fact (1 <= p)] {β : ι -> 类型}
  证明: by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    norm_eq_sum this]

Depends on / 依赖: ENNReal, ENNReal.natCast_ne_top, ENNReal.toReal_natCast, Real.rpow_natCast, natCast_ne_top, ne_of_eq_of_ne, norm_eq_sum, one_div, p.toReal_pos_iff_ne_top.mpr, rpow_natCast, toReal_natCast, toReal_pos_iff_ne_top
-/
theorem norm_eq_of_nat {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*}
    [forall i, SeminormedAddCommGroup (β i)] (n : Nat) (h : p = n) (f : PiLp p β) :
    ‖f‖ = (∑ i, ‖f i‖ ^ n) ^ (1 / (n : Real)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    norm_eq_sum this]

section L1
variable {β} [forall i, SeminormedAddCommGroup (β i)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `norm_eq_of_L1` / 定理 `norm_eq_of_L1`

English:
theorem norm_eq_of_L1
  given: (x : PiLp 1 β)
  statement: ‖x‖ = ∑ i : ι, ‖x i‖
  proof: by
  simp [norm_eq_sum]

中文:
定理 norm_eq_of_L1
  条件: (x : PiLp 1 β)
  结论: ‖x‖ = ∑ i : ι, ‖x i‖
  证明: by
  simp [norm_eq_sum]

Depends on / 依赖: norm_eq_sum
-/
theorem norm_eq_of_L1 (x : PiLp 1 β) : ‖x‖ = ∑ i : ι, ‖x i‖ := by
  simp [norm_eq_sum]

/--
theorem `nnnorm_eq_of_L1` / 定理 `nnnorm_eq_of_L1`

English:
theorem nnnorm_eq_of_L1
  given: (x : PiLp 1 β)
  statement: ‖x‖₊ = ∑ i : ι, ‖x i‖₊
  proof: NNReal.eq by push_cast; exact norm_eq_of_L1 x

中文:
定理 nnnorm_eq_of_L1
  条件: (x : PiLp 1 β)
  结论: ‖x‖₊ = ∑ i : ι, ‖x i‖₊
  证明: NNReal.eq by push_cast; exact norm_eq_of_L1 x

Depends on / 依赖: NNReal, NNReal.eq, norm_eq_of_L1
-/
theorem nnnorm_eq_of_L1 (x : PiLp 1 β) : ‖x‖₊ = ∑ i : ι, ‖x i‖₊ :=
NNReal.eq by push_cast; exact norm_eq_of_L1 x

/--
theorem `dist_eq_of_L1` / 定理 `dist_eq_of_L1`

English:
theorem dist_eq_of_L1
  given: (x y : PiLp 1 β)
  statement: dist x y = ∑ i, dist (x i) (y i)
  proof: by
  simp_rw [dist_eq_norm, norm_eq_of_L1, sub_apply]

中文:
定理 dist_eq_of_L1
  条件: (x y : PiLp 1 β)
  结论: dist x y = ∑ i, dist (x i) (y i)
  证明: by
  simp_rw [dist_eq_norm, norm_eq_of_L1, sub_apply]

Depends on / 依赖: dist_eq_norm, norm_eq_of_L1, simp_rw, sub_apply
-/
theorem dist_eq_of_L1 (x y : PiLp 1 β) : dist x y = ∑ i, dist (x i) (y i) := by
  simp_rw [dist_eq_norm, norm_eq_of_L1, sub_apply]

/--
theorem `nndist_eq_of_L1` / 定理 `nndist_eq_of_L1`

English:
theorem nndist_eq_of_L1
  given: (x y : PiLp 1 β)
  statement: nndist x y = ∑ i, nndist (x i) (y i)
  proof: NNReal.eq by push_cast; exact dist_eq_of_L1 _ _

中文:
定理 nndist_eq_of_L1
  条件: (x y : PiLp 1 β)
  结论: nndist x y = ∑ i, nndist (x i) (y i)
  证明: NNReal.eq by push_cast; exact dist_eq_of_L1 _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_of_L1
-/
theorem nndist_eq_of_L1 (x y : PiLp 1 β) : nndist x y = ∑ i, nndist (x i) (y i) :=
NNReal.eq by push_cast; exact dist_eq_of_L1 _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `edist_eq_of_L1` / 定理 `edist_eq_of_L1`

English:
theorem edist_eq_of_L1
  given: (x y : PiLp 1 β)
  statement: edist x y = ∑ i, edist (x i) (y i)
  proof: by
  simp [PiLp.edist_eq_sum]

中文:
定理 edist_eq_of_L1
  条件: (x y : PiLp 1 β)
  结论: edist x y = ∑ i, edist (x i) (y i)
  证明: by
  simp [PiLp.edist_eq_sum]

Depends on / 依赖: PiLp.edist_eq_sum, edist_eq_sum
-/
theorem edist_eq_of_L1 (x y : PiLp 1 β) : edist x y = ∑ i, edist (x i) (y i) := by
  simp [PiLp.edist_eq_sum]

end L1

section L2
variable {β} [forall i, SeminormedAddCommGroup (β i)]

/--
theorem `norm_eq_of_L2` / 定理 `norm_eq_of_L2`

English:
theorem norm_eq_of_L2
  given: (x : PiLp 2 β)
  proof: by
  rw [norm_eq_of_nat 2 (by norm_cast) _]
  rw [Real.sqrt_eq_rpow]
  norm_cast

中文:
定理 norm_eq_of_L2
  条件: (x : PiLp 2 β)
  证明: by
  rw [norm_eq_of_nat 2 (by norm_cast) _]
  rw [Real.sqrt_eq_rpow]
  norm_cast

Depends on / 依赖: Real.sqrt_eq_rpow, norm_eq_of_nat, sqrt_eq_rpow
-/
theorem norm_eq_of_L2 (x : PiLp 2 β) :
    ‖x‖ = √(∑ i : ι, ‖x i‖ ^ 2) := by
  rw [norm_eq_of_nat 2 (by norm_cast) _]
  rw [Real.sqrt_eq_rpow]
  norm_cast

/--
theorem `nnnorm_eq_of_L2` / 定理 `nnnorm_eq_of_L2`

English:
theorem nnnorm_eq_of_L2
  given: (x : PiLp 2 β)
  proof: NNReal.eq by
    push_cast
    exact norm_eq_of_L2 x

中文:
定理 nnnorm_eq_of_L2
  条件: (x : PiLp 2 β)
  证明: NNReal.eq by
    push_cast
    exact norm_eq_of_L2 x

Depends on / 依赖: NNReal, NNReal.eq, norm_eq_of_L2
-/
theorem nnnorm_eq_of_L2 (x : PiLp 2 β) :
    ‖x‖₊ = NNReal.sqrt (∑ i : ι, ‖x i‖₊ ^ 2) :=
NNReal.eq by
    push_cast
    exact norm_eq_of_L2 x

/--
theorem `norm_sq_eq_of_L2` / 定理 `norm_sq_eq_of_L2`

English:
theorem norm_sq_eq_of_L2
  given: (β : ι -> Type*) [forall i, SeminormedAddCommGroup (β i)] (x : PiLp 2 β)
  proof: by
  suffices ‖x‖₊ ^ 2 = ∑ i : ι, ‖x i‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) this
  rw [nnnorm_eq_of_L2]; rw [NNReal.sq_sqrt]

中文:
定理 norm_sq_eq_of_L2
  条件: (β : ι -> 类型) [对任意 i, SeminormedAddCommGroup (β i)] (x : PiLp 2 β)
  证明: by
  suffices ‖x‖₊ ^ 2 = ∑ i : ι, ‖x i‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) this
  rw [nnnorm_eq_of_L2]; rw [NNReal.sq_sqrt]

Depends on / 依赖: NNReal, NNReal.coe_sum, NNReal.sq_sqrt, coe_sum, congr_arg, nnnorm_eq_of_L2, sq_sqrt
-/
theorem norm_sq_eq_of_L2 (β : ι -> Type*) [forall i, SeminormedAddCommGroup (β i)] (x : PiLp 2 β) :
    ‖x‖ ^ 2 = ∑ i : ι, ‖x i‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ∑ i : ι, ‖x i‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) this
  rw [nnnorm_eq_of_L2]; rw [NNReal.sq_sqrt]

/--
theorem `dist_eq_of_L2` / 定理 `dist_eq_of_L2`

English:
theorem dist_eq_of_L2
  given: (x y : PiLp 2 β)
  proof: by
  simp_rw [dist_eq_norm, norm_eq_of_L2, sub_apply]

中文:
定理 dist_eq_of_L2
  条件: (x y : PiLp 2 β)
  证明: by
  simp_rw [dist_eq_norm, norm_eq_of_L2, sub_apply]

Depends on / 依赖: dist_eq_norm, norm_eq_of_L2, simp_rw, sub_apply
-/
theorem dist_eq_of_L2 (x y : PiLp 2 β) :
    dist x y = √(∑ i, dist (x i) (y i) ^ 2) := by
  simp_rw [dist_eq_norm, norm_eq_of_L2, sub_apply]

/--
theorem `dist_sq_eq_of_L2` / 定理 `dist_sq_eq_of_L2`

English:
theorem dist_sq_eq_of_L2
  given: (x y : PiLp 2 β)
  proof: by
  simp_rw [dist_eq_norm, norm_sq_eq_of_L2, sub_apply]

中文:
定理 dist_sq_eq_of_L2
  条件: (x y : PiLp 2 β)
  证明: by
  simp_rw [dist_eq_norm, norm_sq_eq_of_L2, sub_apply]

Depends on / 依赖: dist_eq_norm, norm_sq_eq_of_L2, simp_rw, sub_apply
-/
theorem dist_sq_eq_of_L2 (x y : PiLp 2 β) :
    dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 := by
  simp_rw [dist_eq_norm, norm_sq_eq_of_L2, sub_apply]

/--
theorem `nndist_eq_of_L2` / 定理 `nndist_eq_of_L2`

English:
theorem nndist_eq_of_L2
  given: (x y : PiLp 2 β)
  proof: NNReal.eq by
    push_cast
    exact dist_eq_of_L2 _ _

中文:
定理 nndist_eq_of_L2
  条件: (x y : PiLp 2 β)
  证明: NNReal.eq by
    push_cast
    exact dist_eq_of_L2 _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_of_L2
-/
theorem nndist_eq_of_L2 (x y : PiLp 2 β) :
    nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
NNReal.eq by
    push_cast
    exact dist_eq_of_L2 _ _

/--
theorem `edist_eq_of_L2` / 定理 `edist_eq_of_L2`

English:
theorem edist_eq_of_L2
  given: (x y : PiLp 2 β)
  proof: by simp [PiLp.edist_eq_sum]

中文:
定理 edist_eq_of_L2
  条件: (x y : PiLp 2 β)
  证明: by simp [PiLp.edist_eq_sum]

Depends on / 依赖: PiLp.edist_eq_sum, edist_eq_sum
-/
theorem edist_eq_of_L2 (x y : PiLp 2 β) :
    edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : Real) := by simp [PiLp.edist_eq_sum]

end L2

/--
Instance `instIsBoundedSMul` / 实例 `instIsBoundedSMul`

English:
instance instIsBoundedSMul
  signature: [SeminormedRing 𝕜] [forall i, SeminormedAddCommGroup (β i)]
  body: .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, ofLp_smul]
      exact nnnorm_smul_le c (ofLp f)
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum 

中文:
实例 instIsBoundedSMul
  签名: [SeminormedRing 𝕜] [对任意 i, SeminormedAddCommGroup (β i)]
  定义体: .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, ofLp_smul]
      exact nnnorm_smul_le c (ofLp f)
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum 

Depends on / 依赖: Finset, Finset.mul_sum, NNReal, NNReal.mul_rpow, NNReal.rpow_inv_le_iff, NNReal.rpow_mul, NNReal.rpow_one, dichotomy, hp0.ne, mul_rpow, mul_sum, nnnorm_eq_sum, nnnorm_ofLp, nnnorm_smul_le, ofLp_smul, of_nnnorm_smul_le, one_div, p.dichotomy, p.toReal, p.toReal_pos_iff_ne_top.mp
-/
instance instIsBoundedSMul [SeminormedRing 𝕜] [forall i, SeminormedAddCommGroup (β i)]
    [forall i, Module 𝕜 (β i)] [forall i, IsBoundedSMul 𝕜 (β i)] :
    IsBoundedSMul 𝕜 (PiLp p β) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, ofLp_smul]
      exact nnnorm_smul_le c (ofLp f)
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt]; rw [nnnorm_eq_sum hpt]; rw [one_div]; rw [NNReal.rpow_inv_le_iff hp0]; rw [NNReal.mul_rpow]; rw [← NNReal.rpow_mul]; rw [inv_mul_cancel₀ hp0.ne']; rw [NNReal.rpow_one]; rw [Finset.mul_sum]
      simp_rw [← NNReal.mul_rpow, smul_apply]
      gcongr
      apply nnnorm_smul_le

/--
Instance `instNormSMulClass` / 实例 `instNormSMulClass`

English:
instance instNormSMulClass
  signature: [SeminormedRing 𝕜] [forall i, SeminormedAddCommGroup (β i)]
  body: .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt]; rw [nnnorm_eq_s

中文:
实例 instNormSMulClass
  签名: [SeminormedRing 𝕜] [对任意 i, SeminormedAddCommGroup (β i)]
  定义体: .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt]; rw [nnnorm_eq_s

Depends on / 依赖: Finset, Finset.mul_sum, NNReal, NNReal.mul_rpow, NNReal.rpow_inv_eq_iff, NNReal.rpow_mul, NNReal.rpow_one, WithLp, WithLp.ofLp_smul, dichotomy, hp0.ne, mul_rpow, mul_sum, nnnorm, nnnorm_eq_sum, nnnorm_ofLp, nnnorm_smul, ofLp_smul, of_nnnorm_smul, one_div
-/
instance instNormSMulClass [SeminormedRing 𝕜] [forall i, SeminormedAddCommGroup (β i)]
    [forall i, Module 𝕜 (β i)] [forall i, NormSMulClass 𝕜 (β i)] :
    NormSMulClass 𝕜 (PiLp p β) :=
  .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt]; rw [nnnorm_eq_sum hpt]; rw [one_div]; rw [NNReal.rpow_inv_eq_iff hp0.ne']; rw [NNReal.mul_rpow]; rw [← NNReal.rpow_mul]; rw [inv_mul_cancel₀ hp0.ne']; rw [NNReal.rpow_one]; rw [Finset.mul_sum]
      simp_rw [← NNReal.mul_rpow, smul_apply, nnnorm_smul]

/--
Instance `normedSpace` / 实例 `normedSpace`

English:
instance normedSpace
  signature: [NormedField 𝕜] [forall i, SeminormedAddCommGroup (β i)]
  body: norm_smul_le

中文:
实例 normedSpace
  签名: [NormedField 𝕜] [对任意 i, SeminormedAddCommGroup (β i)]
  定义体: norm_smul_le

Depends on / 依赖: norm_smul_le
-/
instance normedSpace [NormedField 𝕜] [forall i, SeminormedAddCommGroup (β i)]
    [forall i, NormedSpace 𝕜 (β i)] : NormedSpace 𝕜 (PiLp p β) where
  norm_smul_le := norm_smul_le

variable {𝕜 p α}
variable [Semiring 𝕜] [forall i, SeminormedAddCommGroup (α i)] [forall i, SeminormedAddCommGroup (β i)]
variable [forall i, Module 𝕜 (α i)] [forall i, Module 𝕜 (β i)] (c : 𝕜)

/--
Definition of `equivₗᵢ` / `equivₗᵢ` 的定义

English:
definition equivₗᵢ
  signature: : PiLp ∞ β ≃ₗᵢ[𝕜] (forall i, β i) where
  body: WithLp.linearEquiv ∞ 𝕜 _
  norm_map' := norm_ofLp

中文:
定义 equivₗᵢ
  签名: : PiLp ∞ β ≃ₗᵢ[𝕜] (对任意 i, β i) where
  定义体: WithLp.linearEquiv ∞ 𝕜 _
  norm_map' := norm_ofLp

Depends on / 依赖: WithLp, WithLp.linearEquiv, linearEquiv
-/
def equivₗᵢ : PiLp ∞ β ≃ₗᵢ[𝕜] (forall i, β i) where
  __ := WithLp.linearEquiv ∞ 𝕜 _
  norm_map' := norm_ofLp

section piLpCongrLeft
variable {ι' : Type*}
variable [Fintype ι']
variable (p 𝕜)
variable (E : Type*) [SeminormedAddCommGroup E] [Module 𝕜 E]

/--
Definition of `_root_.LinearIsometryEquiv.piLpCongrLeft` / `_root_.LinearIsometryEquiv.piLpCongrLeft` 的定义

English:
definition _root_.LinearIsometryEquiv.piLpCongrLeft
  signature: (e : ι ≃ ι')
  body: (WithLp.linearEquiv p 𝕜 (ι -> E)).trans
    ((LinearEquiv.piCongrLeft' 𝕜 (fun _ : ι => E) e).trans (WithLp.linearEquiv p 𝕜 (ι' -> E)).symm)
  norm_map' x' := by
    rcases p.dichotomy with (rfl | h)
    · simp_rw [norm_eq_ciSup]
      exact e.symm.iSup_congr fun _ => rfl
    · simp only [norm_eq_sum

中文:
定义 _root_.LinearIsometryEquiv.piLpCongrLeft
  签名: (e : ι ≃ ι')
  定义体: (WithLp.linearEquiv p 𝕜 (ι -> E)).trans
    ((LinearEquiv.piCongrLeft' 𝕜 (fun _ : ι => E) e).trans (WithLp.linearEquiv p 𝕜 (ι' -> E)).symm)
  norm_map' x' := by
    rcases p.dichotomy with (rfl | h)
    · simp_rw [norm_eq_ciSup]
      exact e.symm.iSup_congr fun _ => rfl
    · simp only [norm_eq_sum

Depends on / 依赖: WithLp, WithLp.linearEquiv, linearEquiv
-/
def _root_.LinearIsometryEquiv.piLpCongrLeft (e : ι ≃ ι') :
    (PiLp p fun _ : ι => E) ≃ₗᵢ[𝕜] PiLp p fun _ : ι' => E where
  toLinearEquiv := (WithLp.linearEquiv p 𝕜 (ι -> E)).trans
    ((LinearEquiv.piCongrLeft' 𝕜 (fun _ : ι => E) e).trans (WithLp.linearEquiv p 𝕜 (ι' -> E)).symm)
  norm_map' x' := by
    rcases p.dichotomy with (rfl | h)
    · simp_rw [norm_eq_ciSup]
      exact e.symm.iSup_congr fun _ => rfl
    · simp only [norm_eq_sum (zero_lt_one.trans_le h)]
      congr 1
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

variable {p 𝕜 E}

@[simp]
/--
theorem `_root_.LinearIsometryEquiv.piLpCongrLeft_apply` / 定理 `_root_.LinearIsometryEquiv.piLpCongrLeft_apply`

English:
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_apply
  given: (e : ι ≃ ι') (v : PiLp p fun _ : ι => E)
  proof: rfl

@[simp]

中文:
定理 _root_.LinearIsometryEquiv.piLpCongrLeft_apply
  条件: (e : ι ≃ ι') (v : PiLp p fun _ : ι => E)
  证明: rfl

@[simp]
-/
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_apply (e : ι ≃ ι') (v : PiLp p fun _ : ι => E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e v = Equiv.piCongrLeft' (fun _ : ι => E) e v :=
  rfl

@[simp]
/--
theorem `_root_.LinearIsometryEquiv.piLpCongrLeft_symm` / 定理 `_root_.LinearIsometryEquiv.piLpCongrLeft_symm`

English:
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_symm
  given: (e : ι ≃ ι')
  proof: by
  ext
  simp [LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.symm]

@[simp high]

中文:
定理 _root_.LinearIsometryEquiv.piLpCongrLeft_symm
  条件: (e : ι ≃ ι')
  证明: by
  ext
  simp [LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.symm]

@[simp high]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.symm, piLpCongrLeft
-/
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_symm (e : ι ≃ ι') :
    (LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e).symm =
      LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e.symm := by
  ext
  simp [LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.symm]

@[simp high]
/--
theorem `_root_.LinearIsometryEquiv.piLpCongrLeft_single` / 定理 `_root_.LinearIsometryEquiv.piLpCongrLeft_single`

English:
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_single
  statement: [DecidableEq ι] [DecidableEq ι']
  proof: by
  ext x
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    Pi.single, Function.update, Equiv.symm_apply_eq]

中文:
定理 _root_.LinearIsometryEquiv.piLpCongrLeft_single
  结论: [DecidableEq ι] [DecidableEq ι']
  证明: by
  ext x
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    Pi.single, Function.update, Equiv.symm_apply_eq]

Depends on / 依赖: Equiv.piCongrLeft, Equiv.symm_apply_eq, Function, Function.update, LinearIsometryEquiv, LinearIsometryEquiv.piLpCongrLeft_apply, Pi.single, piCongrLeft, piLpCongrLeft_apply, single, symm_apply_eq, update
-/
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_single [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') (i : ι) (v : E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e (single p i v) = single p (e i) v := by
  ext x
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    Pi.single, Function.update, Equiv.symm_apply_eq]

end piLpCongrLeft

section piLpCongrRight
variable {β}

variable (p) in
/--
Definition of `_root_.LinearIsometryEquiv.piLpCongrRight` / `_root_.LinearIsometryEquiv.piLpCongrRight` 的定义

English:
definition _root_.LinearIsometryEquiv.piLpCongrRight
  signature: (e : forall i, α i ≃ₗᵢ[𝕜] β i)
  body: WithLp.linearEquiv _ _ _
      ≪≫ₗ (LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp only [coe_symm_linearEquiv, LinearEquiv.trans_apply, coe_linearEquiv]
    obtai

中文:
定义 _root_.LinearIsometryEquiv.piLpCongrRight
  签名: (e : 对任意 i, α i ≃ₗᵢ[𝕜] β i)
  定义体: WithLp.linearEquiv _ _ _
      ≪≫ₗ (LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp only [coe_symm_linearEquiv, LinearEquiv.trans_apply, coe_linearEquiv]
    obtai
-/
protected def _root_.LinearIsometryEquiv.piLpCongrRight (e : forall i, α i ≃ₗᵢ[𝕜] β i) :
    PiLp p α ≃ₗᵢ[𝕜] PiLp p β where
  toLinearEquiv :=
    WithLp.linearEquiv _ _ _
      ≪≫ₗ (LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp only [coe_symm_linearEquiv, LinearEquiv.trans_apply, coe_linearEquiv]
    obtain rfl | hp := p.dichotomy
    · simp_rw [PiLp.norm_toLp, Pi.norm_def, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.nnnorm_map]
· have : 0 < p.toReal := zero_lt_one.trans_le by norm_cast
      simp only [PiLp.norm_eq_sum this, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, one_div]

@[simp]
/--
theorem `_root_.LinearIsometryEquiv.piLpCongrRight_apply` / 定理 `_root_.LinearIsometryEquiv.piLpCongrRight_apply`

English:
theorem _root_.LinearIsometryEquiv.piLpCongrRight_apply
  given: (e : forall i, α i ≃ₗᵢ[𝕜] β i) (x : PiLp p α)
  proof: rfl

@[simp]

中文:
定理 _root_.LinearIsometryEquiv.piLpCongrRight_apply
  条件: (e : 对任意 i, α i ≃ₗᵢ[𝕜] β i) (x : PiLp p α)
  证明: rfl

@[simp]
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_apply (e : forall i, α i ≃ₗᵢ[𝕜] β i) (x : PiLp p α) :
    LinearIsometryEquiv.piLpCongrRight p e x = toLp p fun i => e i (x i) := rfl

@[simp]
/--
theorem `_root_.LinearIsometryEquiv.piLpCongrRight_refl` / 定理 `_root_.LinearIsometryEquiv.piLpCongrRight_refl`

English:
theorem _root_.LinearIsometryEquiv.piLpCongrRight_refl
  proof: rfl

@[simp]

中文:
定理 _root_.LinearIsometryEquiv.piLpCongrRight_refl
  证明: rfl

@[simp]
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_refl :
    LinearIsometryEquiv.piLpCongrRight p (fun i => .refl 𝕜 (α i)) = .refl _ _ :=
  rfl

@[simp]
/--
theorem `_root_.LinearIsometryEquiv.piLpCongrRight_symm` / 定理 `_root_.LinearIsometryEquiv.piLpCongrRight_symm`

English:
theorem _root_.LinearIsometryEquiv.piLpCongrRight_symm
  given: (e : forall i, α i ≃ₗᵢ[𝕜] β i)
  proof: rfl

@[simp high]

中文:
定理 _root_.LinearIsometryEquiv.piLpCongrRight_symm
  条件: (e : 对任意 i, α i ≃ₗᵢ[𝕜] β i)
  证明: rfl

@[simp high]
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_symm (e : forall i, α i ≃ₗᵢ[𝕜] β i) :
    (LinearIsometryEquiv.piLpCongrRight p e).symm =
      LinearIsometryEquiv.piLpCongrRight p (fun i => (e i).symm) :=
  rfl

@[simp high]
/--
theorem `_root_.LinearIsometryEquiv.piLpCongrRight_single` / 定理 `_root_.LinearIsometryEquiv.piLpCongrRight_single`

English:
theorem _root_.LinearIsometryEquiv.piLpCongrRight_single
  statement: (e : forall i, α i ≃ₗᵢ[𝕜] β i) [DecidableEq ι]
  proof: PiLp.ext Pi.apply_single (e ·) (fun _ => map_zero _) _ _

中文:
定理 _root_.LinearIsometryEquiv.piLpCongrRight_single
  结论: (e : 对任意 i, α i ≃ₗᵢ[𝕜] β i) [DecidableEq ι]
  证明: PiLp.ext Pi.apply_single (e ·) (fun _ => map_zero _) _ _

Depends on / 依赖: Pi.apply_single, PiLp.ext, apply_single, map_zero
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_single (e : forall i, α i ≃ₗᵢ[𝕜] β i) [DecidableEq ι]
    (i : ι) (v : α i) :
    LinearIsometryEquiv.piLpCongrRight p e (single p i v) = single p i (e _ v) :=
PiLp.ext Pi.apply_single (e ·) (fun _ => map_zero _) _ _

end piLpCongrRight

section piLpCurry

variable {ι : Type*} {κ : ι -> Type*} (p : Real>=0∞) [Fact (1 <= p)]
  [Fintype ι] [forall i, Fintype (κ i)]
  (α : forall i, κ i -> Type*) [forall i k, SeminormedAddCommGroup (α i k)] [forall i k, Module 𝕜 (α i k)]

variable (𝕜) in
/--
Definition of `_root_.LinearIsometryEquiv.piLpCurry` / `_root_.LinearIsometryEquiv.piLpCurry` 的定义

English:
definition _root_.LinearIsometryEquiv.piLpCurry
  signature: :
  body: WithLp.linearEquiv _ _ _
      ≪≫ₗ LinearEquiv.piCurry 𝕜 α
      ≪≫ₗ (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv _ _ _).symm)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp_rw [← coe_nnnorm, NNReal.coe_inj,

中文:
定义 _root_.LinearIsometryEquiv.piLpCurry
  签名: :
  定义体: WithLp.linearEquiv _ _ _
      ≪≫ₗ LinearEquiv.piCurry 𝕜 α
      ≪≫ₗ (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv _ _ _).symm)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp_rw [← coe_nnnorm, NNReal.coe_inj,

Depends on / 依赖: Finset, Finset.sup_sigma, Finset.univ_sigma_univ, LinearEquiv, LinearEquiv.piCongrRight, LinearEquiv.piCurry, NNReal, NNReal.coe_inj, Pi.nnnorm_def, Sigma.curry, WithLp, WithLp.linearEquiv, WithLp.linearEquiv_symm_apply, coe_inj, coe_nnnorm, eq_or_ne, linearEquiv, linearEquiv_symm_apply, nnnorm_def, nnnorm_eq_sum
-/
def _root_.LinearIsometryEquiv.piLpCurry :
    PiLp p (fun i : Sigma _ => α i.1 i.2) ≃ₗᵢ[𝕜] PiLp p (fun i => PiLp p (α i)) where
  toLinearEquiv :=
    WithLp.linearEquiv _ _ _
      ≪≫ₗ LinearEquiv.piCurry 𝕜 α
      ≪≫ₗ (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv _ _ _).symm)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp_rw [← coe_nnnorm, NNReal.coe_inj, WithLp.linearEquiv_symm_apply]
    obtain rfl | hp := eq_or_ne p ⊤
    · simp [Pi.nnnorm_def, ← Finset.univ_sigma_univ, Finset.sup_sigma, Sigma.curry]
    · have : 0 < p.toReal := (toReal_pos_iff_ne_top _).mpr hp
      simp [nnnorm_eq_sum hp, this.ne', ← Finset.univ_sigma_univ, Finset.sum_sigma, Sigma.curry]

/--
theorem `_root_.LinearIsometryEquiv.piLpCurry_apply` / 定理 `_root_.LinearIsometryEquiv.piLpCurry_apply`

English:
theorem _root_.LinearIsometryEquiv.piLpCurry_apply
  proof: rfl

中文:
定理 _root_.LinearIsometryEquiv.piLpCurry_apply
  证明: rfl
-/
@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_apply
    (f : PiLp p (fun i : Sigma κ => α i.1 i.2)) :
    _root_.LinearIsometryEquiv.piLpCurry 𝕜 p α f =
      toLp p (fun i => (toLp p) <| Sigma.curry (ofLp f) i) :=
  rfl

/--
theorem `_root_.LinearIsometryEquiv.piLpCurry_symm_apply` / 定理 `_root_.LinearIsometryEquiv.piLpCurry_symm_apply`

English:
theorem _root_.LinearIsometryEquiv.piLpCurry_symm_apply
  proof: rfl

中文:
定理 _root_.LinearIsometryEquiv.piLpCurry_symm_apply
  证明: rfl
-/
@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_symm_apply
    (f : PiLp p (fun i => PiLp p (α i))) :
    (_root_.LinearIsometryEquiv.piLpCurry 𝕜 p α).symm f =
      toLp p (Sigma.uncurry fun i j => f i j) :=
  rfl

end piLpCurry

section sumPiLpEquivProdLpPiLp

variable {ι κ : Type*} (p : Real>=0∞) (α : ι oplus κ -> Type*) [Fintype ι] [Fintype κ] [Fact (1 <= p)]
variable [forall i, SeminormedAddCommGroup (α i)] [forall i, Module 𝕜 (α i)]

/-- `LinearEquiv.sumPiEquivProdPi` for `PiLp`, as an isometry. -/
@[simps! +simpRhs]
/--
Definition of `sumPiLpEquivProdLpPiLp` / `sumPiLpEquivProdLpPiLp` 的定义

English:
definition sumPiLpEquivProdLpPiLp
  signature: :
  body: WithLp.linearEquiv p _ _
      ≪≫ₗ LinearEquiv.sumPiEquivProdPi _ _ _ α
      ≪≫ₗ LinearEquiv.prodCongr (WithLp.linearEquiv p _ _).symm
        (WithLp.linearEquiv _ _ _).symm
      ≪≫ₗ (WithLp.linearEquiv p _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
   

中文:
定义 sumPiLpEquivProdLpPiLp
  签名: :
  定义体: WithLp.linearEquiv p _ _
      ≪≫ₗ LinearEquiv.sumPiEquivProdPi _ _ _ α
      ≪≫ₗ LinearEquiv.prodCongr (WithLp.linearEquiv p _ _).symm
        (WithLp.linearEquiv _ _ _).symm
      ≪≫ₗ (WithLp.linearEquiv p _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
   

Depends on / 依赖: Finset, Finset.sup_disjSum, Finset.univ_disjSum_univ, LinearEquiv, LinearEquiv.prodCongr, LinearEquiv.sumPiEquivProdPi, Pi.norm_def, WithLp, WithLp.linearEquiv, coe_nnnorm, dichotomy, linearEquiv, norm_def, norm_map, p.dichotomy, p.toReal, prodCongr, simp_rw, sumPiEquivProdPi, sup_disjSum
-/
def sumPiLpEquivProdLpPiLp :
    WithLp p (Π i, α i) ≃ₗᵢ[𝕜]
      WithLp p (WithLp p (Π i, α (.inl i)) × WithLp p (Π i, α (.inr i))) where
  toLinearEquiv :=
    WithLp.linearEquiv p _ _
      ≪≫ₗ LinearEquiv.sumPiEquivProdPi _ _ _ α
      ≪≫ₗ LinearEquiv.prodCongr (WithLp.linearEquiv p _ _).symm
        (WithLp.linearEquiv _ _ _).symm
      ≪≫ₗ (WithLp.linearEquiv p _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    obtain rfl | hp := p.dichotomy
    · simp [← Finset.univ_disjSum_univ, Finset.sup_disjSum, Pi.norm_def]
    · have : 0 < p.toReal := by positivity
      have hpt : p != ⊤ := (toReal_pos_iff_ne_top p).mp this
      simp_rw [← coe_nnnorm]; congr 1 -- convert to nnnorm to avoid needing positivity arguments
      simp [nnnorm_eq_sum hpt, WithLp.prod_nnnorm_eq_add hpt, NNReal.rpow_inv_rpow this.ne']

end sumPiLpEquivProdLpPiLp

section Single

variable (p)
variable [DecidableEq ι]

@[simp]
/--
theorem `nnnorm_single` / 定理 `nnnorm_single`

English:
theorem nnnorm_single
  given: (i : ι) (b : β i)
  statement: ‖single p i b‖₊ = ‖b‖₊
  proof: by
  have : Nonempty ι := ⟨i⟩
  induction p generalizing hp with
  | top =>
    simp_rw [nnnorm_eq_ciSup]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [single_eq_same]
      · s

中文:
定理 nnnorm_single
  条件: (i : ι) (b : β i)
  结论: ‖single p i b‖₊ = ‖b‖₊
  证明: by
  have : Nonempty ι := ⟨i⟩
  induction p generalizing hp with
  | top =>
    simp_rw [nnnorm_eq_ciSup]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [single_eq_same]
      · s

Depends on / 依赖: Decidable, Decidable.eq_or_ne, ENNReal, ENNReal.coe_ne_top, ENNReal.coe_toReal, Fact.out, Fintype, Fintype.sum_eq_singl, Nonempty, ciSup_eq_of_forall_le_of_forall_lt_exists_gt, coe_ne_top, coe_toReal, eq_or_ne, generalizing, hn.trans_eq, mod_cast, nnnorm_eq_ciSup, nnnorm_eq_sum, simp_rw, single_eq_same
-/
theorem nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = ‖b‖₊ := by
  have : Nonempty ι := ⟨i⟩
  induction p generalizing hp with
  | top =>
    simp_rw [nnnorm_eq_ciSup]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [single_eq_same]
      · simp [hij]
    · rw [single_eq_same]
  | coe p =>
    have hp0 : (p : Real) != 0 :=
      mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 <= (p : Real>=0∞))).ne'
    rw [nnnorm_eq_sum ENNReal.coe_ne_top]; rw [ENNReal.coe_toReal]; rw [Fintype.sum_eq_single i]; rw [toLp_apply]; rw [single_eq_same]; rw [← NNReal.rpow_mul]; rw [one_div]; rw [mul_inv_cancel₀ hp0]; rw [NNReal.rpow_one]
    intro j hij
    rw [toLp_apply]; rw [single_eq_of_ne _ hij]; rw [nnnorm_zero]; rw [NNReal.zero_rpow hp0]

@[deprecated nnnorm_single (since := "2026-03-15")]
/--
theorem `nnnorm_toLp_single` / 定理 `nnnorm_toLp_single`

English:
theorem nnnorm_toLp_single
  given: (i : ι) (b : β i)
  statement: ‖toLp p (Pi.single i b)‖₊ = ‖b‖₊
  proof: nnnorm_single p β i b

@[simp]

中文:
定理 nnnorm_toLp_single
  条件: (i : ι) (b : β i)
  结论: ‖toLp p (Pi.single i b)‖₊ = ‖b‖₊
  证明: nnnorm_single p β i b

@[simp]

Depends on / 依赖: nnnorm_single
-/
theorem nnnorm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖₊ = ‖b‖₊ :=
  nnnorm_single p β i b

@[simp]
/--
lemma `norm_single` / 引理 `norm_single`

English:
lemma norm_single
  given: (i : ι) (b : β i)
  statement: ‖single p i b‖ = ‖b‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_single p β i b

@[deprecated norm_single (since := "2026-03-15")]

中文:
引理 norm_single
  条件: (i : ι) (b : β i)
  结论: ‖single p i b‖ = ‖b‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_single p β i b

@[deprecated norm_single (since := "2026-03-15")]

Depends on / 依赖: congr_arg, nnnorm_single
-/
lemma norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_single p β i b

@[deprecated norm_single (since := "2026-03-15")]
/--
lemma `norm_toLp_single` / 引理 `norm_toLp_single`

English:
lemma norm_toLp_single
  given: (i : ι) (b : β i)
  statement: ‖toLp p (Pi.single i b)‖ = ‖b‖
  proof: norm_single p β i b

@[simp]

中文:
引理 norm_toLp_single
  条件: (i : ι) (b : β i)
  结论: ‖toLp p (Pi.single i b)‖ = ‖b‖
  证明: norm_single p β i b

@[simp]

Depends on / 依赖: norm_single
-/
lemma norm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖ = ‖b‖ :=
  norm_single p β i b

@[simp]
/--
lemma `nndist_single_same` / 引理 `nndist_single_same`

English:
lemma nndist_single_same
  given: (i : ι) (b₁ b₂ : β i)
  proof: by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← single_sub]; rw [nnnorm_single]

@[deprecated nndist_single_same (since := "2026-03-15")]

中文:
引理 nndist_single_same
  条件: (i : ι) (b₁ b₂ : β i)
  证明: by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← single_sub]; rw [nnnorm_single]

@[deprecated nndist_single_same (since := "2026-03-15")]

Depends on / 依赖: nndist_eq_nnnorm, nnnorm_single, single_sub
-/
lemma nndist_single_same (i : ι) (b₁ b₂ : β i) :
    nndist (single p i b₁) (single p i b₂) = nndist b₁ b₂ := by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← single_sub]; rw [nnnorm_single]

@[deprecated nndist_single_same (since := "2026-03-15")]
/--
lemma `nndist_toLp_single_same` / 引理 `nndist_toLp_single_same`

English:
lemma nndist_toLp_single_same
  given: (i : ι) (b₁ b₂ : β i)
  proof: nndist_single_same p β i b₁ b₂

@[simp]

中文:
引理 nndist_toLp_single_same
  条件: (i : ι) (b₁ b₂ : β i)
  证明: nndist_single_same p β i b₁ b₂

@[simp]

Depends on / 依赖: nndist_single_same
-/
lemma nndist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    nndist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = nndist b₁ b₂ :=
  nndist_single_same p β i b₁ b₂

@[simp]
/--
lemma `dist_single_same` / 引理 `dist_single_same`

English:
lemma dist_single_same
  given: (i : ι) (b₁ b₂ : β i)
  proof: congr_arg ((↑) : Real>=0 -> Real) nndist_single_same p β i b₁ b₂

@[deprecated dist_single_same (since := "2026-03-15")]

中文:
引理 dist_single_same
  条件: (i : ι) (b₁ b₂ : β i)
  证明: congr_arg ((↑) : Real>=0 -> Real) nndist_single_same p β i b₁ b₂

@[deprecated dist_single_same (since := "2026-03-15")]

Depends on / 依赖: congr_arg, nndist_single_same
-/
lemma dist_single_same (i : ι) (b₁ b₂ : β i) :
    dist (single p i b₁) (single p i b₂) = dist b₁ b₂ :=
congr_arg ((↑) : Real>=0 -> Real) nndist_single_same p β i b₁ b₂

@[deprecated dist_single_same (since := "2026-03-15")]
/--
lemma `dist_toLp_single_same` / 引理 `dist_toLp_single_same`

English:
lemma dist_toLp_single_same
  given: (i : ι) (b₁ b₂ : β i)
  proof: dist_single_same p β i b₁ b₂

@[simp]

中文:
引理 dist_toLp_single_same
  条件: (i : ι) (b₁ b₂ : β i)
  证明: dist_single_same p β i b₁ b₂

@[simp]

Depends on / 依赖: dist_single_same
-/
lemma dist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    dist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = dist b₁ b₂ :=
  dist_single_same p β i b₁ b₂

@[simp]
/--
lemma `edist_single_same` / 引理 `edist_single_same`

English:
lemma edist_single_same
  given: (i : ι) (b₁ b₂ : β i)
  proof: by
  simp only [edist_nndist, nndist_single_same p β i b₁ b₂]

@[deprecated edist_single_same (since := "2026-03-15")]

中文:
引理 edist_single_same
  条件: (i : ι) (b₁ b₂ : β i)
  证明: by
  simp only [edist_nndist, nndist_single_same p β i b₁ b₂]

@[deprecated edist_single_same (since := "2026-03-15")]

Depends on / 依赖: edist_nndist, nndist_single_same
-/
lemma edist_single_same (i : ι) (b₁ b₂ : β i) :
    edist (single p i b₁) (single p i b₂) = edist b₁ b₂ := by
  simp only [edist_nndist, nndist_single_same p β i b₁ b₂]

@[deprecated edist_single_same (since := "2026-03-15")]
/--
lemma `edist_toLp_single_same` / 引理 `edist_toLp_single_same`

English:
lemma edist_toLp_single_same
  given: (i : ι) (b₁ b₂ : β i)
  proof: edist_single_same p β i b₁ b₂

中文:
引理 edist_toLp_single_same
  条件: (i : ι) (b₁ b₂ : β i)
  证明: edist_single_same p β i b₁ b₂

Depends on / 依赖: edist_single_same
-/
lemma edist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    edist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = edist b₁ b₂ :=
  edist_single_same p β i b₁ b₂

end Single

/--
lemma `nnnorm_toLp_const` / 引理 `nnnorm_toLp_const`

English:
lemma nnnorm_toLp_const
  given: {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β)
  proof: by
  rcases p.dichotomy with (h | h)
  · exact False.elim (hp h)
  · have ne_zero : p.toReal != 0 := (zero_lt_one.trans_le h).ne'
    simp_rw [nnnorm_eq_sum hp, Function.const_apply, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, NNReal.mul_rpow, ← NNReal.rpow_mul,
      mul_one_div_cancel 

中文:
引理 nnnorm_toLp_const
  条件: {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β)
  证明: by
  rcases p.dichotomy with (h | h)
  · exact False.elim (hp h)
  · have ne_zero : p.toReal != 0 := (zero_lt_one.trans_le h).ne'
    simp_rw [nnnorm_eq_sum hp, Function.const_apply, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, NNReal.mul_rpow, ← NNReal.rpow_mul,
      mul_one_div_cancel 

Depends on / 依赖: ENNReal, ENNReal.toReal_div, ENNReal.toReal_one, False.elim, Finset, Finset.card_univ, Finset.sum_const, Function, Function.const_apply, NNReal, NNReal.mul_rpow, NNReal.rpow_mul, NNReal.rpow_one, card_univ, const_apply, dichotomy, mul_one_div_cancel, mul_rpow, ne_zero, nnnorm_eq_sum
-/
lemma nnnorm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β) :
    ‖toLp p (Function.const ι b)‖₊ =
      (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases p.dichotomy with (h | h)
  · exact False.elim (hp h)
  · have ne_zero : p.toReal != 0 := (zero_lt_one.trans_le h).ne'
    simp_rw [nnnorm_eq_sum hp, Function.const_apply, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, NNReal.mul_rpow, ← NNReal.rpow_mul,
      mul_one_div_cancel ne_zero, NNReal.rpow_one, ENNReal.toReal_div, ENNReal.toReal_one]

/--
lemma `nnnorm_toLp_const'` / 引理 `nnnorm_toLp_const'`

English:
lemma nnnorm_toLp_const'
  given: {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β)
  proof: by
rcases em p = ∞ with (rfl | hp)
  · simp only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      one_mul, nnnorm_eq_ciSup, Function.const_apply, ciSup_const]
  · exact nnnorm_toLp_const hp b

中文:
引理 nnnorm_toLp_const'
  条件: {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β)
  证明: by
rcases em p = ∞ with (rfl | hp)
  · simp only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      one_mul, nnnorm_eq_ciSup, Function.const_apply, ciSup_const]
  · exact nnnorm_toLp_const hp b

Depends on / 依赖: ENNReal, ENNReal.div_top, ENNReal.toReal_zero, Function, Function.const_apply, NNReal, NNReal.rpow_zero, ciSup_const, const_apply, div_top, nnnorm_eq_ciSup, nnnorm_toLp_const, one_mul, rpow_zero, toReal_zero
-/
lemma nnnorm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖toLp p (Function.const ι b)‖₊ =
      (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b‖₊ := by
rcases em p = ∞ with (rfl | hp)
  · simp only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      one_mul, nnnorm_eq_ciSup, Function.const_apply, ciSup_const]
  · exact nnnorm_toLp_const hp b

/--
lemma `norm_toLp_const` / 引理 `norm_toLp_const`

English:
lemma norm_toLp_const
  given: {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β)
  proof: (congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_toLp_const hp b).trans by simp

中文:
引理 norm_toLp_const
  条件: {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β)
  证明: (congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_toLp_const hp b).trans by simp

Depends on / 依赖: congr_arg, nnnorm_toLp_const
-/
lemma norm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β) :
    ‖toLp p (Function.const ι b)‖ =
      (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b‖ :=
(congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_toLp_const hp b).trans by simp

/--
lemma `norm_toLp_const'` / 引理 `norm_toLp_const'`

English:
lemma norm_toLp_const'
  given: {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β)
  proof: (congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_toLp_const' b).trans by simp

中文:
引理 norm_toLp_const'
  条件: {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β)
  证明: (congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_toLp_const' b).trans by simp

Depends on / 依赖: congr_arg, nnnorm_toLp_const
-/
lemma norm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖toLp p (Function.const ι b)‖ =
      (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b‖ :=
(congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_toLp_const' b).trans by simp

/--
lemma `nnnorm_toLp_one` / 引理 `nnnorm_toLp_one`

English:
lemma nnnorm_toLp_one
  given: {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β]
  proof: (nnnorm_toLp_const hp (1 : β)).trans rfl

中文:
引理 nnnorm_toLp_one
  条件: {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β]
  证明: (nnnorm_toLp_const hp (1 : β)).trans rfl

Depends on / 依赖: nnnorm_toLp_const
-/
lemma nnnorm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β] :
    ‖toLp p (1 : ι -> β)‖₊ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖(1 : β)‖₊ :=
  (nnnorm_toLp_const hp (1 : β)).trans rfl

/--
lemma `norm_toLp_one` / 引理 `norm_toLp_one`

English:
lemma norm_toLp_one
  given: {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β]
  proof: (norm_toLp_const hp (1 : β)).trans rfl

中文:
引理 norm_toLp_one
  条件: {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β]
  证明: (norm_toLp_const hp (1 : β)).trans rfl

Depends on / 依赖: norm_toLp_const
-/
lemma norm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β] :
    ‖toLp p (1 : ι -> β)‖ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖(1 : β)‖ :=
  (norm_toLp_const hp (1 : β)).trans rfl

end Fintype

section

variable [Semiring 𝕜] [forall i, AddCommGroup (β i)] [forall i, Module 𝕜 (β i)] [forall i, TopologicalSpace (β i)]

/-- `WithLp.linearEquiv` as a continuous linear equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `continuousLinearEquiv` / `continuousLinearEquiv` 的定义

English:
definition continuousLinearEquiv
  signature: : PiLp p β ≃L[𝕜] forall i, β i where
  body: WithLp.linearEquiv _ _ _
  continuous_invFun := (by fun_prop : Continuous fun (a : Π i, β i) => toLp p a)

中文:
定义 continuousLinearEquiv
  签名: : PiLp p β ≃L[𝕜] 对任意 i, β i where
  定义体: WithLp.linearEquiv _ _ _
  continuous_invFun := (by fun_prop : Continuous fun (a : Π i, β i) => toLp p a)

Depends on / 依赖: WithLp, WithLp.linearEquiv, linearEquiv
-/
def continuousLinearEquiv : PiLp p β ≃L[𝕜] forall i, β i where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_invFun := (by fun_prop : Continuous fun (a : Π i, β i) => toLp p a)

/--
lemma `coe_continuousLinearEquiv` / 引理 `coe_continuousLinearEquiv`

English:
lemma coe_continuousLinearEquiv
  proof: rfl

中文:
引理 coe_continuousLinearEquiv
  证明: rfl
-/
lemma coe_continuousLinearEquiv :
    ⇑(PiLp.continuousLinearEquiv p 𝕜 β) = ofLp := rfl

/--
lemma `coe_symm_continuousLinearEquiv` / 引理 `coe_symm_continuousLinearEquiv`

English:
lemma coe_symm_continuousLinearEquiv
  proof: rfl

中文:
引理 coe_symm_continuousLinearEquiv
  证明: rfl
-/
lemma coe_symm_continuousLinearEquiv :
    ⇑(PiLp.continuousLinearEquiv p 𝕜 β).symm = toLp p := rfl

/-- The natural equivalence between `PiLp p β` and `β default`,
for any index type `ι` with a unique element. -/
@[simps! apply symm_apply]
/--
Definition of `equivOfUnique` / `equivOfUnique` 的定义

English:
definition equivOfUnique
  signature: [Unique ι]
  body: (continuousLinearEquiv p 𝕜 β).trans .piUnique 𝕜 β

中文:
定义 equivOfUnique
  签名: [Unique ι]
  定义体: (continuousLinearEquiv p 𝕜 β).trans .piUnique 𝕜 β

Depends on / 依赖: continuousLinearEquiv, piUnique
-/
def equivOfUnique [Unique ι] : PiLp p β ≃L[𝕜] β default :=
(continuousLinearEquiv p 𝕜 β).trans .piUnique 𝕜 β

end

section

variable [Semiring 𝕜] [forall i, NormedAddCommGroup (β i)] [forall i, Module 𝕜 (β i)]

variable {𝕜} in
/-- The projection on the `i`-th coordinate of `PiLp p β`, as a continuous linear map. -/
@[simps!]
/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (i : ι)
  body: projₗ p β i
  cont := (by fun_prop : Continuous fun a : PiLp p β => a.ofLp i)

中文:
定义 proj
  签名: (i : ι)
  定义体: projₗ p β i
  cont := (by fun_prop : Continuous fun a : PiLp p β => a.ofLp i)
-/
def proj (i : ι) : PiLp p β ->L[𝕜] β i where
  __ := projₗ p β i
  cont := (by fun_prop : Continuous fun a : PiLp p β => a.ofLp i)

end

section Basis

variable [Finite ι] [Ring 𝕜]
variable (ι)

/--
Definition of `basisFun` / `basisFun` 的定义

English:
definition basisFun
  signature: : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜)
  body: Basis.ofEquivFun (WithLp.linearEquiv p 𝕜 (ι -> 𝕜))

@[simp]

中文:
定义 basisFun
  签名: : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜)
  定义体: Basis.ofEquivFun (WithLp.linearEquiv p 𝕜 (ι -> 𝕜))

@[simp]

Depends on / 依赖: Basis.ofEquivFun, WithLp, WithLp.linearEquiv, linearEquiv, ofEquivFun
-/
def basisFun : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜) :=
  Basis.ofEquivFun (WithLp.linearEquiv p 𝕜 (ι -> 𝕜))

@[simp]
/--
theorem `basisFun_apply` / 定理 `basisFun_apply`

English:
theorem basisFun_apply
  given: [DecidableEq ι] (i)
  proof: by
  simp_rw [basisFun, Basis.coe_ofEquivFun, WithLp.coe_symm_linearEquiv, toLp_single]

@[simp]

中文:
定理 basisFun_apply
  条件: [DecidableEq ι] (i)
  证明: by
  simp_rw [basisFun, Basis.coe_ofEquivFun, WithLp.coe_symm_linearEquiv, toLp_single]

@[simp]

Depends on / 依赖: Basis.coe_ofEquivFun, WithLp, WithLp.coe_symm_linearEquiv, basisFun, coe_ofEquivFun, coe_symm_linearEquiv, simp_rw, toLp_single
-/
theorem basisFun_apply [DecidableEq ι] (i) :
    basisFun p 𝕜 ι i = single p i 1 := by
  simp_rw [basisFun, Basis.coe_ofEquivFun, WithLp.coe_symm_linearEquiv, toLp_single]

@[simp]
/--
theorem `basisFun_repr` / 定理 `basisFun_repr`

English:
theorem basisFun_repr
  given: (x : PiLp p fun _ : ι => 𝕜) (i : ι)
  statement: (basisFun p 𝕜 ι).repr x i = x i
  proof: rfl

@[simp]

中文:
定理 basisFun_repr
  条件: (x : PiLp p fun _ : ι => 𝕜) (i : ι)
  结论: (basisFun p 𝕜 ι).repr x i = x i
  证明: rfl

@[simp]
-/
theorem basisFun_repr (x : PiLp p fun _ : ι => 𝕜) (i : ι) : (basisFun p 𝕜 ι).repr x i = x i :=
  rfl

@[simp]
/--
theorem `basisFun_equivFun` / 定理 `basisFun_equivFun`

English:
theorem basisFun_equivFun
  statement: (basisFun p 𝕜 ι).equivFun = WithLp.linearEquiv p 𝕜 (ι -> 𝕜)
  proof: Basis.equivFun_ofEquivFun _

中文:
定理 basisFun_equivFun
  结论: (basisFun p 𝕜 ι).equivFun = WithLp.linearEquiv p 𝕜 (ι -> 𝕜)
  证明: Basis.equivFun_ofEquivFun _

Depends on / 依赖: Basis.equivFun_ofEquivFun, equivFun_ofEquivFun
-/
theorem basisFun_equivFun : (basisFun p 𝕜 ι).equivFun = WithLp.linearEquiv p 𝕜 (ι -> 𝕜) :=
  Basis.equivFun_ofEquivFun _

/--
theorem `basisFun_eq_pi_basisFun` / 定理 `basisFun_eq_pi_basisFun`

English:
theorem basisFun_eq_pi_basisFun
  proof: rfl

@[simp]

中文:
定理 basisFun_eq_pi_basisFun
  证明: rfl

@[simp]
-/
theorem basisFun_eq_pi_basisFun :
    basisFun p 𝕜 ι = (Pi.basisFun 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι -> 𝕜)).symm :=
  rfl

@[simp]
/--
theorem `basisFun_map` / 定理 `basisFun_map`

English:
theorem basisFun_map
  proof: rfl

中文:
定理 basisFun_map
  证明: rfl
-/
theorem basisFun_map :
    (basisFun p 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι -> 𝕜)) = Pi.basisFun 𝕜 ι := rfl

end Basis

open Matrix

nonrec theorem basis_toMatrix_basisFun_mul [Fintype ι]
    {𝕜} [SeminormedCommRing 𝕜] (b : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜))
    (A : Matrix ι ι 𝕜) :
    b.toMatrix (PiLp.basisFun _ _ _) * A =
      Matrix.of fun i j => b.repr (toLp p (Aᵀ j)) i := by
  have := basis_toMatrix_basisFun_mul (b.map (WithLp.linearEquiv _ 𝕜 _)) A
  simp_rw [← PiLp.basisFun_map p, Basis.map_repr, LinearEquiv.trans_apply,
    WithLp.linearEquiv_symm_apply, Basis.toMatrix_map, Function.comp_def, Basis.map_apply,
    LinearEquiv.symm_apply_apply] at this
  exact this

section toPi

/-!
### `L^p` distance on a product space

In this section we define a pseudometric space structure on `Π i, α i`, as well as a seminormed
group structure. These are meant to be used to put the desired instances on type synonyms
of `Π i, α i`. See for instance `Matrix.frobeniusSeminormedAddCommGroup`.
-/

-- This prevents Lean from elaborating terms of `Π i, α i` with an unintended norm.
attribute [-instance] Pi.seminormedAddGroup

variable [Fact (1 <= p)] [Fintype ι]

/--
Definition of `pseudoMetricSpaceToPi` / `pseudoMetricSpaceToPi` 的定义

English:
abbreviation pseudoMetricSpaceToPi
  signature: [forall i, PseudoMetricSpace (α i)]
  body: (isUniformInducing_toLp p α).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (antilipschitzWith_toLp p α).tendsto_cobounded.le_comap
        (lipschitzWith_toLp p α).comap_cobounded_le) sᶜ

中文:
缩写 pseudoMetricSpaceToPi
  签名: [对任意 i, PseudoMetricSpace (α i)]
  定义体: (isUniformInducing_toLp p α).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (antilipschitzWith_toLp p α).tendsto_cobounded.le_comap
        (lipschitzWith_toLp p α).comap_cobounded_le) sᶜ

Depends on / 依赖: Filter, Filter.ext_iff, antilipschitzWith_toLp, comapPseudoMetricSpace, comapPseudoMetricSpace.replaceBornology, comap_cobounded_le, ext_iff, isUniformInducing_toLp, le_antisymm, le_comap, lipschitzWith_toLp, replaceBornology, tendsto_cobounded, tendsto_cobounded.le_comap
-/
abbrev pseudoMetricSpaceToPi [forall i, PseudoMetricSpace (α i)] :
    PseudoMetricSpace (Π i, α i) :=
  (isUniformInducing_toLp p α).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (antilipschitzWith_toLp p α).tendsto_cobounded.le_comap
        (lipschitzWith_toLp p α).comap_cobounded_le) sᶜ

/--
lemma `dist_pseudoMetricSpaceToPi` / 引理 `dist_pseudoMetricSpaceToPi`

English:
lemma dist_pseudoMetricSpaceToPi
  given: [forall i, PseudoMetricSpace (α i)] (x y : Π i, α i)
  proof: rfl

中文:
引理 dist_pseudoMetricSpaceToPi
  条件: [对任意 i, PseudoMetricSpace (α i)] (x y : Π i, α i)
  证明: rfl
-/
lemma dist_pseudoMetricSpaceToPi [forall i, PseudoMetricSpace (α i)] (x y : Π i, α i) :
    @dist _ (pseudoMetricSpaceToPi p α).toDist x y = dist (toLp p x) (toLp p y) := rfl

/--
Definition of `seminormedAddCommGroupToPi` / `seminormedAddCommGroupToPi` 的定义

English:
abbreviation seminormedAddCommGroupToPi
  signature: [forall i, SeminormedAddCommGroup (α i)]
  body: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]

中文:
缩写 seminormedAddCommGroupToPi
  签名: [对任意 i, SeminormedAddCommGroup (α i)]
  定义体: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
-/
abbrev seminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup (α i)] :
    SeminormedAddCommGroup (Π i, α i) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]

/--
lemma `norm_seminormedAddCommGroupToPi` / 引理 `norm_seminormedAddCommGroupToPi`

English:
lemma norm_seminormedAddCommGroupToPi
  given: [forall i, SeminormedAddCommGroup (α i)] (x : Π i, α i)
  proof: rfl

中文:
引理 norm_seminormedAddCommGroupToPi
  条件: [对任意 i, SeminormedAddCommGroup (α i)] (x : Π i, α i)
  证明: rfl
-/
lemma norm_seminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup (α i)] (x : Π i, α i) :
    @Norm.norm _ (seminormedAddCommGroupToPi p α).toNorm x = ‖toLp p x‖ := rfl

/--
lemma `nnnorm_seminormedAddCommGroupToPi` / 引理 `nnnorm_seminormedAddCommGroupToPi`

English:
lemma nnnorm_seminormedAddCommGroupToPi
  given: [forall i, SeminormedAddCommGroup (α i)] (x : Π i, α i)
  proof: rfl

中文:
引理 nnnorm_seminormedAddCommGroupToPi
  条件: [对任意 i, SeminormedAddCommGroup (α i)] (x : Π i, α i)
  证明: rfl
-/
lemma nnnorm_seminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup (α i)] (x : Π i, α i) :
    @NNNorm.nnnorm _ (seminormedAddCommGroupToPi p α).toSeminormedAddGroup.toNNNorm x =
    ‖toLp p x‖₊ := rfl

/--
lemma `isBoundedSMulSeminormedAddCommGroupToPi` / 引理 `isBoundedSMulSeminormedAddCommGroupToPi`

English:
lemma isBoundedSMulSeminormedAddCommGroupToPi
  proof: pseudoMetricSpaceToPi p α
    IsBoundedSMul R (Π i, α i) := by
  let := pseudoMetricSpaceToPi p α
  refine ⟨fun x y z => ?_, fun x y z => ?_⟩
  · simpa [dist_pseudoMetricSpaceToPi] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToPi] using dist_pair_smul x y (toLp p z)

中文:
引理 isBoundedSMulSeminormedAddCommGroupToPi
  证明: pseudoMetricSpaceToPi p α
    IsBoundedSMul R (Π i, α i) := by
  let := pseudoMetricSpaceToPi p α
  refine ⟨fun x y z => ?_, fun x y z => ?_⟩
  · simpa [dist_pseudoMetricSpaceToPi] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToPi] using dist_pair_smul x y (toLp p z)

Depends on / 依赖: pseudoMetricSpaceToPi
-/
lemma isBoundedSMulSeminormedAddCommGroupToPi
    [forall i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRing R]
    [forall i, Module R (α i)] [forall i, IsBoundedSMul R (α i)] :
    letI := pseudoMetricSpaceToPi p α
    IsBoundedSMul R (Π i, α i) := by
  let := pseudoMetricSpaceToPi p α
  refine ⟨fun x y z => ?_, fun x y z => ?_⟩
  · simpa [dist_pseudoMetricSpaceToPi] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToPi] using dist_pair_smul x y (toLp p z)

/--
lemma `normSMulClassSeminormedAddCommGroupToPi` / 引理 `normSMulClassSeminormedAddCommGroupToPi`

English:
lemma normSMulClassSeminormedAddCommGroupToPi
  proof: seminormedAddCommGroupToPi p α
    NormSMulClass R (Π i, α i) := by
  let := seminormedAddCommGroupToPi p α
  refine ⟨fun x y => ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

中文:
引理 normSMulClassSeminormedAddCommGroupToPi
  证明: seminormedAddCommGroupToPi p α
    NormSMulClass R (Π i, α i) := by
  let := seminormedAddCommGroupToPi p α
  refine ⟨fun x y => ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

Depends on / 依赖: seminormedAddCommGroupToPi
-/
lemma normSMulClassSeminormedAddCommGroupToPi
    [forall i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRing R]
    [forall i, Module R (α i)] [forall i, NormSMulClass R (α i)] :
    letI := seminormedAddCommGroupToPi p α
    NormSMulClass R (Π i, α i) := by
  let := seminormedAddCommGroupToPi p α
  refine ⟨fun x y => ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

/--
Definition of `normedSpaceSeminormedAddCommGroupToPi` / `normedSpaceSeminormedAddCommGroupToPi` 的定义

English:
abbreviation normedSpaceSeminormedAddCommGroupToPi
  body: seminormedAddCommGroupToPi p α
    NormedSpace R (Π i, α i) := by
  letI := seminormedAddCommGroupToPi p α
  refine ⟨fun x y => ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

中文:
缩写 normedSpaceSeminormedAddCommGroupToPi
  定义体: seminormedAddCommGroupToPi p α
    NormedSpace R (Π i, α i) := by
  letI := seminormedAddCommGroupToPi p α
  refine ⟨fun x y => ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

Depends on / 依赖: seminormedAddCommGroupToPi
-/
abbrev normedSpaceSeminormedAddCommGroupToPi
    [forall i, SeminormedAddCommGroup (α i)] {R : Type*} [NormedField R]
    [forall i, NormedSpace R (α i)] :
    letI := seminormedAddCommGroupToPi p α
    NormedSpace R (Π i, α i) := by
  letI := seminormedAddCommGroupToPi p α
  refine ⟨fun x y => ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

/--
Definition of `normedAddCommGroupToPi` / `normedAddCommGroupToPi` 的定义

English:
abbreviation normedAddCommGroupToPi
  signature: [forall i, NormedAddCommGroup (α i)]
  body: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToPi] at h
    apply eq_of_dist_eq_zero at h
    e

中文:
缩写 normedAddCommGroupToPi
  签名: [对任意 i, NormedAddCommGroup (α i)]
  定义体: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToPi] at h
    apply eq_of_dist_eq_zero at h
    e
-/
abbrev normedAddCommGroupToPi [forall i, NormedAddCommGroup (α i)] :
    NormedAddCommGroup (Π i, α i) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToPi] at h
    apply eq_of_dist_eq_zero at h
    exact WithLp.toLp_injective p h

end toPi

end PiLp
