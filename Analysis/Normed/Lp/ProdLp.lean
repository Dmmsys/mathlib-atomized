/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Sébastien Gouëzel, Jireh Loreaux
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Lp.WithLp

/-!
# `L^p` distance on products of two metric spaces

Given two metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `α × β`
is given by
$$
d(x, y) = \left(d(x_1, y_1)^p + d(x_2, y_2)^p\right)^{1/p}.
$$
For `p = ∞` the distance is the supremum of the distances and `p = 0` the distance is the
cardinality of the elements that are not equal.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Prod-type, named
`WithLp p (α × β)`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space
instances.

We ensure that the topology, bornology and uniform structure on `WithLp p (α × β)` are (defeq to)
the product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

If you wish to endow a type synonym of `α × β` with the `L^p` distance, you can use
`pseudoMetricSpaceToProd` and the declarations below that one.


## Implementation notes

This file is a straight-forward adaptation of `Mathlib/Analysis/Normed/Lp/PiLp.lean`.

## TODO

TODO: the results about uniformity and bornology in the `Aux` section should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.

-/

@[expose] public section

open Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal

noncomputable section

variable (p : Real>=0∞) (𝕜 α β : Type*)

namespace WithLp

section algebra

/- Register simplification lemmas for the applications of `WithLp p (α × β)` elements, as the usual
lemmas for `Prod` will not trigger. -/

variable {p 𝕜 α β}
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable (x y : WithLp p (α × β)) (c : 𝕜)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: (x : WithLp p (α × β))
  body: (ofLp x).fst

中文:
定义 fst
  签名: (x : WithLp p (α × β))
  定义体: (ofLp x).fst
-/
protected def fst (x : WithLp p (α × β)) : α := (ofLp x).fst

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: (x : WithLp p (α × β))
  body: (ofLp x).snd

@[simp]

中文:
定义 snd
  签名: (x : WithLp p (α × β))
  定义体: (ofLp x).snd

@[simp]
-/
protected def snd (x : WithLp p (α × β)) : β := (ofLp x).snd

@[simp]
/--
theorem `zero_fst` / 定理 `zero_fst`

English:
theorem zero_fst
  statement: (0 : WithLp p (α × β)).fst = 0
  proof: rfl

@[simp]

中文:
定理 zero_fst
  结论: (0 : WithLp p (α × β)).fst = 0
  证明: rfl

@[simp]
-/
theorem zero_fst : (0 : WithLp p (α × β)).fst = 0 :=
  rfl

@[simp]
/--
theorem `zero_snd` / 定理 `zero_snd`

English:
theorem zero_snd
  statement: (0 : WithLp p (α × β)).snd = 0
  proof: rfl

@[simp]

中文:
定理 zero_snd
  结论: (0 : WithLp p (α × β)).snd = 0
  证明: rfl

@[simp]
-/
theorem zero_snd : (0 : WithLp p (α × β)).snd = 0 :=
  rfl

@[simp]
/--
theorem `add_fst` / 定理 `add_fst`

English:
theorem add_fst
  statement: (x + y).fst = x.fst + y.fst
  proof: rfl

@[simp]

中文:
定理 add_fst
  结论: (x + y).fst = x.fst + y.fst
  证明: rfl

@[simp]
-/
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

@[simp]
/--
theorem `add_snd` / 定理 `add_snd`

English:
theorem add_snd
  statement: (x + y).snd = x.snd + y.snd
  proof: rfl

@[simp]

中文:
定理 add_snd
  结论: (x + y).snd = x.snd + y.snd
  证明: rfl

@[simp]
-/
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

@[simp]
/--
theorem `sub_fst` / 定理 `sub_fst`

English:
theorem sub_fst
  statement: (x - y).fst = x.fst - y.fst
  proof: rfl

@[simp]

中文:
定理 sub_fst
  结论: (x - y).fst = x.fst - y.fst
  证明: rfl

@[simp]
-/
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

@[simp]
/--
theorem `sub_snd` / 定理 `sub_snd`

English:
theorem sub_snd
  statement: (x - y).snd = x.snd - y.snd
  proof: rfl

@[simp]

中文:
定理 sub_snd
  结论: (x - y).snd = x.snd - y.snd
  证明: rfl

@[simp]
-/
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

@[simp]
/--
theorem `neg_fst` / 定理 `neg_fst`

English:
theorem neg_fst
  statement: (-x).fst = -x.fst
  proof: rfl

@[simp]

中文:
定理 neg_fst
  结论: (-x).fst = -x.fst
  证明: rfl

@[simp]
-/
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

@[simp]
/--
theorem `neg_snd` / 定理 `neg_snd`

English:
theorem neg_snd
  statement: (-x).snd = -x.snd
  proof: rfl

中文:
定理 neg_snd
  结论: (-x).snd = -x.snd
  证明: rfl
-/
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

variable [Module 𝕜 α] [Module 𝕜 β]

@[simp]
/--
theorem `smul_fst` / 定理 `smul_fst`

English:
theorem smul_fst
  statement: (c • x).fst = c • x.fst
  proof: rfl

@[simp]

中文:
定理 smul_fst
  结论: (c • x).fst = c • x.fst
  证明: rfl

@[simp]
-/
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

@[simp]
/--
theorem `smul_snd` / 定理 `smul_snd`

English:
theorem smul_snd
  statement: (c • x).snd = c • x.snd
  proof: rfl

中文:
定理 smul_snd
  结论: (c • x).snd = c • x.snd
  证明: rfl
-/
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

variable (p 𝕜 α β)

/-- `WithLp.fst` as a linear map. -/
@[simps]
/--
Definition of `fstₗ` / `fstₗ` 的定义

English:
definition fstₗ
  signature: : WithLp p (α × β) ->ₗ[𝕜] α where
  body: WithLp.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 fstₗ
  签名: : WithLp p (α × β) ->ₗ[𝕜] α where
  定义体: WithLp.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: WithLp, WithLp.fst
-/
def fstₗ : WithLp p (α × β) ->ₗ[𝕜] α where
  toFun := WithLp.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `WithLp.snd` as a linear map. -/
@[simps]
/--
Definition of `sndₗ` / `sndₗ` 的定义

English:
definition sndₗ
  signature: : WithLp p (α × β) ->ₗ[𝕜] β where
  body: WithLp.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 sndₗ
  签名: : WithLp p (α × β) ->ₗ[𝕜] β where
  定义体: WithLp.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: WithLp, WithLp.snd
-/
def sndₗ : WithLp p (α × β) ->ₗ[𝕜] β where
  toFun := WithLp.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end algebra

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

section equiv

variable {p α β}

/--
lemma `toLp_fst` / 引理 `toLp_fst`

English:
lemma toLp_fst
  given: (x : α × β)
  statement: (toLp p x).fst = x.fst
  proof: rfl

中文:
引理 toLp_fst
  条件: (x : α × β)
  结论: (toLp p x).fst = x.fst
  证明: rfl
-/
@[simp] lemma toLp_fst (x : α × β) : (toLp p x).fst = x.fst := rfl
/--
lemma `toLp_snd` / 引理 `toLp_snd`

English:
lemma toLp_snd
  given: (x : α × β)
  statement: (toLp p x).snd = x.snd
  proof: rfl

中文:
引理 toLp_snd
  条件: (x : α × β)
  结论: (toLp p x).snd = x.snd
  证明: rfl
-/
@[simp] lemma toLp_snd (x : α × β) : (toLp p x).snd = x.snd := rfl
/--
lemma `ofLp_fst` / 引理 `ofLp_fst`

English:
lemma ofLp_fst
  given: (x : WithLp p (α × β))
  statement: (ofLp x).fst = x.fst
  proof: rfl

中文:
引理 ofLp_fst
  条件: (x : WithLp p (α × β))
  结论: (ofLp x).fst = x.fst
  证明: rfl
-/
@[simp] lemma ofLp_fst (x : WithLp p (α × β)) : (ofLp x).fst = x.fst := rfl
/--
lemma `ofLp_snd` / 引理 `ofLp_snd`

English:
lemma ofLp_snd
  given: (x : WithLp p (α × β))
  statement: (ofLp x).snd = x.snd
  proof: rfl

中文:
引理 ofLp_snd
  条件: (x : WithLp p (α × β))
  结论: (ofLp x).snd = x.snd
  证明: rfl
-/
@[simp] lemma ofLp_snd (x : WithLp p (α × β)) : (ofLp x).snd = x.snd := rfl

end equiv

section DistNorm

/-!
### Definition of `edist`, `dist` and `norm` on `WithLp p (α × β)`

In this section we define the `edist`, `dist` and `norm` functions on `WithLp p (α × β)` without
assuming `[Fact (1 ≤ p)]` or metric properties of the spaces `α` and `β`. This allows us to provide
the rewrite lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.toReal`.
-/


section EDist

variable [EDist α] [EDist β]

/--
Instance `instProdEDist` / 实例 `instProdEDist`

English:
instance instProdEDist
  signature: : EDist (WithLp p (α × β)) where
  body: if _hp : p = 0 then
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      edist f.fst g.fst ⊔ edist f.snd g.snd
    else
      (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

中文:
实例 instProdEDist
  签名: : EDist (WithLp p (α × β)) where
  定义体: if _hp : p = 0 then
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      edist f.fst g.fst ⊔ edist f.snd g.snd
    else
      (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

Depends on / 依赖: f.fst, f.snd, g.fst, g.snd, p.toReal, toReal
-/
instance instProdEDist : EDist (WithLp p (α × β)) where
  edist f g :=
    if _hp : p = 0 then
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      edist f.fst g.fst ⊔ edist f.snd g.snd
    else
      (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

@[simp]
/--
theorem `prod_edist_eq_card` / 定理 `prod_edist_eq_card`

English:
theorem prod_edist_eq_card
  given: (f g : WithLp 0 (α × β))
  proof: by
  convert! if_pos rfl

中文:
定理 prod_edist_eq_card
  条件: (f g : WithLp 0 (α × β))
  证明: by
  convert! if_pos rfl

Depends on / 依赖: convert, if_pos
-/
theorem prod_edist_eq_card (f g : WithLp 0 (α × β)) :
    edist f g =
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1) := by
  convert! if_pos rfl

/--
theorem `prod_edist_eq_add` / 定理 `prod_edist_eq_add`

English:
theorem prod_edist_eq_add
  given: (hp : 0 < p.toReal) (f g : WithLp p (α × β))
  proof: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

中文:
定理 prod_edist_eq_add
  条件: (hp : 0 < p.to实数) (f g : WithLp p (α × β))
  证明: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff.mp, if_neg, toReal_pos_iff
-/
theorem prod_edist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

/--
theorem `prod_edist_eq_sup` / 定理 `prod_edist_eq_sup`

English:
theorem prod_edist_eq_sup
  given: (f g : WithLp ∞ (α × β))
  proof: rfl

中文:
定理 prod_edist_eq_sup
  条件: (f g : WithLp ∞ (α × β))
  证明: rfl
-/
theorem prod_edist_eq_sup (f g : WithLp ∞ (α × β)) :
    edist f g = edist f.fst g.fst ⊔ edist f.snd g.snd := rfl

end EDist

section EDistProp

variable {α β}
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/--
theorem `prod_edist_self` / 定理 `prod_edist_self`

English:
theorem prod_edist_self
  given: (f : WithLp p (α × β))
  statement: edist f f = 0
  proof: by
  rcases p.trichotomy with (rfl | rfl | h)
  · classical
    simp
  · simp [prod_edist_eq_sup]
  · simp [prod_edist_eq_add h, ENNReal.zero_rpow_of_pos h,
      ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

中文:
定理 prod_edist_self
  条件: (f : WithLp p (α × β))
  结论: edist f f = 0
  证明: by
  rcases p.trichotomy with (rfl | rfl | h)
  · classical
    simp
  · simp [prod_edist_eq_sup]
  · simp [prod_edist_eq_add h, ENNReal.zero_rpow_of_pos h,
      ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

Depends on / 依赖: ENNReal, ENNReal.zero_rpow_of_pos, classical, inv_pos, p.trichotomy, prod_edist_eq_add, prod_edist_eq_sup, trichotomy, zero_rpow_of_pos
-/
theorem prod_edist_self (f : WithLp p (α × β)) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · classical
    simp
  · simp [prod_edist_eq_sup]
  · simp [prod_edist_eq_add h, ENNReal.zero_rpow_of_pos h,
      ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/--
theorem `prod_edist_comm` / 定理 `prod_edist_comm`

English:
theorem prod_edist_comm
  given: (f g : WithLp p (α × β))
  statement: edist f g = edist g f
  proof: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [prod_edist_eq_card, edist_comm]
  · simp only [prod_edist_eq_sup, edist_comm]
  · simp only [prod_edist_eq_add h, edist_comm]

中文:
定理 prod_edist_comm
  条件: (f g : WithLp p (α × β))
  结论: edist f g = edist g f
  证明: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [prod_edist_eq_card, edist_comm]
  · simp only [prod_edist_eq_sup, edist_comm]
  · simp only [prod_edist_eq_add h, edist_comm]

Depends on / 依赖: edist_comm, p.trichotomy, prod_edist_eq_add, prod_edist_eq_card, prod_edist_eq_sup, trichotomy
-/
theorem prod_edist_comm (f g : WithLp p (α × β)) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [prod_edist_eq_card, edist_comm]
  · simp only [prod_edist_eq_sup, edist_comm]
  · simp only [prod_edist_eq_add h, edist_comm]

end EDistProp

section Dist

variable [Dist α] [Dist β]

/--
Instance `instProdDist` / 实例 `instProdDist`

English:
instance instProdDist
  signature: : Dist (WithLp p (α × β)) where
  body: if _hp : p = 0 then
      (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      dist f.fst g.fst ⊔ dist f.snd g.snd
    else
      (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

中文:
实例 instProdDist
  签名: : Dist (WithLp p (α × β)) where
  定义体: if _hp : p = 0 then
      (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      dist f.fst g.fst ⊔ dist f.snd g.snd
    else
      (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

Depends on / 依赖: f.fst, f.snd, g.fst, g.snd, p.toReal, toReal
-/
instance instProdDist : Dist (WithLp p (α × β)) where
  dist f g :=
    if _hp : p = 0 then
      (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      dist f.fst g.fst ⊔ dist f.snd g.snd
    else
      (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

/--
theorem `prod_dist_eq_card` / 定理 `prod_dist_eq_card`

English:
theorem prod_dist_eq_card
  given: (f g : WithLp 0 (α × β))
  statement: dist f g =
  proof: by
  convert! if_pos rfl

中文:
定理 prod_dist_eq_card
  条件: (f g : WithLp 0 (α × β))
  结论: dist f g =
  证明: by
  convert! if_pos rfl

Depends on / 依赖: convert, if_pos
-/
theorem prod_dist_eq_card (f g : WithLp 0 (α × β)) : dist f g =
    (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1) := by
  convert! if_pos rfl

/--
theorem `prod_dist_eq_add` / 定理 `prod_dist_eq_add`

English:
theorem prod_dist_eq_add
  given: (hp : 0 < p.toReal) (f g : WithLp p (α × β))
  proof: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

中文:
定理 prod_dist_eq_add
  条件: (hp : 0 < p.to实数) (f g : WithLp p (α × β))
  证明: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff.mp, if_neg, toReal_pos_iff
-/
theorem prod_dist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    dist f g = (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

/--
theorem `prod_dist_eq_sup` / 定理 `prod_dist_eq_sup`

English:
theorem prod_dist_eq_sup
  given: (f g : WithLp ∞ (α × β))
  proof: rfl

中文:
定理 prod_dist_eq_sup
  条件: (f g : WithLp ∞ (α × β))
  证明: rfl
-/
theorem prod_dist_eq_sup (f g : WithLp ∞ (α × β)) :
    dist f g = dist f.fst g.fst ⊔ dist f.snd g.snd := rfl

end Dist

section Norm

variable [Norm α] [Norm β]

/--
Instance `instProdNorm` / 实例 `instProdNorm`

English:
instance instProdNorm
  signature: : Norm (WithLp p (α × β)) where
  body: if _hp : p = 0 then
      (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1)
    else if p = ∞ then
      ‖f.fst‖ ⊔ ‖f.snd‖
    else
      (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

中文:
实例 instProdNorm
  签名: : Norm (WithLp p (α × β)) where
  定义体: if _hp : p = 0 then
      (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1)
    else if p = ∞ then
      ‖f.fst‖ ⊔ ‖f.snd‖
    else
      (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

Depends on / 依赖: f.fst, f.snd, p.toReal, toReal
-/
instance instProdNorm : Norm (WithLp p (α × β)) where
  norm f :=
    if _hp : p = 0 then
      (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1)
    else if p = ∞ then
      ‖f.fst‖ ⊔ ‖f.snd‖
    else
      (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

@[simp]
/--
theorem `prod_norm_eq_card` / 定理 `prod_norm_eq_card`

English:
theorem prod_norm_eq_card
  given: (f : WithLp 0 (α × β))
  proof: by
  convert! if_pos rfl

中文:
定理 prod_norm_eq_card
  条件: (f : WithLp 0 (α × β))
  证明: by
  convert! if_pos rfl

Depends on / 依赖: convert, if_pos
-/
theorem prod_norm_eq_card (f : WithLp 0 (α × β)) :
    ‖f‖ = (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1) := by
  convert! if_pos rfl

/--
theorem `prod_norm_eq_sup` / 定理 `prod_norm_eq_sup`

English:
theorem prod_norm_eq_sup
  given: (f : WithLp ∞ (α × β))
  statement: ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖
  proof: rfl

中文:
定理 prod_norm_eq_sup
  条件: (f : WithLp ∞ (α × β))
  结论: ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖
  证明: rfl
-/
theorem prod_norm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖ := rfl

/--
theorem `prod_norm_eq_add` / 定理 `prod_norm_eq_add`

English:
theorem prod_norm_eq_add
  given: (hp : 0 < p.toReal) (f : WithLp p (α × β))
  proof: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

中文:
定理 prod_norm_eq_add
  条件: (hp : 0 < p.to实数) (f : WithLp p (α × β))
  证明: let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff.mp, if_neg, toReal_pos_iff
-/
theorem prod_norm_eq_add (hp : 0 < p.toReal) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `WithLp p (α × β)`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Prod type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.

TODO: the results about uniformity and bornology should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/


variable [hp : Fact (1 <= p)]

/-- Endowing the space `WithLp p (α × β)` with the `L^p` pseudoemetric structure. This definition is
not satisfactory, as it does not register the fact that the topology and the uniform structure
coincide with the product one. Therefore, we do not register it as an instance. Using this as a
temporary pseudoemetric space instance, we will show that the uniform structure is equal (but not
defeq) to the product one, and then register an instance in which we replace the uniform structure
by the product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
@[instance_reducible]
/--
Definition of `prodPseudoEMetricAux` / `prodPseudoEMetricAux` 的定义

English:
definition prodPseudoEMetricAux
  signature: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  body: prod_edist_self p
  edist_comm := prod_edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [prod_edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_

中文:
定义 prodPseudoEMetricAux
  签名: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  定义体: prod_edist_self p
  edist_comm := prod_edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [prod_edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_

Depends on / 依赖: prod_edist_self
-/
def prodPseudoEMetricAux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) where
  edist_self := prod_edist_self p
  edist_comm := prod_edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [prod_edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_add le_sup_right le_sup_right)
    · simp only [prod_edist_eq_add (zero_lt_one.trans_le hp)]
      calc
        (edist f.fst h.fst ^ p.toReal + edist f.snd h.snd ^ p.toReal) ^ (1 / p.toReal) <=
            ((edist f.fst g.fst + edist g.fst h.fst) ^ p.toReal +
              (edist f.snd g.snd + edist g.snd h.snd) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr <;> apply edist_triangle
        _ <=
            (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) +
              (edist g.fst h.fst ^ p.toReal + edist g.snd h.snd ^ p.toReal) ^ (1 / p.toReal) := by
          have := ENNReal.Lp_add_le {0, 1}
            (if · = 0 then edist f.fst g.fst else edist f.snd g.snd)
            (if · = 0 then edist g.fst h.fst else edist g.snd h.snd) hp
          simp only [Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
            Finset.sum_singleton, reduceCtorEq] at this
          exact this

attribute [local instance] WithLp.prodPseudoEMetricAux

variable {α β}

/--
theorem `prod_sup_edist_ne_top_aux` / 定理 `prod_sup_edist_ne_top_aux`

English:
theorem prod_sup_edist_ne_top_aux
  statement: [PseudoMetricSpace α] [PseudoMetricSpace β]
  proof: ne_of_lt by simp [edist, PseudoMetricSpace.edist_dist]

中文:
定理 prod_sup_edist_ne_top_aux
  结论: [PseudoMetricSpace α] [PseudoMetricSpace β]
  证明: ne_of_lt by simp [edist, PseudoMetricSpace.edist_dist]

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.edist_dist, edist_dist, ne_of_lt
-/
theorem prod_sup_edist_ne_top_aux [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f g : WithLp ∞ (α × β)) :
    edist f.fst g.fst ⊔ edist f.snd g.snd != ⊤ :=
ne_of_lt by simp [edist, PseudoMetricSpace.edist_dist]

variable (α β)

/--
Definition of `prodPseudoMetricAux` / `prodPseudoMetricAux` 的定义

English:
abbreviation prodPseudoMetricAux
  signature: [PseudoMetricSpace α] [PseudoMetricSpace β]
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp [prod_dist_eq_sup]
      · simp only [dist, one_div, dite_eq_ite]
        split_ifs with hp' <;> positivity)
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · refine 

中文:
缩写 prodPseudoMetricAux
  签名: [PseudoMetricSpace α] [PseudoMetricSpace β]
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp [prod_dist_eq_sup]
      · simp only [dist, one_div, dite_eq_ite]
        split_ifs with hp' <;> positivity)
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · refine 

Depends on / 依赖: ENNReal, ENNReal.eq_of_forall_le_nnreal_iff, ENNReal.toReal_pos_iff_ne_top, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, dichotomy, dite_eq_ite, edist_dist, eq_of_forall_le_nnreal_iff, one_div, p.dichotomy, p.toReal, prod_dist_e, prod_dist_eq_sup, prod_edist_eq_add, prod_edist_eq_sup, split_ifs, toPseudoMetricSpaceOfDist, toReal, toReal_pos_iff_ne_top
-/
abbrev prodPseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp [prod_dist_eq_sup]
      · simp only [dist, one_div, dite_eq_ite]
        split_ifs with hp' <;> positivity)
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
      simp [prod_edist_eq_sup, prod_dist_eq_sup]
    · have : 0 < p.toReal := by rw [ENNReal.toReal_pos_iff_ne_top]; rintro rfl; norm_num at h
      simp only [prod_edist_eq_add, edist_dist, one_div, prod_dist_eq_add, this]
      rw [← ENNReal.ofReal_rpow_of_nonneg]; rw [ENNReal.ofReal_add]; rw [← ENNReal.ofReal_rpow_of_nonneg]; rw [← ENNReal.ofReal_rpow_of_nonneg] <;> simp [Real.rpow_nonneg, add_nonneg]

attribute [local instance] WithLp.prodPseudoMetricAux

variable {α β} in
/--
theorem `edist_proj_le_edist_aux` / 定理 `edist_proj_le_edist_aux`

English:
theorem edist_proj_le_edist_aux
  statement: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: by
  rcases p.dichotomy with (rfl | h)
  · simp [prod_edist_eq_sup]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
    constructor
    · calc
        edist x.fst y.fst <= (edist x.fst y.fst ^ p.toR

中文:
定理 edist_proj_le_edist_aux
  结论: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: by
  rcases p.dichotomy with (rfl | h)
  · simp [prod_edist_eq_sup]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
    constructor
    · calc
        edist x.fst y.fst <= (edist x.fst y.fst ^ p.toR
-/
private theorem edist_proj_le_edist_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (x y : WithLp p (α × β)) :
    edist x.fst y.fst <= edist x y ∧ edist x.snd y.snd <= edist x y := by
  rcases p.dichotomy with (rfl | h)
  · simp [prod_edist_eq_sup]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
    constructor
    · calc
        edist x.fst y.fst <= (edist x.fst y.fst ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ <= (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_right]
    · calc
        edist x.snd y.snd <= (edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ <= (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_left]

/--
lemma `prod_lipschitzWith_ofLp_aux` / 引理 `prod_lipschitzWith_ofLp_aux`

English:
lemma prod_lipschitzWith_ofLp_aux
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: by
  intro x y
  change max _ _ <= _
  rw [ENNReal.coe_one]; rw [one_mul]; rw [sup_le_iff]
  exact edist_proj_le_edist_aux p x y

中文:
引理 prod_lipschitzWith_ofLp_aux
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: by
  intro x y
  change max _ _ <= _
  rw [ENNReal.coe_one]; rw [one_mul]; rw [sup_le_iff]
  exact edist_proj_le_edist_aux p x y
-/
private lemma prod_lipschitzWith_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (@ofLp p (α × β)) := by
  intro x y
  change max _ _ <= _
  rw [ENNReal.coe_one]; rw [one_mul]; rw [sup_le_iff]
  exact edist_proj_le_edist_aux p x y

/--
lemma `prod_antilipschitzWith_ofLp_aux` / 引理 `prod_antilipschitzWith_ofLp_aux`

English:
lemma prod_antilipschitzWith_ofLp_aux
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 <= 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [prod_edist_eq_add pos]; rw [ENNReal.toReal

中文:
引理 prod_antilipschitzWith_ofLp_aux
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 <= 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [prod_edist_eq_add pos]; rw [ENNReal.toReal
-/
private lemma prod_antilipschitzWith_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : Real>=0) ^ (1 / p).toReal) (@ofLp p (α × β)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 <= 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [prod_edist_eq_add pos]; rw [ENNReal.toReal_div 1 p]
    simp only [edist, ENNReal.toReal_one]
    calc
      (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) <=
          (edist (ofLp x) (ofLp y) ^ p.toReal +
          edist (ofLp x) (ofLp y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr <;> simp [edist]
      _ = (2 ^ (1 / p.toReal) : Real>=0) * edist (ofLp x) (ofLp y) := by
        simp only [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel,
          ENNReal.rpow_one, ENNReal.coe_rpow_of_nonneg _ nonneg, coe_ofNat]

/--
lemma `isUniformInducing_ofLp_aux` / 引理 `isUniformInducing_ofLp_aux`

English:
lemma isUniformInducing_ofLp_aux
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: (prod_antilipschitzWith_ofLp_aux p α β).isUniformInducing
    (prod_lipschitzWith_ofLp_aux p α β).uniformContinuous

中文:
引理 isUniformInducing_ofLp_aux
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: (prod_antilipschitzWith_ofLp_aux p α β).isUniformInducing
    (prod_lipschitzWith_ofLp_aux p α β).uniformContinuous
-/
private lemma isUniformInducing_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    IsUniformInducing (@ofLp p (α × β)) :=
  (prod_antilipschitzWith_ofLp_aux p α β).isUniformInducing
    (prod_lipschitzWith_ofLp_aux p α β).uniformContinuous

set_option backward.privateInPublic true in
/--
lemma `prod_uniformity_aux` / 引理 `prod_uniformity_aux`

English:
lemma prod_uniformity_aux
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: by
  rw [← (isUniformInducing_ofLp_aux p α β).comap_uniformity]
  rfl

中文:
引理 prod_uniformity_aux
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: by
  rw [← (isUniformInducing_ofLp_aux p α β).comap_uniformity]
  rfl
-/
private lemma prod_uniformity_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    𝓤 (WithLp p (α × β)) = 𝓤[UniformSpace.comap ofLp inferInstance] := by
  rw [← (isUniformInducing_ofLp_aux p α β).comap_uniformity]
  rfl

/--
Instance `instProdBornology` / 实例 `instProdBornology`

English:
instance instProdBornology
  signature: (p : Real>=0∞) (α β : Type*) [Bornology α] [Bornology β]
  body: Bornology.induced ofLp

中文:
实例 instProdBornology
  签名: (p : 实数>=0∞) (α β : 类型) [Bornology α] [Bornology β]
  定义体: Bornology.induced ofLp

Depends on / 依赖: Bornology, Bornology.induced, induced
-/
instance instProdBornology (p : Real>=0∞) (α β : Type*) [Bornology α] [Bornology β] :
    Bornology (WithLp p (α × β)) := Bornology.induced ofLp

set_option backward.privateInPublic true in
/--
lemma `prod_cobounded_aux` / 引理 `prod_cobounded_aux`

English:
lemma prod_cobounded_aux
  given: [PseudoMetricSpace α] [PseudoMetricSpace β]
  proof: le_antisymm (prod_antilipschitzWith_ofLp_aux p α β).tendsto_cobounded.le_comap
      (prod_lipschitzWith_ofLp_aux p α β).comap_cobounded_le

中文:
引理 prod_cobounded_aux
  条件: [PseudoMetricSpace α] [PseudoMetricSpace β]
  证明: le_antisymm (prod_antilipschitzWith_ofLp_aux p α β).tendsto_cobounded.le_comap
      (prod_lipschitzWith_ofLp_aux p α β).comap_cobounded_le
-/
private lemma prod_cobounded_aux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    @cobounded _ PseudoMetricSpace.toBornology = cobounded (WithLp p (α × β)) :=
  le_antisymm (prod_antilipschitzWith_ofLp_aux p α β).tendsto_cobounded.le_comap
      (prod_lipschitzWith_ofLp_aux p α β).comap_cobounded_le

end Aux

/-! ### Instances on `L^p` products -/

section TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β]

/--
Instance `instProdTopologicalSpace` / 实例 `instProdTopologicalSpace`

English:
instance instProdTopologicalSpace
  signature: : TopologicalSpace (WithLp p (α × β))
  body: instTopologicalSpaceProd.induced ofLp

@[continuity, fun_prop]

中文:
实例 instProdTopologicalSpace
  签名: : TopologicalSpace (WithLp p (α × β))
  定义体: instTopologicalSpaceProd.induced ofLp

@[continuity, fun_prop]

Depends on / 依赖: induced, instTopologicalSpaceProd, instTopologicalSpaceProd.induced
-/
instance instProdTopologicalSpace : TopologicalSpace (WithLp p (α × β)) :=
  instTopologicalSpaceProd.induced ofLp

@[continuity, fun_prop]
/--
lemma `prod_continuous_toLp` / 引理 `prod_continuous_toLp`

English:
lemma prod_continuous_toLp
  statement: Continuous (@toLp p (α × β))
  proof: continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]

中文:
引理 prod_continuous_toLp
  结论: Continuous (@toLp p (α × β))
  证明: continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]

Depends on / 依赖: continuous_id, continuous_induced_rng
-/
lemma prod_continuous_toLp : Continuous (@toLp p (α × β)) :=
  continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]
/--
lemma `prod_continuous_ofLp` / 引理 `prod_continuous_ofLp`

English:
lemma prod_continuous_ofLp
  statement: Continuous (@ofLp p (α × β))
  proof: continuous_induced_dom

中文:
引理 prod_continuous_ofLp
  结论: Continuous (@ofLp p (α × β))
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
lemma prod_continuous_ofLp : Continuous (@ofLp p (α × β)) := continuous_induced_dom

/--
Definition of `homeomorphProd` / `homeomorphProd` 的定义

English:
definition homeomorphProd
  signature: : WithLp p (α × β) ≃ₜ α × β where
  body: WithLp.equiv p (α × β)

@[simp]

中文:
定义 homeomorphProd
  签名: : WithLp p (α × β) ≃ₜ α × β where
  定义体: WithLp.equiv p (α × β)

@[simp]

Depends on / 依赖: WithLp, WithLp.equiv
-/
def homeomorphProd : WithLp p (α × β) ≃ₜ α × β where
  toEquiv := WithLp.equiv p (α × β)

@[simp]
/--
lemma `toEquiv_homeomorphProd` / 引理 `toEquiv_homeomorphProd`

English:
lemma toEquiv_homeomorphProd
  statement: (homeomorphProd p α β).toEquiv = WithLp.equiv p (α × β)
  proof: rfl

@[fun_prop]

中文:
引理 toEquiv_homeomorphProd
  结论: (homeomorphProd p α β).toEquiv = WithLp.equiv p (α × β)
  证明: rfl

@[fun_prop]
-/
lemma toEquiv_homeomorphProd : (homeomorphProd p α β).toEquiv = WithLp.equiv p (α × β) := rfl

@[fun_prop]
/--
lemma `continuous_fst` / 引理 `continuous_fst`

English:
lemma continuous_fst
  statement: Continuous (@WithLp.fst p α β)
  proof: continuous_fst.comp prod_continuous_ofLp ..

@[fun_prop]

中文:
引理 continuous_fst
  结论: Continuous (@WithLp.fst p α β)
  证明: continuous_fst.comp prod_continuous_ofLp ..

@[fun_prop]
-/
protected lemma continuous_fst : Continuous (@WithLp.fst p α β) :=
continuous_fst.comp prod_continuous_ofLp ..

@[fun_prop]
/--
lemma `continuous_snd` / 引理 `continuous_snd`

English:
lemma continuous_snd
  statement: Continuous (@WithLp.snd p α β)
  proof: continuous_snd.comp prod_continuous_ofLp ..

中文:
引理 continuous_snd
  结论: Continuous (@WithLp.snd p α β)
  证明: continuous_snd.comp prod_continuous_ofLp ..
-/
protected lemma continuous_snd : Continuous (@WithLp.snd p α β) :=
continuous_snd.comp prod_continuous_ofLp ..

variable [T0Space α] [T0Space β]

/--
Instance `instProdT0Space` / 实例 `instProdT0Space`

English:
instance instProdT0Space
  signature: : T0Space (WithLp p (α × β))
  body: (homeomorphProd p α β).symm.t0Space

中文:
实例 instProdT0Space
  签名: : T0Space (WithLp p (α × β))
  定义体: (homeomorphProd p α β).symm.t0Space

Depends on / 依赖: homeomorphProd, symm.t0Space, t0Space
-/
instance instProdT0Space : T0Space (WithLp p (α × β)) :=
  (homeomorphProd p α β).symm.t0Space

variable [SecondCountableTopology α] [SecondCountableTopology β]

/--
Instance `secondCountableTopology` / 实例 `secondCountableTopology`

English:
instance secondCountableTopology
  signature: : SecondCountableTopology (WithLp p (α × β))
  body: (homeomorphProd p α β).secondCountableTopology

中文:
实例 secondCountableTopology
  签名: : SecondCountableTopology (WithLp p (α × β))
  定义体: (homeomorphProd p α β).secondCountableTopology

Depends on / 依赖: homeomorphProd, secondCountableTopology
-/
instance secondCountableTopology : SecondCountableTopology (WithLp p (α × β)) :=
  (homeomorphProd p α β).secondCountableTopology

end TopologicalSpace

section UniformSpace

variable [UniformSpace α] [UniformSpace β]

/--
Instance `instProdUniformSpace` / 实例 `instProdUniformSpace`

English:
instance instProdUniformSpace
  signature: : UniformSpace (WithLp p (α × β))
  body: instUniformSpaceProd.comap ofLp

@[fun_prop]

中文:
实例 instProdUniformSpace
  签名: : UniformSpace (WithLp p (α × β))
  定义体: instUniformSpaceProd.comap ofLp

@[fun_prop]

Depends on / 依赖: instUniformSpaceProd, instUniformSpaceProd.comap
-/
instance instProdUniformSpace : UniformSpace (WithLp p (α × β)) :=
  instUniformSpaceProd.comap ofLp

@[fun_prop]
/--
lemma `prod_uniformContinuous_toLp` / 引理 `prod_uniformContinuous_toLp`

English:
lemma prod_uniformContinuous_toLp
  statement: UniformContinuous (@toLp p (α × β))
  proof: uniformContinuous_comap' uniformContinuous_id

@[fun_prop]

中文:
引理 prod_uniformContinuous_toLp
  结论: UniformContinuous (@toLp p (α × β))
  证明: uniformContinuous_comap' uniformContinuous_id

@[fun_prop]

Depends on / 依赖: uniformContinuous_comap, uniformContinuous_id
-/
lemma prod_uniformContinuous_toLp : UniformContinuous (@toLp p (α × β)) :=
  uniformContinuous_comap' uniformContinuous_id

@[fun_prop]
/--
lemma `prod_uniformContinuous_ofLp` / 引理 `prod_uniformContinuous_ofLp`

English:
lemma prod_uniformContinuous_ofLp
  statement: UniformContinuous (@ofLp p (α × β))
  proof: uniformContinuous_comap

中文:
引理 prod_uniformContinuous_ofLp
  结论: UniformContinuous (@ofLp p (α × β))
  证明: uniformContinuous_comap

Depends on / 依赖: uniformContinuous_comap
-/
lemma prod_uniformContinuous_ofLp : UniformContinuous (@ofLp p (α × β)) :=
  uniformContinuous_comap

/--
Definition of `uniformEquivProd` / `uniformEquivProd` 的定义

English:
definition uniformEquivProd
  signature: : WithLp p (α × β) ≃ᵤ α × β where
  body: WithLp.equiv p (α × β)
  uniformContinuous_toFun := prod_uniformContinuous_ofLp p α β
  uniformContinuous_invFun := prod_uniformContinuous_toLp p α β

@[simp]

中文:
定义 uniformEquivProd
  签名: : WithLp p (α × β) ≃ᵤ α × β where
  定义体: WithLp.equiv p (α × β)
  uniformContinuous_toFun := prod_uniformContinuous_ofLp p α β
  uniformContinuous_invFun := prod_uniformContinuous_toLp p α β

@[simp]

Depends on / 依赖: WithLp, WithLp.equiv
-/
def uniformEquivProd : WithLp p (α × β) ≃ᵤ α × β where
  toEquiv := WithLp.equiv p (α × β)
  uniformContinuous_toFun := prod_uniformContinuous_ofLp p α β
  uniformContinuous_invFun := prod_uniformContinuous_toLp p α β

@[simp]
/--
lemma `toHomeomorph_uniformEquivProd` / 引理 `toHomeomorph_uniformEquivProd`

English:
lemma toHomeomorph_uniformEquivProd
  proof: rfl

@[simp]

中文:
引理 toHomeomorph_uniformEquivProd
  证明: rfl

@[simp]
-/
lemma toHomeomorph_uniformEquivProd :
    (uniformEquivProd p α β).toHomeomorph = homeomorphProd p α β := rfl

@[simp]
/--
lemma `toEquiv_uniformEquivProd` / 引理 `toEquiv_uniformEquivProd`

English:
lemma toEquiv_uniformEquivProd
  statement: (uniformEquivProd p α β).toEquiv = WithLp.equiv p (α × β)
  proof: rfl

中文:
引理 toEquiv_uniformEquivProd
  结论: (uniformEquivProd p α β).toEquiv = WithLp.equiv p (α × β)
  证明: rfl
-/
lemma toEquiv_uniformEquivProd : (uniformEquivProd p α β).toEquiv = WithLp.equiv p (α × β) := rfl

variable [CompleteSpace α] [CompleteSpace β]

/--
Instance `instProdCompleteSpace` / 实例 `instProdCompleteSpace`

English:
instance instProdCompleteSpace
  signature: : CompleteSpace (WithLp p (α × β))
  body: (uniformEquivProd p α β).completeSpace_iff.2 inferInstance

中文:
实例 instProdCompleteSpace
  签名: : CompleteSpace (WithLp p (α × β))
  定义体: (uniformEquivProd p α β).completeSpace_iff.2 inferInstance

Depends on / 依赖: completeSpace_iff, uniformEquivProd
-/
instance instProdCompleteSpace : CompleteSpace (WithLp p (α × β)) :=
  (uniformEquivProd p α β).completeSpace_iff.2 inferInstance

end UniformSpace

section ContinuousLinearEquiv

variable [TopologicalSpace α] [TopologicalSpace β]
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable [Module 𝕜 α] [Module 𝕜 β]

/-- `WithLp.equiv` as a continuous linear equivalence. -/
-- This is not specific to products and should be generalised!
@[simps!]
/--
Definition of `prodContinuousLinearEquiv` / `prodContinuousLinearEquiv` 的定义

English:
definition prodContinuousLinearEquiv
  signature: : WithLp p (α × β) ≃L[𝕜] α × β where
  body: WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_ofLp p α β
  continuous_invFun := prod_continuous_toLp p α β

@[simp]

中文:
定义 prodContinuousLinearEquiv
  签名: : WithLp p (α × β) ≃L[𝕜] α × β where
  定义体: WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_ofLp p α β
  continuous_invFun := prod_continuous_toLp p α β

@[simp]

Depends on / 依赖: WithLp, WithLp.linearEquiv, linearEquiv
-/
def prodContinuousLinearEquiv : WithLp p (α × β) ≃L[𝕜] α × β where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_ofLp p α β
  continuous_invFun := prod_continuous_toLp p α β

@[simp]
/--
lemma `prodContinuousLinearEquiv_symm_apply` / 引理 `prodContinuousLinearEquiv_symm_apply`

English:
lemma prodContinuousLinearEquiv_symm_apply
  given: (x : α × β)
  proof: rfl

中文:
引理 prodContinuousLinearEquiv_symm_apply
  条件: (x : α × β)
  证明: rfl
-/
lemma prodContinuousLinearEquiv_symm_apply (x : α × β) :
    (prodContinuousLinearEquiv p 𝕜 α β).symm x = toLp p x := rfl

/-- `WithLp.fst` as a continuous linear map. -/
@[simps! coe apply]
/--
Definition of `fstL` / `fstL` 的定义

English:
definition fstL
  signature: : WithLp p (α × β) ->L[𝕜] α where
  body: fstₗ ..

中文:
定义 fstL
  签名: : WithLp p (α × β) ->L[𝕜] α where
  定义体: fstₗ ..
-/
def fstL : WithLp p (α × β) ->L[𝕜] α where
  __ := fstₗ ..

/-- `WithLp.snd` as a continuous linear map. -/
@[simps! coe apply]
/--
Definition of `sndL` / `sndL` 的定义

English:
definition sndL
  signature: : WithLp p (α × β) ->L[𝕜] β where
  body: sndₗ ..

中文:
定义 sndL
  签名: : WithLp p (α × β) ->L[𝕜] β where
  定义体: sndₗ ..
-/
def sndL : WithLp p (α × β) ->L[𝕜] β where
  __ := sndₗ ..

end ContinuousLinearEquiv

/-! Throughout the rest of the file, we assume `1 ≤ p`. -/
variable [hp : Fact (1 <= p)]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instProdPseudoEMetricSpace` / 实例 `instProdPseudoEMetricSpace`

English:
instance instProdPseudoEMetricSpace
  signature: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  body: (prodPseudoEMetricAux p α β).replaceUniformity (prod_uniformity_aux p α β).symm

中文:
实例 instProdPseudoEMetricSpace
  签名: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  定义体: (prodPseudoEMetricAux p α β).replaceUniformity (prod_uniformity_aux p α β).symm

Depends on / 依赖: prodPseudoEMetricAux, prod_uniformity_aux, replaceUniformity
-/
instance instProdPseudoEMetricSpace [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) :=
  (prodPseudoEMetricAux p α β).replaceUniformity (prod_uniformity_aux p α β).symm

/--
Instance `instProdEMetricSpace` / 实例 `instProdEMetricSpace`

English:
instance instProdEMetricSpace
  signature: [EMetricSpace α] [EMetricSpace β]
  body: EMetricSpace.ofT0PseudoEMetricSpace (WithLp p (α × β))

中文:
实例 instProdEMetricSpace
  签名: [EMetricSpace α] [EMetricSpace β]
  定义体: EMetricSpace.ofT0PseudoEMetricSpace (WithLp p (α × β))

Depends on / 依赖: EMetricSpace, EMetricSpace.ofT0PseudoEMetricSpace, WithLp, ofT0PseudoEMetricSpace
-/
instance instProdEMetricSpace [EMetricSpace α] [EMetricSpace β] : EMetricSpace (WithLp p (α × β)) :=
  EMetricSpace.ofT0PseudoEMetricSpace (WithLp p (α × β))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instProdPseudoMetricSpace` / 实例 `instProdPseudoMetricSpace`

English:
instance instProdPseudoMetricSpace
  signature: [PseudoMetricSpace α] [PseudoMetricSpace β]
  body: ((prodPseudoMetricAux p α β).replaceUniformity
    (prod_uniformity_aux p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (prod_cobounded_aux p α β).symm sᶜ

中文:
实例 instProdPseudoMetricSpace
  签名: [PseudoMetricSpace α] [PseudoMetricSpace β]
  定义体: ((prodPseudoMetricAux p α β).replaceUniformity
    (prod_uniformity_aux p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (prod_cobounded_aux p α β).symm sᶜ

Depends on / 依赖: Filter, Filter.ext_iff, ext_iff, prodPseudoMetricAux, prod_cobounded_aux, prod_uniformity_aux, replaceBornology, replaceUniformity
-/
instance instProdPseudoMetricSpace [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  ((prodPseudoMetricAux p α β).replaceUniformity
    (prod_uniformity_aux p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (prod_cobounded_aux p α β).symm sᶜ

/--
Instance `instProdMetricSpace` / 实例 `instProdMetricSpace`

English:
instance instProdMetricSpace
  signature: [MetricSpace α] [MetricSpace β]
  body: MetricSpace.ofT0PseudoMetricSpace _

中文:
实例 instProdMetricSpace
  签名: [MetricSpace α] [MetricSpace β]
  定义体: MetricSpace.ofT0PseudoMetricSpace _

Depends on / 依赖: MetricSpace, MetricSpace.ofT0PseudoMetricSpace, ofT0PseudoMetricSpace
-/
instance instProdMetricSpace [MetricSpace α] [MetricSpace β] : MetricSpace (WithLp p (α × β)) :=
  MetricSpace.ofT0PseudoMetricSpace _

variable {p α β}

/--
theorem `prod_nndist_eq_add` / 定理 `prod_nndist_eq_add`

English:
theorem prod_nndist_eq_add
  statement: [PseudoMetricSpace α] [PseudoMetricSpace β]
  proof: NNReal.eq by
    push_cast
    exact prod_dist_eq_add (p.toReal_pos_iff_ne_top.mpr hp) _ _

中文:
定理 prod_nndist_eq_add
  结论: [PseudoMetricSpace α] [PseudoMetricSpace β]
  证明: NNReal.eq by
    push_cast
    exact prod_dist_eq_add (p.toReal_pos_iff_ne_top.mpr hp) _ _

Depends on / 依赖: NNReal, NNReal.eq, p.toReal_pos_iff_ne_top.mpr, prod_dist_eq_add, toReal_pos_iff_ne_top
-/
theorem prod_nndist_eq_add [PseudoMetricSpace α] [PseudoMetricSpace β]
    (hp : p != ∞) (x y : WithLp p (α × β)) :
    nndist x y = (nndist x.fst y.fst ^ p.toReal + nndist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) :=
NNReal.eq by
    push_cast
    exact prod_dist_eq_add (p.toReal_pos_iff_ne_top.mpr hp) _ _

/--
theorem `prod_nndist_eq_sup` / 定理 `prod_nndist_eq_sup`

English:
theorem prod_nndist_eq_sup
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp ∞ (α × β))
  proof: NNReal.eq by
    push_cast
    exact prod_dist_eq_sup _ _

中文:
定理 prod_nndist_eq_sup
  条件: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp ∞ (α × β))
  证明: NNReal.eq by
    push_cast
    exact prod_dist_eq_sup _ _

Depends on / 依赖: NNReal, NNReal.eq, prod_dist_eq_sup
-/
theorem prod_nndist_eq_sup [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp ∞ (α × β)) :
    nndist x y = nndist x.fst y.fst ⊔ nndist x.snd y.snd :=
NNReal.eq by
    push_cast
    exact prod_dist_eq_sup _ _

/--
theorem `edist_fst_le` / 定理 `edist_fst_le`

English:
theorem edist_fst_le
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β))
  proof: (edist_proj_le_edist_aux p x y).1

中文:
定理 edist_fst_le
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β))
  证明: (edist_proj_le_edist_aux p x y).1

Depends on / 依赖: edist_proj_le_edist_aux
-/
theorem edist_fst_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β)) :
    edist x.fst y.fst <= edist x y :=
  (edist_proj_le_edist_aux p x y).1

/--
theorem `edist_snd_le` / 定理 `edist_snd_le`

English:
theorem edist_snd_le
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β))
  proof: (edist_proj_le_edist_aux p x y).2

中文:
定理 edist_snd_le
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β))
  证明: (edist_proj_le_edist_aux p x y).2

Depends on / 依赖: edist_proj_le_edist_aux
-/
theorem edist_snd_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β)) :
    edist x.snd y.snd <= edist x y :=
  (edist_proj_le_edist_aux p x y).2

/--
theorem `nndist_fst_le` / 定理 `nndist_fst_le`

English:
theorem nndist_fst_le
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  proof: by
  simpa [← coe_nnreal_ennreal_nndist] using edist_fst_le x y

中文:
定理 nndist_fst_le
  条件: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  证明: by
  simpa [← coe_nnreal_ennreal_nndist] using edist_fst_le x y

Depends on / 依赖: coe_nnreal_ennreal_nndist, edist_fst_le
-/
theorem nndist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    nndist x.fst y.fst <= nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_fst_le x y

/--
theorem `nndist_snd_le` / 定理 `nndist_snd_le`

English:
theorem nndist_snd_le
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  proof: by
  simpa [← coe_nnreal_ennreal_nndist] using edist_snd_le x y

中文:
定理 nndist_snd_le
  条件: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  证明: by
  simpa [← coe_nnreal_ennreal_nndist] using edist_snd_le x y

Depends on / 依赖: coe_nnreal_ennreal_nndist, edist_snd_le
-/
theorem nndist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    nndist x.snd y.snd <= nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_snd_le x y

/--
theorem `dist_fst_le` / 定理 `dist_fst_le`

English:
theorem dist_fst_le
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  proof: nndist_fst_le x y

中文:
定理 dist_fst_le
  条件: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  证明: nndist_fst_le x y

Depends on / 依赖: nndist_fst_le
-/
theorem dist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    dist x.fst y.fst <= dist x y :=
  nndist_fst_le x y

/--
theorem `dist_snd_le` / 定理 `dist_snd_le`

English:
theorem dist_snd_le
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  proof: nndist_snd_le x y

中文:
定理 dist_snd_le
  条件: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β))
  证明: nndist_snd_le x y

Depends on / 依赖: nndist_snd_le
-/
theorem dist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    dist x.snd y.snd <= dist x y :=
  nndist_snd_le x y

variable (p α β)

/--
lemma `prod_lipschitzWith_ofLp` / 引理 `prod_lipschitzWith_ofLp`

English:
lemma prod_lipschitzWith_ofLp
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: prod_lipschitzWith_ofLp_aux p α β

中文:
引理 prod_lipschitzWith_ofLp
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: prod_lipschitzWith_ofLp_aux p α β

Depends on / 依赖: prod_lipschitzWith_ofLp_aux
-/
lemma prod_lipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (@ofLp p (α × β)) :=
  prod_lipschitzWith_ofLp_aux p α β

/--
lemma `prod_antilipschitzWith_toLp` / 引理 `prod_antilipschitzWith_toLp`

English:
lemma prod_antilipschitzWith_toLp
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: (prod_lipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

中文:
引理 prod_antilipschitzWith_toLp
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: (prod_lipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

Depends on / 依赖: ofLp_toLp, prod_lipschitzWith_ofLp, to_rightInverse
-/
lemma prod_antilipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith 1 (@toLp p (α × β)) :=
  (prod_lipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

/--
lemma `prod_antilipschitzWith_ofLp` / 引理 `prod_antilipschitzWith_ofLp`

English:
lemma prod_antilipschitzWith_ofLp
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: prod_antilipschitzWith_ofLp_aux p α β

中文:
引理 prod_antilipschitzWith_ofLp
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: prod_antilipschitzWith_ofLp_aux p α β

Depends on / 依赖: prod_antilipschitzWith_ofLp_aux
-/
lemma prod_antilipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : Real>=0) ^ (1 / p).toReal) (@ofLp p (α × β)) :=
  prod_antilipschitzWith_ofLp_aux p α β

/--
lemma `prod_lipschitzWith_toLp` / 引理 `prod_lipschitzWith_toLp`

English:
lemma prod_lipschitzWith_toLp
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: (prod_antilipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

中文:
引理 prod_lipschitzWith_toLp
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: (prod_antilipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

Depends on / 依赖: ofLp_toLp, prod_antilipschitzWith_ofLp, to_rightInverse
-/
lemma prod_lipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith ((2 : Real>=0) ^ (1 / p).toReal) (@toLp p (α × β)) :=
  (prod_antilipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

/--
lemma `prod_isometry_ofLp_infty` / 引理 `prod_isometry_ofLp_infty`

English:
lemma prod_isometry_ofLp_infty
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using prod_lipschitzWith_ofLp ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using prod_antilipschitzWith_ofLp ∞ α β x y)

中文:
引理 prod_isometry_ofLp_infty
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using prod_lipschitzWith_ofLp ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using prod_antilipschitzWith_ofLp ∞ α β x y)

Depends on / 依赖: ENNReal, ENNReal.coe_one, ENNReal.div_top, ENNReal.toReal_zero, NNReal, NNReal.rpow_zero, coe_one, div_top, le_antisymm, one_mul, prod_antilipschitzWith_ofLp, prod_lipschitzWith_ofLp, rpow_zero, toReal_zero
-/
lemma prod_isometry_ofLp_infty [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    Isometry (@ofLp ∞ (α × β)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using prod_lipschitzWith_ofLp ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using prod_antilipschitzWith_ofLp ∞ α β x y)

/--
Instance `instProdSeminormedAddCommGroup` / 实例 `instProdSeminormedAddCommGroup`

English:
instance instProdSeminormedAddCommGroup
  signature: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  body: by
    rcases p.dichotomy with (rfl | h)
    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm, ← norm_neg_add]
      rfl
    · simp only [prod_dist_eq_add (zero_lt_one.trans_le h),
        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm, ← norm_neg_add]
      rfl

@[fun_prop]

中文:
实例 instProdSeminormedAddCommGroup
  签名: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  定义体: by
    rcases p.dichotomy with (rfl | h)
    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm, ← norm_neg_add]
      rfl
    · simp only [prod_dist_eq_add (zero_lt_one.trans_le h),
        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm, ← norm_neg_add]
      rfl

@[fun_prop]

Depends on / 依赖: dichotomy, dist_eq_norm, norm_neg_add, p.dichotomy, prod_dist_eq_add, prod_dist_eq_sup, prod_norm_eq_add, prod_norm_eq_sup, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
instance instProdSeminormedAddCommGroup [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (WithLp p (α × β)) where
  dist_eq x y := by
    rcases p.dichotomy with (rfl | h)
    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm, ← norm_neg_add]
      rfl
    · simp only [prod_dist_eq_add (zero_lt_one.trans_le h),
        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm, ← norm_neg_add]
      rfl

@[fun_prop]
/--
lemma `isUniformInducing_toLp` / 引理 `isUniformInducing_toLp`

English:
lemma isUniformInducing_toLp
  given: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: (prod_antilipschitzWith_toLp p α β).isUniformInducing
    (prod_lipschitzWith_toLp p α β).uniformContinuous

中文:
引理 isUniformInducing_toLp
  条件: [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: (prod_antilipschitzWith_toLp p α β).isUniformInducing
    (prod_lipschitzWith_toLp p α β).uniformContinuous

Depends on / 依赖: isUniformInducing, prod_antilipschitzWith_toLp, prod_lipschitzWith_toLp, uniformContinuous
-/
lemma isUniformInducing_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    IsUniformInducing (@toLp p (α × β)) :=
  (prod_antilipschitzWith_toLp p α β).isUniformInducing
    (prod_lipschitzWith_toLp p α β).uniformContinuous

section
variable {β p}

/--
theorem `enorm_fst_le` / 定理 `enorm_fst_le`

English:
theorem enorm_fst_le
  given: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  proof: by
  simpa using edist_fst_le x 0

中文:
定理 enorm_fst_le
  条件: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  证明: by
  simpa using edist_fst_le x 0

Depends on / 依赖: edist_fst_le
-/
theorem enorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖ₑ <= ‖x‖ₑ := by
  simpa using edist_fst_le x 0

/--
theorem `enorm_snd_le` / 定理 `enorm_snd_le`

English:
theorem enorm_snd_le
  given: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  proof: by
  simpa using edist_snd_le x 0

中文:
定理 enorm_snd_le
  条件: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  证明: by
  simpa using edist_snd_le x 0

Depends on / 依赖: edist_snd_le
-/
theorem enorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖ₑ <= ‖x‖ₑ := by
  simpa using edist_snd_le x 0

/--
theorem `nnnorm_fst_le` / 定理 `nnnorm_fst_le`

English:
theorem nnnorm_fst_le
  given: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  proof: by
  simpa using nndist_fst_le x 0

中文:
定理 nnnorm_fst_le
  条件: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  证明: by
  simpa using nndist_fst_le x 0

Depends on / 依赖: nndist_fst_le
-/
theorem nnnorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖₊ <= ‖x‖₊ := by
  simpa using nndist_fst_le x 0

/--
theorem `nnnorm_snd_le` / 定理 `nnnorm_snd_le`

English:
theorem nnnorm_snd_le
  given: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  proof: by
  simpa using nndist_snd_le x 0

中文:
定理 nnnorm_snd_le
  条件: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  证明: by
  simpa using nndist_snd_le x 0

Depends on / 依赖: nndist_snd_le
-/
theorem nnnorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖₊ <= ‖x‖₊ := by
  simpa using nndist_snd_le x 0

/--
theorem `norm_fst_le` / 定理 `norm_fst_le`

English:
theorem norm_fst_le
  given: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  proof: by
  simpa using dist_fst_le x 0

中文:
定理 norm_fst_le
  条件: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  证明: by
  simpa using dist_fst_le x 0

Depends on / 依赖: dist_fst_le
-/
theorem norm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖ <= ‖x‖ := by
  simpa using dist_fst_le x 0

/--
theorem `norm_snd_le` / 定理 `norm_snd_le`

English:
theorem norm_snd_le
  given: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  proof: by
  simpa using dist_snd_le x 0

中文:
定理 norm_snd_le
  条件: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β))
  证明: by
  simpa using dist_snd_le x 0

Depends on / 依赖: dist_snd_le
-/
theorem norm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖ <= ‖x‖ := by
  simpa using dist_snd_le x 0

end

/--
Instance `instProdNormedAddCommGroup` / 实例 `instProdNormedAddCommGroup`

English:
instance instProdNormedAddCommGroup
  signature: [NormedAddCommGroup α] [NormedAddCommGroup β]
  body: { instProdSeminormedAddCommGroup p α β with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace.toTopologicalSpace =
    instProdTopologicalSpace p α β :=
  rfl

example [NormedAdd

中文:
实例 instProdNormedAddCommGroup
  签名: [NormedAddCommGroup α] [NormedAddCommGroup β]
  定义体: { instProdSeminormedAddCommGroup p α β with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace.toTopologicalSpace =
    instProdTopologicalSpace p α β :=
  rfl

example [NormedAdd

Depends on / 依赖: eq_of_dist_eq_zero, instProdSeminormedAddCommGroup
-/
instance instProdNormedAddCommGroup [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (WithLp p (α × β)) :=
  { instProdSeminormedAddCommGroup p α β with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace.toTopologicalSpace =
    instProdTopologicalSpace p α β :=
  rfl

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace = instProdUniformSpace p α β :=
  rfl

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toBornology = instProdBornology p α β :=
  rfl

section norm_of

variable {p α β}

/--
theorem `prod_norm_eq_of_nat` / 定理 `prod_norm_eq_of_nat`

English:
theorem prod_norm_eq_of_nat
  given: [Norm α] [Norm β] (n : Nat) (h : p = n) (f : WithLp p (α × β))
  proof: by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    prod_norm_eq_add this]

中文:
定理 prod_norm_eq_of_nat
  条件: [Norm α] [Norm β] (n : 自然数) (h : p = n) (f : WithLp p (α × β))
  证明: by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    prod_norm_eq_add this]

Depends on / 依赖: ENNReal, ENNReal.natCast_ne_top, ENNReal.toReal_natCast, Real.rpow_natCast, natCast_ne_top, ne_of_eq_of_ne, one_div, p.toReal_pos_iff_ne_top.mpr, prod_norm_eq_add, rpow_natCast, toReal_natCast, toReal_pos_iff_ne_top
-/
theorem prod_norm_eq_of_nat [Norm α] [Norm β] (n : Nat) (h : p = n) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ n + ‖f.snd‖ ^ n) ^ (1 / (n : Real)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    prod_norm_eq_add this]

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/--
theorem `prod_nnnorm_eq_add` / 定理 `prod_nnnorm_eq_add`

English:
theorem prod_nnnorm_eq_add
  given: (hp : p != ∞) (f : WithLp p (α × β))
  proof: by
  ext
  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]

中文:
定理 prod_nnnorm_eq_add
  条件: (hp : p != ∞) (f : WithLp p (α × β))
  证明: by
  ext
  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]

Depends on / 依赖: p.toReal_pos_iff_ne_top.mpr, prod_norm_eq_add, toReal_pos_iff_ne_top
-/
theorem prod_nnnorm_eq_add (hp : p != ∞) (f : WithLp p (α × β)) :
    ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]

/--
theorem `prod_nnnorm_eq_sup` / 定理 `prod_nnnorm_eq_sup`

English:
theorem prod_nnnorm_eq_sup
  given: (f : WithLp ∞ (α × β))
  statement: ‖f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊
  proof: by
  ext
  norm_cast

中文:
定理 prod_nnnorm_eq_sup
  条件: (f : WithLp ∞ (α × β))
  结论: ‖f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊
  证明: by
  ext
  norm_cast
-/
theorem prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊ := by
  ext
  norm_cast

/--
lemma `prod_nnnorm_ofLp` / 引理 `prod_nnnorm_ofLp`

English:
lemma prod_nnnorm_ofLp
  given: (f : WithLp ∞ (α × β))
  statement: ‖ofLp f‖₊ = ‖f‖₊
  proof: by
  rw [prod_nnnorm_eq_sup]; rw [Prod.nnnorm_def]; rw [ofLp_fst]; rw [ofLp_snd]

中文:
引理 prod_nnnorm_ofLp
  条件: (f : WithLp ∞ (α × β))
  结论: ‖ofLp f‖₊ = ‖f‖₊
  证明: by
  rw [prod_nnnorm_eq_sup]; rw [Prod.nnnorm_def]; rw [ofLp_fst]; rw [ofLp_snd]
-/
@[simp] lemma prod_nnnorm_ofLp (f : WithLp ∞ (α × β)) : ‖ofLp f‖₊ = ‖f‖₊ := by
  rw [prod_nnnorm_eq_sup]; rw [Prod.nnnorm_def]; rw [ofLp_fst]; rw [ofLp_snd]

/--
lemma `prod_nnnorm_toLp` / 引理 `prod_nnnorm_toLp`

English:
lemma prod_nnnorm_toLp
  given: (f : α × β)
  statement: ‖toLp ⊤ f‖₊ = ‖f‖₊
  proof: (prod_nnnorm_ofLp _).symm

中文:
引理 prod_nnnorm_toLp
  条件: (f : α × β)
  结论: ‖toLp ⊤ f‖₊ = ‖f‖₊
  证明: (prod_nnnorm_ofLp _).symm
-/
@[simp] lemma prod_nnnorm_toLp (f : α × β) : ‖toLp ⊤ f‖₊ = ‖f‖₊ :=
  (prod_nnnorm_ofLp _).symm

/--
lemma `prod_norm_ofLp` / 引理 `prod_norm_ofLp`

English:
lemma prod_norm_ofLp
  given: (f : WithLp ∞ (α × β))
  statement: ‖ofLp f‖ = ‖f‖
  proof: congr_arg NNReal.toReal prod_nnnorm_ofLp f

中文:
引理 prod_norm_ofLp
  条件: (f : WithLp ∞ (α × β))
  结论: ‖ofLp f‖ = ‖f‖
  证明: congr_arg NNReal.toReal prod_nnnorm_ofLp f
-/
@[simp] lemma prod_norm_ofLp (f : WithLp ∞ (α × β)) : ‖ofLp f‖ = ‖f‖ :=
congr_arg NNReal.toReal prod_nnnorm_ofLp f

/--
lemma `prod_norm_toLp` / 引理 `prod_norm_toLp`

English:
lemma prod_norm_toLp
  given: (f : α × β)
  statement: ‖toLp ⊤ f‖ = ‖f‖
  proof: (prod_norm_ofLp _).symm

中文:
引理 prod_norm_toLp
  条件: (f : α × β)
  结论: ‖toLp ⊤ f‖ = ‖f‖
  证明: (prod_norm_ofLp _).symm
-/
@[simp] lemma prod_norm_toLp (f : α × β) : ‖toLp ⊤ f‖ = ‖f‖ :=
  (prod_norm_ofLp _).symm

section L1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `prod_norm_eq_of_L1` / 定理 `prod_norm_eq_of_L1`

English:
theorem prod_norm_eq_of_L1
  given: (x : WithLp 1 (α × β))
  proof: by
  simp [prod_norm_eq_add]

中文:
定理 prod_norm_eq_of_L1
  条件: (x : WithLp 1 (α × β))
  证明: by
  simp [prod_norm_eq_add]

Depends on / 依赖: prod_norm_eq_add
-/
theorem prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) :
    ‖x‖ = ‖x.fst‖ + ‖x.snd‖ := by
  simp [prod_norm_eq_add]

/--
theorem `prod_nnnorm_eq_of_L1` / 定理 `prod_nnnorm_eq_of_L1`

English:
theorem prod_nnnorm_eq_of_L1
  given: (x : WithLp 1 (α × β))
  proof: NNReal.eq by
    push_cast
    exact prod_norm_eq_of_L1 x

中文:
定理 prod_nnnorm_eq_of_L1
  条件: (x : WithLp 1 (α × β))
  证明: NNReal.eq by
    push_cast
    exact prod_norm_eq_of_L1 x

Depends on / 依赖: NNReal, NNReal.eq, prod_norm_eq_of_L1
-/
theorem prod_nnnorm_eq_of_L1 (x : WithLp 1 (α × β)) :
    ‖x‖₊ = ‖x.fst‖₊ + ‖x.snd‖₊ :=
NNReal.eq by
    push_cast
    exact prod_norm_eq_of_L1 x

/--
theorem `prod_dist_eq_of_L1` / 定理 `prod_dist_eq_of_L1`

English:
theorem prod_dist_eq_of_L1
  given: (x y : WithLp 1 (α × β))
  proof: by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L1, sub_fst, sub_snd]

中文:
定理 prod_dist_eq_of_L1
  条件: (x y : WithLp 1 (α × β))
  证明: by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L1, sub_fst, sub_snd]

Depends on / 依赖: dist_eq_norm, prod_norm_eq_of_L1, simp_rw, sub_fst, sub_snd
-/
theorem prod_dist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    dist x y = dist x.fst y.fst + dist x.snd y.snd := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L1, sub_fst, sub_snd]

/--
theorem `prod_nndist_eq_of_L1` / 定理 `prod_nndist_eq_of_L1`

English:
theorem prod_nndist_eq_of_L1
  given: (x y : WithLp 1 (α × β))
  proof: NNReal.eq by
    push_cast
    exact prod_dist_eq_of_L1 _ _

中文:
定理 prod_nndist_eq_of_L1
  条件: (x y : WithLp 1 (α × β))
  证明: NNReal.eq by
    push_cast
    exact prod_dist_eq_of_L1 _ _

Depends on / 依赖: NNReal, NNReal.eq, prod_dist_eq_of_L1
-/
theorem prod_nndist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    nndist x y = nndist x.fst y.fst + nndist x.snd y.snd :=
NNReal.eq by
    push_cast
    exact prod_dist_eq_of_L1 _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `prod_edist_eq_of_L1` / 定理 `prod_edist_eq_of_L1`

English:
theorem prod_edist_eq_of_L1
  given: (x y : WithLp 1 (α × β))
  proof: by
  simp [prod_edist_eq_add]

中文:
定理 prod_edist_eq_of_L1
  条件: (x y : WithLp 1 (α × β))
  证明: by
  simp [prod_edist_eq_add]

Depends on / 依赖: prod_edist_eq_add
-/
theorem prod_edist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    edist x y = edist x.fst y.fst + edist x.snd y.snd := by
  simp [prod_edist_eq_add]

end L1

section L2

/--
theorem `prod_norm_eq_of_L2` / 定理 `prod_norm_eq_of_L2`

English:
theorem prod_norm_eq_of_L2
  given: (x : WithLp 2 (α × β))
  proof: by
  rw [prod_norm_eq_of_nat 2 (by norm_cast) _]; rw [Real.sqrt_eq_rpow]
  norm_cast

中文:
定理 prod_norm_eq_of_L2
  条件: (x : WithLp 2 (α × β))
  证明: by
  rw [prod_norm_eq_of_nat 2 (by norm_cast) _]; rw [Real.sqrt_eq_rpow]
  norm_cast

Depends on / 依赖: Real.sqrt_eq_rpow, prod_norm_eq_of_nat, sqrt_eq_rpow
-/
theorem prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
  rw [prod_norm_eq_of_nat 2 (by norm_cast) _]; rw [Real.sqrt_eq_rpow]
  norm_cast

/--
theorem `prod_nnnorm_eq_of_L2` / 定理 `prod_nnnorm_eq_of_L2`

English:
theorem prod_nnnorm_eq_of_L2
  given: (x : WithLp 2 (α × β))
  proof: NNReal.eq by
    push_cast
    exact prod_norm_eq_of_L2 x

中文:
定理 prod_nnnorm_eq_of_L2
  条件: (x : WithLp 2 (α × β))
  证明: NNReal.eq by
    push_cast
    exact prod_norm_eq_of_L2 x

Depends on / 依赖: NNReal, NNReal.eq, prod_norm_eq_of_L2
-/
theorem prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2) :=
NNReal.eq by
    push_cast
    exact prod_norm_eq_of_L2 x

/--
theorem `prod_norm_sq_eq_of_L2` / 定理 `prod_norm_sq_eq_of_L2`

English:
theorem prod_norm_sq_eq_of_L2
  given: (x : WithLp 2 (α × β))
  statement: ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2
  proof: by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) this
  rw [prod_nnnorm_eq_of_L2]; rw [NNReal.sq_sqrt]

中文:
定理 prod_norm_sq_eq_of_L2
  条件: (x : WithLp 2 (α × β))
  结论: ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2
  证明: by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) this
  rw [prod_nnnorm_eq_of_L2]; rw [NNReal.sq_sqrt]

Depends on / 依赖: NNReal, NNReal.coe_sum, NNReal.sq_sqrt, coe_sum, congr_arg, prod_nnnorm_eq_of_L2, sq_sqrt, x.fst, x.snd
-/
theorem prod_norm_sq_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) this
  rw [prod_nnnorm_eq_of_L2]; rw [NNReal.sq_sqrt]

/--
theorem `prod_dist_eq_of_L2` / 定理 `prod_dist_eq_of_L2`

English:
theorem prod_dist_eq_of_L2
  given: (x y : WithLp 2 (α × β))
  proof: by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L2, sub_fst, sub_snd]

中文:
定理 prod_dist_eq_of_L2
  条件: (x y : WithLp 2 (α × β))
  证明: by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L2, sub_fst, sub_snd]

Depends on / 依赖: dist_eq_norm, prod_norm_eq_of_L2, simp_rw, sub_fst, sub_snd
-/
theorem prod_dist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    dist x y = √(dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2) := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L2, sub_fst, sub_snd]

/--
theorem `prod_nndist_eq_of_L2` / 定理 `prod_nndist_eq_of_L2`

English:
theorem prod_nndist_eq_of_L2
  given: (x y : WithLp 2 (α × β))
  proof: NNReal.eq by
    push_cast
    exact prod_dist_eq_of_L2 _ _

中文:
定理 prod_nndist_eq_of_L2
  条件: (x y : WithLp 2 (α × β))
  证明: NNReal.eq by
    push_cast
    exact prod_dist_eq_of_L2 _ _

Depends on / 依赖: NNReal, NNReal.eq, prod_dist_eq_of_L2
-/
theorem prod_nndist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    nndist x y = NNReal.sqrt (nndist x.fst y.fst ^ 2 + nndist x.snd y.snd ^ 2) :=
NNReal.eq by
    push_cast
    exact prod_dist_eq_of_L2 _ _

/--
theorem `prod_edist_eq_of_L2` / 定理 `prod_edist_eq_of_L2`

English:
theorem prod_edist_eq_of_L2
  given: (x y : WithLp 2 (α × β))
  proof: by
  simp [prod_edist_eq_add]

中文:
定理 prod_edist_eq_of_L2
  条件: (x y : WithLp 2 (α × β))
  证明: by
  simp [prod_edist_eq_add]

Depends on / 依赖: prod_edist_eq_add
-/
theorem prod_edist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    edist x y = (edist x.fst y.fst ^ 2 + edist x.snd y.snd ^ 2) ^ (1 / 2 : Real) := by
  simp [prod_edist_eq_add]

end L2

end norm_of

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

section Single

/--
lemma `nnnorm_toLp_inl` / 引理 `nnnorm_toLp_inl`

English:
lemma nnnorm_toLp_inl
  given: (x : α)
  statement: ‖toLp p (x, (0 : β))‖₊ = ‖x‖₊
  proof: by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : Real) != 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 <= (p : Real>=0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

中文:
引理 nnnorm_toLp_inl
  条件: (x : α)
  结论: ‖toLp p (x, (0 : β))‖₊ = ‖x‖₊
  证明: by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : Real) != 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 <= (p : Real>=0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]
-/
@[simp] lemma nnnorm_toLp_inl (x : α) : ‖toLp p (x, (0 : β))‖₊ = ‖x‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : Real) != 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 <= (p : Real>=0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

/--
lemma `nnnorm_toLp_inr` / 引理 `nnnorm_toLp_inr`

English:
lemma nnnorm_toLp_inr
  given: (y : β)
  statement: ‖toLp p ((0 : α), y)‖₊ = ‖y‖₊
  proof: by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : Real) != 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 <= (p : Real>=0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp

中文:
引理 nnnorm_toLp_inr
  条件: (y : β)
  结论: ‖toLp p ((0 : α), y)‖₊ = ‖y‖₊
  证明: by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : Real) != 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 <= (p : Real>=0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp
-/
@[simp] lemma nnnorm_toLp_inr (y : β) : ‖toLp p ((0 : α), y)‖₊ = ‖y‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : Real) != 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 <= (p : Real>=0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp]
/--
lemma `norm_toLp_fst` / 引理 `norm_toLp_fst`

English:
lemma norm_toLp_fst
  given: (x : α)
  statement: ‖toLp p (x, (0 : β))‖ = ‖x‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_toLp_inl p α β x

@[simp]

中文:
引理 norm_toLp_fst
  条件: (x : α)
  结论: ‖toLp p (x, (0 : β))‖ = ‖x‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_toLp_inl p α β x

@[simp]

Depends on / 依赖: congr_arg, nnnorm_toLp_inl
-/
lemma norm_toLp_fst (x : α) : ‖toLp p (x, (0 : β))‖ = ‖x‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_toLp_inl p α β x

@[simp]
/--
lemma `norm_toLp_snd` / 引理 `norm_toLp_snd`

English:
lemma norm_toLp_snd
  given: (y : β)
  statement: ‖toLp p ((0 : α), y)‖ = ‖y‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_toLp_inr p α β y

@[simp]

中文:
引理 norm_toLp_snd
  条件: (y : β)
  结论: ‖toLp p ((0 : α), y)‖ = ‖y‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_toLp_inr p α β y

@[simp]

Depends on / 依赖: congr_arg, nnnorm_toLp_inr
-/
lemma norm_toLp_snd (y : β) : ‖toLp p ((0 : α), y)‖ = ‖y‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_toLp_inr p α β y

@[simp]
/--
lemma `nndist_toLp_fst` / 引理 `nndist_toLp_fst`

English:
lemma nndist_toLp_fst
  given: (x₁ x₂ : α)
  proof: by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← toLp_sub]; rw [Prod.mk_sub_mk]; rw [sub_zero]; rw [nnnorm_toLp_inl]

@[simp]

中文:
引理 nndist_toLp_fst
  条件: (x₁ x₂ : α)
  证明: by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← toLp_sub]; rw [Prod.mk_sub_mk]; rw [sub_zero]; rw [nnnorm_toLp_inl]

@[simp]

Depends on / 依赖: Prod.mk_sub_mk, mk_sub_mk, nndist_eq_nnnorm, nnnorm_toLp_inl, sub_zero, toLp_sub
-/
lemma nndist_toLp_fst (x₁ x₂ : α) :
    nndist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = nndist x₁ x₂ := by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← toLp_sub]; rw [Prod.mk_sub_mk]; rw [sub_zero]; rw [nnnorm_toLp_inl]

@[simp]
/--
lemma `nndist_toLp_snd` / 引理 `nndist_toLp_snd`

English:
lemma nndist_toLp_snd
  given: (y₁ y₂ : β)
  proof: by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← toLp_sub]; rw [Prod.mk_sub_mk]; rw [sub_zero]; rw [nnnorm_toLp_inr]

@[simp]

中文:
引理 nndist_toLp_snd
  条件: (y₁ y₂ : β)
  证明: by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← toLp_sub]; rw [Prod.mk_sub_mk]; rw [sub_zero]; rw [nnnorm_toLp_inr]

@[simp]

Depends on / 依赖: Prod.mk_sub_mk, mk_sub_mk, nndist_eq_nnnorm, nnnorm_toLp_inr, sub_zero, toLp_sub
-/
lemma nndist_toLp_snd (y₁ y₂ : β) :
    nndist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = nndist y₁ y₂ := by
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← toLp_sub]; rw [Prod.mk_sub_mk]; rw [sub_zero]; rw [nnnorm_toLp_inr]

@[simp]
/--
lemma `dist_toLp_fst` / 引理 `dist_toLp_fst`

English:
lemma dist_toLp_fst
  given: (x₁ x₂ : α)
  statement: dist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = dist x₁ x₂
  proof: congr_arg ((↑) : Real>=0 -> Real) nndist_toLp_fst p α β x₁ x₂

@[simp]

中文:
引理 dist_toLp_fst
  条件: (x₁ x₂ : α)
  结论: dist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = dist x₁ x₂
  证明: congr_arg ((↑) : Real>=0 -> Real) nndist_toLp_fst p α β x₁ x₂

@[simp]

Depends on / 依赖: congr_arg, nndist_toLp_fst
-/
lemma dist_toLp_fst (x₁ x₂ : α) : dist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = dist x₁ x₂ :=
congr_arg ((↑) : Real>=0 -> Real) nndist_toLp_fst p α β x₁ x₂

@[simp]
/--
lemma `dist_toLp_snd` / 引理 `dist_toLp_snd`

English:
lemma dist_toLp_snd
  given: (y₁ y₂ : β)
  proof: congr_arg ((↑) : Real>=0 -> Real) nndist_toLp_snd p α β y₁ y₂

@[simp]

中文:
引理 dist_toLp_snd
  条件: (y₁ y₂ : β)
  证明: congr_arg ((↑) : Real>=0 -> Real) nndist_toLp_snd p α β y₁ y₂

@[simp]

Depends on / 依赖: congr_arg, nndist_toLp_snd
-/
lemma dist_toLp_snd (y₁ y₂ : β) :
    dist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = dist y₁ y₂ :=
congr_arg ((↑) : Real>=0 -> Real) nndist_toLp_snd p α β y₁ y₂

@[simp]
/--
lemma `edist_toLp_fst` / 引理 `edist_toLp_fst`

English:
lemma edist_toLp_fst
  given: (x₁ x₂ : α)
  statement: edist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = edist x₁ x₂
  proof: by
  simp only [edist_nndist, nndist_toLp_fst p α β x₁ x₂]

@[simp]

中文:
引理 edist_toLp_fst
  条件: (x₁ x₂ : α)
  结论: edist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = edist x₁ x₂
  证明: by
  simp only [edist_nndist, nndist_toLp_fst p α β x₁ x₂]

@[simp]

Depends on / 依赖: edist_nndist, nndist_toLp_fst
-/
lemma edist_toLp_fst (x₁ x₂ : α) : edist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = edist x₁ x₂ := by
  simp only [edist_nndist, nndist_toLp_fst p α β x₁ x₂]

@[simp]
/--
lemma `edist_toLp_snd` / 引理 `edist_toLp_snd`

English:
lemma edist_toLp_snd
  given: (y₁ y₂ : β)
  proof: by
  simp only [edist_nndist, nndist_toLp_snd p α β y₁ y₂]

中文:
引理 edist_toLp_snd
  条件: (y₁ y₂ : β)
  证明: by
  simp only [edist_nndist, nndist_toLp_snd p α β y₁ y₂]

Depends on / 依赖: edist_nndist, nndist_toLp_snd
-/
lemma edist_toLp_snd (y₁ y₂ : β) :
    edist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = edist y₁ y₂ := by
  simp only [edist_nndist, nndist_toLp_snd p α β y₁ y₂]

end Single

section IsBoundedSMul
variable [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β] [IsBoundedSMul 𝕜 α] [IsBoundedSMul 𝕜 β]

/--
Instance `instProdIsBoundedSMul` / 实例 `instProdIsBoundedSMul`

English:
instance instProdIsBoundedSMul
  signature: : IsBoundedSMul 𝕜 (WithLp p (α × β))
  body: .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, ofLp_smul]
      exact norm_smul_le _ _
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt]; r

中文:
实例 instProdIsBoundedSMul
  签名: : IsBoundedSMul 𝕜 (WithLp p (α × β))
  定义体: .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, ofLp_smul]
      exact norm_smul_le _ _
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt]; r

Depends on / 依赖: NNReal, NNReal.mul_rp, NNReal.mul_rpow, NNReal.rpow_inv_le_iff, NNReal.rpow_mul, NNReal.rpow_one, dichotomy, hp0.ne, mul_add, mul_rp, mul_rpow, norm_smul_le, ofLp_smul, of_nnnorm_smul_le, one_div, p.dichotomy, p.toReal, p.toReal_pos_iff_ne_top.mp, prod_nnnorm_eq_add, prod_nnnorm_ofLp
-/
instance instProdIsBoundedSMul : IsBoundedSMul 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, ofLp_smul]
      exact norm_smul_le _ _
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt]; rw [prod_nnnorm_eq_add hpt]; rw [one_div]; rw [NNReal.rpow_inv_le_iff hp0]; rw [NNReal.mul_rpow]; rw [← NNReal.rpow_mul]; rw [inv_mul_cancel₀ hp0.ne']; rw [NNReal.rpow_one]; rw [mul_add]; rw [← NNReal.mul_rpow]; rw [← NNReal.mul_rpow]
      gcongr <;> exact nnnorm_smul_le _ _

variable {𝕜 p α β}

/--
Definition of `prodEquivₗᵢ` / `prodEquivₗᵢ` 的定义

English:
definition prodEquivₗᵢ
  signature: : WithLp ∞ (α × β) ≃ₗᵢ[𝕜] α × β where
  body: WithLp.equiv ∞ _
  map_add' _f _g := rfl
  map_smul' _c _f := rfl
  norm_map' x := prod_norm_toLp (ofLp x)

中文:
定义 prodEquivₗᵢ
  签名: : WithLp ∞ (α × β) ≃ₗᵢ[𝕜] α × β where
  定义体: WithLp.equiv ∞ _
  map_add' _f _g := rfl
  map_smul' _c _f := rfl
  norm_map' x := prod_norm_toLp (ofLp x)

Depends on / 依赖: WithLp, WithLp.equiv
-/
def prodEquivₗᵢ : WithLp ∞ (α × β) ≃ₗᵢ[𝕜] α × β where
  __ := WithLp.equiv ∞ _
  map_add' _f _g := rfl
  map_smul' _c _f := rfl
  norm_map' x := prod_norm_toLp (ofLp x)


end IsBoundedSMul

/--
Instance `instProdNormSMulClass` / 实例 `instProdNormSMulClass`

English:
instance instProdNormSMulClass
  signature: [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β]
  body: .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt]; rw [prod_nnno

中文:
实例 instProdNormSMulClass
  签名: [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β]
  定义体: .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt]; rw [prod_nnno

Depends on / 依赖: NNReal, NNReal.mul_rpow, NNReal.rpow_inv_eq_iff, NNReal.rpow_mul, NNReal.rpow_one, WithLp, WithLp.ofLp_smul, dichotomy, hp0.ne, mul_add, mul_rpow, nnnorm_smul, ofLp_smul, of_nnnorm_smul, one_div, p.dichotomy, p.toReal, p.toReal_pos_iff_ne_top.mp, prod_nnnorm_eq_add, prod_nnnorm_ofLp
-/
instance instProdNormSMulClass [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β]
    [NormSMulClass 𝕜 α] [NormSMulClass 𝕜 β] : NormSMulClass 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p != ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt]; rw [prod_nnnorm_eq_add hpt]; rw [one_div]; rw [NNReal.rpow_inv_eq_iff hp0.ne']; rw [NNReal.mul_rpow]; rw [← NNReal.rpow_mul]; rw [inv_mul_cancel₀ hp0.ne']; rw [NNReal.rpow_one]; rw [mul_add]; rw [← NNReal.mul_rpow]; rw [← NNReal.mul_rpow]; rw [smul_fst]; rw [smul_snd]; rw [nnnorm_smul]; rw [nnnorm_smul]

section SeminormedAddCommGroup

open ENNReal

variable {p : Real>=0∞} {α β}

/--
Definition of `idemFst` / `idemFst` 的定义

English:
definition idemFst
  signature: : AddMonoid.End (WithLp p (α × β)) where
  body: toLp p (x.fst, 0)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

中文:
定义 idemFst
  签名: : AddMonoid.End (WithLp p (α × β)) where
  定义体: toLp p (x.fst, 0)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

Depends on / 依赖: x.fst
-/
def idemFst : AddMonoid.End (WithLp p (α × β)) where
  toFun x := toLp p (x.fst, 0)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

/--
Definition of `idemSnd` / `idemSnd` 的定义

English:
definition idemSnd
  signature: : AddMonoid.End (WithLp p (α × β)) where
  body: toLp p (0, x.snd)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

中文:
定义 idemSnd
  签名: : AddMonoid.End (WithLp p (α × β)) where
  定义体: toLp p (0, x.snd)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

Depends on / 依赖: x.snd
-/
def idemSnd : AddMonoid.End (WithLp p (α × β)) where
  toFun x := toLp p (0, x.snd)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

/--
lemma `idemFst_apply` / 引理 `idemFst_apply`

English:
lemma idemFst_apply
  given: (x : WithLp p (α × β))
  statement: idemFst x = toLp p (x.fst, 0)
  proof: rfl

中文:
引理 idemFst_apply
  条件: (x : WithLp p (α × β))
  结论: idemFst x = toLp p (x.fst, 0)
  证明: rfl
-/
lemma idemFst_apply (x : WithLp p (α × β)) : idemFst x = toLp p (x.fst, 0) := rfl

/--
lemma `idemSnd_apply` / 引理 `idemSnd_apply`

English:
lemma idemSnd_apply
  given: (x : WithLp p (α × β))
  statement: idemSnd x = toLp p (0, x.snd)
  proof: rfl

中文:
引理 idemSnd_apply
  条件: (x : WithLp p (α × β))
  结论: idemSnd x = toLp p (0, x.snd)
  证明: rfl
-/
lemma idemSnd_apply (x : WithLp p (α × β)) : idemSnd x = toLp p (0, x.snd) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `idemFst_add_idemSnd` / 引理 `idemFst_add_idemSnd`

English:
lemma idemFst_add_idemSnd
  proof: AddMonoidHom.ext
  fun x => by
    rw [AddMonoidHom.add_apply]; rw [idemFst_apply]; rw [idemSnd_apply]; rw [AddMonoid.End.coe_one]; rw [id_eq]; rw [← toLp_add]; rw [Prod.mk_add_mk]; rw [zero_add]; rw [add_zero]
    rfl

中文:
引理 idemFst_add_idemSnd
  证明: AddMonoidHom.ext
  fun x => by
    rw [AddMonoidHom.add_apply]; rw [idemFst_apply]; rw [idemSnd_apply]; rw [AddMonoid.End.coe_one]; rw [id_eq]; rw [← toLp_add]; rw [Prod.mk_add_mk]; rw [zero_add]; rw [add_zero]
    rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext
-/
lemma idemFst_add_idemSnd :
    idemFst + idemSnd = (1 : AddMonoid.End (WithLp p (α × β))) := AddMonoidHom.ext
  fun x => by
    rw [AddMonoidHom.add_apply]; rw [idemFst_apply]; rw [idemSnd_apply]; rw [AddMonoid.End.coe_one]; rw [id_eq]; rw [← toLp_add]; rw [Prod.mk_add_mk]; rw [zero_add]; rw [add_zero]
    rfl

/--
lemma `idemFst_compl` / 引理 `idemFst_compl`

English:
lemma idemFst_compl
  statement: (1 : AddMonoid.End (WithLp p (α × β))) - idemFst = idemSnd
  proof: by
  rw [← idemFst_add_idemSnd]; rw [add_sub_cancel_left]

中文:
引理 idemFst_compl
  结论: (1 : AddMonoid.End (WithLp p (α × β))) - idemFst = idemSnd
  证明: by
  rw [← idemFst_add_idemSnd]; rw [add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, idemFst_add_idemSnd
-/
lemma idemFst_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemFst = idemSnd := by
  rw [← idemFst_add_idemSnd]; rw [add_sub_cancel_left]

/--
lemma `idemSnd_compl` / 引理 `idemSnd_compl`

English:
lemma idemSnd_compl
  statement: (1 : AddMonoid.End (WithLp p (α × β))) - idemSnd = idemFst
  proof: by
  rw [← idemFst_add_idemSnd]; rw [add_sub_cancel_right]

中文:
引理 idemSnd_compl
  结论: (1 : AddMonoid.End (WithLp p (α × β))) - idemSnd = idemFst
  证明: by
  rw [← idemFst_add_idemSnd]; rw [add_sub_cancel_right]

Depends on / 依赖: add_sub_cancel_right, idemFst_add_idemSnd
-/
lemma idemSnd_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemSnd = idemFst := by
  rw [← idemFst_add_idemSnd]; rw [add_sub_cancel_right]

/--
theorem `prod_norm_eq_idemFst_sup_idemSnd` / 定理 `prod_norm_eq_idemFst_sup_idemSnd`

English:
theorem prod_norm_eq_idemFst_sup_idemSnd
  given: (x : WithLp ∞ (α × β))
  proof: by
  rw [WithLp.prod_norm_eq_sup]; rw [← WithLp.norm_toLp_fst ∞ α β x.fst]; rw [← WithLp.norm_toLp_snd ∞ α β x.snd]
  rfl

中文:
定理 prod_norm_eq_idemFst_sup_idemSnd
  条件: (x : WithLp ∞ (α × β))
  证明: by
  rw [WithLp.prod_norm_eq_sup]; rw [← WithLp.norm_toLp_fst ∞ α β x.fst]; rw [← WithLp.norm_toLp_snd ∞ α β x.snd]
  rfl

Depends on / 依赖: WithLp, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd, WithLp.prod_norm_eq_sup, norm_toLp_fst, norm_toLp_snd, prod_norm_eq_sup, x.fst, x.snd
-/
theorem prod_norm_eq_idemFst_sup_idemSnd (x : WithLp ∞ (α × β)) :
    ‖x‖ = max ‖idemFst x‖ ‖idemSnd x‖ := by
  rw [WithLp.prod_norm_eq_sup]; rw [← WithLp.norm_toLp_fst ∞ α β x.fst]; rw [← WithLp.norm_toLp_snd ∞ α β x.snd]
  rfl

/--
lemma `prod_norm_eq_add_idemFst` / 引理 `prod_norm_eq_add_idemFst`

English:
lemma prod_norm_eq_add_idemFst
  given: [Fact (1 <= p)] (hp : 0 < p.toReal) (x : WithLp p (α × β))
  proof: by
  rw [WithLp.prod_norm_eq_add hp]; rw [← WithLp.norm_toLp_fst p α β x.fst]; rw [← WithLp.norm_toLp_snd p α β x.snd]
  rfl

中文:
引理 prod_norm_eq_add_idemFst
  条件: [Fact (1 <= p)] (hp : 0 < p.to实数) (x : WithLp p (α × β))
  证明: by
  rw [WithLp.prod_norm_eq_add hp]; rw [← WithLp.norm_toLp_fst p α β x.fst]; rw [← WithLp.norm_toLp_snd p α β x.snd]
  rfl

Depends on / 依赖: WithLp, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd, WithLp.prod_norm_eq_add, norm_toLp_fst, norm_toLp_snd, prod_norm_eq_add, x.fst, x.snd
-/
lemma prod_norm_eq_add_idemFst [Fact (1 <= p)] (hp : 0 < p.toReal) (x : WithLp p (α × β)) :
    ‖x‖ = (‖idemFst x‖ ^ p.toReal + ‖idemSnd x‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [WithLp.prod_norm_eq_add hp]; rw [← WithLp.norm_toLp_fst p α β x.fst]; rw [← WithLp.norm_toLp_snd p α β x.snd]
  rfl

/--
lemma `prod_norm_eq_idemFst_of_L1` / 引理 `prod_norm_eq_idemFst_of_L1`

English:
lemma prod_norm_eq_idemFst_of_L1
  given: (x : WithLp 1 (α × β))
  statement: ‖x‖ = ‖idemFst x‖ + ‖idemSnd x‖
  proof: by
  rw [prod_norm_eq_add_idemFst (lt_of_lt_of_eq zero_lt_one toReal_one.symm)]
  simp only [toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]

中文:
引理 prod_norm_eq_idemFst_of_L1
  条件: (x : WithLp 1 (α × β))
  结论: ‖x‖ = ‖idemFst x‖ + ‖idemSnd x‖
  证明: by
  rw [prod_norm_eq_add_idemFst (lt_of_lt_of_eq zero_lt_one toReal_one.symm)]
  simp only [toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]

Depends on / 依赖: Real.rpow_one, div_self, lt_of_lt_of_eq, ne_eq, not_false_eq_true, one_ne_zero, prod_norm_eq_add_idemFst, rpow_one, toReal_one, toReal_one.symm, zero_lt_one
-/
lemma prod_norm_eq_idemFst_of_L1 (x : WithLp 1 (α × β)) : ‖x‖ = ‖idemFst x‖ + ‖idemSnd x‖ := by
  rw [prod_norm_eq_add_idemFst (lt_of_lt_of_eq zero_lt_one toReal_one.symm)]
  simp only [toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]

end SeminormedAddCommGroup

section NormedSpace

/--
Instance `instProdNormedSpace` / 实例 `instProdNormedSpace`

English:
instance instProdNormedSpace
  signature: [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β]
  body: norm_smul_le

中文:
实例 instProdNormedSpace
  签名: [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β]
  定义体: norm_smul_le

Depends on / 依赖: norm_smul_le
-/
instance instProdNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β] :
    NormedSpace 𝕜 (WithLp p (α × β)) where
  norm_smul_le := norm_smul_le

end NormedSpace

section toProd

/-!
### `L^p` distance on a product space

In this section we define a pseudometric space structure on `α × β`, as well as a seminormed
group structure. These are meant to be used to put the desired instances on type synonyms
of `α × β`. See for instance `TrivSqZeroExt.instL1SeminormedAddCommGroup`.
-/

variable (α β : Type*)

-- This prevents Lean from elaborating terms of `α × β` with an unintended norm.
attribute [-instance] Prod.toNorm

/--
Definition of `pseudoMetricSpaceToProd` / `pseudoMetricSpaceToProd` 的定义

English:
abbreviation pseudoMetricSpaceToProd
  signature: [PseudoMetricSpace α] [PseudoMetricSpace β]
  body: (isUniformInducing_toLp p α β).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (prod_antilipschitzWith_toLp p α β).tendsto_cobounded.le_comap
        (prod_lipschitzWith_toLp p α β).comap_cobounded_le) sᶜ

中文:
缩写 pseudoMetricSpaceToProd
  签名: [PseudoMetricSpace α] [PseudoMetricSpace β]
  定义体: (isUniformInducing_toLp p α β).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (prod_antilipschitzWith_toLp p α β).tendsto_cobounded.le_comap
        (prod_lipschitzWith_toLp p α β).comap_cobounded_le) sᶜ

Depends on / 依赖: Filter, Filter.ext_iff, comapPseudoMetricSpace, comapPseudoMetricSpace.replaceBornology, comap_cobounded_le, ext_iff, isUniformInducing_toLp, le_antisymm, le_comap, prod_antilipschitzWith_toLp, prod_lipschitzWith_toLp, replaceBornology, tendsto_cobounded, tendsto_cobounded.le_comap
-/
abbrev pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (α × β) :=
  (isUniformInducing_toLp p α β).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (prod_antilipschitzWith_toLp p α β).tendsto_cobounded.le_comap
        (prod_lipschitzWith_toLp p α β).comap_cobounded_le) sᶜ

/--
lemma `dist_pseudoMetricSpaceToProd` / 引理 `dist_pseudoMetricSpaceToProd`

English:
lemma dist_pseudoMetricSpaceToProd
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : α × β)
  proof: rfl

中文:
引理 dist_pseudoMetricSpaceToProd
  条件: [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : α × β)
  证明: rfl
-/
lemma dist_pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : α × β) :
    @dist _ (pseudoMetricSpaceToProd p α β).toDist x y = dist (toLp p x) (toLp p y) := rfl

/--
Definition of `seminormedAddCommGroupToProd` / `seminormedAddCommGroupToProd` 的定义

English:
abbreviation seminormedAddCommGroupToProd
  signature: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  body: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]

中文:
缩写 seminormedAddCommGroupToProd
  签名: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  定义体: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
-/
abbrev seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (α × β) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]

/--
lemma `norm_seminormedAddCommGroupToProd` / 引理 `norm_seminormedAddCommGroupToProd`

English:
lemma norm_seminormedAddCommGroupToProd
  statement: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  proof: rfl

中文:
引理 norm_seminormedAddCommGroupToProd
  结论: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  证明: rfl
-/
lemma norm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (x : α × β) :
    @Norm.norm _ (seminormedAddCommGroupToProd p α β).toNorm x = ‖toLp p x‖ := rfl

/--
lemma `nnnorm_seminormedAddCommGroupToProd` / 引理 `nnnorm_seminormedAddCommGroupToProd`

English:
lemma nnnorm_seminormedAddCommGroupToProd
  statement: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  proof: rfl

中文:
引理 nnnorm_seminormedAddCommGroupToProd
  结论: [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
  证明: rfl
-/
lemma nnnorm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (x : α × β) :
    @NNNorm.nnnorm _ (seminormedAddCommGroupToProd p α β).toSeminormedAddGroup.toNNNorm x =
    ‖toLp p x‖₊ := rfl

/--
lemma `isBoundedSMulSeminormedAddCommGroupToProd` / 引理 `isBoundedSMulSeminormedAddCommGroupToProd`

English:
lemma isBoundedSMulSeminormedAddCommGroupToProd
  proof: pseudoMetricSpaceToProd p α β
    IsBoundedSMul R (α × β) := by
  let := pseudoMetricSpaceToProd p α β
  refine ⟨fun x y z => ?_, fun x y z => ?_⟩
  · simpa [dist_pseudoMetricSpaceToProd] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToProd] using dist_pair_smul x y (

中文:
引理 isBoundedSMulSeminormedAddCommGroupToProd
  证明: pseudoMetricSpaceToProd p α β
    IsBoundedSMul R (α × β) := by
  let := pseudoMetricSpaceToProd p α β
  refine ⟨fun x y z => ?_, fun x y z => ?_⟩
  · simpa [dist_pseudoMetricSpaceToProd] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToProd] using dist_pair_smul x y (

Depends on / 依赖: pseudoMetricSpaceToProd
-/
lemma isBoundedSMulSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [SeminormedRing R]
    [Module R α] [Module R β] [IsBoundedSMul R α] [IsBoundedSMul R β] :
    letI := pseudoMetricSpaceToProd p α β
    IsBoundedSMul R (α × β) := by
  let := pseudoMetricSpaceToProd p α β
  refine ⟨fun x y z => ?_, fun x y z => ?_⟩
  · simpa [dist_pseudoMetricSpaceToProd] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToProd] using dist_pair_smul x y (toLp p z)

/--
lemma `normSMulClassSeminormedAddCommGroupToProd` / 引理 `normSMulClassSeminormedAddCommGroupToProd`

English:
lemma normSMulClassSeminormedAddCommGroupToProd
  proof: seminormedAddCommGroupToProd p α β
    NormSMulClass R (α × β) := by
  let := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y => norm_smul x (toLp p y)⟩

中文:
引理 normSMulClassSeminormedAddCommGroupToProd
  证明: seminormedAddCommGroupToProd p α β
    NormSMulClass R (α × β) := by
  let := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y => norm_smul x (toLp p y)⟩

Depends on / 依赖: seminormedAddCommGroupToProd
-/
lemma normSMulClassSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [SeminormedRing R]
    [Module R α] [Module R β] [NormSMulClass R α] [NormSMulClass R β] :
    letI := seminormedAddCommGroupToProd p α β
    NormSMulClass R (α × β) := by
  let := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y => norm_smul x (toLp p y)⟩

/--
Definition of `normedSpaceSeminormedAddCommGroupToProd` / `normedSpaceSeminormedAddCommGroupToProd` 的定义

English:
abbreviation normedSpaceSeminormedAddCommGroupToProd
  body: seminormedAddCommGroupToProd p α β
    NormedSpace R (α × β) := by
  letI := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y => norm_smul_le x (toLp p y)⟩

中文:
缩写 normedSpaceSeminormedAddCommGroupToProd
  定义体: seminormedAddCommGroupToProd p α β
    NormedSpace R (α × β) := by
  letI := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y => norm_smul_le x (toLp p y)⟩

Depends on / 依赖: seminormedAddCommGroupToProd
-/
abbrev normedSpaceSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [NormedField R]
    [NormedSpace R α] [NormedSpace R β] :
    letI := seminormedAddCommGroupToProd p α β
    NormedSpace R (α × β) := by
  letI := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y => norm_smul_le x (toLp p y)⟩

/--
Definition of `normedAddCommGroupToProd` / `normedAddCommGroupToProd` 的定义

English:
abbreviation normedAddCommGroupToProd
  signature: [NormedAddCommGroup α] [NormedAddCommGroup β]
  body: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToProd] at h
    exact toLp_injective p (eq_

中文:
缩写 normedAddCommGroupToProd
  签名: [NormedAddCommGroup α] [NormedAddCommGroup β]
  定义体: ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToProd] at h
    exact toLp_injective p (eq_
-/
abbrev normedAddCommGroupToProd [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (α × β) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd]; rw [SeminormedAddCommGroup.dist_eq]; rw [toLp_add]; rw [toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToProd] at h
    exact toLp_injective p (eq_of_dist_eq_zero h)

end toProd

end WithLp

variable (γ : Type*) {α' β' : Type*}

section Isometry

variable [hp : Fact (1 <= p)] [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
  [PseudoEMetricSpace α'] [PseudoEMetricSpace β']

variable {α β} in
/--
theorem `Isometry.withLpProdMap` / 定理 `Isometry.withLpProdMap`

English:
theorem Isometry.withLpProdMap
  given: {f : α -> α'} (hf : Isometry f) {g : β -> β'} (hg : Isometry g)
  proof: by
  intro _ _
  rcases p.trichotomy with rfl | rfl | hp
  · absurd hp.elim; simp
  · simp [WithLp.prod_edist_eq_sup, hf.edist_eq, hg.edist_eq]
  · simp [WithLp.prod_edist_eq_add hp, hf.edist_eq, hg.edist_eq]

中文:
定理 Isometry.withLpProdMap
  条件: {f : α -> α'} (hf : Isometry f) {g : β -> β'} (hg : Isometry g)
  证明: by
  intro _ _
  rcases p.trichotomy with rfl | rfl | hp
  · absurd hp.elim; simp
  · simp [WithLp.prod_edist_eq_sup, hf.edist_eq, hg.edist_eq]
  · simp [WithLp.prod_edist_eq_add hp, hf.edist_eq, hg.edist_eq]

Depends on / 依赖: WithLp, WithLp.prod_edist_eq_add, WithLp.prod_edist_eq_sup, absurd, edist_eq, hf.edist_eq, hg.edist_eq, hp.elim, p.trichotomy, prod_edist_eq_add, prod_edist_eq_sup, trichotomy
-/
theorem Isometry.withLpProdMap {f : α -> α'} (hf : Isometry f) {g : β -> β'} (hg : Isometry g) :
    Isometry (WithLp.map p (Prod.map f g)) := by
  intro _ _
  rcases p.trichotomy with rfl | rfl | hp
  · absurd hp.elim; simp
  · simp [WithLp.prod_edist_eq_sup, hf.edist_eq, hg.edist_eq]
  · simp [WithLp.prod_edist_eq_add hp, hf.edist_eq, hg.edist_eq]

namespace IsometryEquiv

variable {α β} in
/-- The `L^p` product of two isometric equivalences. -/
@[simps! apply symm_apply]
/--
Definition of `withLpProdCongr` / `withLpProdCongr` 的定义

English:
definition withLpProdCongr
  signature: (f : α ≃ᵢ α') (g : β ≃ᵢ β')
  body: WithLp.congr p (f.toEquiv.prodCongr g.toEquiv)
  isometry_toFun := f.isometry.withLpProdMap p g.isometry

中文:
定义 withLpProdCongr
  签名: (f : α ≃ᵢ α') (g : β ≃ᵢ β')
  定义体: WithLp.congr p (f.toEquiv.prodCongr g.toEquiv)
  isometry_toFun := f.isometry.withLpProdMap p g.isometry

Depends on / 依赖: WithLp, WithLp.congr, f.toEquiv.prodCongr, g.toEquiv, prodCongr, toEquiv
-/
def withLpProdCongr (f : α ≃ᵢ α') (g : β ≃ᵢ β') : WithLp p (α × β) ≃ᵢ WithLp p (α' × β') where
  __ := WithLp.congr p (f.toEquiv.prodCongr g.toEquiv)
  isometry_toFun := f.isometry.withLpProdMap p g.isometry

/--
Definition of `withLpProdComm` / `withLpProdComm` 的定义

English:
definition withLpProdComm
  signature: : WithLp p (α × β) ≃ᵢ WithLp p (β × α) where
  body: WithLp.congr p (Equiv.prodComm α β)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_comm]
    · simp [WithLp.prod_edist_eq_add hp, add_comm]

@[simp]

中文:
定义 withLpProdComm
  签名: : WithLp p (α × β) ≃ᵢ WithLp p (β × α) where
  定义体: WithLp.congr p (Equiv.prodComm α β)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_comm]
    · simp [WithLp.prod_edist_eq_add hp, add_comm]

@[simp]

Depends on / 依赖: Equiv.prodComm, WithLp, WithLp.congr, prodComm
-/
def withLpProdComm : WithLp p (α × β) ≃ᵢ WithLp p (β × α) where
  __ := WithLp.congr p (Equiv.prodComm α β)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_comm]
    · simp [WithLp.prod_edist_eq_add hp, add_comm]

@[simp]
/--
theorem `withLpProdComm_apply` / 定理 `withLpProdComm_apply`

English:
theorem withLpProdComm_apply
  given: (x : WithLp p (α × β))
  proof: rfl

@[simp]

中文:
定理 withLpProdComm_apply
  条件: (x : WithLp p (α × β))
  证明: rfl

@[simp]
-/
theorem withLpProdComm_apply (x : WithLp p (α × β)) :
    withLpProdComm p α β x = .toLp p (x.snd, x.fst) :=
  rfl

@[simp]
/--
theorem `withLpProdComm_symm` / 定理 `withLpProdComm_symm`

English:
theorem withLpProdComm_symm
  statement: (withLpProdComm p α β).symm = withLpProdComm p β α
  proof: rfl

中文:
定理 withLpProdComm_symm
  结论: (withLpProdComm p α β).symm = withLpProdComm p β α
  证明: rfl
-/
theorem withLpProdComm_symm : (withLpProdComm p α β).symm = withLpProdComm p β α :=
  rfl

/-- Associativity of the `L^p` product as an isometric equivalence. -/
@[simps apply symm_apply]
/--
Definition of `withLpProdAssoc` / `withLpProdAssoc` 的定义

English:
definition withLpProdAssoc
  signature: : WithLp p (WithLp p (α × β) × γ) ≃ᵢ WithLp p (α × WithLp p (β × γ)) where
  body: .toLp p (x.fst.fst, .toLp p (x.fst.snd, x.snd))
  invFun x := .toLp p (.toLp p (x.fst, x.snd.fst), x.snd.snd)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_assoc]
    · simp [WithLp.prod_edist_eq_add hp, EN

中文:
定义 withLpProdAssoc
  签名: : WithLp p (WithLp p (α × β) × γ) ≃ᵢ WithLp p (α × WithLp p (β × γ)) where
  定义体: .toLp p (x.fst.fst, .toLp p (x.fst.snd, x.snd))
  invFun x := .toLp p (.toLp p (x.fst, x.snd.fst), x.snd.snd)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_assoc]
    · simp [WithLp.prod_edist_eq_add hp, EN

Depends on / 依赖: x.fst.fst, x.fst.snd, x.snd
-/
def withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ᵢ WithLp p (α × WithLp p (β × γ)) where
  toFun x := .toLp p (x.fst.fst, .toLp p (x.fst.snd, x.snd))
  invFun x := .toLp p (.toLp p (x.fst, x.snd.fst), x.snd.snd)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_assoc]
    · simp [WithLp.prod_edist_eq_add hp, ENNReal.rpow_inv_rpow hp.ne', add_assoc]

/-- Right identity of the `L^p` product as an isometric equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `withLpProdUnique` / `withLpProdUnique` 的定义

English:
definition withLpProdUnique
  signature: [Unique β]
  body: (WithLp.equiv _ _).trans (Equiv.prodUnique _ _)
  isometry_toFun x y : edist x.fst y.fst = edist x y := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp_rw [WithLp.prod_edist_eq_sup, Unique.eq_default, edist_self, max_zero]
    · simp_rw [WithLp.prod_edist_eq_add 

中文:
定义 withLpProdUnique
  签名: [Unique β]
  定义体: (WithLp.equiv _ _).trans (Equiv.prodUnique _ _)
  isometry_toFun x y : edist x.fst y.fst = edist x y := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp_rw [WithLp.prod_edist_eq_sup, Unique.eq_default, edist_self, max_zero]
    · simp_rw [WithLp.prod_edist_eq_add 

Depends on / 依赖: Equiv.prodUnique, WithLp, WithLp.equiv, prodUnique
-/
def withLpProdUnique [Unique β] : WithLp p (α × β) ≃ᵢ α where
  __ := (WithLp.equiv _ _).trans (Equiv.prodUnique _ _)
  isometry_toFun x y : edist x.fst y.fst = edist x y := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp_rw [WithLp.prod_edist_eq_sup, Unique.eq_default, edist_self, max_zero]
    · simp_rw [WithLp.prod_edist_eq_add hp, Unique.eq_default, edist_self,
        ENNReal.zero_rpow_of_pos hp, add_zero, one_div, ENNReal.rpow_rpow_inv hp.ne']

/--
theorem `coe_withLpProdUnique` / 定理 `coe_withLpProdUnique`

English:
theorem coe_withLpProdUnique
  given: [Unique β]
  statement: ⇑(withLpProdUnique p α β) = WithLp.fst
  proof: rfl

中文:
定理 coe_withLpProdUnique
  条件: [Unique β]
  结论: ⇑(withLpProdUnique p α β) = WithLp.fst
  证明: rfl
-/
theorem coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p α β) = WithLp.fst :=
  rfl

/-- Left identity of the `L^p` product as an isometric equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `withLpUniqueProd` / `withLpUniqueProd` 的定义

English:
definition withLpUniqueProd
  signature: [Unique α]
  body: (withLpProdComm p α β).trans (withLpProdUnique p β α)

中文:
定义 withLpUniqueProd
  签名: [Unique α]
  定义体: (withLpProdComm p α β).trans (withLpProdUnique p β α)

Depends on / 依赖: withLpProdComm, withLpProdUnique
-/
def withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ᵢ β :=
  (withLpProdComm p α β).trans (withLpProdUnique p β α)

/--
theorem `coe_withLpUniqueProd` / 定理 `coe_withLpUniqueProd`

English:
theorem coe_withLpUniqueProd
  given: [Unique α]
  statement: ⇑(withLpUniqueProd p α β) = WithLp.snd
  proof: rfl

中文:
定理 coe_withLpUniqueProd
  条件: [Unique α]
  结论: ⇑(withLpUniqueProd p α β) = WithLp.snd
  证明: rfl
-/
theorem coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p α β) = WithLp.snd :=
  rfl

end IsometryEquiv

end Isometry

section Linear

variable [hp : Fact (1 <= p)] [Semiring 𝕜]
  [SeminormedAddCommGroup α] [Module 𝕜 α]
  [SeminormedAddCommGroup β] [Module 𝕜 β]
  [SeminormedAddCommGroup γ] [Module 𝕜 γ]
  [SeminormedAddCommGroup α'] [Module 𝕜 α']
  [SeminormedAddCommGroup β'] [Module 𝕜 β']

variable {𝕜 α β} in
/-- The `L^p` product of two linear isometries. -/
@[simps! apply]
/--
Definition of `LinearIsometry.withLpProdMap` / `LinearIsometry.withLpProdMap` 的定义

English:
definition LinearIsometry.withLpProdMap
  signature: (f : α ->ₗᵢ[𝕜] α') (g : β ->ₗᵢ[𝕜] β')
  body: (f.toLinearMap.prodMap g.toLinearMap).withLpMap p
  norm_map' := (f.isometry.withLpProdMap p g.isometry).norm_map_of_map_zero
    ((f.toLinearMap.prodMap g.toLinearMap).withLpMap p).map_zero

中文:
定义 LinearIsometry.withLpProdMap
  签名: (f : α ->ₗᵢ[𝕜] α') (g : β ->ₗᵢ[𝕜] β')
  定义体: (f.toLinearMap.prodMap g.toLinearMap).withLpMap p
  norm_map' := (f.isometry.withLpProdMap p g.isometry).norm_map_of_map_zero
    ((f.toLinearMap.prodMap g.toLinearMap).withLpMap p).map_zero

Depends on / 依赖: f.toLinearMap.prodMap, g.toLinearMap, prodMap, toLinearMap, withLpMap
-/
def LinearIsometry.withLpProdMap (f : α ->ₗᵢ[𝕜] α') (g : β ->ₗᵢ[𝕜] β') :
    WithLp p (α × β) ->ₗᵢ[𝕜] WithLp p (α' × β') where
  __ := (f.toLinearMap.prodMap g.toLinearMap).withLpMap p
  norm_map' := (f.isometry.withLpProdMap p g.isometry).norm_map_of_map_zero
    ((f.toLinearMap.prodMap g.toLinearMap).withLpMap p).map_zero

namespace LinearIsometryEquiv

variable {𝕜 α β} in
/-- The `L^p` product of two linear isometric equivalences. -/
@[simps! apply symm_apply]
/--
Definition of `withLpProdCongr` / `withLpProdCongr` 的定义

English:
definition withLpProdCongr
  signature: (f : α ≃ₗᵢ[𝕜] α') (g : β ≃ₗᵢ[𝕜] β')
  body: (f.toLinearEquiv.prodCongr g.toLinearEquiv).withLpCongr p
  norm_map' := (f.toLinearIsometry.withLpProdMap p g.toLinearIsometry).norm_map

中文:
定义 withLpProdCongr
  签名: (f : α ≃ₗᵢ[𝕜] α') (g : β ≃ₗᵢ[𝕜] β')
  定义体: (f.toLinearEquiv.prodCongr g.toLinearEquiv).withLpCongr p
  norm_map' := (f.toLinearIsometry.withLpProdMap p g.toLinearIsometry).norm_map

Depends on / 依赖: f.toLinearEquiv.prodCongr, g.toLinearEquiv, prodCongr, toLinearEquiv, withLpCongr
-/
def withLpProdCongr (f : α ≃ₗᵢ[𝕜] α') (g : β ≃ₗᵢ[𝕜] β') :
    WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (α' × β') where
  __ := (f.toLinearEquiv.prodCongr g.toLinearEquiv).withLpCongr p
  norm_map' := (f.toLinearIsometry.withLpProdMap p g.toLinearIsometry).norm_map

/--
Definition of `withLpProdComm` / `withLpProdComm` 的定义

English:
definition withLpProdComm
  signature: : WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (β × α) where
  body: (LinearEquiv.prodComm 𝕜 α β).withLpCongr p
  norm_map' := (IsometryEquiv.withLpProdComm p α β).isometry.norm_map_of_map_zero rfl

@[simp]

中文:
定义 withLpProdComm
  签名: : WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (β × α) where
  定义体: (LinearEquiv.prodComm 𝕜 α β).withLpCongr p
  norm_map' := (IsometryEquiv.withLpProdComm p α β).isometry.norm_map_of_map_zero rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.prodComm, prodComm, withLpCongr
-/
def withLpProdComm : WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (β × α) where
  __ := (LinearEquiv.prodComm 𝕜 α β).withLpCongr p
  norm_map' := (IsometryEquiv.withLpProdComm p α β).isometry.norm_map_of_map_zero rfl

@[simp]
/--
theorem `withLpProdComm_apply` / 定理 `withLpProdComm_apply`

English:
theorem withLpProdComm_apply
  given: (x : WithLp p (α × β))
  proof: rfl

@[simp]

中文:
定理 withLpProdComm_apply
  条件: (x : WithLp p (α × β))
  证明: rfl

@[simp]
-/
theorem withLpProdComm_apply (x : WithLp p (α × β)) :
    withLpProdComm p 𝕜 α β x = WithLp.toLp p (x.snd, x.fst) :=
  rfl

@[simp]
/--
theorem `withLpProdComm_symm` / 定理 `withLpProdComm_symm`

English:
theorem withLpProdComm_symm
  statement: (withLpProdComm p 𝕜 α β).symm = withLpProdComm p 𝕜 β α
  proof: rfl

中文:
定理 withLpProdComm_symm
  结论: (withLpProdComm p 𝕜 α β).symm = withLpProdComm p 𝕜 β α
  证明: rfl
-/
theorem withLpProdComm_symm : (withLpProdComm p 𝕜 α β).symm = withLpProdComm p 𝕜 β α :=
  rfl

/-- Associativity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `withLpProdAssoc` / `withLpProdAssoc` 的定义

English:
definition withLpProdAssoc
  signature: : WithLp p (WithLp p (α × β) × γ) ≃ₗᵢ[𝕜] WithLp p (α × WithLp p (β × γ)) where
  body: (IsometryEquiv.withLpProdAssoc p α β γ).toEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := (IsometryEquiv.withLpProdAssoc p α β γ).isometry.norm_map_of_map_zero rfl

中文:
定义 withLpProdAssoc
  签名: : WithLp p (WithLp p (α × β) × γ) ≃ₗᵢ[𝕜] WithLp p (α × WithLp p (β × γ)) where
  定义体: (IsometryEquiv.withLpProdAssoc p α β γ).toEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := (IsometryEquiv.withLpProdAssoc p α β γ).isometry.norm_map_of_map_zero rfl

Depends on / 依赖: IsometryEquiv, IsometryEquiv.withLpProdAssoc, toEquiv, withLpProdAssoc
-/
def withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ₗᵢ[𝕜] WithLp p (α × WithLp p (β × γ)) where
  __ := (IsometryEquiv.withLpProdAssoc p α β γ).toEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := (IsometryEquiv.withLpProdAssoc p α β γ).isometry.norm_map_of_map_zero rfl

/-- Right identity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `withLpProdUnique` / `withLpProdUnique` 的定义

English:
definition withLpProdUnique
  signature: [Unique β]
  body: (WithLp.linearEquiv _ _ _).trans LinearEquiv.prodUnique
  norm_map' := (IsometryEquiv.withLpProdUnique _ _ _).isometry.norm_map_of_map_zero rfl

中文:
定义 withLpProdUnique
  签名: [Unique β]
  定义体: (WithLp.linearEquiv _ _ _).trans LinearEquiv.prodUnique
  norm_map' := (IsometryEquiv.withLpProdUnique _ _ _).isometry.norm_map_of_map_zero rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.prodUnique, WithLp, WithLp.linearEquiv, linearEquiv, prodUnique
-/
def withLpProdUnique [Unique β] : WithLp p (α × β) ≃ₗᵢ[𝕜] α where
  __ := (WithLp.linearEquiv _ _ _).trans LinearEquiv.prodUnique
  norm_map' := (IsometryEquiv.withLpProdUnique _ _ _).isometry.norm_map_of_map_zero rfl

/--
theorem `coe_withLpProdUnique` / 定理 `coe_withLpProdUnique`

English:
theorem coe_withLpProdUnique
  given: [Unique β]
  statement: ⇑(withLpProdUnique p 𝕜 α β) = WithLp.fst
  proof: rfl

中文:
定理 coe_withLpProdUnique
  条件: [Unique β]
  结论: ⇑(withLpProdUnique p 𝕜 α β) = WithLp.fst
  证明: rfl
-/
theorem coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p 𝕜 α β) = WithLp.fst :=
  rfl

/-- Left identity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `withLpUniqueProd` / `withLpUniqueProd` 的定义

English:
definition withLpUniqueProd
  signature: [Unique α]
  body: (withLpProdComm p 𝕜 α β).trans (withLpProdUnique p 𝕜 β α)

中文:
定义 withLpUniqueProd
  签名: [Unique α]
  定义体: (withLpProdComm p 𝕜 α β).trans (withLpProdUnique p 𝕜 β α)

Depends on / 依赖: withLpProdComm, withLpProdUnique
-/
def withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ₗᵢ[𝕜] β :=
  (withLpProdComm p 𝕜 α β).trans (withLpProdUnique p 𝕜 β α)

/--
theorem `coe_withLpUniqueProd` / 定理 `coe_withLpUniqueProd`

English:
theorem coe_withLpUniqueProd
  given: [Unique α]
  statement: ⇑(withLpUniqueProd p 𝕜 α β) = WithLp.snd
  proof: rfl

中文:
定理 coe_withLpUniqueProd
  条件: [Unique α]
  结论: ⇑(withLpUniqueProd p 𝕜 α β) = WithLp.snd
  证明: rfl
-/
theorem coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p 𝕜 α β) = WithLp.snd :=
  rfl

end LinearIsometryEquiv

end Linear
