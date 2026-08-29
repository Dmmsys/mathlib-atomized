/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Separation.SeparatedNhds

/-!
# Disjoint unions and products of topological spaces

This file constructs sums (disjoint unions) and products of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

We also provide basic homeomorphisms, to show that sums and products are commutative, associative
and distributive (up to homeomorphism).

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union

-/

@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Filter Function

universe u v u' v'

variable {X : Type u} {Y : Type v} {W Z ε ζ : Type*}

/--
Instance `instTopologicalSpaceSum` / 实例 `instTopologicalSpaceSum`

English:
instance instTopologicalSpaceSum
  signature: [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y]
  body: coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

中文:
实例 instTopologicalSpaceSum
  签名: [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y]
  定义体: coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

Depends on / 依赖: Sum.inl, Sum.inr, coinduced
-/
instance instTopologicalSpaceSum [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X oplus Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

/--
Instance `instTopologicalSpaceProd` / 实例 `instTopologicalSpaceProd`

English:
instance instTopologicalSpaceProd
  signature: [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y]
  body: induced Prod.fst t₁ ⊓ induced Prod.snd t₂

中文:
实例 instTopologicalSpaceProd
  签名: [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y]
  定义体: induced Prod.fst t₁ ⊓ induced Prod.snd t₂

Depends on / 依赖: Prod.fst, Prod.snd, induced
-/
instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  [TopologicalSpace ε] [TopologicalSpace ζ]

@[simp]
/--
theorem `continuous_prodMk` / 定理 `continuous_prodMk`

English:
theorem continuous_prodMk
  given: {f : X -> Y} {g : X -> Z}
  proof: continuous_inf_rng.trans continuous_induced_rng.and continuous_induced_rng

@[continuity]

中文:
定理 continuous_prodMk
  条件: {f : X -> Y} {g : X -> Z}
  证明: continuous_inf_rng.trans continuous_induced_rng.and continuous_induced_rng

@[continuity]

Depends on / 依赖: continuous_induced_rng, continuous_induced_rng.and, continuous_inf_rng, continuous_inf_rng.trans
-/
theorem continuous_prodMk {f : X -> Y} {g : X -> Z} :
    (Continuous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
continuous_inf_rng.trans continuous_induced_rng.and continuous_induced_rng

@[continuity]
/--
theorem `continuous_fst` / 定理 `continuous_fst`

English:
theorem continuous_fst
  statement: Continuous (@Prod.fst X Y)
  proof: (continuous_prodMk.1 continuous_id).1

中文:
定理 continuous_fst
  结论: Continuous (@Prod.fst X Y)
  证明: (continuous_prodMk.1 continuous_id).1
-/
theorem continuous_fst : Continuous (@Prod.fst X Y) :=
  (continuous_prodMk.1 continuous_id).1

/-- Postcomposing `f` with `Prod.fst` is continuous -/
@[fun_prop]
/--
theorem `Continuous.fst` / 定理 `Continuous.fst`

English:
theorem Continuous.fst
  given: {f : X -> Y × Z} (hf : Continuous f)
  statement: Continuous fun x : X => (f x).1
  proof: continuous_fst.comp hf

中文:
定理 Continuous.fst
  条件: {f : X -> Y × Z} (hf : Continuous f)
  结论: Continuous fun x : X => (f x).1
  证明: continuous_fst.comp hf

Depends on / 依赖: continuous_fst, continuous_fst.comp
-/
theorem Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).1 :=
  continuous_fst.comp hf

/--
theorem `Continuous.fst'` / 定理 `Continuous.fst'`

English:
theorem Continuous.fst'
  given: {f : X -> Z} (hf : Continuous f)
  statement: Continuous fun x : X × Y => f x.fst
  proof: hf.comp continuous_fst

中文:
定理 Continuous.fst'
  条件: {f : X -> Z} (hf : Continuous f)
  结论: Continuous fun x : X × Y => f x.fst
  证明: hf.comp continuous_fst

Depends on / 依赖: continuous_fst, hf.comp
-/
theorem Continuous.fst' {f : X -> Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.fst :=
  hf.comp continuous_fst

/--
theorem `continuousAt_fst` / 定理 `continuousAt_fst`

English:
theorem continuousAt_fst
  given: {p : X × Y}
  statement: ContinuousAt Prod.fst p
  proof: continuous_fst.continuousAt

中文:
定理 continuousAt_fst
  条件: {p : X × Y}
  结论: ContinuousAt Prod.fst p
  证明: continuous_fst.continuousAt

Depends on / 依赖: continuousAt, continuous_fst, continuous_fst.continuousAt
-/
theorem continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p :=
  continuous_fst.continuousAt

/-- Postcomposing `f` with `Prod.fst` is continuous at `x` -/
@[fun_prop]
/--
theorem `ContinuousAt.fst` / 定理 `ContinuousAt.fst`

English:
theorem ContinuousAt.fst
  given: {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x)
  proof: continuousAt_fst.comp hf

中文:
定理 ContinuousAt.fst
  条件: {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x)
  证明: continuousAt_fst.comp hf

Depends on / 依赖: continuousAt_fst, continuousAt_fst.comp
-/
theorem ContinuousAt.fst {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).1) x :=
  continuousAt_fst.comp hf

/--
theorem `ContinuousAt.fst'` / 定理 `ContinuousAt.fst'`

English:
theorem ContinuousAt.fst'
  given: {f : X -> Z} {x : X} {y : Y} (hf : ContinuousAt f x)
  proof: ContinuousAt.comp hf continuousAt_fst

中文:
定理 ContinuousAt.fst'
  条件: {f : X -> Z} {x : X} {y : Y} (hf : ContinuousAt f x)
  证明: ContinuousAt.comp hf continuousAt_fst

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, continuousAt_fst
-/
theorem ContinuousAt.fst' {f : X -> Z} {x : X} {y : Y} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X × Y => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuousAt_fst

/--
theorem `ContinuousAt.fst''` / 定理 `ContinuousAt.fst''`

English:
theorem ContinuousAt.fst''
  given: {f : X -> Z} {x : X × Y} (hf : ContinuousAt f x.fst)
  proof: hf.comp continuousAt_fst

中文:
定理 ContinuousAt.fst''
  条件: {f : X -> Z} {x : X × Y} (hf : ContinuousAt f x.fst)
  证明: hf.comp continuousAt_fst

Depends on / 依赖: continuousAt_fst, hf.comp
-/
theorem ContinuousAt.fst'' {f : X -> Z} {x : X × Y} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : X × Y => f x.fst) x :=
  hf.comp continuousAt_fst

/--
theorem `Filter.Tendsto.fst_nhds` / 定理 `Filter.Tendsto.fst_nhds`

English:
theorem Filter.Tendsto.fst_nhds
  statement: {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z}
  proof: continuousAt_fst.tendsto.comp h

@[continuity]

中文:
定理 Filter.Tendsto.fst_nhds
  结论: {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z}
  证明: continuousAt_fst.tendsto.comp h

@[continuity]

Depends on / 依赖: continuousAt_fst, continuousAt_fst.tendsto.comp, tendsto
-/
theorem Filter.Tendsto.fst_nhds {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a => (f a).1) l (𝓝 <| p.1) :=
  continuousAt_fst.tendsto.comp h

@[continuity]
/--
theorem `continuous_snd` / 定理 `continuous_snd`

English:
theorem continuous_snd
  statement: Continuous (@Prod.snd X Y)
  proof: (continuous_prodMk.1 continuous_id).2

中文:
定理 continuous_snd
  结论: Continuous (@Prod.snd X Y)
  证明: (continuous_prodMk.1 continuous_id).2
-/
theorem continuous_snd : Continuous (@Prod.snd X Y) :=
  (continuous_prodMk.1 continuous_id).2

/-- Postcomposing `f` with `Prod.snd` is continuous -/
@[fun_prop]
/--
theorem `Continuous.snd` / 定理 `Continuous.snd`

English:
theorem Continuous.snd
  given: {f : X -> Y × Z} (hf : Continuous f)
  statement: Continuous fun x : X => (f x).2
  proof: continuous_snd.comp hf

中文:
定理 Continuous.snd
  条件: {f : X -> Y × Z} (hf : Continuous f)
  结论: Continuous fun x : X => (f x).2
  证明: continuous_snd.comp hf

Depends on / 依赖: continuous_snd, continuous_snd.comp
-/
theorem Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).2 :=
  continuous_snd.comp hf

/--
theorem `Continuous.snd'` / 定理 `Continuous.snd'`

English:
theorem Continuous.snd'
  given: {f : Y -> Z} (hf : Continuous f)
  statement: Continuous fun x : X × Y => f x.snd
  proof: hf.comp continuous_snd

中文:
定理 Continuous.snd'
  条件: {f : Y -> Z} (hf : Continuous f)
  结论: Continuous fun x : X × Y => f x.snd
  证明: hf.comp continuous_snd

Depends on / 依赖: continuous_snd, hf.comp
-/
theorem Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.snd :=
  hf.comp continuous_snd

/--
theorem `continuousAt_snd` / 定理 `continuousAt_snd`

English:
theorem continuousAt_snd
  given: {p : X × Y}
  statement: ContinuousAt Prod.snd p
  proof: continuous_snd.continuousAt

中文:
定理 continuousAt_snd
  条件: {p : X × Y}
  结论: ContinuousAt Prod.snd p
  证明: continuous_snd.continuousAt

Depends on / 依赖: continuousAt, continuous_snd, continuous_snd.continuousAt
-/
theorem continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p :=
  continuous_snd.continuousAt

/-- Postcomposing `f` with `Prod.snd` is continuous at `x` -/
@[fun_prop]
/--
theorem `ContinuousAt.snd` / 定理 `ContinuousAt.snd`

English:
theorem ContinuousAt.snd
  given: {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x)
  proof: continuousAt_snd.comp hf

中文:
定理 ContinuousAt.snd
  条件: {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x)
  证明: continuousAt_snd.comp hf

Depends on / 依赖: continuousAt_snd, continuousAt_snd.comp
-/
theorem ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).2) x :=
  continuousAt_snd.comp hf

/--
theorem `ContinuousAt.snd'` / 定理 `ContinuousAt.snd'`

English:
theorem ContinuousAt.snd'
  given: {f : Y -> Z} {x : X} {y : Y} (hf : ContinuousAt f y)
  proof: ContinuousAt.comp hf continuousAt_snd

中文:
定理 ContinuousAt.snd'
  条件: {f : Y -> Z} {x : X} {y : Y} (hf : ContinuousAt f y)
  证明: ContinuousAt.comp hf continuousAt_snd

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, continuousAt_snd
-/
theorem ContinuousAt.snd' {f : Y -> Z} {x : X} {y : Y} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : X × Y => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuousAt_snd

/--
theorem `ContinuousAt.snd''` / 定理 `ContinuousAt.snd''`

English:
theorem ContinuousAt.snd''
  given: {f : Y -> Z} {x : X × Y} (hf : ContinuousAt f x.snd)
  proof: hf.comp continuousAt_snd

中文:
定理 ContinuousAt.snd''
  条件: {f : Y -> Z} {x : X × Y} (hf : ContinuousAt f x.snd)
  证明: hf.comp continuousAt_snd

Depends on / 依赖: continuousAt_snd, hf.comp
-/
theorem ContinuousAt.snd'' {f : Y -> Z} {x : X × Y} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : X × Y => f x.snd) x :=
  hf.comp continuousAt_snd

/--
theorem `Filter.Tendsto.snd_nhds` / 定理 `Filter.Tendsto.snd_nhds`

English:
theorem Filter.Tendsto.snd_nhds
  statement: {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z}
  proof: continuousAt_snd.tendsto.comp h

@[continuity, fun_prop]

中文:
定理 Filter.Tendsto.snd_nhds
  结论: {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z}
  证明: continuousAt_snd.tendsto.comp h

@[continuity, fun_prop]

Depends on / 依赖: continuousAt_snd, continuousAt_snd.tendsto.comp, tendsto
-/
theorem Filter.Tendsto.snd_nhds {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a => (f a).2) l (𝓝 <| p.2) :=
  continuousAt_snd.tendsto.comp h

@[continuity, fun_prop]
/--
theorem `Continuous.prodMk` / 定理 `Continuous.prodMk`

English:
theorem Continuous.prodMk
  given: {f : Z -> X} {g : Z -> Y} (hf : Continuous f) (hg : Continuous g)
  proof: continuous_prodMk.2 ⟨hf, hg⟩

@[continuity]

中文:
定理 Continuous.prodMk
  条件: {f : Z -> X} {g : Z -> Y} (hf : Continuous f) (hg : Continuous g)
  证明: continuous_prodMk.2 ⟨hf, hg⟩

@[continuity]

Depends on / 依赖: continuous_prodMk
-/
theorem Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_prodMk.2 ⟨hf, hg⟩

@[continuity]
/--
theorem `Continuous.prodMk_right` / 定理 `Continuous.prodMk_right`

English:
theorem Continuous.prodMk_right
  given: (x : X)
  statement: Continuous fun y : Y => (x, y)
  proof: by fun_prop

@[continuity]

中文:
定理 Continuous.prodMk_right
  条件: (x : X)
  结论: Continuous fun y : Y => (x, y)
  证明: by fun_prop

@[continuity]

Depends on / 依赖: fun_prop
-/
theorem Continuous.prodMk_right (x : X) : Continuous fun y : Y => (x, y) := by fun_prop

@[continuity]
/--
theorem `Continuous.prodMk_left` / 定理 `Continuous.prodMk_left`

English:
theorem Continuous.prodMk_left
  given: (y : Y)
  statement: Continuous fun x : X => (x, y)
  proof: by fun_prop

@[continuity, fun_prop]

中文:
定理 Continuous.prodMk_left
  条件: (y : Y)
  结论: Continuous fun x : X => (x, y)
  证明: by fun_prop

@[continuity, fun_prop]

Depends on / 依赖: fun_prop
-/
theorem Continuous.prodMk_left (y : Y) : Continuous fun x : X => (x, y) := by fun_prop

@[continuity, fun_prop]
/--
theorem `continuous_diag` / 定理 `continuous_diag`

English:
theorem continuous_diag
  statement: Continuous (Function.diag : X -> X × X)
  proof: continuous_id.prodMk continuous_id

中文:
定理 continuous_diag
  结论: Continuous (Function.diag : X -> X × X)
  证明: continuous_id.prodMk continuous_id

Depends on / 依赖: continuous_id, continuous_id.prodMk, prodMk
-/
theorem continuous_diag : Continuous (Function.diag : X -> X × X) :=
  continuous_id.prodMk continuous_id

/--
lemma `IsClosed.setOfPred_mapsTo` / 引理 `IsClosed.setOfPred_mapsTo`

English:
lemma IsClosed.setOfPred_mapsTo
  statement: {α : Type*} {f : X -> α -> Z} {s : Set α} {t : Set Z}
  proof: by
  simpa only [MapsTo, ofPred_forall] using! isClosed_biInter fun y hy => ht.preimage (hf y hy)

@[deprecated (since := "2026-07-09")]
alias IsClosed.setOf_mapsTo := IsClosed.setOfPred_mapsTo

中文:
引理 IsClosed.setOfPred_mapsTo
  结论: {α : 类型} {f : X -> α -> Z} {s : Set α} {t : Set Z}
  证明: by
  simpa only [MapsTo, ofPred_forall] using! isClosed_biInter fun y hy => ht.preimage (hf y hy)

@[deprecated (since := "2026-07-09")]
alias IsClosed.setOf_mapsTo := IsClosed.setOfPred_mapsTo

Depends on / 依赖: MapsTo, ht.preimage, isClosed_biInter, ofPred_forall, preimage
-/
lemma IsClosed.setOfPred_mapsTo {α : Type*} {f : X -> α -> Z} {s : Set α} {t : Set Z}
    (ht : IsClosed t)
    (hf : forall a in s, Continuous (f · a)) : IsClosed {x | MapsTo (f x) s t} := by
  simpa only [MapsTo, ofPred_forall] using! isClosed_biInter fun y hy => ht.preimage (hf y hy)

@[deprecated (since := "2026-07-09")]
alias IsClosed.setOf_mapsTo := IsClosed.setOfPred_mapsTo

/--
theorem `Continuous.comp₂` / 定理 `Continuous.comp₂`

English:
theorem Continuous.comp₂
  statement: {g : X × Y -> Z} (hg : Continuous g) {e : W -> X} (he : Continuous e)
  proof: hg.comp he.prodMk hf

中文:
定理 Continuous.comp₂
  结论: {g : X × Y -> Z} (hg : Continuous g) {e : W -> X} (he : Continuous e)
  证明: hg.comp he.prodMk hf

Depends on / 依赖: he.prodMk, hg.comp, prodMk
-/
theorem Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) {e : W -> X} (he : Continuous e)
    {f : W -> Y} (hf : Continuous f) : Continuous fun w => g (e w, f w) :=
hg.comp he.prodMk hf

/--
theorem `Continuous.comp₃` / 定理 `Continuous.comp₃`

English:
theorem Continuous.comp₃
  statement: {g : X × Y × Z -> ε} (hg : Continuous g) {e : W -> X} (he : Continuous e)
  proof: hg.comp₂ he hf.prodMk hk

中文:
定理 Continuous.comp₃
  结论: {g : X × Y × Z -> ε} (hg : Continuous g) {e : W -> X} (he : Continuous e)
  证明: hg.comp₂ he hf.prodMk hk

Depends on / 依赖: hf.prodMk, hg.comp, prodMk
-/
theorem Continuous.comp₃ {g : X × Y × Z -> ε} (hg : Continuous g) {e : W -> X} (he : Continuous e)
    {f : W -> Y} (hf : Continuous f) {k : W -> Z} (hk : Continuous k) :
    Continuous fun w => g (e w, f w, k w) :=
hg.comp₂ he hf.prodMk hk

/--
theorem `Continuous.comp₄` / 定理 `Continuous.comp₄`

English:
theorem Continuous.comp₄
  statement: {g : X × Y × Z × ζ -> ε} (hg : Continuous g) {e : W -> X} (he : Continuous e)
  proof: hg.comp₃ he hf hk.prodMk hl

@[continuity, fun_prop]

中文:
定理 Continuous.comp₄
  结论: {g : X × Y × Z × ζ -> ε} (hg : Continuous g) {e : W -> X} (he : Continuous e)
  证明: hg.comp₃ he hf hk.prodMk hl

@[continuity, fun_prop]

Depends on / 依赖: hg.comp, hk.prodMk, prodMk
-/
theorem Continuous.comp₄ {g : X × Y × Z × ζ -> ε} (hg : Continuous g) {e : W -> X} (he : Continuous e)
    {f : W -> Y} (hf : Continuous f) {k : W -> Z} (hk : Continuous k) {l : W -> ζ}
    (hl : Continuous l) : Continuous fun w => g (e w, f w, k w, l w) :=
hg.comp₃ he hf hk.prodMk hl

@[continuity, fun_prop]
/--
theorem `Continuous.prodMap` / 定理 `Continuous.prodMap`

English:
theorem Continuous.prodMap
  given: {f : Z -> X} {g : W -> Y} (hf : Continuous f) (hg : Continuous g)
  proof: hf.fst'.prodMk hg.snd'

中文:
定理 Continuous.prodMap
  条件: {f : Z -> X} {g : W -> Y} (hf : Continuous f) (hg : Continuous g)
  证明: hf.fst'.prodMk hg.snd'

Depends on / 依赖: hf.fst, hg.snd, prodMk
-/
theorem Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Prod.map f g) :=
  hf.fst'.prodMk hg.snd'

/--
theorem `continuous_inf_dom_left₂` / 定理 `continuous_inf_dom_left₂`

English:
theorem continuous_inf_dom_left₂
  statement: {X Y Z} {f : X -> Y -> Z} {ta1 ta2 : TopologicalSpace X}
  proof: ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _

中文:
定理 continuous_inf_dom_left₂
  结论: {X Y Z} {f : X -> Y -> Z} {ta1 ta2 : TopologicalSpace X}
  证明: ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _

Depends on / 依赖: Continuous, Continuous.comp, Continuous.prodMap, continuous_id, continuous_inf_dom_left, h_continuous_id, prodMap
-/
theorem continuous_inf_dom_left₂ {X Y Z} {f : X -> Y -> Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta1; haveI := tb1; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/--
theorem `continuous_inf_dom_right₂` / 定理 `continuous_inf_dom_right₂`

English:
theorem continuous_inf_dom_right₂
  statement: {X Y Z} {f : X -> Y -> Z} {ta1 ta2 : TopologicalSpace X}
  proof: ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _

中文:
定理 continuous_inf_dom_right₂
  结论: {X Y Z} {f : X -> Y -> Z} {ta1 ta2 : TopologicalSpace X}
  证明: ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _

Depends on / 依赖: Continuous, Continuous.comp, Continuous.prodMap, continuous_id, continuous_inf_dom_right, h_continuous_id, prodMap
-/
theorem continuous_inf_dom_right₂ {X Y Z} {f : X -> Y -> Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta2; haveI := tb2; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/--
theorem `continuous_sInf_dom₂` / 定理 `continuous_sInf_dom₂`

English:
theorem continuous_sInf_dom₂
  statement: {X Y Z} {f : X -> Y -> Z} {tas : Set (TopologicalSpace X)}
  proof: sInf tas; haveI := sInf tbs
    exact @Continuous _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := continuous_sInf_dom hX continuous_id
  have hY := continuous_sInf_dom hY continuous_id
  have h_continuous_id := @Continuous.prodMap _ _ _ _ tX tY (sInf tas) (sInf tbs) _ _ hX hY
  exact @Continu

中文:
定理 continuous_sInf_dom₂
  结论: {X Y Z} {f : X -> Y -> Z} {tas : Set (TopologicalSpace X)}
  证明: sInf tas; haveI := sInf tbs
    exact @Continuous _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := continuous_sInf_dom hX continuous_id
  have hY := continuous_sInf_dom hY continuous_id
  have h_continuous_id := @Continuous.prodMap _ _ _ _ tX tY (sInf tas) (sInf tbs) _ _ hX hY
  exact @Continu
-/
theorem continuous_sInf_dom₂ {X Y Z} {f : X -> Y -> Z} {tas : Set (TopologicalSpace X)}
    {tbs : Set (TopologicalSpace Y)} {tX : TopologicalSpace X} {tY : TopologicalSpace Y}
    {tc : TopologicalSpace Z} (hX : tX in tas) (hY : tY in tbs)
    (hf : Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := sInf tas; haveI := sInf tbs
    exact @Continuous _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := continuous_sInf_dom hX continuous_id
  have hY := continuous_sInf_dom hY continuous_id
  have h_continuous_id := @Continuous.prodMap _ _ _ _ tX tY (sInf tas) (sInf tbs) _ _ hX hY
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id

/--
theorem `Filter.Eventually.prod_inl_nhds` / 定理 `Filter.Eventually.prod_inl_nhds`

English:
theorem Filter.Eventually.prod_inl_nhds
  given: {p : X -> Prop} {x : X} (h : forallᶠ x in 𝓝 x, p x) (y : Y)
  proof: continuousAt_fst h

中文:
定理 Filter.Eventually.prod_inl_nhds
  条件: {p : X -> 命题} {x : X} (h : 对任意ᶠ x in 𝓝 x, p x) (y : Y)
  证明: continuousAt_fst h

Depends on / 依赖: continuousAt_fst
-/
theorem Filter.Eventually.prod_inl_nhds {p : X -> Prop} {x : X} (h : forallᶠ x in 𝓝 x, p x) (y : Y) :
    forallᶠ x in 𝓝 (x, y), p (x : X × Y).1 :=
  continuousAt_fst h

/--
theorem `Filter.Eventually.prod_inr_nhds` / 定理 `Filter.Eventually.prod_inr_nhds`

English:
theorem Filter.Eventually.prod_inr_nhds
  given: {p : Y -> Prop} {y : Y} (h : forallᶠ x in 𝓝 y, p x) (x : X)
  proof: continuousAt_snd h

中文:
定理 Filter.Eventually.prod_inr_nhds
  条件: {p : Y -> 命题} {y : Y} (h : 对任意ᶠ x in 𝓝 y, p x) (x : X)
  证明: continuousAt_snd h

Depends on / 依赖: continuousAt_snd
-/
theorem Filter.Eventually.prod_inr_nhds {p : Y -> Prop} {y : Y} (h : forallᶠ x in 𝓝 y, p x) (x : X) :
    forallᶠ x in 𝓝 (x, y), p (x : X × Y).2 :=
  continuousAt_snd h

/--
theorem `Filter.Eventually.prodMk_nhds` / 定理 `Filter.Eventually.prodMk_nhds`

English:
theorem Filter.Eventually.prodMk_nhds
  statement: {px : X -> Prop} {x} (hx : forallᶠ x in 𝓝 x, px x) {py : Y -> Prop}
  proof: (hx.prod_inl_nhds y).and (hy.prod_inr_nhds x)

@[fun_prop]

中文:
定理 Filter.Eventually.prodMk_nhds
  结论: {px : X -> 命题} {x} (hx : 对任意ᶠ x in 𝓝 x, px x) {py : Y -> 命题}
  证明: (hx.prod_inl_nhds y).and (hy.prod_inr_nhds x)

@[fun_prop]

Depends on / 依赖: hx.prod_inl_nhds, hy.prod_inr_nhds, prod_inl_nhds, prod_inr_nhds
-/
theorem Filter.Eventually.prodMk_nhds {px : X -> Prop} {x} (hx : forallᶠ x in 𝓝 x, px x) {py : Y -> Prop}
    {y} (hy : forallᶠ y in 𝓝 y, py y) : forallᶠ p in 𝓝 (x, y), px (p : X × Y).1 ∧ py p.2 :=
  (hx.prod_inl_nhds y).and (hy.prod_inr_nhds x)

@[fun_prop]
/--
theorem `continuous_swap` / 定理 `continuous_swap`

English:
theorem continuous_swap
  statement: Continuous (Prod.swap : X × Y -> Y × X)
  proof: continuous_snd.prodMk continuous_fst

中文:
定理 continuous_swap
  结论: Continuous (Prod.swap : X × Y -> Y × X)
  证明: continuous_snd.prodMk continuous_fst

Depends on / 依赖: continuous_fst, continuous_snd, continuous_snd.prodMk, prodMk
-/
theorem continuous_swap : Continuous (Prod.swap : X × Y -> Y × X) :=
  continuous_snd.prodMk continuous_fst

/--
lemma `isClosedMap_swap` / 引理 `isClosedMap_swap`

English:
lemma isClosedMap_swap
  statement: IsClosedMap (Prod.swap : X × Y -> Y × X)
  proof: fun s hs => by
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap

中文:
引理 isClosedMap_swap
  结论: IsClosedMap (Prod.swap : X × Y -> Y × X)
  证明: fun s hs => by
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap

Depends on / 依赖: continuous_swap, hs.preimage, image_swap_eq_preimage_swap, preimage
-/
lemma isClosedMap_swap : IsClosedMap (Prod.swap : X × Y -> Y × X) := fun s hs => by
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap

/--
theorem `Continuous.uncurry_left` / 定理 `Continuous.uncurry_left`

English:
theorem Continuous.uncurry_left
  given: {f : X -> Y -> Z} (x : X) (h : Continuous (uncurry f))
  proof: h.comp (.prodMk_right _)

中文:
定理 Continuous.uncurry_left
  条件: {f : X -> Y -> Z} (x : X) (h : Continuous (uncurry f))
  证明: h.comp (.prodMk_right _)

Depends on / 依赖: h.comp, prodMk_right
-/
theorem Continuous.uncurry_left {f : X -> Y -> Z} (x : X) (h : Continuous (uncurry f)) :
    Continuous (f x) :=
  h.comp (.prodMk_right _)

/--
theorem `Continuous.uncurry_right` / 定理 `Continuous.uncurry_right`

English:
theorem Continuous.uncurry_right
  given: {f : X -> Y -> Z} (y : Y) (h : Continuous (uncurry f))
  proof: h.comp (.prodMk_left _)

中文:
定理 Continuous.uncurry_right
  条件: {f : X -> Y -> Z} (y : Y) (h : Continuous (uncurry f))
  证明: h.comp (.prodMk_left _)

Depends on / 依赖: h.comp, prodMk_left
-/
theorem Continuous.uncurry_right {f : X -> Y -> Z} (y : Y) (h : Continuous (uncurry f)) :
    Continuous fun a => f a y :=
  h.comp (.prodMk_left _)

/--
theorem `continuous_curry` / 定理 `continuous_curry`

English:
theorem continuous_curry
  given: {g : X × Y -> Z} (x : X) (h : Continuous g)
  statement: Continuous (curry g x)
  proof: Continuous.uncurry_left x h

中文:
定理 continuous_curry
  条件: {g : X × Y -> Z} (x : X) (h : Continuous g)
  结论: Continuous (curry g x)
  证明: Continuous.uncurry_left x h

Depends on / 依赖: Continuous, Continuous.uncurry_left, uncurry_left
-/
theorem continuous_curry {g : X × Y -> Z} (x : X) (h : Continuous g) : Continuous (curry g x) :=
  Continuous.uncurry_left x h

/--
theorem `IsOpen.prod` / 定理 `IsOpen.prod`

English:
theorem IsOpen.prod
  given: {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t)
  statement: IsOpen (s ×ˢ t)
  proof: (hs.preimage continuous_fst).inter (ht.preimage continuous_snd)

中文:
定理 IsOpen.prod
  条件: {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t)
  结论: IsOpen (s ×ˢ t)
  证明: (hs.preimage continuous_fst).inter (ht.preimage continuous_snd)

Depends on / 依赖: continuous_fst, continuous_snd, hs.preimage, ht.preimage, preimage
-/
theorem IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.preimage continuous_fst).inter (ht.preimage continuous_snd)

-- Porting note: Lean fails to find `t₁` and `t₂` by unification
/--
theorem `nhds_prod_eq` / 定理 `nhds_prod_eq`

English:
theorem nhds_prod_eq
  given: {x : X} {y : Y}
  statement: 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
  proof: by
  rw [prod_eq_inf]; rw [instTopologicalSpaceProd]; rw [nhds_inf (t₁ := TopologicalSpace.induced Prod.fst _)
    (t₂ := TopologicalSpace.induced Prod.snd _)]; rw [nhds_induced]; rw [nhds_induced]

中文:
定理 nhds_prod_eq
  条件: {x : X} {y : Y}
  结论: 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
  证明: by
  rw [prod_eq_inf]; rw [instTopologicalSpaceProd]; rw [nhds_inf (t₁ := TopologicalSpace.induced Prod.fst _)
    (t₂ := TopologicalSpace.induced Prod.snd _)]; rw [nhds_induced]; rw [nhds_induced]

Depends on / 依赖: Prod.fst, Prod.snd, TopologicalSpace, TopologicalSpace.induced, induced, instTopologicalSpaceProd, nhds_induced, nhds_inf, prod_eq_inf
-/
theorem nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y := by
  rw [prod_eq_inf]; rw [instTopologicalSpaceProd]; rw [nhds_inf (t₁ := TopologicalSpace.induced Prod.fst _)
    (t₂ := TopologicalSpace.induced Prod.snd _)]; rw [nhds_induced]; rw [nhds_induced]

/--
theorem `nhdsWithin_prod_eq` / 定理 `nhdsWithin_prod_eq`

English:
theorem nhdsWithin_prod_eq
  given: (x : X) (y : Y) (s : Set X) (t : Set Y)
  proof: by
  simp only [nhdsWithin, nhds_prod_eq, ← prod_inf_prod, prod_principal_principal]

中文:
定理 nhdsWithin_prod_eq
  条件: (x : X) (y : Y) (s : Set X) (t : Set Y)
  证明: by
  simp only [nhdsWithin, nhds_prod_eq, ← prod_inf_prod, prod_principal_principal]

Depends on / 依赖: nhdsWithin, nhds_prod_eq, prod_inf_prod, prod_principal_principal
-/
theorem nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : Set Y) :
    𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y := by
  simp only [nhdsWithin, nhds_prod_eq, ← prod_inf_prod, prod_principal_principal]

/--
Instance `Prod.instNeBotNhdsWithinIio` / 实例 `Prod.instNeBotNhdsWithinIio`

English:
instance Prod.instNeBotNhdsWithinIio
  signature: [Preorder X] [Preorder Y] {x : X × Y}
  body: by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ => Prod.lt_iff.2 .inl ⟨h₁, h₂.le⟩

中文:
实例 Prod.instNeBotNhdsWithinIio
  签名: [Preorder X] [Preorder Y] {x : X × Y}
  定义体: by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ => Prod.lt_iff.2 .inl ⟨h₁, h₂.le⟩

Depends on / 依赖: Prod.lt_iff, lt_iff, nhdsWithin_mono, nhdsWithin_prod_eq
-/
instance Prod.instNeBotNhdsWithinIio [Preorder X] [Preorder Y] {x : X × Y}
    [hx₁ : (𝓝[<] x.1).NeBot] [hx₂ : (𝓝[<] x.2).NeBot] : (𝓝[<] x).NeBot := by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ => Prod.lt_iff.2 .inl ⟨h₁, h₂.le⟩

/--
Instance `Prod.instNeBotNhdsWithinIoi` / 实例 `Prod.instNeBotNhdsWithinIoi`

English:
instance Prod.instNeBotNhdsWithinIoi
  signature: [Preorder X] [Preorder Y] {x : X × Y}
  body: by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ => Prod.lt_iff.2 .inl ⟨h₁, h₂.le⟩

中文:
实例 Prod.instNeBotNhdsWithinIoi
  签名: [Preorder X] [Preorder Y] {x : X × Y}
  定义体: by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ => Prod.lt_iff.2 .inl ⟨h₁, h₂.le⟩

Depends on / 依赖: Prod.lt_iff, lt_iff, nhdsWithin_mono, nhdsWithin_prod_eq
-/
instance Prod.instNeBotNhdsWithinIoi [Preorder X] [Preorder Y] {x : X × Y}
    [hx₁ : (𝓝[>] x.1).NeBot] [hx₂ : (𝓝[>] x.2).NeBot] : (𝓝[>] x).NeBot := by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ => Prod.lt_iff.2 .inl ⟨h₁, h₂.le⟩

/--
theorem `mem_nhds_prod_iff` / 定理 `mem_nhds_prod_iff`

English:
theorem mem_nhds_prod_iff
  given: {x : X} {y : Y} {s : Set (X × Y)}
  proof: by rw [nhds_prod_eq, mem_prod_iff]

中文:
定理 mem_nhds_prod_iff
  条件: {x : X} {y : Y} {s : Set (X × Y)}
  证明: by rw [nhds_prod_eq, mem_prod_iff]

Depends on / 依赖: mem_prod_iff, nhds_prod_eq
-/
theorem mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
    s in 𝓝 (x, y) ↔ exists u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s := by rw [nhds_prod_eq, mem_prod_iff]

/--
theorem `mem_nhdsWithin_prod_iff` / 定理 `mem_nhdsWithin_prod_iff`

English:
theorem mem_nhdsWithin_prod_iff
  given: {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty : Set Y}
  proof: by
  rw [nhdsWithin_prod_eq]; rw [mem_prod_iff]

中文:
定理 mem_nhdsWithin_prod_iff
  条件: {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty : Set Y}
  证明: by
  rw [nhdsWithin_prod_eq]; rw [mem_prod_iff]

Depends on / 依赖: mem_prod_iff, nhdsWithin_prod_eq
-/
theorem mem_nhdsWithin_prod_iff {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty : Set Y} :
    s in 𝓝[tx ×ˢ ty] (x, y) ↔ exists u in 𝓝[tx] x, exists v in 𝓝[ty] y, u ×ˢ v subseteq s := by
  rw [nhdsWithin_prod_eq]; rw [mem_prod_iff]

/--
theorem `Filter.HasBasis.prod_nhds` / 定理 `Filter.HasBasis.prod_nhds`

English:
theorem Filter.HasBasis.prod_nhds
  statement: {ιX ιY : Type*} {px : ιX -> Prop} {py : ιY -> Prop}
  proof: by
  rw [nhds_prod_eq]
  exact hx.prod hy

中文:
定理 Filter.HasBasis.prod_nhds
  结论: {ιX ιY : 类型} {px : ιX -> 命题} {py : ιY -> 命题}
  证明: by
  rw [nhds_prod_eq]
  exact hx.prod hy

Depends on / 依赖: hx.prod, nhds_prod_eq
-/
theorem Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px : ιX -> Prop} {py : ιY -> Prop}
    {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {y : Y} (hx : (𝓝 x).HasBasis px sx)
    (hy : (𝓝 y).HasBasis py sy) :
    (𝓝 (x, y)).HasBasis (fun i : ιX × ιY => px i.1 ∧ py i.2) fun i => sx i.1 ×ˢ sy i.2 := by
  rw [nhds_prod_eq]
  exact hx.prod hy

/--
theorem `Filter.HasBasis.prod_nhds'` / 定理 `Filter.HasBasis.prod_nhds'`

English:
theorem Filter.HasBasis.prod_nhds'
  statement: {ιX ιY : Type*} {pX : ιX -> Prop} {pY : ιY -> Prop}
  proof: hx.prod_nhds hy

中文:
定理 Filter.HasBasis.prod_nhds'
  结论: {ιX ιY : 类型} {pX : ιX -> 命题} {pY : ιY -> 命题}
  证明: hx.prod_nhds hy

Depends on / 依赖: hx.prod_nhds, prod_nhds
-/
theorem Filter.HasBasis.prod_nhds' {ιX ιY : Type*} {pX : ιX -> Prop} {pY : ιY -> Prop}
    {sx : ιX -> Set X} {sy : ιY -> Set Y} {p : X × Y} (hx : (𝓝 p.1).HasBasis pX sx)
    (hy : (𝓝 p.2).HasBasis pY sy) :
    (𝓝 p).HasBasis (fun i : ιX × ιY => pX i.1 ∧ pY i.2) fun i => sx i.1 ×ˢ sy i.2 :=
  hx.prod_nhds hy

/--
theorem `mem_nhds_prod_iff'` / 定理 `mem_nhds_prod_iff'`

English:
theorem mem_nhds_prod_iff'
  given: {x : X} {y : Y} {s : Set (X × Y)}
  proof: ((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]

中文:
定理 mem_nhds_prod_iff'
  条件: {x : X} {y : Y} {s : Set (X × Y)}
  证明: ((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]

Depends on / 依赖: Prod.exists, and_assoc, and_comm, and_left_comm, mem_iff, mem_iff.trans, nhds_basis_opens, prod_nhds
-/
theorem mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)} :
    s in 𝓝 (x, y) ↔ exists u v, IsOpen u ∧ x in u ∧ IsOpen v ∧ y in v ∧ u ×ˢ v subseteq s :=
((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]

/--
theorem `Prod.tendsto_iff` / 定理 `Prod.tendsto_iff`

English:
theorem Prod.tendsto_iff
  given: {X} (seq : X -> Y × Z) {f : Filter X} (p : Y × Z)
  proof: by
  rw [nhds_prod_eq]; rw [Filter.tendsto_prod_iff']

中文:
定理 Prod.tendsto_iff
  条件: {X} (seq : X -> Y × Z) {f : Filter X} (p : Y × Z)
  证明: by
  rw [nhds_prod_eq]; rw [Filter.tendsto_prod_iff']

Depends on / 依赖: Filter, Filter.tendsto_prod_iff, nhds_prod_eq, tendsto_prod_iff
-/
theorem Prod.tendsto_iff {X} (seq : X -> Y × Z) {f : Filter X} (p : Y × Z) :
    Tendsto seq f (𝓝 p) ↔
      Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 p.snd) := by
  rw [nhds_prod_eq]; rw [Filter.tendsto_prod_iff']

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: X] [DiscreteTopology Y] : DiscreteTopology (X × Y)
  body: discreteTopology_iff_nhds.2 fun (a, b) => by
    rw [nhds_prod_eq]; rw [nhds_discrete X]; rw [nhds_discrete Y]; rw [prod_pure_pure]

中文:
实例 [DiscreteTopology
  签名: X] [DiscreteTopology Y] : DiscreteTopology (X × Y)
  定义体: discreteTopology_iff_nhds.2 fun (a, b) => by
    rw [nhds_prod_eq]; rw [nhds_discrete X]; rw [nhds_discrete Y]; rw [prod_pure_pure]

Depends on / 依赖: discreteTopology_iff_nhds, nhds_discrete, nhds_prod_eq, prod_pure_pure
-/
instance [DiscreteTopology X] [DiscreteTopology Y] : DiscreteTopology (X × Y) :=
  discreteTopology_iff_nhds.2 fun (a, b) => by
    rw [nhds_prod_eq]; rw [nhds_discrete X]; rw [nhds_discrete Y]; rw [prod_pure_pure]

/--
theorem `prod_mem_nhds_iff` / 定理 `prod_mem_nhds_iff`

English:
theorem prod_mem_nhds_iff
  given: {s : Set X} {t : Set Y} {x : X} {y : Y}
  proof: by rw [nhds_prod_eq, prod_mem_prod_iff]

中文:
定理 prod_mem_nhds_iff
  条件: {s : Set X} {t : Set Y} {x : X} {y : Y}
  证明: by rw [nhds_prod_eq, prod_mem_prod_iff]

Depends on / 依赖: nhds_prod_eq, prod_mem_prod_iff
-/
theorem prod_mem_nhds_iff {s : Set X} {t : Set Y} {x : X} {y : Y} :
    s ×ˢ t in 𝓝 (x, y) ↔ s in 𝓝 x ∧ t in 𝓝 y := by rw [nhds_prod_eq, prod_mem_prod_iff]

/--
theorem `prod_mem_nhds` / 定理 `prod_mem_nhds`

English:
theorem prod_mem_nhds
  given: {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s in 𝓝 x) (hy : t in 𝓝 y)
  proof: prod_mem_nhds_iff.2 ⟨hx, hy⟩

中文:
定理 prod_mem_nhds
  条件: {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s in 𝓝 x) (hy : t in 𝓝 y)
  证明: prod_mem_nhds_iff.2 ⟨hx, hy⟩

Depends on / 依赖: prod_mem_nhds_iff
-/
theorem prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s in 𝓝 x) (hy : t in 𝓝 y) :
    s ×ˢ t in 𝓝 (x, y) :=
  prod_mem_nhds_iff.2 ⟨hx, hy⟩

/--
theorem `isOpen_setOfPred_disjoint_nhds_nhds` / 定理 `isOpen_setOfPred_disjoint_nhds_nhds`

English:
theorem isOpen_setOfPred_disjoint_nhds_nhds
  statement: IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) }
  proof: by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_ofPred_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact mem_nhds_prod_iff'.mpr ⟨U, V, hU.2, hU.1, hV.2, hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    disjoint_of_disjoint_of_mem hd (hU.

中文:
定理 isOpen_setOfPred_disjoint_nhds_nhds
  结论: IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) }
  证明: by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_ofPred_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact mem_nhds_prod_iff'.mpr ⟨U, V, hU.2, hU.1, hV.2, hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    disjoint_of_disjoint_of_mem hd (hU.

Depends on / 依赖: Prod.forall, disjoint_iff, disjoint_of_disjoint_of_mem, isOpen_iff_mem_nhds, mem_nhds, mem_nhds_prod_iff, mem_ofPred_eq, nhds_basis_opens
-/
theorem isOpen_setOfPred_disjoint_nhds_nhds : IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) } := by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_ofPred_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact mem_nhds_prod_iff'.mpr ⟨U, V, hU.2, hU.1, hV.2, hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    disjoint_of_disjoint_of_mem hd (hU.2.mem_nhds hx') (hV.2.mem_nhds hy')⟩

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_disjoint_nhds_nhds := isOpen_setOfPred_disjoint_nhds_nhds

/--
theorem `Filter.Eventually.prod_nhds` / 定理 `Filter.Eventually.prod_nhds`

English:
theorem Filter.Eventually.prod_nhds
  statement: {p : X -> Prop} {q : Y -> Prop} {x : X} {y : Y}
  proof: prod_mem_nhds hx hy

中文:
定理 Filter.Eventually.prod_nhds
  结论: {p : X -> 命题} {q : Y -> 命题} {x : X} {y : Y}
  证明: prod_mem_nhds hx hy

Depends on / 依赖: prod_mem_nhds
-/
theorem Filter.Eventually.prod_nhds {p : X -> Prop} {q : Y -> Prop} {x : X} {y : Y}
    (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in 𝓝 y, q y) : forallᶠ z : X × Y in 𝓝 (x, y), p z.1 ∧ q z.2 :=
  prod_mem_nhds hx hy

/--
theorem `Filter.EventuallyEq.prodMap_nhds` / 定理 `Filter.EventuallyEq.prodMap_nhds`

English:
theorem Filter.EventuallyEq.prodMap_nhds
  statement: {α β : Type*} {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β}
  proof: by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

中文:
定理 Filter.EventuallyEq.prodMap_nhds
  结论: {α β : 类型} {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β}
  证明: by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

Depends on / 依赖: hf.prodMap, nhds_prod_eq, prodMap
-/
theorem Filter.EventuallyEq.prodMap_nhds {α β : Type*} {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β}
    {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) (hg : g₁ =ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ =ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

/--
theorem `Filter.EventuallyLE.prodMap_nhds` / 定理 `Filter.EventuallyLE.prodMap_nhds`

English:
theorem Filter.EventuallyLE.prodMap_nhds
  statement: {α β : Type*} [LE α] [LE β] {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β}
  proof: by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

中文:
定理 Filter.EventuallyLE.prodMap_nhds
  结论: {α β : 类型} [LE α] [LE β] {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β}
  证明: by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

Depends on / 依赖: hf.prodMap, nhds_prod_eq, prodMap
-/
theorem Filter.EventuallyLE.prodMap_nhds {α β : Type*} [LE α] [LE β] {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β}
    {x : X} {y : Y} (hf : f₁ <=ᶠ[𝓝 x] f₂) (hg : g₁ <=ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ <=ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

/--
theorem `nhds_swap` / 定理 `nhds_swap`

English:
theorem nhds_swap
  given: (x : X) (y : Y)
  statement: 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap
  proof: by
  rw [nhds_prod_eq]; rw [Filter.prod_comm]; rw [nhds_prod_eq]

中文:
定理 nhds_swap
  条件: (x : X) (y : Y)
  结论: 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap
  证明: by
  rw [nhds_prod_eq]; rw [Filter.prod_comm]; rw [nhds_prod_eq]

Depends on / 依赖: Filter, Filter.prod_comm, nhds_prod_eq, prod_comm
-/
theorem nhds_swap (x : X) (y : Y) : 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap := by
  rw [nhds_prod_eq]; rw [Filter.prod_comm]; rw [nhds_prod_eq]

/--
theorem `Filter.Tendsto.prodMk_nhds` / 定理 `Filter.Tendsto.prodMk_nhds`

English:
theorem Filter.Tendsto.prodMk_nhds
  statement: {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y}
  proof: by
  rw [nhds_prod_eq]
  exact hx.prodMk hy

中文:
定理 Filter.Tendsto.prodMk_nhds
  结论: {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y}
  证明: by
  rw [nhds_prod_eq]
  exact hx.prodMk hy

Depends on / 依赖: hx.prodMk, nhds_prod_eq, prodMk
-/
theorem Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y}
    (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) :
    Tendsto (fun c => (mx c, my c)) f (𝓝 (x, y)) := by
  rw [nhds_prod_eq]
  exact hx.prodMk hy

/--
theorem `Filter.Tendsto.prodMap_nhds` / 定理 `Filter.Tendsto.prodMap_nhds`

English:
theorem Filter.Tendsto.prodMap_nhds
  statement: {x : X} {y : Y} {z : Z} {w : W} {f : X -> Y} {g : Z -> W}
  proof: by
  rw [nhds_prod_eq]; rw [nhds_prod_eq]
  exact hf.prodMap hg

中文:
定理 Filter.Tendsto.prodMap_nhds
  结论: {x : X} {y : Y} {z : Z} {w : W} {f : X -> Y} {g : Z -> W}
  证明: by
  rw [nhds_prod_eq]; rw [nhds_prod_eq]
  exact hf.prodMap hg

Depends on / 依赖: hf.prodMap, nhds_prod_eq, prodMap
-/
theorem Filter.Tendsto.prodMap_nhds {x : X} {y : Y} {z : Z} {w : W} {f : X -> Y} {g : Z -> W}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : Tendsto g (𝓝 z) (𝓝 w)) :
    Tendsto (Prod.map f g) (𝓝 (x, z)) (𝓝 (y, w)) := by
  rw [nhds_prod_eq]; rw [nhds_prod_eq]
  exact hf.prodMap hg

/--
theorem `Filter.Eventually.curry_nhds` / 定理 `Filter.Eventually.curry_nhds`

English:
theorem Filter.Eventually.curry_nhds
  statement: {p : X × Y -> Prop} {x : X} {y : Y}
  proof: by
  rw [nhds_prod_eq] at h
  exact h.curry

@[fun_prop]

中文:
定理 Filter.Eventually.curry_nhds
  结论: {p : X × Y -> 命题} {x : X} {y : Y}
  证明: by
  rw [nhds_prod_eq] at h
  exact h.curry

@[fun_prop]

Depends on / 依赖: h.curry, nhds_prod_eq
-/
theorem Filter.Eventually.curry_nhds {p : X × Y -> Prop} {x : X} {y : Y}
    (h : forallᶠ x in 𝓝 (x, y), p x) : forallᶠ x' in 𝓝 x, forallᶠ y' in 𝓝 y, p (x', y') := by
  rw [nhds_prod_eq] at h
  exact h.curry

@[fun_prop]
/--
theorem `ContinuousAt.prodMk` / 定理 `ContinuousAt.prodMk`

English:
theorem ContinuousAt.prodMk
  statement: {f : X -> Y} {g : X -> Z} {x : X} (hf : ContinuousAt f x)
  proof: hf.prodMk_nhds hg

中文:
定理 ContinuousAt.prodMk
  结论: {f : X -> Y} {g : X -> Z} {x : X} (hf : ContinuousAt f x)
  证明: hf.prodMk_nhds hg

Depends on / 依赖: hf.prodMk_nhds, prodMk_nhds
-/
theorem ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : X} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x :=
  hf.prodMk_nhds hg

/--
theorem `ContinuousAt.prodMap` / 定理 `ContinuousAt.prodMap`

English:
theorem ContinuousAt.prodMap
  statement: {f : X -> Z} {g : Y -> W} {p : X × Y} (hf : ContinuousAt f p.fst)
  proof: hf.fst''.prodMk hg.snd''

中文:
定理 ContinuousAt.prodMap
  结论: {f : X -> Z} {g : Y -> W} {p : X × Y} (hf : ContinuousAt f p.fst)
  证明: hf.fst''.prodMk hg.snd''

Depends on / 依赖: hf.fst, hg.snd, prodMk
-/
theorem ContinuousAt.prodMap {f : X -> Z} {g : Y -> W} {p : X × Y} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (Prod.map f g) p :=
  hf.fst''.prodMk hg.snd''

/--
theorem `ContinuousAt.prodMap'` / 定理 `ContinuousAt.prodMap'`

English:
theorem ContinuousAt.prodMap'
  statement: {f : X -> Z} {g : Y -> W} {x : X} {y : Y} (hf : ContinuousAt f x)
  proof: hf.prodMap hg

@[simp]

中文:
定理 ContinuousAt.prodMap'
  结论: {f : X -> Z} {g : Y -> W} {x : X} {y : Y} (hf : ContinuousAt f x)
  证明: hf.prodMap hg

@[simp]

Depends on / 依赖: hf.prodMap, prodMap
-/
theorem ContinuousAt.prodMap' {f : X -> Z} {g : Y -> W} {x : X} {y : Y} (hf : ContinuousAt f x)
    (hg : ContinuousAt g y) : ContinuousAt (Prod.map f g) (x, y) :=
  hf.prodMap hg

@[simp]
/--
theorem `continuousAt_prodMap_iff` / 定理 `continuousAt_prodMap_iff`

English:
theorem continuousAt_prodMap_iff
  given: {f : X -> Z} {g : Y -> W} {x : X} {y : Y}
  proof: by
  simp [ContinuousAt, nhds_prod_eq, tendsto_iff_comap, comap_prodMap_prod]

@[simp]

中文:
定理 continuousAt_prodMap_iff
  条件: {f : X -> Z} {g : Y -> W} {x : X} {y : Y}
  证明: by
  simp [ContinuousAt, nhds_prod_eq, tendsto_iff_comap, comap_prodMap_prod]

@[simp]

Depends on / 依赖: ContinuousAt, comap_prodMap_prod, nhds_prod_eq, tendsto_iff_comap
-/
theorem continuousAt_prodMap_iff {f : X -> Z} {g : Y -> W} {x : X} {y : Y} :
    ContinuousAt (Prod.map f g) (x, y) ↔ ContinuousAt f x ∧ ContinuousAt g y := by
  simp [ContinuousAt, nhds_prod_eq, tendsto_iff_comap, comap_prodMap_prod]

@[simp]
/--
theorem `continuous_prodMap_iff` / 定理 `continuous_prodMap_iff`

English:
theorem continuous_prodMap_iff
  given: [Nonempty Z] [Nonempty W] {f : Z -> X} {g : W -> Y}
  proof: by
  simp [continuous_iff_continuousAt, forall_and]

中文:
定理 continuous_prodMap_iff
  条件: [Nonempty Z] [Nonempty W] {f : Z -> X} {g : W -> Y}
  证明: by
  simp [continuous_iff_continuousAt, forall_and]

Depends on / 依赖: continuous_iff_continuousAt, forall_and
-/
theorem continuous_prodMap_iff [Nonempty Z] [Nonempty W] {f : Z -> X} {g : W -> Y} :
    Continuous (Prod.map f g) ↔ Continuous f ∧ Continuous g := by
  simp [continuous_iff_continuousAt, forall_and]

/--
theorem `ContinuousAt.comp₂` / 定理 `ContinuousAt.comp₂`

English:
theorem ContinuousAt.comp₂
  statement: {f : Y × Z -> W} {g : X -> Y} {h : X -> Z} {x : X}
  proof: ContinuousAt.comp hf (hg.prodMk hh)

中文:
定理 ContinuousAt.comp₂
  结论: {f : Y × Z -> W} {g : X -> Y} {h : X -> Z} {x : X}
  证明: ContinuousAt.comp hf (hg.prodMk hh)

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, hg.prodMk, prodMk
-/
theorem ContinuousAt.comp₂ {f : Y × Z -> W} {g : X -> Y} {h : X -> Z} {x : X}
    (hf : ContinuousAt f (g x, h x)) (hg : ContinuousAt g x) (hh : ContinuousAt h x) :
    ContinuousAt (fun x => f (g x, h x)) x :=
  ContinuousAt.comp hf (hg.prodMk hh)

/--
theorem `ContinuousAt.comp₂_of_eq` / 定理 `ContinuousAt.comp₂_of_eq`

English:
theorem ContinuousAt.comp₂_of_eq
  statement: {f : Y × Z -> W} {g : X -> Y} {h : X -> Z} {x : X} {y : Y × Z}
  proof: by
  rw [← e] at hf
  exact hf.comp₂ hg hh

中文:
定理 ContinuousAt.comp₂_of_eq
  结论: {f : Y × Z -> W} {g : X -> Y} {h : X -> Z} {x : X} {y : Y × Z}
  证明: by
  rw [← e] at hf
  exact hf.comp₂ hg hh

Depends on / 依赖: hf.comp
-/
theorem ContinuousAt.comp₂_of_eq {f : Y × Z -> W} {g : X -> Y} {h : X -> Z} {x : X} {y : Y × Z}
    (hf : ContinuousAt f y) (hg : ContinuousAt g x) (hh : ContinuousAt h x) (e : (g x, h x) = y) :
    ContinuousAt (fun x => f (g x, h x)) x := by
  rw [← e] at hf
  exact hf.comp₂ hg hh

/--
theorem `Continuous.curry_left` / 定理 `Continuous.curry_left`

English:
theorem Continuous.curry_left
  given: {f : X × Y -> Z} (hf : Continuous f) {y : Y}
  proof: hf.comp (.prodMk_left _)
alias Continuous.along_fst := Continuous.curry_left

中文:
定理 Continuous.curry_left
  条件: {f : X × Y -> Z} (hf : Continuous f) {y : Y}
  证明: hf.comp (.prodMk_left _)
alias Continuous.along_fst := Continuous.curry_left

Depends on / 依赖: Continuous, Continuous.along_fst, Continuous.curry_left, along_fst, curry_left, hf.comp, prodMk_left
-/
theorem Continuous.curry_left {f : X × Y -> Z} (hf : Continuous f) {y : Y} :
    Continuous fun x => f (x, y) :=
  hf.comp (.prodMk_left _)
alias Continuous.along_fst := Continuous.curry_left

/--
theorem `Continuous.curry_right` / 定理 `Continuous.curry_right`

English:
theorem Continuous.curry_right
  given: {f : X × Y -> Z} (hf : Continuous f) {x : X}
  proof: hf.comp (.prodMk_right _)
alias Continuous.along_snd := Continuous.curry_right

中文:
定理 Continuous.curry_right
  条件: {f : X × Y -> Z} (hf : Continuous f) {x : X}
  证明: hf.comp (.prodMk_right _)
alias Continuous.along_snd := Continuous.curry_right

Depends on / 依赖: Continuous, Continuous.along_snd, Continuous.curry_right, along_snd, curry_right, hf.comp, prodMk_right
-/
theorem Continuous.curry_right {f : X × Y -> Z} (hf : Continuous f) {x : X} :
    Continuous fun y => f (x, y) :=
  hf.comp (.prodMk_right _)
alias Continuous.along_snd := Continuous.curry_right

-- todo: prove a version of `generateFrom_union` with `image2 (∩) s t` in the LHS and use it here
/--
theorem `prod_generateFrom_generateFrom_eq` / 定理 `prod_generateFrom_generateFrom_eq`

English:
theorem prod_generateFrom_generateFrom_eq
  statement: {X Y : Type*} {s : Set (Set X)} {t : Set (Set Y)}
  proof: let G := generateFrom (image2 (· ×ˢ ·) s t)
  le_antisymm
    (le_generateFrom fun _ ⟨_, hu, _, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.

中文:
定理 prod_generateFrom_generateFrom_eq
  结论: {X Y : 类型} {s : Set (Set X)} {t : Set (Set Y)}
  证明: let G := generateFrom (image2 (· ×ˢ ·) s t)
  le_antisymm
    (le_generateFrom fun _ ⟨_, hu, _, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.

Depends on / 依赖: G.IsOpen, GenerateOpen, GenerateOpen.basic, IsOpen, IsOpen.prod, Prod.fst, coinduced_le_iff_le_induced, coinduced_le_iff_le_induced.mp, g_eq, g_eq.symm, generateFrom, image2, isOpen_iUnion, le_antisymm, le_generateFrom, le_inf, prod_iUnion, prod_univ, sUnion_eq_biUnion, simp_rw
-/
theorem prod_generateFrom_generateFrom_eq {X Y : Type*} {s : Set (Set X)} {t : Set (Set Y)}
    (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
    @instTopologicalSpaceProd X Y (generateFrom s) (generateFrom t) =
      generateFrom (image2 (· ×ˢ ·) s t) :=
  let G := generateFrom (image2 (· ×ˢ ·) s t)
  le_antisymm
    (le_generateFrom fun _ ⟨_, hu, _, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun u hu =>
          have : ⋃ v in t, u ×ˢ v = Prod.fst ⁻¹' u := by
            simp_rw [← prod_iUnion, ← sUnion_eq_biUnion, ht, prod_univ]
          show G.IsOpen (Prod.fst ⁻¹' u) by
            rw [← this]
            exact
              isOpen_iUnion fun v =>
                isOpen_iUnion fun hv => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩)
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun v hv =>
          have : ⋃ u in s, u ×ˢ v = Prod.snd ⁻¹' v := by
            simp_rw [← iUnion_prod_const, ← sUnion_eq_biUnion, hs, univ_prod]
          show G.IsOpen (Prod.snd ⁻¹' v) by
            rw [← this]
            exact
              isOpen_iUnion fun u =>
                isOpen_iUnion fun hu => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩))

/--
theorem `prod_eq_generateFrom` / 定理 `prod_eq_generateFrom`

English:
theorem prod_eq_generateFrom
  proof: le_antisymm (le_generateFrom fun _ ⟨_, _, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (coinduced_le_iff_le_induced.mp fun U hU =>
        .basic _ ⟨U, univ, hU, isOpen_univ, prod_univ.symm⟩)
      (coinduced_le_iff_le_induced.mp fun U hU =>
        .basic _ ⟨univ, U, isOpen_univ, hU, 

中文:
定理 prod_eq_generateFrom
  证明: le_antisymm (le_generateFrom fun _ ⟨_, _, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (coinduced_le_iff_le_induced.mp fun U hU =>
        .basic _ ⟨U, univ, hU, isOpen_univ, prod_univ.symm⟩)
      (coinduced_le_iff_le_induced.mp fun U hU =>
        .basic _ ⟨univ, U, isOpen_univ, hU, 

Depends on / 依赖: coinduced_le_iff_le_induced, coinduced_le_iff_le_induced.mp, g_eq, g_eq.symm, hs.prod, isOpen_univ, le_antisymm, le_generateFrom, le_inf, prod_univ, prod_univ.symm, univ_prod, univ_prod.symm
-/
theorem prod_eq_generateFrom :
    instTopologicalSpaceProd =
      generateFrom { g | exists (s : Set X) (t : Set Y), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymm (le_generateFrom fun _ ⟨_, _, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (coinduced_le_iff_le_induced.mp fun U hU =>
        .basic _ ⟨U, univ, hU, isOpen_univ, prod_univ.symm⟩)
      (coinduced_le_iff_le_induced.mp fun U hU =>
        .basic _ ⟨univ, U, isOpen_univ, hU, univ_prod.symm⟩))

-- TODO: align with `mem_nhds_prod_iff'`
/--
theorem `isOpen_prod_iff` / 定理 `isOpen_prod_iff`

English:
theorem isOpen_prod_iff
  given: {s : Set (X × Y)}
  proof: isOpen_iff_mem_nhds.trans by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]

中文:
定理 isOpen_prod_iff
  条件: {s : Set (X × Y)}
  证明: isOpen_iff_mem_nhds.trans by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]

Depends on / 依赖: Prod.forall, and_left_comm, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.trans, mem_nhds_prod_iff, simp_rw
-/
theorem isOpen_prod_iff {s : Set (X × Y)} :
    IsOpen s ↔ forall a b, (a, b) in s ->
      exists u v, IsOpen u ∧ IsOpen v ∧ a in u ∧ b in v ∧ u ×ˢ v subseteq s :=
isOpen_iff_mem_nhds.trans by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]

/--
theorem `prod_induced_induced` / 定理 `prod_induced_induced`

English:
theorem prod_induced_induced
  given: {X Z} (f : X -> Y) (g : Z -> W)
  proof: by
  delta instTopologicalSpaceProd
  simp_rw [induced_inf, induced_compose]
  rfl

中文:
定理 prod_induced_induced
  条件: {X Z} (f : X -> Y) (g : Z -> W)
  证明: by
  delta instTopologicalSpaceProd
  simp_rw [induced_inf, induced_compose]
  rfl

Depends on / 依赖: induced_compose, induced_inf, instTopologicalSpaceProd, simp_rw
-/
theorem prod_induced_induced {X Z} (f : X -> Y) (g : Z -> W) :
    @instTopologicalSpaceProd X Z (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) instTopologicalSpaceProd := by
  delta instTopologicalSpaceProd
  simp_rw [induced_inf, induced_compose]
  rfl

/--
theorem `exists_nhds_square` / 定理 `exists_nhds_square`

English:
theorem exists_nhds_square
  given: {s : Set (X × X)} {x : X} (hx : s in 𝓝 (x, x))
  proof: by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx

中文:
定理 exists_nhds_square
  条件: {s : Set (X × X)} {x : X} (hx : s in 𝓝 (x, x))
  证明: by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx

Depends on / 依赖: and_assoc, and_left_comm, mem_iff, nhds_basis_opens, nhds_prod_eq, prod_self, prod_self.mem_iff
-/
theorem exists_nhds_square {s : Set (X × X)} {x : X} (hx : s in 𝓝 (x, x)) :
    exists U : Set X, IsOpen U ∧ x in U ∧ U ×ˢ U subseteq s := by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx

/--
theorem `map_fst_nhdsWithin` / 定理 `map_fst_nhdsWithin`

English:
theorem map_fst_nhdsWithin
  given: (x : X × Y)
  statement: map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1
  proof: by
  refine le_antisymm (continuousAt_fst.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map]; rw [nhdsWithin]; rw [mem_inf_principal]; rw [mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage

中文:
定理 map_fst_nhdsWithin
  条件: (x : X × Y)
  结论: map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1
  证明: by
  refine le_antisymm (continuousAt_fst.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map]; rw [nhdsWithin]; rw [mem_inf_principal]; rw [mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage

Depends on / 依赖: continuousAt_fst, continuousAt_fst.mono_left, inf_le_left, le_antisymm, mem_inf_principal, mem_map, mem_nhds_prod_iff, mem_ofPred_eq, mem_of_mem_nhds, mem_of_superset, mem_preimage, mem_singleton_iff, mono_left, nhdsWithin, prod_subset_iff
-/
theorem map_fst_nhdsWithin (x : X × Y) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 := by
  refine le_antisymm (continuousAt_fst.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map]; rw [nhdsWithin]; rw [mem_inf_principal]; rw [mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl

@[simp]
/--
theorem `map_fst_nhds` / 定理 `map_fst_nhds`

English:
theorem map_fst_nhds
  given: (x : X × Y)
  statement: map Prod.fst (𝓝 x) = 𝓝 x.1
  proof: le_antisymm continuousAt_fst (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

中文:
定理 map_fst_nhds
  条件: (x : X × Y)
  结论: map Prod.fst (𝓝 x) = 𝓝 x.1
  证明: le_antisymm continuousAt_fst (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

Depends on / 依赖: continuousAt_fst, inf_le_left, le_antisymm, map_fst_nhdsWithin, map_mono, symm.trans_le, trans_le
-/
theorem map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
le_antisymm continuousAt_fst (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/--
theorem `isOpenMap_fst` / 定理 `isOpenMap_fst`

English:
theorem isOpenMap_fst
  statement: IsOpenMap (@Prod.fst X Y)
  proof: isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge

中文:
定理 isOpenMap_fst
  结论: IsOpenMap (@Prod.fst X Y)
  证明: isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge

Depends on / 依赖: isOpenMap_iff_nhds_le, map_fst_nhds
-/
theorem isOpenMap_fst : IsOpenMap (@Prod.fst X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge

/--
theorem `map_snd_nhdsWithin` / 定理 `map_snd_nhdsWithin`

English:
theorem map_snd_nhdsWithin
  given: (x : X × Y)
  statement: map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2
  proof: by
  refine le_antisymm (continuousAt_snd.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map]; rw [nhdsWithin]; rw [mem_inf_principal]; rw [mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage

中文:
定理 map_snd_nhdsWithin
  条件: (x : X × Y)
  结论: map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2
  证明: by
  refine le_antisymm (continuousAt_snd.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map]; rw [nhdsWithin]; rw [mem_inf_principal]; rw [mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage

Depends on / 依赖: continuousAt_snd, continuousAt_snd.mono_left, inf_le_left, le_antisymm, mem_inf_principal, mem_map, mem_nhds_prod_iff, mem_ofPred_eq, mem_of_mem_nhds, mem_of_superset, mem_preimage, mem_singleton_iff, mono_left, nhdsWithin, prod_subset_iff
-/
theorem map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 := by
  refine le_antisymm (continuousAt_snd.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map]; rw [nhdsWithin]; rw [mem_inf_principal]; rw [mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl

@[simp]
/--
theorem `map_snd_nhds` / 定理 `map_snd_nhds`

English:
theorem map_snd_nhds
  given: (x : X × Y)
  statement: map Prod.snd (𝓝 x) = 𝓝 x.2
  proof: le_antisymm continuousAt_snd (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

中文:
定理 map_snd_nhds
  条件: (x : X × Y)
  结论: map Prod.snd (𝓝 x) = 𝓝 x.2
  证明: le_antisymm continuousAt_snd (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

Depends on / 依赖: continuousAt_snd, inf_le_left, le_antisymm, map_mono, map_snd_nhdsWithin, symm.trans_le, trans_le
-/
theorem map_snd_nhds (x : X × Y) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
le_antisymm continuousAt_snd (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/--
theorem `isOpenMap_snd` / 定理 `isOpenMap_snd`

English:
theorem isOpenMap_snd
  statement: IsOpenMap (@Prod.snd X Y)
  proof: isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge

中文:
定理 isOpenMap_snd
  结论: IsOpenMap (@Prod.snd X Y)
  证明: isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge

Depends on / 依赖: isOpenMap_iff_nhds_le, map_snd_nhds
-/
theorem isOpenMap_snd : IsOpenMap (@Prod.snd X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge

/--
theorem `isOpen_prod_iff'` / 定理 `isOpen_prod_iff'`

English:
theorem isOpen_prod_iff'
  given: {s : Set X} {t : Set Y}
  proof: by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.Nonempty ∧ t.Nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [fst_image_prod _ st.2] using isOpenMap_fst _ H
  

中文:
定理 isOpen_prod_iff'
  条件: {s : Set X} {t : Set Y}
  证明: by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.Nonempty ∧ t.Nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [fst_image_prod _ st.2] using isOpenMap_fst _ H
  

Depends on / 依赖: IsOpen, Nonempty, Or.inl, eq_empty_or_nonempty, fst_image_prod, isOpenMap_fst, isOpenMap_snd, ne_empty, or_false, prod_eq_empty_iff, prod_nonempty_iff, s.Nonempty, snd_image_prod, t.Nonempty
-/
theorem isOpen_prod_iff' {s : Set X} {t : Set Y} :
    IsOpen (s ×ˢ t) ↔ IsOpen s ∧ IsOpen t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.Nonempty ∧ t.Nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [fst_image_prod _ st.2] using isOpenMap_fst _ H
      · simpa only [snd_image_prod st.1 t] using isOpenMap_snd _ H
    · intro H
      simp only [st.1.ne_empty, st.2.ne_empty, or_false] at H
      exact H.1.prod H.2

/--
theorem `isOpenQuotientMap_fst` / 定理 `isOpenQuotientMap_fst`

English:
theorem isOpenQuotientMap_fst
  given: [Nonempty Y]
  statement: IsOpenQuotientMap (Prod.fst : X × Y -> X)
  proof: ⟨Prod.fst_surjective, continuous_fst, isOpenMap_fst⟩

中文:
定理 isOpenQuotientMap_fst
  条件: [Nonempty Y]
  结论: IsOpenQuotientMap (Prod.fst : X × Y -> X)
  证明: ⟨Prod.fst_surjective, continuous_fst, isOpenMap_fst⟩

Depends on / 依赖: Prod.fst_surjective, continuous_fst, fst_surjective, isOpenMap_fst
-/
theorem isOpenQuotientMap_fst [Nonempty Y] : IsOpenQuotientMap (Prod.fst : X × Y -> X) :=
  ⟨Prod.fst_surjective, continuous_fst, isOpenMap_fst⟩

/--
theorem `isOpenQuotientMap_snd` / 定理 `isOpenQuotientMap_snd`

English:
theorem isOpenQuotientMap_snd
  given: [Nonempty X]
  statement: IsOpenQuotientMap (Prod.snd : X × Y -> Y)
  proof: ⟨Prod.snd_surjective, continuous_snd, isOpenMap_snd⟩

中文:
定理 isOpenQuotientMap_snd
  条件: [Nonempty X]
  结论: IsOpenQuotientMap (Prod.snd : X × Y -> Y)
  证明: ⟨Prod.snd_surjective, continuous_snd, isOpenMap_snd⟩

Depends on / 依赖: Prod.snd_surjective, continuous_snd, isOpenMap_snd, snd_surjective
-/
theorem isOpenQuotientMap_snd [Nonempty X] : IsOpenQuotientMap (Prod.snd : X × Y -> Y) :=
  ⟨Prod.snd_surjective, continuous_snd, isOpenMap_snd⟩

/--
theorem `isQuotientMap_fst` / 定理 `isQuotientMap_fst`

English:
theorem isQuotientMap_fst
  given: [Nonempty Y]
  statement: IsQuotientMap (Prod.fst : X × Y -> X)
  proof: isOpenQuotientMap_fst.isQuotientMap

中文:
定理 isQuotientMap_fst
  条件: [Nonempty Y]
  结论: IsQuotientMap (Prod.fst : X × Y -> X)
  证明: isOpenQuotientMap_fst.isQuotientMap

Depends on / 依赖: isOpenQuotientMap_fst, isOpenQuotientMap_fst.isQuotientMap, isQuotientMap
-/
theorem isQuotientMap_fst [Nonempty Y] : IsQuotientMap (Prod.fst : X × Y -> X) :=
  isOpenQuotientMap_fst.isQuotientMap

/--
theorem `isQuotientMap_snd` / 定理 `isQuotientMap_snd`

English:
theorem isQuotientMap_snd
  given: [Nonempty X]
  statement: IsQuotientMap (Prod.snd : X × Y -> Y)
  proof: isOpenQuotientMap_snd.isQuotientMap

中文:
定理 isQuotientMap_snd
  条件: [Nonempty X]
  结论: IsQuotientMap (Prod.snd : X × Y -> Y)
  证明: isOpenQuotientMap_snd.isQuotientMap

Depends on / 依赖: isOpenQuotientMap_snd, isOpenQuotientMap_snd.isQuotientMap, isQuotientMap
-/
theorem isQuotientMap_snd [Nonempty X] : IsQuotientMap (Prod.snd : X × Y -> Y) :=
  isOpenQuotientMap_snd.isQuotientMap

/--
theorem `closure_prod_eq` / 定理 `closure_prod_eq`

English:
theorem closure_prod_eq
  given: {s : Set X} {t : Set Y}
  statement: closure (s ×ˢ t) = closure s ×ˢ closure t
  proof: ext fun ⟨a, b⟩ => by
    simp_rw [mem_prod, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_prod_eq, prod_neBot]

中文:
定理 closure_prod_eq
  条件: {s : Set X} {t : Set Y}
  结论: closure (s ×ˢ t) = closure s ×ˢ closure t
  证明: ext fun ⟨a, b⟩ => by
    simp_rw [mem_prod, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_prod_eq, prod_neBot]

Depends on / 依赖: mem_closure_iff_nhdsWithin_neBot, mem_prod, nhdsWithin_prod_eq, prod_neBot, simp_rw
-/
theorem closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ t) = closure s ×ˢ closure t :=
  ext fun ⟨a, b⟩ => by
    simp_rw [mem_prod, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_prod_eq, prod_neBot]

/--
theorem `interior_prod_eq` / 定理 `interior_prod_eq`

English:
theorem interior_prod_eq
  given: (s : Set X) (t : Set Y)
  statement: interior (s ×ˢ t) = interior s ×ˢ interior t
  proof: ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

中文:
定理 interior_prod_eq
  条件: (s : Set X) (t : Set Y)
  结论: interior (s ×ˢ t) = interior s ×ˢ interior t
  证明: ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

Depends on / 依赖: mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff
-/
theorem interior_prod_eq (s : Set X) (t : Set Y) : interior (s ×ˢ t) = interior s ×ˢ interior t :=
  ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

/--
theorem `frontier_prod_eq` / 定理 `frontier_prod_eq`

English:
theorem frontier_prod_eq
  given: (s : Set X) (t : Set Y)
  proof: by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_sdiff_prod]

@[simp]

中文:
定理 frontier_prod_eq
  条件: (s : Set X) (t : Set Y)
  证明: by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_sdiff_prod]

@[simp]

Depends on / 依赖: closure_prod_eq, frontier, interior_prod_eq, prod_sdiff_prod
-/
theorem frontier_prod_eq (s : Set X) (t : Set Y) :
    frontier (s ×ˢ t) = closure s ×ˢ frontier t union frontier s ×ˢ closure t := by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_sdiff_prod]

@[simp]
/--
theorem `frontier_prod_univ_eq` / 定理 `frontier_prod_univ_eq`

English:
theorem frontier_prod_univ_eq
  given: (s : Set X)
  proof: by
  simp [frontier_prod_eq]

@[simp]

中文:
定理 frontier_prod_univ_eq
  条件: (s : Set X)
  证明: by
  simp [frontier_prod_eq]

@[simp]

Depends on / 依赖: frontier_prod_eq
-/
theorem frontier_prod_univ_eq (s : Set X) :
    frontier (s ×ˢ (univ : Set Y)) = frontier s ×ˢ univ := by
  simp [frontier_prod_eq]

@[simp]
/--
theorem `frontier_univ_prod_eq` / 定理 `frontier_univ_prod_eq`

English:
theorem frontier_univ_prod_eq
  given: (s : Set Y)
  proof: by
  simp [frontier_prod_eq]

中文:
定理 frontier_univ_prod_eq
  条件: (s : Set Y)
  证明: by
  simp [frontier_prod_eq]

Depends on / 依赖: frontier_prod_eq
-/
theorem frontier_univ_prod_eq (s : Set Y) :
    frontier ((univ : Set X) ×ˢ s) = univ ×ˢ frontier s := by
  simp [frontier_prod_eq]

/--
theorem `map_mem_closure₂'` / 定理 `map_mem_closure₂'`

English:
theorem map_mem_closure₂'
  statement: {f : X -> Y -> Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
  proof: by
  rw [← isClosed_closure.closure_eq]
  apply map_mem_closure (hf₁ x) hy fun b hb => ?_
  apply map_mem_closure (hf₂ b) hx fun a ha => h a ha b hb

中文:
定理 map_mem_closure₂'
  结论: {f : X -> Y -> Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
  证明: by
  rw [← isClosed_closure.closure_eq]
  apply map_mem_closure (hf₁ x) hy fun b hb => ?_
  apply map_mem_closure (hf₂ b) hx fun a ha => h a ha b hb

Depends on / 依赖: closure_eq, isClosed_closure, isClosed_closure.closure_eq, map_mem_closure
-/
theorem map_mem_closure₂' {f : X -> Y -> Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
    (hf₁ : forall x, Continuous (f x)) (hf₂ : forall y, Continuous (f · y))
    (hx : x in closure s) (hy : y in closure t) (h : forall a in s, forall b in t, f a b in u) :
    f x y in closure u := by
  rw [← isClosed_closure.closure_eq]
  apply map_mem_closure (hf₁ x) hy fun b hb => ?_
  apply map_mem_closure (hf₂ b) hx fun a ha => h a ha b hb

/--
theorem `map_mem_closure₂` / 定理 `map_mem_closure₂`

English:
theorem map_mem_closure₂
  statement: {f : X -> Y -> Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
  proof: have H₁ : (x, y) in closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod hx hy
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁

中文:
定理 map_mem_closure₂
  结论: {f : X -> Y -> Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
  证明: have H₁ : (x, y) in closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod hx hy
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁

Depends on / 依赖: MapsTo, closure, closure_prod_eq, forall_prod_set, mk_mem_prod, uncurry
-/
theorem map_mem_closure₂ {f : X -> Y -> Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
    (hf : Continuous (uncurry f)) (hx : x in closure s) (hy : y in closure t)
    (h : forall a in s, forall b in t, f a b in u) : f x y in closure u :=
  have H₁ : (x, y) in closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod hx hy
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁

/--
theorem `IsClosed.prod` / 定理 `IsClosed.prod`

English:
theorem IsClosed.prod
  given: {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂)
  proof: closure_eq_iff_isClosed.mp by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

中文:
定理 IsClosed.prod
  条件: {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂)
  证明: closure_eq_iff_isClosed.mp by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

Depends on / 依赖: closure_eq, closure_eq_iff_isClosed, closure_eq_iff_isClosed.mp, closure_prod_eq
-/
theorem IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) :
    IsClosed (s₁ ×ˢ s₂) :=
closure_eq_iff_isClosed.mp by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

/--
theorem `Dense.prod` / 定理 `Dense.prod`

English:
theorem Dense.prod
  given: {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t)
  statement: Dense (s ×ˢ t)
  proof: fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩

中文:
定理 Dense.prod
  条件: {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t)
  结论: Dense (s ×ˢ t)
  证明: fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩

Depends on / 依赖: closure_prod_eq
-/
theorem Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) :=
  fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩

/--
theorem `DenseRange.prodMap` / 定理 `DenseRange.prodMap`

English:
theorem DenseRange.prodMap
  statement: {ι : Type*} {κ : Type*} {f : ι -> Y} {g : κ -> Z} (hf : DenseRange f)
  proof: by
  simpa only [DenseRange, prod_range_range_eq] using! hf.prod hg

中文:
定理 DenseRange.prodMap
  结论: {ι : 类型} {κ : 类型} {f : ι -> Y} {g : κ -> Z} (hf : DenseRange f)
  证明: by
  simpa only [DenseRange, prod_range_range_eq] using! hf.prod hg

Depends on / 依赖: DenseRange, hf.prod, prod_range_range_eq
-/
theorem DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι -> Y} {g : κ -> Z} (hf : DenseRange f)
    (hg : DenseRange g) : DenseRange (Prod.map f g) := by
  simpa only [DenseRange, prod_range_range_eq] using! hf.prod hg

/--
lemma `Topology.IsInducing.prodMap` / 引理 `Topology.IsInducing.prodMap`

English:
lemma Topology.IsInducing.prodMap
  given: {f : X -> Y} {g : Z -> W} (hf : IsInducing f) (hg : IsInducing g)
  proof: isInducing_iff_nhds.2 fun (x, z) => by simp_rw [Prod.map_def, nhds_prod_eq, hf.nhds_eq_comap,
    hg.nhds_eq_comap, prod_comap_comap_eq]

@[simp]

中文:
引理 Topology.IsInducing.prodMap
  条件: {f : X -> Y} {g : Z -> W} (hf : IsInducing f) (hg : IsInducing g)
  证明: isInducing_iff_nhds.2 fun (x, z) => by simp_rw [Prod.map_def, nhds_prod_eq, hf.nhds_eq_comap,
    hg.nhds_eq_comap, prod_comap_comap_eq]

@[simp]

Depends on / 依赖: Prod.map_def, hf.nhds_eq_comap, hg.nhds_eq_comap, isInducing_iff_nhds, map_def, nhds_eq_comap, nhds_prod_eq, prod_comap_comap_eq, simp_rw
-/
lemma Topology.IsInducing.prodMap {f : X -> Y} {g : Z -> W} (hf : IsInducing f) (hg : IsInducing g) :
    IsInducing (Prod.map f g) :=
  isInducing_iff_nhds.2 fun (x, z) => by simp_rw [Prod.map_def, nhds_prod_eq, hf.nhds_eq_comap,
    hg.nhds_eq_comap, prod_comap_comap_eq]

@[simp]
/--
lemma `Topology.isInducing_const_prod` / 引理 `Topology.isInducing_const_prod`

English:
lemma Topology.isInducing_const_prod
  given: {x : X} {f : Y -> Z}
  proof: by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, top_inf_eq]

@[simp]

中文:
引理 Topology.isInducing_const_prod
  条件: {x : X} {f : Y -> Z}
  证明: by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, top_inf_eq]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_def, induced_compose, induced_const, induced_inf, instTopologicalSpaceProd, isInducing_iff, simp_rw, top_inf_eq
-/
lemma Topology.isInducing_const_prod {x : X} {f : Y -> Z} :
    IsInducing (fun x' => (x, f x')) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, top_inf_eq]

@[simp]
/--
lemma `Topology.isInducing_prod_const` / 引理 `Topology.isInducing_prod_const`

English:
lemma Topology.isInducing_prod_const
  given: {y : Y} {f : X -> Z}
  proof: by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, inf_top_eq]

中文:
引理 Topology.isInducing_prod_const
  条件: {y : Y} {f : X -> Z}
  证明: by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, inf_top_eq]

Depends on / 依赖: Function, Function.comp_def, comp_def, induced_compose, induced_const, induced_inf, inf_top_eq, instTopologicalSpaceProd, isInducing_iff, simp_rw
-/
lemma Topology.isInducing_prod_const {y : Y} {f : X -> Z} :
    IsInducing (fun x => (f x, y)) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, inf_top_eq]

/--
lemma `isInducing_prodMkLeft` / 引理 `isInducing_prodMkLeft`

English:
lemma isInducing_prodMkLeft
  given: (y : Y)
  statement: IsInducing (fun x : X => (x, y))
  proof: .of_comp (.prodMk_left y) continuous_fst .id

中文:
引理 isInducing_prodMkLeft
  条件: (y : Y)
  结论: IsInducing (fun x : X => (x, y))
  证明: .of_comp (.prodMk_left y) continuous_fst .id

Depends on / 依赖: continuous_fst, of_comp, prodMk_left
-/
lemma isInducing_prodMkLeft (y : Y) : IsInducing (fun x : X => (x, y)) :=
  .of_comp (.prodMk_left y) continuous_fst .id

/--
lemma `isInducing_prodMkRight` / 引理 `isInducing_prodMkRight`

English:
lemma isInducing_prodMkRight
  given: (x : X)
  statement: IsInducing (Prod.mk x : Y -> X × Y)
  proof: .of_comp (.prodMk_right x) continuous_snd .id

中文:
引理 isInducing_prodMkRight
  条件: (x : X)
  结论: IsInducing (Prod.mk x : Y -> X × Y)
  证明: .of_comp (.prodMk_right x) continuous_snd .id

Depends on / 依赖: continuous_snd, of_comp, prodMk_right
-/
lemma isInducing_prodMkRight (x : X) : IsInducing (Prod.mk x : Y -> X × Y) :=
  .of_comp (.prodMk_right x) continuous_snd .id

/--
lemma `Topology.IsEmbedding.prodMap` / 引理 `Topology.IsEmbedding.prodMap`

English:
lemma Topology.IsEmbedding.prodMap
  statement: {f : X -> Y} {g : Z -> W} (hf : IsEmbedding f)
  proof: hf.isInducing.prodMap hg.isInducing
  injective := hf.injective.prodMap hg.injective

中文:
引理 Topology.IsEmbedding.prodMap
  结论: {f : X -> Y} {g : Z -> W} (hf : IsEmbedding f)
  证明: hf.isInducing.prodMap hg.isInducing
  injective := hf.injective.prodMap hg.injective

Depends on / 依赖: hf.isInducing.prodMap, hg.isInducing, isInducing, prodMap
-/
lemma Topology.IsEmbedding.prodMap {f : X -> Y} {g : Z -> W} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (Prod.map f g) where
  toIsInducing := hf.isInducing.prodMap hg.isInducing
  injective := hf.injective.prodMap hg.injective

/--
theorem `IsOpenMap.prodMap` / 定理 `IsOpenMap.prodMap`

English:
theorem IsOpenMap.prodMap
  given: {f : X -> Y} {g : Z -> W} (hf : IsOpenMap f) (hg : IsOpenMap g)
  proof: by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq]; rw [nhds_prod_eq]; rw [← Filter.prod_map_map_eq']
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)

@[simp]

中文:
定理 IsOpenMap.prodMap
  条件: {f : X -> Y} {g : Z -> W} (hf : IsOpenMap f) (hg : IsOpenMap g)
  证明: by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq]; rw [nhds_prod_eq]; rw [← Filter.prod_map_map_eq']
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)

@[simp]
-/
protected theorem IsOpenMap.prodMap {f : X -> Y} {g : Z -> W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Prod.map f g) := by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq]; rw [nhds_prod_eq]; rw [← Filter.prod_map_map_eq']
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)

@[simp]
/--
theorem `isOpenMap_prodMap_iff` / 定理 `isOpenMap_prodMap_iff`

English:
theorem isOpenMap_prodMap_iff
  given: [Nonempty X] [Nonempty Z] {f : X -> Y} {g : Z -> W}
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hf, hg⟩ => hf.prodMap hg⟩
  · rw [(isOpenQuotientMap_fst (Y := Z)).isOpenMap_iff]
    exact isOpenMap_fst.comp h
  · rw [(isOpenQuotientMap_snd (X := X)).isOpenMap_iff]
    exact isOpenMap_snd.comp h

中文:
定理 isOpenMap_prodMap_iff
  条件: [Nonempty X] [Nonempty Z] {f : X -> Y} {g : Z -> W}
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hf, hg⟩ => hf.prodMap hg⟩
  · rw [(isOpenQuotientMap_fst (Y := Z)).isOpenMap_iff]
    exact isOpenMap_fst.comp h
  · rw [(isOpenQuotientMap_snd (X := X)).isOpenMap_iff]
    exact isOpenMap_snd.comp h

Depends on / 依赖: hf.prodMap, isOpenMap_fst, isOpenMap_fst.comp, isOpenMap_iff, isOpenMap_snd, isOpenMap_snd.comp, isOpenQuotientMap_fst, isOpenQuotientMap_snd, prodMap
-/
theorem isOpenMap_prodMap_iff [Nonempty X] [Nonempty Z] {f : X -> Y} {g : Z -> W} :
    IsOpenMap (Prod.map f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hf, hg⟩ => hf.prodMap hg⟩
  · rw [(isOpenQuotientMap_fst (Y := Z)).isOpenMap_iff]
    exact isOpenMap_fst.comp h
  · rw [(isOpenQuotientMap_snd (X := X)).isOpenMap_iff]
    exact isOpenMap_snd.comp h

/--
lemma `Topology.IsOpenEmbedding.prodMap` / 引理 `Topology.IsOpenEmbedding.prodMap`

English:
lemma Topology.IsOpenEmbedding.prodMap
  statement: {f : X -> Y} {g : Z -> W} (hf : IsOpenEmbedding f)
  proof: .of_isEmbedding_isOpenMap (hf.1.prodMap hg.1) (hf.isOpenMap.prodMap hg.isOpenMap)

中文:
引理 Topology.IsOpenEmbedding.prodMap
  结论: {f : X -> Y} {g : Z -> W} (hf : IsOpenEmbedding f)
  证明: .of_isEmbedding_isOpenMap (hf.1.prodMap hg.1) (hf.isOpenMap.prodMap hg.isOpenMap)
-/
protected lemma Topology.IsOpenEmbedding.prodMap {f : X -> Y} {g : Z -> W} (hf : IsOpenEmbedding f)
    (hg : IsOpenEmbedding g) : IsOpenEmbedding (Prod.map f g) :=
  .of_isEmbedding_isOpenMap (hf.1.prodMap hg.1) (hf.isOpenMap.prodMap hg.isOpenMap)

/--
lemma `Topology.IsClosedEmbedding.prodMap` / 引理 `Topology.IsClosedEmbedding.prodMap`

English:
lemma Topology.IsClosedEmbedding.prodMap
  statement: {f : X -> Y} {g : Z -> W}
  proof: { hf.isEmbedding.prodMap hg.isEmbedding with
    isClosed_range := range_prodMap ▸ hf.isClosed_range.prod hg.isClosed_range }

中文:
引理 Topology.IsClosedEmbedding.prodMap
  结论: {f : X -> Y} {g : Z -> W}
  证明: { hf.isEmbedding.prodMap hg.isEmbedding with
    isClosed_range := range_prodMap ▸ hf.isClosed_range.prod hg.isClosed_range }
-/
protected lemma Topology.IsClosedEmbedding.prodMap {f : X -> Y} {g : Z -> W}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsClosedEmbedding (Prod.map f g) :=
  { hf.isEmbedding.prodMap hg.isEmbedding with
    isClosed_range := range_prodMap ▸ hf.isClosed_range.prod hg.isClosed_range }

/--
lemma `isEmbedding_graph` / 引理 `isEmbedding_graph`

English:
lemma isEmbedding_graph
  given: {f : X -> Y} (hf : Continuous f)
  statement: IsEmbedding fun x => (x, f x)
  proof: .of_comp (continuous_id.prodMk hf) continuous_fst .id

中文:
引理 isEmbedding_graph
  条件: {f : X -> Y} (hf : Continuous f)
  结论: IsEmbedding fun x => (x, f x)
  证明: .of_comp (continuous_id.prodMk hf) continuous_fst .id

Depends on / 依赖: continuous_fst, continuous_id, continuous_id.prodMk, of_comp, prodMk
-/
lemma isEmbedding_graph {f : X -> Y} (hf : Continuous f) : IsEmbedding fun x => (x, f x) :=
  .of_comp (continuous_id.prodMk hf) continuous_fst .id

/--
lemma `isEmbedding_prodMkLeft` / 引理 `isEmbedding_prodMkLeft`

English:
lemma isEmbedding_prodMkLeft
  given: (y : Y)
  statement: IsEmbedding (fun x : X => (x, y))
  proof: .of_comp (.prodMk_left y) continuous_fst .id

中文:
引理 isEmbedding_prodMkLeft
  条件: (y : Y)
  结论: IsEmbedding (fun x : X => (x, y))
  证明: .of_comp (.prodMk_left y) continuous_fst .id

Depends on / 依赖: continuous_fst, of_comp, prodMk_left
-/
lemma isEmbedding_prodMkLeft (y : Y) : IsEmbedding (fun x : X => (x, y)) :=
  .of_comp (.prodMk_left y) continuous_fst .id

/--
lemma `isEmbedding_prodMkRight` / 引理 `isEmbedding_prodMkRight`

English:
lemma isEmbedding_prodMkRight
  given: (x : X)
  statement: IsEmbedding (Prod.mk x : Y -> X × Y)
  proof: .of_comp (.prodMk_right x) continuous_snd .id

中文:
引理 isEmbedding_prodMkRight
  条件: (x : X)
  结论: IsEmbedding (Prod.mk x : Y -> X × Y)
  证明: .of_comp (.prodMk_right x) continuous_snd .id

Depends on / 依赖: continuous_snd, of_comp, prodMk_right
-/
lemma isEmbedding_prodMkRight (x : X) : IsEmbedding (Prod.mk x : Y -> X × Y) :=
  .of_comp (.prodMk_right x) continuous_snd .id

/--
theorem `IsOpenQuotientMap.prodMap` / 定理 `IsOpenQuotientMap.prodMap`

English:
theorem IsOpenQuotientMap.prodMap
  statement: {f : X -> Y} {g : Z -> W} (hf : IsOpenQuotientMap f)
  proof: ⟨.prodMap hf.1 hg.1, .prodMap hf.2 hg.2, .prodMap hf.3 hg.3⟩

@[simp]

中文:
定理 IsOpenQuotientMap.prodMap
  结论: {f : X -> Y} {g : Z -> W} (hf : IsOpenQuotientMap f)
  证明: ⟨.prodMap hf.1 hg.1, .prodMap hf.2 hg.2, .prodMap hf.3 hg.3⟩

@[simp]

Depends on / 依赖: prodMap
-/
theorem IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z -> W} (hf : IsOpenQuotientMap f)
    (hg : IsOpenQuotientMap g) : IsOpenQuotientMap (Prod.map f g) :=
  ⟨.prodMap hf.1 hg.1, .prodMap hf.2 hg.2, .prodMap hf.3 hg.3⟩

@[simp]
/--
theorem `isOpenQuotientMap_prodMap_iff` / 定理 `isOpenQuotientMap_prodMap_iff`

English:
theorem isOpenQuotientMap_prodMap_iff
  given: [Nonempty X] [Nonempty Z] {f : X -> Y} {g : Z -> W}
  proof: by
  have : Nonempty Y := .map f inferInstance
  have : Nonempty W := .map g inferInstance
  grind [isOpenQuotientMap_iff, continuous_prodMap_iff, isOpenMap_prodMap_iff, Prod.map_surjective]

中文:
定理 isOpenQuotientMap_prodMap_iff
  条件: [Nonempty X] [Nonempty Z] {f : X -> Y} {g : Z -> W}
  证明: by
  have : Nonempty Y := .map f inferInstance
  have : Nonempty W := .map g inferInstance
  grind [isOpenQuotientMap_iff, continuous_prodMap_iff, isOpenMap_prodMap_iff, Prod.map_surjective]

Depends on / 依赖: Nonempty, Prod.map_surjective, continuous_prodMap_iff, isOpenMap_prodMap_iff, isOpenQuotientMap_iff, map_surjective
-/
theorem isOpenQuotientMap_prodMap_iff [Nonempty X] [Nonempty Z] {f : X -> Y} {g : Z -> W} :
    IsOpenQuotientMap (Prod.map f g) ↔ IsOpenQuotientMap f ∧ IsOpenQuotientMap g := by
  have : Nonempty Y := .map f inferInstance
  have : Nonempty W := .map g inferInstance
  grind [isOpenQuotientMap_iff, continuous_prodMap_iff, isOpenMap_prodMap_iff, Prod.map_surjective]

/--
theorem `TopologicalSpace.prod_mono` / 定理 `TopologicalSpace.prod_mono`

English:
theorem TopologicalSpace.prod_mono
  statement: {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
  proof: le_inf (inf_le_left.trans <| induced_mono hσ) (inf_le_right.trans <| induced_mono hτ)

中文:
定理 TopologicalSpace.prod_mono
  结论: {α β : 类型} {σ₁ σ₂ : TopologicalSpace α}
  证明: le_inf (inf_le_left.trans <| induced_mono hσ) (inf_le_right.trans <| induced_mono hτ)

Depends on / 依赖: induced_mono, inf_le_left, inf_le_left.trans, inf_le_right, inf_le_right.trans, le_inf
-/
theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ <= σ₂) (hτ : τ₁ <= τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ <= @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (inf_le_left.trans <| induced_mono hσ) (inf_le_right.trans <| induced_mono hτ)

-- Homeomorphisms between the various product: products of two homeomorphisms,
-- as well as commutativity and associativity. See below for the analogous results for sums,
-- as well as distributivity, etc.
namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  body: h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]

中文:
定义 prodCongr
  签名: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  定义体: h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]

Depends on / 依赖: prodCongr, toEquiv, toEquiv.prodCongr
-/
def prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X × Y ≃ₜ X' × Y' where
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
/--
theorem `prodCongr_symm` / 定理 `prodCongr_symm`

English:
theorem prodCongr_symm
  given: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  proof: rfl

@[simp]

中文:
定理 prodCongr_symm
  条件: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  证明: rfl

@[simp]
-/
theorem prodCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
/--
theorem `coe_prodCongr` / 定理 `coe_prodCongr`

English:
theorem coe_prodCongr
  given: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  statement: ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂
  proof: rfl

中文:
定理 coe_prodCongr
  条件: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  结论: ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂
  证明: rfl
-/
theorem coe_prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

variable (W X Y Z)

/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : X × Y ≃ₜ Y × X where
  body: Equiv.prodComm X Y

@[simp]

中文:
定义 prodComm
  签名: : X × Y ≃ₜ Y × X where
  定义体: Equiv.prodComm X Y

@[simp]

Depends on / 依赖: Equiv.prodComm, prodComm
-/
def prodComm : X × Y ≃ₜ Y × X where
  toEquiv := Equiv.prodComm X Y

@[simp]
/--
theorem `prodComm_symm` / 定理 `prodComm_symm`

English:
theorem prodComm_symm
  statement: (prodComm X Y).symm = prodComm Y X
  proof: rfl

@[simp]

中文:
定理 prodComm_symm
  结论: (prodComm X Y).symm = prodComm Y X
  证明: rfl

@[simp]
-/
theorem prodComm_symm : (prodComm X Y).symm = prodComm Y X :=
  rfl

@[simp]
/--
theorem `coe_prodComm` / 定理 `coe_prodComm`

English:
theorem coe_prodComm
  statement: ⇑(prodComm X Y) = Prod.swap
  proof: rfl

中文:
定理 coe_prodComm
  结论: ⇑(prodComm X Y) = Prod.swap
  证明: rfl
-/
theorem coe_prodComm : ⇑(prodComm X Y) = Prod.swap :=
  rfl

/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : (X × Y) × Z ≃ₜ X × Y × Z where
  body: Equiv.prodAssoc X Y Z

@[simp]

中文:
定义 prodAssoc
  签名: : (X × Y) × Z ≃ₜ X × Y × Z where
  定义体: Equiv.prodAssoc X Y Z

@[simp]

Depends on / 依赖: Equiv.prodAssoc, prodAssoc
-/
def prodAssoc : (X × Y) × Z ≃ₜ X × Y × Z where
  toEquiv := Equiv.prodAssoc X Y Z

@[simp]
/--
lemma `prodAssoc_toEquiv` / 引理 `prodAssoc_toEquiv`

English:
lemma prodAssoc_toEquiv
  statement: (prodAssoc X Y Z).toEquiv = Equiv.prodAssoc X Y Z
  proof: rfl

中文:
引理 prodAssoc_toEquiv
  结论: (prodAssoc X Y Z).toEquiv = Equiv.prodAssoc X Y Z
  证明: rfl
-/
lemma prodAssoc_toEquiv : (prodAssoc X Y Z).toEquiv = Equiv.prodAssoc X Y Z := rfl

/--
Definition of `prodProdProdComm` / `prodProdProdComm` 的定义

English:
definition prodProdProdComm
  signature: : (X × Y) × W × Z ≃ₜ (X × W) × Y × Z where
  body: Equiv.prodProdProdComm X Y W Z

@[simp]

中文:
定义 prodProdProdComm
  签名: : (X × Y) × W × Z ≃ₜ (X × W) × Y × Z where
  定义体: Equiv.prodProdProdComm X Y W Z

@[simp]

Depends on / 依赖: Equiv.prodProdProdComm, prodProdProdComm
-/
def prodProdProdComm : (X × Y) × W × Z ≃ₜ (X × W) × Y × Z where
  toEquiv := Equiv.prodProdProdComm X Y W Z

@[simp]
/--
theorem `prodProdProdComm_symm` / 定理 `prodProdProdComm_symm`

English:
theorem prodProdProdComm_symm
  statement: (prodProdProdComm X Y W Z).symm = prodProdProdComm X W Y Z
  proof: rfl

中文:
定理 prodProdProdComm_symm
  结论: (prodProdProdComm X Y W Z).symm = prodProdProdComm X W Y Z
  证明: rfl
-/
theorem prodProdProdComm_symm : (prodProdProdComm X Y W Z).symm = prodProdProdComm X W Y Z :=
  rfl

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! -fullyApplied apply]
/--
Definition of `prodPUnit` / `prodPUnit` 的定义

English:
definition prodPUnit
  signature: : X × PUnit ≃ₜ X where
  body: Equiv.prodPUnit X

中文:
定义 prodPUnit
  签名: : X × PUnit ≃ₜ X where
  定义体: Equiv.prodPUnit X

Depends on / 依赖: Equiv.prodPUnit, prodPUnit
-/
def prodPUnit : X × PUnit ≃ₜ X where
  toEquiv := Equiv.prodPUnit X

/--
Definition of `punitProd` / `punitProd` 的定义

English:
definition punitProd
  signature: : PUnit × X ≃ₜ X
  body: (prodComm _ _).trans (prodPUnit _)

中文:
定义 punitProd
  签名: : PUnit × X ≃ₜ X
  定义体: (prodComm _ _).trans (prodPUnit _)

Depends on / 依赖: prodComm, prodPUnit
-/
def punitProd : PUnit × X ≃ₜ X :=
  (prodComm _ _).trans (prodPUnit _)

/--
theorem `coe_punitProd` / 定理 `coe_punitProd`

English:
theorem coe_punitProd
  statement: ⇑(punitProd X) = Prod.snd
  proof: rfl

中文:
定理 coe_punitProd
  结论: ⇑(punitProd X) = Prod.snd
  证明: rfl
-/
@[simp] theorem coe_punitProd : ⇑(punitProd X) = Prod.snd := rfl

end Homeomorph

end Prod

section Sum

open Sum

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]

/--
theorem `continuous_sum_dom` / 定理 `continuous_sum_dom`

English:
theorem continuous_sum_dom
  given: {f : X oplus Y -> Z}
  proof: (continuous_sup_dom (t₁ := TopologicalSpace.coinduced Sum.inl _)
    (t₂ := TopologicalSpace.coinduced Sum.inr _)).trans <|
    continuous_coinduced_dom.and continuous_coinduced_dom

中文:
定理 continuous_sum_dom
  条件: {f : X oplus Y -> Z}
  证明: (continuous_sup_dom (t₁ := TopologicalSpace.coinduced Sum.inl _)
    (t₂ := TopologicalSpace.coinduced Sum.inr _)).trans <|
    continuous_coinduced_dom.and continuous_coinduced_dom

Depends on / 依赖: Sum.inl, Sum.inr, TopologicalSpace, TopologicalSpace.coinduced, coinduced, continuous_coinduced_dom, continuous_coinduced_dom.and, continuous_sup_dom
-/
theorem continuous_sum_dom {f : X oplus Y -> Z} :
    Continuous f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr) :=
  (continuous_sup_dom (t₁ := TopologicalSpace.coinduced Sum.inl _)
    (t₂ := TopologicalSpace.coinduced Sum.inr _)).trans <|
    continuous_coinduced_dom.and continuous_coinduced_dom

/--
theorem `continuous_sumElim` / 定理 `continuous_sumElim`

English:
theorem continuous_sumElim
  given: {f : X -> Z} {g : Y -> Z}
  proof: continuous_sum_dom

@[continuity, fun_prop]

中文:
定理 continuous_sumElim
  条件: {f : X -> Z} {g : Y -> Z}
  证明: continuous_sum_dom

@[continuity, fun_prop]

Depends on / 依赖: continuous_sum_dom
-/
theorem continuous_sumElim {f : X -> Z} {g : Y -> Z} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_dom

@[continuity, fun_prop]
/--
theorem `Continuous.sumElim` / 定理 `Continuous.sumElim`

English:
theorem Continuous.sumElim
  given: {f : X -> Z} {g : Y -> Z} (hf : Continuous f) (hg : Continuous g)
  proof: continuous_sumElim.2 ⟨hf, hg⟩

@[continuity, fun_prop]

中文:
定理 Continuous.sumElim
  条件: {f : X -> Z} {g : Y -> Z} (hf : Continuous f) (hg : Continuous g)
  证明: continuous_sumElim.2 ⟨hf, hg⟩

@[continuity, fun_prop]

Depends on / 依赖: continuous_sumElim
-/
theorem Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sumElim.2 ⟨hf, hg⟩

@[continuity, fun_prop]
/--
theorem `continuous_isLeft` / 定理 `continuous_isLeft`

English:
theorem continuous_isLeft
  statement: Continuous (isLeft : X oplus Y -> Bool)
  proof: continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]

中文:
定理 continuous_isLeft
  结论: Continuous (isLeft : X oplus Y -> 布尔)
  证明: continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]

Depends on / 依赖: continuous_const, continuous_sum_dom
-/
theorem continuous_isLeft : Continuous (isLeft : X oplus Y -> Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
/--
theorem `continuous_isRight` / 定理 `continuous_isRight`

English:
theorem continuous_isRight
  statement: Continuous (isRight : X oplus Y -> Bool)
  proof: continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]

中文:
定理 continuous_isRight
  结论: Continuous (isRight : X oplus Y -> 布尔)
  证明: continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]

Depends on / 依赖: continuous_const, continuous_sum_dom
-/
theorem continuous_isRight : Continuous (isRight : X oplus Y -> Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
/--
theorem `continuous_inl` / 定理 `continuous_inl`

English:
theorem continuous_inl
  statement: Continuous (@inl X Y)
  proof: ⟨fun _ => And.left⟩

@[continuity, fun_prop]

中文:
定理 continuous_inl
  结论: Continuous (@inl X Y)
  证明: ⟨fun _ => And.left⟩

@[continuity, fun_prop]

Depends on / 依赖: And.left
-/
theorem continuous_inl : Continuous (@inl X Y) := ⟨fun _ => And.left⟩

@[continuity, fun_prop]
/--
theorem `continuous_inr` / 定理 `continuous_inr`

English:
theorem continuous_inr
  statement: Continuous (@inr X Y)
  proof: ⟨fun _ => And.right⟩

@[fun_prop, continuity]

中文:
定理 continuous_inr
  结论: Continuous (@inr X Y)
  证明: ⟨fun _ => And.right⟩

@[fun_prop, continuity]

Depends on / 依赖: And.right
-/
theorem continuous_inr : Continuous (@inr X Y) := ⟨fun _ => And.right⟩

@[fun_prop, continuity]
/--
lemma `continuous_sum_swap` / 引理 `continuous_sum_swap`

English:
lemma continuous_sum_swap
  statement: Continuous (@Sum.swap X Y)
  proof: Continuous.sumElim continuous_inr continuous_inl

中文:
引理 continuous_sum_swap
  结论: Continuous (@Sum.swap X Y)
  证明: Continuous.sumElim continuous_inr continuous_inl

Depends on / 依赖: Continuous, Continuous.sumElim, continuous_inl, continuous_inr, sumElim
-/
lemma continuous_sum_swap : Continuous (@Sum.swap X Y) :=
  Continuous.sumElim continuous_inr continuous_inl

/--
theorem `isOpen_sum_iff` / 定理 `isOpen_sum_iff`

English:
theorem isOpen_sum_iff
  given: {s : Set (X oplus Y)}
  statement: IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s)
  proof: Iff.rfl

中文:
定理 isOpen_sum_iff
  条件: {s : Set (X oplus Y)}
  结论: IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_sum_iff {s : Set (X oplus Y)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl

/--
theorem `isClosed_sum_iff` / 定理 `isClosed_sum_iff`

English:
theorem isClosed_sum_iff
  given: {s : Set (X oplus Y)}
  proof: by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]

中文:
定理 isClosed_sum_iff
  条件: {s : Set (X oplus Y)}
  证明: by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]

Depends on / 依赖: isOpen_compl_iff, isOpen_sum_iff, preimage_compl
-/
theorem isClosed_sum_iff {s : Set (X oplus Y)} :
    IsClosed s ↔ IsClosed (inl ⁻¹' s) ∧ IsClosed (inr ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]

/--
theorem `isOpenMap_inl` / 定理 `isOpenMap_inl`

English:
theorem isOpenMap_inl
  statement: IsOpenMap (@inl X Y)
  proof: fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]

中文:
定理 isOpenMap_inl
  结论: IsOpenMap (@inl X Y)
  证明: fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]

Depends on / 依赖: Sum.inl_injective, inl_injective, isOpen_sum_iff, preimage_image_eq
-/
theorem isOpenMap_inl : IsOpenMap (@inl X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]

/--
theorem `isOpenMap_inr` / 定理 `isOpenMap_inr`

English:
theorem isOpenMap_inr
  statement: IsOpenMap (@inr X Y)
  proof: fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]

中文:
定理 isOpenMap_inr
  结论: IsOpenMap (@inr X Y)
  证明: fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]

Depends on / 依赖: Sum.inr_injective, inr_injective, isOpen_sum_iff, preimage_image_eq
-/
theorem isOpenMap_inr : IsOpenMap (@inr X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]

/--
theorem `isClosedMap_inl` / 定理 `isClosedMap_inl`

English:
theorem isClosedMap_inl
  statement: IsClosedMap (@inl X Y)
  proof: fun u hu => by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inl_injective]

中文:
定理 isClosedMap_inl
  结论: IsClosedMap (@inl X Y)
  证明: fun u hu => by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inl_injective]

Depends on / 依赖: Sum.inl_injective, inl_injective, isClosed_sum_iff, preimage_image_eq
-/
theorem isClosedMap_inl : IsClosedMap (@inl X Y) := fun u hu => by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inl_injective]

/--
theorem `isClosedMap_inr` / 定理 `isClosedMap_inr`

English:
theorem isClosedMap_inr
  statement: IsClosedMap (@inr X Y)
  proof: fun u hu => by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inr_injective]

中文:
定理 isClosedMap_inr
  结论: IsClosedMap (@inr X Y)
  证明: fun u hu => by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inr_injective]

Depends on / 依赖: Sum.inr_injective, inr_injective, isClosed_sum_iff, preimage_image_eq
-/
theorem isClosedMap_inr : IsClosedMap (@inr X Y) := fun u hu => by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inr_injective]

/--
lemma `Topology.IsOpenEmbedding.inl` / 引理 `Topology.IsOpenEmbedding.inl`

English:
lemma Topology.IsOpenEmbedding.inl
  statement: IsOpenEmbedding (@inl X Y)
  proof: .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl

中文:
引理 Topology.IsOpenEmbedding.inl
  结论: IsOpenEmbedding (@inl X Y)
  证明: .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl
-/
protected lemma Topology.IsOpenEmbedding.inl : IsOpenEmbedding (@inl X Y) :=
  .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl

/--
lemma `Topology.IsOpenEmbedding.inr` / 引理 `Topology.IsOpenEmbedding.inr`

English:
lemma Topology.IsOpenEmbedding.inr
  statement: IsOpenEmbedding (@inr X Y)
  proof: .of_continuous_injective_isOpenMap continuous_inr inr_injective isOpenMap_inr

中文:
引理 Topology.IsOpenEmbedding.inr
  结论: IsOpenEmbedding (@inr X Y)
  证明: .of_continuous_injective_isOpenMap continuous_inr inr_injective isOpenMap_inr
-/
protected lemma Topology.IsOpenEmbedding.inr : IsOpenEmbedding (@inr X Y) :=
  .of_continuous_injective_isOpenMap continuous_inr inr_injective isOpenMap_inr

/--
lemma `Topology.IsEmbedding.inl` / 引理 `Topology.IsEmbedding.inl`

English:
lemma Topology.IsEmbedding.inl
  statement: IsEmbedding (@inl X Y)
  proof: IsOpenEmbedding.inl.1

中文:
引理 Topology.IsEmbedding.inl
  结论: IsEmbedding (@inl X Y)
  证明: IsOpenEmbedding.inl.1
-/
protected lemma Topology.IsEmbedding.inl : IsEmbedding (@inl X Y) := IsOpenEmbedding.inl.1
/--
lemma `Topology.IsEmbedding.inr` / 引理 `Topology.IsEmbedding.inr`

English:
lemma Topology.IsEmbedding.inr
  statement: IsEmbedding (@inr X Y)
  proof: IsOpenEmbedding.inr.1

中文:
引理 Topology.IsEmbedding.inr
  结论: IsEmbedding (@inr X Y)
  证明: IsOpenEmbedding.inr.1
-/
protected lemma Topology.IsEmbedding.inr : IsEmbedding (@inr X Y) := IsOpenEmbedding.inr.1

/--
lemma `isOpen_range_inl` / 引理 `isOpen_range_inl`

English:
lemma isOpen_range_inl
  statement: IsOpen (range (inl : X -> X oplus Y))
  proof: IsOpenEmbedding.inl.2

中文:
引理 isOpen_range_inl
  结论: IsOpen (range (inl : X -> X oplus Y))
  证明: IsOpenEmbedding.inl.2

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.inl
-/
lemma isOpen_range_inl : IsOpen (range (inl : X -> X oplus Y)) := IsOpenEmbedding.inl.2
/--
lemma `isOpen_range_inr` / 引理 `isOpen_range_inr`

English:
lemma isOpen_range_inr
  statement: IsOpen (range (inr : Y -> X oplus Y))
  proof: IsOpenEmbedding.inr.2

中文:
引理 isOpen_range_inr
  结论: IsOpen (range (inr : Y -> X oplus Y))
  证明: IsOpenEmbedding.inr.2

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.inr
-/
lemma isOpen_range_inr : IsOpen (range (inr : Y -> X oplus Y)) := IsOpenEmbedding.inr.2

/--
theorem `isClosed_range_inl` / 定理 `isClosed_range_inl`

English:
theorem isClosed_range_inl
  statement: IsClosed (range (inl : X -> X oplus Y))
  proof: by
  rw [← isOpen_compl_iff]; rw [compl_range_inl]
  exact isOpen_range_inr

中文:
定理 isClosed_range_inl
  结论: IsClosed (range (inl : X -> X oplus Y))
  证明: by
  rw [← isOpen_compl_iff]; rw [compl_range_inl]
  exact isOpen_range_inr

Depends on / 依赖: compl_range_inl, isOpen_compl_iff, isOpen_range_inr
-/
theorem isClosed_range_inl : IsClosed (range (inl : X -> X oplus Y)) := by
  rw [← isOpen_compl_iff]; rw [compl_range_inl]
  exact isOpen_range_inr

/--
theorem `isClosed_range_inr` / 定理 `isClosed_range_inr`

English:
theorem isClosed_range_inr
  statement: IsClosed (range (inr : Y -> X oplus Y))
  proof: by
  rw [← isOpen_compl_iff]; rw [compl_range_inr]
  exact isOpen_range_inl

中文:
定理 isClosed_range_inr
  结论: IsClosed (range (inr : Y -> X oplus Y))
  证明: by
  rw [← isOpen_compl_iff]; rw [compl_range_inr]
  exact isOpen_range_inl

Depends on / 依赖: compl_range_inr, isOpen_compl_iff, isOpen_range_inl
-/
theorem isClosed_range_inr : IsClosed (range (inr : Y -> X oplus Y)) := by
  rw [← isOpen_compl_iff]; rw [compl_range_inr]
  exact isOpen_range_inl

/--
theorem `Topology.IsClosedEmbedding.inl` / 定理 `Topology.IsClosedEmbedding.inl`

English:
theorem Topology.IsClosedEmbedding.inl
  statement: IsClosedEmbedding (inl : X -> X oplus Y)
  proof: ⟨.inl, isClosed_range_inl⟩

中文:
定理 Topology.IsClosedEmbedding.inl
  结论: IsClosedEmbedding (inl : X -> X oplus Y)
  证明: ⟨.inl, isClosed_range_inl⟩

Depends on / 依赖: isClosed_range_inl
-/
theorem Topology.IsClosedEmbedding.inl : IsClosedEmbedding (inl : X -> X oplus Y) :=
  ⟨.inl, isClosed_range_inl⟩

/--
theorem `Topology.IsClosedEmbedding.inr` / 定理 `Topology.IsClosedEmbedding.inr`

English:
theorem Topology.IsClosedEmbedding.inr
  statement: IsClosedEmbedding (inr : Y -> X oplus Y)
  proof: ⟨.inr, isClosed_range_inr⟩

中文:
定理 Topology.IsClosedEmbedding.inr
  结论: IsClosedEmbedding (inr : Y -> X oplus Y)
  证明: ⟨.inr, isClosed_range_inr⟩

Depends on / 依赖: isClosed_range_inr
-/
theorem Topology.IsClosedEmbedding.inr : IsClosedEmbedding (inr : Y -> X oplus Y) :=
  ⟨.inr, isClosed_range_inr⟩

/--
theorem `nhds_inl` / 定理 `nhds_inl`

English:
theorem nhds_inl
  given: (x : X)
  statement: 𝓝 (inl x : X oplus Y) = map inl (𝓝 x)
  proof: (IsOpenEmbedding.inl.map_nhds_eq _).symm

中文:
定理 nhds_inl
  条件: (x : X)
  结论: 𝓝 (inl x : X oplus Y) = map inl (𝓝 x)
  证明: (IsOpenEmbedding.inl.map_nhds_eq _).symm

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.inl.map_nhds_eq, map_nhds_eq
-/
theorem nhds_inl (x : X) : 𝓝 (inl x : X oplus Y) = map inl (𝓝 x) :=
  (IsOpenEmbedding.inl.map_nhds_eq _).symm

/--
theorem `nhds_inr` / 定理 `nhds_inr`

English:
theorem nhds_inr
  given: (y : Y)
  statement: 𝓝 (inr y : X oplus Y) = map inr (𝓝 y)
  proof: (IsOpenEmbedding.inr.map_nhds_eq _).symm

@[simp]

中文:
定理 nhds_inr
  条件: (y : Y)
  结论: 𝓝 (inr y : X oplus Y) = map inr (𝓝 y)
  证明: (IsOpenEmbedding.inr.map_nhds_eq _).symm

@[simp]

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.inr.map_nhds_eq, map_nhds_eq
-/
theorem nhds_inr (y : Y) : 𝓝 (inr y : X oplus Y) = map inr (𝓝 y) :=
  (IsOpenEmbedding.inr.map_nhds_eq _).symm

@[simp]
/--
theorem `continuous_sumMap` / 定理 `continuous_sumMap`

English:
theorem continuous_sumMap
  given: {f : X -> Y} {g : Z -> W}
  proof: continuous_sumElim.trans
    IsEmbedding.inl.continuous_iff.symm.and IsEmbedding.inr.continuous_iff.symm

@[continuity, fun_prop]

中文:
定理 continuous_sumMap
  条件: {f : X -> Y} {g : Z -> W}
  证明: continuous_sumElim.trans
    IsEmbedding.inl.continuous_iff.symm.and IsEmbedding.inr.continuous_iff.symm

@[continuity, fun_prop]

Depends on / 依赖: IsEmbedding, IsEmbedding.inl.continuous_iff.symm.and, IsEmbedding.inr.continuous_iff.symm, continuous_iff, continuous_sumElim, continuous_sumElim.trans
-/
theorem continuous_sumMap {f : X -> Y} {g : Z -> W} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
continuous_sumElim.trans
    IsEmbedding.inl.continuous_iff.symm.and IsEmbedding.inr.continuous_iff.symm

@[continuity, fun_prop]
/--
theorem `Continuous.sumMap` / 定理 `Continuous.sumMap`

English:
theorem Continuous.sumMap
  given: {f : X -> Y} {g : Z -> W} (hf : Continuous f) (hg : Continuous g)
  proof: continuous_sumMap.2 ⟨hf, hg⟩

中文:
定理 Continuous.sumMap
  条件: {f : X -> Y} {g : Z -> W} (hf : Continuous f) (hg : Continuous g)
  证明: continuous_sumMap.2 ⟨hf, hg⟩

Depends on / 依赖: continuous_sumMap
-/
theorem Continuous.sumMap {f : X -> Y} {g : Z -> W} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sumMap.2 ⟨hf, hg⟩

/--
theorem `isOpenMap_sum` / 定理 `isOpenMap_sum`

English:
theorem isOpenMap_sum
  given: {f : X oplus Y -> Z}
  proof: by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp_def]

中文:
定理 isOpenMap_sum
  条件: {f : X oplus Y -> Z}
  证明: by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp_def]

Depends on / 依赖: Filter, Filter.map_map, Sum.forall, comp_def, isOpenMap_iff_nhds_le, map_map, nhds_inl, nhds_inr
-/
theorem isOpenMap_sum {f : X oplus Y -> Z} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp_def]

/--
theorem `IsOpenMap.sumMap` / 定理 `IsOpenMap.sumMap`

English:
theorem IsOpenMap.sumMap
  given: {f : X -> Y} {g : Z -> W} (hf : IsOpenMap f) (hg : IsOpenMap g)
  proof: isOpenMap_sum.2 ⟨isOpenMap_inl.comp hf, isOpenMap_inr.comp hg⟩

@[simp]

中文:
定理 IsOpenMap.sumMap
  条件: {f : X -> Y} {g : Z -> W} (hf : IsOpenMap f) (hg : IsOpenMap g)
  证明: isOpenMap_sum.2 ⟨isOpenMap_inl.comp hf, isOpenMap_inr.comp hg⟩

@[simp]

Depends on / 依赖: isOpenMap_inl, isOpenMap_inl.comp, isOpenMap_inr, isOpenMap_inr.comp, isOpenMap_sum
-/
theorem IsOpenMap.sumMap {f : X -> Y} {g : Z -> W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.map f g) :=
  isOpenMap_sum.2 ⟨isOpenMap_inl.comp hf, isOpenMap_inr.comp hg⟩

@[simp]
/--
theorem `isOpenMap_sumElim` / 定理 `isOpenMap_sumElim`

English:
theorem isOpenMap_sumElim
  given: {f : X -> Z} {g : Y -> Z}
  proof: by
  simp only [isOpenMap_sum, elim_inl, elim_inr]

中文:
定理 isOpenMap_sumElim
  条件: {f : X -> Z} {g : Y -> Z}
  证明: by
  simp only [isOpenMap_sum, elim_inl, elim_inr]

Depends on / 依赖: elim_inl, elim_inr, isOpenMap_sum
-/
theorem isOpenMap_sumElim {f : X -> Z} {g : Y -> Z} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [isOpenMap_sum, elim_inl, elim_inr]

/--
theorem `IsOpenMap.sumElim` / 定理 `IsOpenMap.sumElim`

English:
theorem IsOpenMap.sumElim
  given: {f : X -> Z} {g : Y -> Z} (hf : IsOpenMap f) (hg : IsOpenMap g)
  proof: isOpenMap_sumElim.2 ⟨hf, hg⟩

中文:
定理 IsOpenMap.sumElim
  条件: {f : X -> Z} {g : Y -> Z} (hf : IsOpenMap f) (hg : IsOpenMap g)
  证明: isOpenMap_sumElim.2 ⟨hf, hg⟩

Depends on / 依赖: isOpenMap_sumElim
-/
theorem IsOpenMap.sumElim {f : X -> Z} {g : Y -> Z} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  isOpenMap_sumElim.2 ⟨hf, hg⟩

/--
lemma `Topology.IsOpenEmbedding.sumElim` / 引理 `Topology.IsOpenEmbedding.sumElim`

English:
lemma Topology.IsOpenEmbedding.sumElim
  statement: {f : X -> Z} {g : Y -> Z}
  proof: by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

中文:
引理 Topology.IsOpenEmbedding.sumElim
  结论: {f : X -> Z} {g : Y -> Z}
  证明: by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

Depends on / 依赖: isOpenEmbedding_iff_continuous_injective_isOpenMap, sumElim
-/
lemma Topology.IsOpenEmbedding.sumElim {f : X -> Z} {g : Y -> Z}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (h : Injective (Sum.elim f g)) :
    IsOpenEmbedding (Sum.elim f g) := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

/--
theorem `isClosedMap_sum` / 定理 `isClosedMap_sum`

English:
theorem isClosedMap_sum
  given: {f : X oplus Y -> Z}
  proof: by
  constructor
  · intro h
    exact ⟨h.comp IsClosedEmbedding.inl.isClosedMap, h.comp IsClosedEmbedding.inr.isClosedMap⟩
  · rintro h Z hZ
    rw [isClosed_sum_iff] at hZ
    convert! (h.1 _ hZ.1).union (h.2 _ hZ.2)
    ext
    simp only [mem_image, Sum.exists, mem_union, mem_preimage]

中文:
定理 isClosedMap_sum
  条件: {f : X oplus Y -> Z}
  证明: by
  constructor
  · intro h
    exact ⟨h.comp IsClosedEmbedding.inl.isClosedMap, h.comp IsClosedEmbedding.inr.isClosedMap⟩
  · rintro h Z hZ
    rw [isClosed_sum_iff] at hZ
    convert! (h.1 _ hZ.1).union (h.2 _ hZ.2)
    ext
    simp only [mem_image, Sum.exists, mem_union, mem_preimage]

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.inl.isClosedMap, IsClosedEmbedding.inr.isClosedMap, Sum.exists, convert, h.comp, isClosedMap, isClosed_sum_iff, mem_image, mem_preimage, mem_union
-/
theorem isClosedMap_sum {f : X oplus Y -> Z} :
    IsClosedMap f ↔ (IsClosedMap fun a => f (.inl a)) ∧ IsClosedMap fun b => f (.inr b) := by
  constructor
  · intro h
    exact ⟨h.comp IsClosedEmbedding.inl.isClosedMap, h.comp IsClosedEmbedding.inr.isClosedMap⟩
  · rintro h Z hZ
    rw [isClosed_sum_iff] at hZ
    convert! (h.1 _ hZ.1).union (h.2 _ hZ.2)
    ext
    simp only [mem_image, Sum.exists, mem_union, mem_preimage]

/--
theorem `IsClosedMap.sumMap` / 定理 `IsClosedMap.sumMap`

English:
theorem IsClosedMap.sumMap
  given: {f : X -> Y} {g : Z -> W} (hf : IsClosedMap f) (hg : IsClosedMap g)
  proof: isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf, isClosedMap_inr.comp hg⟩

@[simp]

中文:
定理 IsClosedMap.sumMap
  条件: {f : X -> Y} {g : Z -> W} (hf : IsClosedMap f) (hg : IsClosedMap g)
  证明: isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf, isClosedMap_inr.comp hg⟩

@[simp]

Depends on / 依赖: isClosedMap_inl, isClosedMap_inl.comp, isClosedMap_inr, isClosedMap_inr.comp, isClosedMap_sum
-/
theorem IsClosedMap.sumMap {f : X -> Y} {g : Z -> W} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.map f g) :=
  isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf, isClosedMap_inr.comp hg⟩

@[simp]
/--
theorem `isClosedMap_sumElim` / 定理 `isClosedMap_sumElim`

English:
theorem isClosedMap_sumElim
  given: {f : X -> Z} {g : Y -> Z}
  proof: by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]

中文:
定理 isClosedMap_sumElim
  条件: {f : X -> Z} {g : Y -> Z}
  证明: by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]

Depends on / 依赖: Sum.elim_inl, Sum.elim_inr, elim_inl, elim_inr, isClosedMap_sum
-/
theorem isClosedMap_sumElim {f : X -> Z} {g : Y -> Z} :
    IsClosedMap (Sum.elim f g) ↔ IsClosedMap f ∧ IsClosedMap g := by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]

/--
theorem `IsClosedMap.sumElim` / 定理 `IsClosedMap.sumElim`

English:
theorem IsClosedMap.sumElim
  given: {f : X -> Z} {g : Y -> Z} (hf : IsClosedMap f) (hg : IsClosedMap g)
  proof: isClosedMap_sumElim.2 ⟨hf, hg⟩

中文:
定理 IsClosedMap.sumElim
  条件: {f : X -> Z} {g : Y -> Z} (hf : IsClosedMap f) (hg : IsClosedMap g)
  证明: isClosedMap_sumElim.2 ⟨hf, hg⟩

Depends on / 依赖: isClosedMap_sumElim
-/
theorem IsClosedMap.sumElim {f : X -> Z} {g : Y -> Z} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.elim f g) :=
  isClosedMap_sumElim.2 ⟨hf, hg⟩

/--
lemma `Topology.IsClosedEmbedding.sumElim` / 引理 `Topology.IsClosedEmbedding.sumElim`

English:
lemma Topology.IsClosedEmbedding.sumElim
  statement: {f : X -> Z} {g : Y -> Z}
  proof: by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

中文:
引理 Topology.IsClosedEmbedding.sumElim
  结论: {f : X -> Z} {g : Y -> Z}
  证明: by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap, isClosedEmbedding_iff_continuous_injective_isClosedMap, sumElim
-/
lemma Topology.IsClosedEmbedding.sumElim {f : X -> Z} {g : Y -> Z}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) (h : Injective (Sum.elim f g)) :
    IsClosedEmbedding (Sum.elim f g) := by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

-- Homeomorphisms between the various constructions: sums of two homeomorphisms,
-- as well as commutativity, associativity and distributivity with products.
namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `sumCongr` / `sumCongr` 的定义

English:
definition sumCongr
  signature: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  body: h₁.toEquiv.sumCongr h₂.toEquiv

@[simp]

中文:
定义 sumCongr
  签名: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  定义体: h₁.toEquiv.sumCongr h₂.toEquiv

@[simp]

Depends on / 依赖: sumCongr, toEquiv, toEquiv.sumCongr
-/
def sumCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X oplus Y ≃ₜ X' oplus Y' where
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv

@[simp]
/--
lemma `sumCongr_symm` / 引理 `sumCongr_symm`

English:
lemma sumCongr_symm
  given: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  proof: rfl

@[simp]

中文:
引理 sumCongr_symm
  条件: (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y')
  证明: rfl

@[simp]
-/
lemma sumCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
    (sumCongr h₁ h₂).symm = sumCongr h₁.symm h₂.symm := rfl

@[simp]
/--
theorem `sumCongr_refl` / 定理 `sumCongr_refl`

English:
theorem sumCongr_refl
  statement: sumCongr (.refl X) (.refl Y) = .refl (X oplus Y)
  proof: by
  ext i
  cases i <;> rfl

@[simp]

中文:
定理 sumCongr_refl
  结论: sumCongr (.refl X) (.refl Y) = .refl (X oplus Y)
  证明: by
  ext i
  cases i <;> rfl

@[simp]
-/
theorem sumCongr_refl : sumCongr (.refl X) (.refl Y) = .refl (X oplus Y) := by
  ext i
  cases i <;> rfl

@[simp]
/--
theorem `sumCongr_trans` / 定理 `sumCongr_trans`

English:
theorem sumCongr_trans
  statement: {X'' Y'' : Type*} [TopologicalSpace X''] [TopologicalSpace Y'']
  proof: by
  ext i
  cases i <;> rfl

中文:
定理 sumCongr_trans
  结论: {X'' Y'' : 类型} [TopologicalSpace X''] [TopologicalSpace Y'']
  证明: by
  ext i
  cases i <;> rfl
-/
theorem sumCongr_trans {X'' Y'' : Type*} [TopologicalSpace X''] [TopologicalSpace Y'']
    (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') (h₃ : X' ≃ₜ X'') (h₄ : Y' ≃ₜ Y'') :
    (sumCongr h₁ h₂).trans (sumCongr h₃ h₄) = sumCongr (h₁.trans h₃) (h₂.trans h₄) := by
  ext i
  cases i <;> rfl

variable (W X Y Z)

/--
Definition of `sumComm` / `sumComm` 的定义

English:
definition sumComm
  signature: : X oplus Y ≃ₜ Y oplus X where
  body: Equiv.sumComm X Y

@[simp]

中文:
定义 sumComm
  签名: : X oplus Y ≃ₜ Y oplus X where
  定义体: Equiv.sumComm X Y

@[simp]

Depends on / 依赖: Equiv.sumComm, sumComm
-/
def sumComm : X oplus Y ≃ₜ Y oplus X where
  toEquiv := Equiv.sumComm X Y

@[simp]
/--
theorem `sumComm_symm` / 定理 `sumComm_symm`

English:
theorem sumComm_symm
  statement: (sumComm X Y).symm = sumComm Y X
  proof: rfl

@[simp]

中文:
定理 sumComm_symm
  结论: (sumComm X Y).symm = sumComm Y X
  证明: rfl

@[simp]
-/
theorem sumComm_symm : (sumComm X Y).symm = sumComm Y X :=
  rfl

@[simp]
/--
theorem `coe_sumComm` / 定理 `coe_sumComm`

English:
theorem coe_sumComm
  statement: ⇑(sumComm X Y) = Sum.swap
  proof: rfl

@[continuity, fun_prop]

中文:
定理 coe_sumComm
  结论: ⇑(sumComm X Y) = Sum.swap
  证明: rfl

@[continuity, fun_prop]
-/
theorem coe_sumComm : ⇑(sumComm X Y) = Sum.swap :=
  rfl

@[continuity, fun_prop]
/--
lemma `continuous_sumAssoc` / 引理 `continuous_sumAssoc`

English:
lemma continuous_sumAssoc
  statement: Continuous (Equiv.sumAssoc X Y Z)
  proof: Continuous.sumElim (by fun_prop) (by fun_prop)

@[continuity, fun_prop]

中文:
引理 continuous_sumAssoc
  结论: Continuous (Equiv.sumAssoc X Y Z)
  证明: Continuous.sumElim (by fun_prop) (by fun_prop)

@[continuity, fun_prop]

Depends on / 依赖: Continuous, Continuous.sumElim, fun_prop, sumElim
-/
lemma continuous_sumAssoc : Continuous (Equiv.sumAssoc X Y Z) :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

@[continuity, fun_prop]
/--
lemma `continuous_sumAssoc_symm` / 引理 `continuous_sumAssoc_symm`

English:
lemma continuous_sumAssoc_symm
  statement: Continuous (Equiv.sumAssoc X Y Z).symm
  proof: Continuous.sumElim (by fun_prop) (by fun_prop)

中文:
引理 continuous_sumAssoc_symm
  结论: Continuous (Equiv.sumAssoc X Y Z).symm
  证明: Continuous.sumElim (by fun_prop) (by fun_prop)

Depends on / 依赖: Continuous, Continuous.sumElim, fun_prop, sumElim
-/
lemma continuous_sumAssoc_symm : Continuous (Equiv.sumAssoc X Y Z).symm :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

/--
Definition of `sumAssoc` / `sumAssoc` 的定义

English:
definition sumAssoc
  signature: : (X oplus Y) oplus Z ≃ₜ X oplus Y oplus Z where
  body: Equiv.sumAssoc X Y Z

@[simp]

中文:
定义 sumAssoc
  签名: : (X oplus Y) oplus Z ≃ₜ X oplus Y oplus Z where
  定义体: Equiv.sumAssoc X Y Z

@[simp]

Depends on / 依赖: Equiv.sumAssoc, sumAssoc
-/
def sumAssoc : (X oplus Y) oplus Z ≃ₜ X oplus Y oplus Z where
  toEquiv := Equiv.sumAssoc X Y Z

@[simp]
/--
lemma `sumAssoc_toEquiv` / 引理 `sumAssoc_toEquiv`

English:
lemma sumAssoc_toEquiv
  statement: (sumAssoc X Y Z).toEquiv = Equiv.sumAssoc X Y Z
  proof: rfl

中文:
引理 sumAssoc_toEquiv
  结论: (sumAssoc X Y Z).toEquiv = Equiv.sumAssoc X Y Z
  证明: rfl
-/
lemma sumAssoc_toEquiv : (sumAssoc X Y Z).toEquiv = Equiv.sumAssoc X Y Z := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `sumSumSumComm` / `sumSumSumComm` 的定义

English:
definition sumSumSumComm
  signature: : (X oplus Y) oplus W oplus Z ≃ₜ (X oplus W) oplus Y oplus Z where
  body: Equiv.sumSumSumComm X Y W Z

@[simp]

中文:
定义 sumSumSumComm
  签名: : (X oplus Y) oplus W oplus Z ≃ₜ (X oplus W) oplus Y oplus Z where
  定义体: Equiv.sumSumSumComm X Y W Z

@[simp]

Depends on / 依赖: Equiv.sumSumSumComm, sumSumSumComm
-/
def sumSumSumComm : (X oplus Y) oplus W oplus Z ≃ₜ (X oplus W) oplus Y oplus Z where
  toEquiv := Equiv.sumSumSumComm X Y W Z

@[simp]
/--
lemma `sumSumSumComm_toEquiv` / 引理 `sumSumSumComm_toEquiv`

English:
lemma sumSumSumComm_toEquiv
  statement: (sumSumSumComm W X Y Z).toEquiv = (Equiv.sumSumSumComm W X Y Z)
  proof: rfl

@[simp]

中文:
引理 sumSumSumComm_toEquiv
  结论: (sumSumSumComm W X Y Z).toEquiv = (Equiv.sumSumSumComm W X Y Z)
  证明: rfl

@[simp]
-/
lemma sumSumSumComm_toEquiv : (sumSumSumComm W X Y Z).toEquiv = (Equiv.sumSumSumComm W X Y Z) := rfl

@[simp]
/--
lemma `sumSumSumComm_symm` / 引理 `sumSumSumComm_symm`

English:
lemma sumSumSumComm_symm
  statement: (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z)
  proof: rfl

中文:
引理 sumSumSumComm_symm
  结论: (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z)
  证明: rfl
-/
lemma sumSumSumComm_symm : (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z) := rfl

/-- The sum of `X` with any empty topological space is homeomorphic to `X`. -/
@[simps! -fullyApplied apply]
/--
Definition of `sumEmpty` / `sumEmpty` 的定义

English:
definition sumEmpty
  signature: [IsEmpty Y]
  body: Equiv.sumEmpty X Y

中文:
定义 sumEmpty
  签名: [IsEmpty Y]
  定义体: Equiv.sumEmpty X Y

Depends on / 依赖: Equiv.sumEmpty, sumEmpty
-/
def sumEmpty [IsEmpty Y] : X oplus Y ≃ₜ X where
  toEquiv := Equiv.sumEmpty X Y

/--
Definition of `emptySum` / `emptySum` 的定义

English:
definition emptySum
  signature: [IsEmpty Y]
  body: (sumComm Y X).trans (sumEmpty X Y)

中文:
定义 emptySum
  签名: [IsEmpty Y]
  定义体: (sumComm Y X).trans (sumEmpty X Y)

Depends on / 依赖: sumComm, sumEmpty
-/
def emptySum [IsEmpty Y] : Y oplus X ≃ₜ X := (sumComm Y X).trans (sumEmpty X Y)

/--
theorem `coe_emptySum` / 定理 `coe_emptySum`

English:
theorem coe_emptySum
  given: [IsEmpty Y]
  statement: (emptySum X Y).toEquiv = Equiv.emptySum Y X
  proof: rfl

中文:
定理 coe_emptySum
  条件: [IsEmpty Y]
  结论: (emptySum X Y).toEquiv = Equiv.emptySum Y X
  证明: rfl
-/
@[simp] theorem coe_emptySum [IsEmpty Y] : (emptySum X Y).toEquiv = Equiv.emptySum Y X := rfl

variable {W X Y Z}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `(X ⊕ Y) × Z` is homeomorphic to `X × Z ⊕ Y × Z`. -/
@[simps!]
/--
Definition of `sumProdDistrib` / `sumProdDistrib` 的定义

English:
definition sumProdDistrib
  signature: : (X oplus Y) × Z ≃ₜ (X × Z) oplus (Y × Z)
  body: Homeomorph.symm
    (Equiv.sumProdDistrib X Y Z).symm.toHomeomorphOfContinuousOpen
        ((continuous_inl.prodMap continuous_id).sumElim
          (continuous_inr.prodMap continuous_id)) <|
      (isOpenMap_inl.prodMap IsOpenMap.id).sumElim (isOpenMap_inr.prodMap IsOpenMap.id)

中文:
定义 sumProdDistrib
  签名: : (X oplus Y) × Z ≃ₜ (X × Z) oplus (Y × Z)
  定义体: Homeomorph.symm
    (Equiv.sumProdDistrib X Y Z).symm.toHomeomorphOfContinuousOpen
        ((continuous_inl.prodMap continuous_id).sumElim
          (continuous_inr.prodMap continuous_id)) <|
      (isOpenMap_inl.prodMap IsOpenMap.id).sumElim (isOpenMap_inr.prodMap IsOpenMap.id)

Depends on / 依赖: Equiv.sumProdDistrib, Homeomorph, Homeomorph.symm, IsOpenMap, IsOpenMap.id, continuous_id, continuous_inl, continuous_inl.prodMap, continuous_inr, continuous_inr.prodMap, isOpenMap_inl, isOpenMap_inl.prodMap, isOpenMap_inr, isOpenMap_inr.prodMap, prodMap, sumElim, sumProdDistrib, symm.toHomeomorphOfContinuousOpen, toHomeomorphOfContinuousOpen
-/
def sumProdDistrib : (X oplus Y) × Z ≃ₜ (X × Z) oplus (Y × Z) :=
Homeomorph.symm
    (Equiv.sumProdDistrib X Y Z).symm.toHomeomorphOfContinuousOpen
        ((continuous_inl.prodMap continuous_id).sumElim
          (continuous_inr.prodMap continuous_id)) <|
      (isOpenMap_inl.prodMap IsOpenMap.id).sumElim (isOpenMap_inr.prodMap IsOpenMap.id)

/--
Definition of `prodSumDistrib` / `prodSumDistrib` 的定义

English:
definition prodSumDistrib
  signature: : X × (Y oplus Z) ≃ₜ (X × Y) oplus (X × Z)
  body: (prodComm _ _).trans sumProdDistrib.trans sumCongr (prodComm _ _) (prodComm _ _)

中文:
定义 prodSumDistrib
  签名: : X × (Y oplus Z) ≃ₜ (X × Y) oplus (X × Z)
  定义体: (prodComm _ _).trans sumProdDistrib.trans sumCongr (prodComm _ _) (prodComm _ _)

Depends on / 依赖: prodComm, sumCongr, sumProdDistrib, sumProdDistrib.trans
-/
def prodSumDistrib : X × (Y oplus Z) ≃ₜ (X × Y) oplus (X × Z) :=
(prodComm _ _).trans sumProdDistrib.trans sumCongr (prodComm _ _) (prodComm _ _)

end Homeomorph

section IsInducing

variable {f : X -> Z} {g : Y -> Z}

/--
lemma `Topology.IsInducing.sumElim_left` / 引理 `Topology.IsInducing.sumElim_left`

English:
lemma Topology.IsInducing.sumElim_left
  given: (h : IsInducing (Sum.elim f g))
  statement: IsInducing f
  proof: elim_comp_inl f g ▸ h.comp IsEmbedding.inl.isInducing

中文:
引理 Topology.IsInducing.sumElim_left
  条件: (h : IsInducing (Sum.elim f g))
  结论: IsInducing f
  证明: elim_comp_inl f g ▸ h.comp IsEmbedding.inl.isInducing

Depends on / 依赖: IsEmbedding, IsEmbedding.inl.isInducing, elim_comp_inl, h.comp, isInducing
-/
lemma Topology.IsInducing.sumElim_left (h : IsInducing (Sum.elim f g)) : IsInducing f :=
  elim_comp_inl f g ▸ h.comp IsEmbedding.inl.isInducing

/--
lemma `Topology.IsInducing.sumElim_right` / 引理 `Topology.IsInducing.sumElim_right`

English:
lemma Topology.IsInducing.sumElim_right
  given: (h : IsInducing (Sum.elim f g))
  statement: IsInducing g
  proof: elim_comp_inr f g ▸ h.comp IsEmbedding.inr.isInducing

中文:
引理 Topology.IsInducing.sumElim_right
  条件: (h : IsInducing (Sum.elim f g))
  结论: IsInducing g
  证明: elim_comp_inr f g ▸ h.comp IsEmbedding.inr.isInducing

Depends on / 依赖: IsEmbedding, IsEmbedding.inr.isInducing, elim_comp_inr, h.comp, isInducing
-/
lemma Topology.IsInducing.sumElim_right (h : IsInducing (Sum.elim f g)) : IsInducing g :=
  elim_comp_inr f g ▸ h.comp IsEmbedding.inr.isInducing

/--
theorem `Topology.IsInducing.sumElim` / 定理 `Topology.IsInducing.sumElim`

English:
theorem Topology.IsInducing.sumElim
  statement: (hf : IsInducing f) (hg : IsInducing g)
  proof: by
  rw [← disjoint_principal_nhdsSet] at hFg
  rw [← disjoint_nhdsSet_principal] at hfG
  rw [isInducing_iff_nhds]
  intro x
  apply le_antisymm ((hf.continuous.sumElim hg.continuous).tendsto x).le_comap
  obtain x | x := x <;>
  simp only [comap_sumElim_eq, nhds_inl, nhds_inr, elim_inl, elim_inr, 

中文:
定理 Topology.IsInducing.sumElim
  结论: (hf : IsInducing f) (hg : IsInducing g)
  证明: by
  rw [← disjoint_principal_nhdsSet] at hFg
  rw [← disjoint_nhdsSet_principal] at hfG
  rw [isInducing_iff_nhds]
  intro x
  apply le_antisymm ((hf.continuous.sumElim hg.continuous).tendsto x).le_comap
  obtain x | x := x <;>
  simp only [comap_sumElim_eq, nhds_inl, nhds_inr, elim_inl, elim_inr, 

Depends on / 依赖: Filter, and_true, bot_le, comap_eq_bot_iff_compl_range, comap_sumElim_eq, continuous, convert, disjoint_nhdsSet_principal, disjoint_principal_nhdsSet, disjoint_principal_ri, elim_inl, elim_inr, hf.continuous.sumElim, hf.nhds_eq_comap, hg.continuous, hg.nhds_eq_comap, isInducing_iff_nhds, le_antisymm, le_comap, le_rfl
-/
theorem Topology.IsInducing.sumElim (hf : IsInducing f) (hg : IsInducing g)
    (hFg : Disjoint (closure (range f)) (range g)) (hfG : Disjoint (range f) (closure (range g))) :
    IsInducing (Sum.elim f g) := by
  rw [← disjoint_principal_nhdsSet] at hFg
  rw [← disjoint_nhdsSet_principal] at hfG
  rw [isInducing_iff_nhds]
  intro x
  apply le_antisymm ((hf.continuous.sumElim hg.continuous).tendsto x).le_comap
  obtain x | x := x <;>
  simp only [comap_sumElim_eq, nhds_inl, nhds_inr, elim_inl, elim_inr, ← hf.nhds_eq_comap,
    ← hg.nhds_eq_comap, sup_le_iff, le_rfl, true_and, and_true] <;>
  convert! bot_le (α := Filter (X oplus Y)) <;>
  rw [map_eq_bot_iff]; rw [comap_eq_bot_iff_compl_range]
  · rw [← disjoint_principal_right]
    exact hfG.mono_left (nhds_le_nhdsSet (mem_range_self x))
  · rw [← disjoint_principal_left]
    exact hFg.mono_right (nhds_le_nhdsSet (mem_range_self x))

/--
theorem `Topology.IsInducing.disjoint_of_sumElim_aux` / 定理 `Topology.IsInducing.disjoint_of_sumElim_aux`

English:
theorem Topology.IsInducing.disjoint_of_sumElim_aux
  given: (h : IsInducing (Sum.elim f g))
  proof: by
  rcases h.isClosed_iff.mp isClosed_range_inl with ⟨C, C_closed, hC⟩
  have A : closure (range f) subseteq C := by
    rw [C_closed.closure_subset_iff]; rw [← elim_comp_inl f g]; rw [range_comp]; rw [image_subset_iff]; rw [hC]
  have B : Disjoint C (range g) := by
    rw [← image_univ]; rw [disjo

中文:
定理 Topology.IsInducing.disjoint_of_sumElim_aux
  条件: (h : IsInducing (Sum.elim f g))
  证明: by
  rcases h.isClosed_iff.mp isClosed_range_inl with ⟨C, C_closed, hC⟩
  have A : closure (range f) subseteq C := by
    rw [C_closed.closure_subset_iff]; rw [← elim_comp_inl f g]; rw [range_comp]; rw [image_subset_iff]; rw [hC]
  have B : Disjoint C (range g) := by
    rw [← image_univ]; rw [disjo

Depends on / 依赖: B.mono_left, C_closed, C_closed.closure_subset_iff, Disjoint, closure, closure_subset_iff, disjoint_image_inl_image_inr, disjoint_image_right, elim_comp_inl, elim_comp_inr, h.isClosed_iff.mp, image_subset_iff, image_univ, isClosed_iff, isClosed_range_inl, mono_left, preimage_comp, range_comp, subseteq
-/
theorem Topology.IsInducing.disjoint_of_sumElim_aux (h : IsInducing (Sum.elim f g)) :
    Disjoint (closure (range f)) (range g) := by
  rcases h.isClosed_iff.mp isClosed_range_inl with ⟨C, C_closed, hC⟩
  have A : closure (range f) subseteq C := by
    rw [C_closed.closure_subset_iff]; rw [← elim_comp_inl f g]; rw [range_comp]; rw [image_subset_iff]; rw [hC]
  have B : Disjoint C (range g) := by
    rw [← image_univ]; rw [disjoint_image_right]; rw [← elim_comp_inr f g]; rw [preimage_comp]; rw [hC]; rw [← disjoint_image_right]; rw [← image_univ]
    exact disjoint_image_inl_image_inr
  exact B.mono_left A

/--
theorem `Topology.IsOpenEmbedding.sumSwap` / 定理 `Topology.IsOpenEmbedding.sumSwap`

English:
theorem Topology.IsOpenEmbedding.sumSwap
  statement: IsOpenEmbedding (@Sum.swap X Y)
  proof: (Homeomorph.sumComm X Y).isOpenEmbedding

中文:
定理 Topology.IsOpenEmbedding.sumSwap
  结论: IsOpenEmbedding (@Sum.swap X Y)
  证明: (Homeomorph.sumComm X Y).isOpenEmbedding

Depends on / 依赖: Homeomorph, Homeomorph.sumComm, isOpenEmbedding, sumComm
-/
theorem Topology.IsOpenEmbedding.sumSwap : IsOpenEmbedding (@Sum.swap X Y) :=
  (Homeomorph.sumComm X Y).isOpenEmbedding

/--
theorem `Topology.IsInducing.sumSwap` / 定理 `Topology.IsInducing.sumSwap`

English:
theorem Topology.IsInducing.sumSwap
  statement: IsInducing (@Sum.swap X Y)
  proof: IsOpenEmbedding.sumSwap.isInducing

中文:
定理 Topology.IsInducing.sumSwap
  结论: IsInducing (@Sum.swap X Y)
  证明: IsOpenEmbedding.sumSwap.isInducing

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.sumSwap.isInducing, isInducing, sumSwap
-/
theorem Topology.IsInducing.sumSwap : IsInducing (@Sum.swap X Y) :=
  IsOpenEmbedding.sumSwap.isInducing

/--
theorem `isInducing_sumElim` / 定理 `isInducing_sumElim`

English:
theorem isInducing_sumElim
  proof: ⟨fun h => ⟨h.sumElim_left, h.sumElim_right, h.disjoint_of_sumElim_aux,
    ((Sum.elim_swap ▸ h.comp .sumSwap).disjoint_of_sumElim_aux ).symm⟩,
    fun ⟨hf, hg, hFg, hfG⟩ => hf.sumElim hg hFg hfG⟩

中文:
定理 isInducing_sumElim
  证明: ⟨fun h => ⟨h.sumElim_left, h.sumElim_right, h.disjoint_of_sumElim_aux,
    ((Sum.elim_swap ▸ h.comp .sumSwap).disjoint_of_sumElim_aux ).symm⟩,
    fun ⟨hf, hg, hFg, hfG⟩ => hf.sumElim hg hFg hfG⟩

Depends on / 依赖: Sum.elim_swap, disjoint_of_sumElim_aux, elim_swap, h.comp, h.disjoint_of_sumElim_aux, h.sumElim_left, h.sumElim_right, hf.sumElim, sumElim, sumElim_left, sumElim_right, sumSwap
-/
theorem isInducing_sumElim :
    IsInducing (Sum.elim f g) ↔ IsInducing f ∧ IsInducing g ∧
      Disjoint (closure (range f)) (range g) ∧ Disjoint (range f) (closure (range g)) :=
  ⟨fun h => ⟨h.sumElim_left, h.sumElim_right, h.disjoint_of_sumElim_aux,
    ((Sum.elim_swap ▸ h.comp .sumSwap).disjoint_of_sumElim_aux ).symm⟩,
    fun ⟨hf, hg, hFg, hfG⟩ => hf.sumElim hg hFg hfG⟩

/--
lemma `Topology.IsInducing.sumElim_of_separatedNhds` / 引理 `Topology.IsInducing.sumElim_of_separatedNhds`

English:
lemma Topology.IsInducing.sumElim_of_separatedNhds
  proof: hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

中文:
引理 Topology.IsInducing.sumElim_of_separatedNhds
  证明: hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

Depends on / 依赖: disjoint_closure_left, disjoint_closure_right, hf.sumElim, hsep.disjoint_closure_left, hsep.disjoint_closure_right, sumElim
-/
lemma Topology.IsInducing.sumElim_of_separatedNhds
    (hf : IsInducing f) (hg : IsInducing g) (hsep : SeparatedNhds (range f) (range g)) :
    IsInducing (Sum.elim f g) :=
  hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

/--
lemma `Topology.IsEmbedding.sumElim_left` / 引理 `Topology.IsEmbedding.sumElim_left`

English:
lemma Topology.IsEmbedding.sumElim_left
  given: (h : IsEmbedding (Sum.elim f g))
  statement: IsEmbedding f
  proof: elim_comp_inl f g ▸ h.comp IsEmbedding.inl

中文:
引理 Topology.IsEmbedding.sumElim_left
  条件: (h : IsEmbedding (Sum.elim f g))
  结论: IsEmbedding f
  证明: elim_comp_inl f g ▸ h.comp IsEmbedding.inl

Depends on / 依赖: IsEmbedding, IsEmbedding.inl, elim_comp_inl, h.comp
-/
lemma Topology.IsEmbedding.sumElim_left (h : IsEmbedding (Sum.elim f g)) : IsEmbedding f :=
  elim_comp_inl f g ▸ h.comp IsEmbedding.inl

/--
lemma `Topology.IsEmbedding.sumElim_right` / 引理 `Topology.IsEmbedding.sumElim_right`

English:
lemma Topology.IsEmbedding.sumElim_right
  given: (h : IsEmbedding (Sum.elim f g))
  statement: IsEmbedding g
  proof: elim_comp_inr f g ▸ h.comp IsEmbedding.inr

中文:
引理 Topology.IsEmbedding.sumElim_right
  条件: (h : IsEmbedding (Sum.elim f g))
  结论: IsEmbedding g
  证明: elim_comp_inr f g ▸ h.comp IsEmbedding.inr

Depends on / 依赖: IsEmbedding, IsEmbedding.inr, elim_comp_inr, h.comp
-/
lemma Topology.IsEmbedding.sumElim_right (h : IsEmbedding (Sum.elim f g)) : IsEmbedding g :=
  elim_comp_inr f g ▸ h.comp IsEmbedding.inr

/--
theorem `isEmbedding_sumElim` / 定理 `isEmbedding_sumElim`

English:
theorem isEmbedding_sumElim
  proof: by
  simp_rw [isEmbedding_iff, isInducing_sumElim, Sum.elim_injective]
  constructor
  · intro ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, f_ne_g⟩⟩
    exact ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
  · intro ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
    refine ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, ?_⟩⟩
    exact fun a b => h

中文:
定理 isEmbedding_sumElim
  证明: by
  simp_rw [isEmbedding_iff, isInducing_sumElim, Sum.elim_injective]
  constructor
  · intro ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, f_ne_g⟩⟩
    exact ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
  · intro ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
    refine ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, ?_⟩⟩
    exact fun a b => h

Depends on / 依赖: Sum.elim_injective, elim_injective, f_ne_g, hfG.ne_of_mem, isEmbedding_iff, isInducing_sumElim, mem_range_self, ne_of_mem, simp_rw, subset_closure
-/
theorem isEmbedding_sumElim :
    IsEmbedding (Sum.elim f g) ↔ IsEmbedding f ∧ IsEmbedding g ∧
      Disjoint (closure (range f)) (range g) ∧ Disjoint (range f) (closure (range g)) := by
  simp_rw [isEmbedding_iff, isInducing_sumElim, Sum.elim_injective]
  constructor
  · intro ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, f_ne_g⟩⟩
    exact ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
  · intro ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
    refine ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, ?_⟩⟩
    exact fun a b => hfG.ne_of_mem (mem_range_self a) (subset_closure (mem_range_self b))

/--
theorem `Topology.IsEmbedding.sumElim` / 定理 `Topology.IsEmbedding.sumElim`

English:
theorem Topology.IsEmbedding.sumElim
  statement: (hf : IsEmbedding f) (hg : IsEmbedding g)
  proof: isEmbedding_sumElim.mpr ⟨hf, hg, hFg, hfG⟩

中文:
定理 Topology.IsEmbedding.sumElim
  结论: (hf : IsEmbedding f) (hg : IsEmbedding g)
  证明: isEmbedding_sumElim.mpr ⟨hf, hg, hFg, hfG⟩

Depends on / 依赖: isEmbedding_sumElim, isEmbedding_sumElim.mpr
-/
theorem Topology.IsEmbedding.sumElim (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hFg : Disjoint (closure (range f)) (range g)) (hfG : Disjoint (range f) (closure (range g))) :
    IsEmbedding (Sum.elim f g) :=
  isEmbedding_sumElim.mpr ⟨hf, hg, hFg, hfG⟩

/--
lemma `Topology.IsEmbedding.sumElim_of_separatedNhds` / 引理 `Topology.IsEmbedding.sumElim_of_separatedNhds`

English:
lemma Topology.IsEmbedding.sumElim_of_separatedNhds
  proof: hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

中文:
引理 Topology.IsEmbedding.sumElim_of_separatedNhds
  证明: hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

Depends on / 依赖: disjoint_closure_left, disjoint_closure_right, hf.sumElim, hsep.disjoint_closure_left, hsep.disjoint_closure_right, sumElim
-/
lemma Topology.IsEmbedding.sumElim_of_separatedNhds
    (hf : IsEmbedding f) (hg : IsEmbedding g) (hsep : SeparatedNhds (range f) (range g)) :
    IsEmbedding (Sum.elim f g) :=
  hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

end IsInducing

end Sum
