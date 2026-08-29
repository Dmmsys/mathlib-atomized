/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Higher differentiability of usual operations

We prove that the usual operations (addition, multiplication, difference, and
so on) preserve `C^n` functions.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

@[expose] public section

open scoped NNReal Nat ContDiff

universe u uE uF uG

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

open Set Fin Filter Function

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E -> F}
  {g : F -> G} {x x₀ : E} {b : E × F -> G} {m n : Nat∞ω} {p : E -> FormalMultilinearSeries 𝕜 E F}

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/

section Pi

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {F' : ι -> Type*} [forall i, NormedAddCommGroup (F' i)]
  [forall i, NormedSpace 𝕜 (F' i)] {φ : forall i, E -> F' i} {p' : forall i, E -> FormalMultilinearSeries 𝕜 E (F' i)}
  {Φ : E -> forall i, F' i} {P' : E -> FormalMultilinearSeries 𝕜 E (forall i, F' i)}

/--
theorem `hasFTaylorSeriesUpToOn_pi` / 定理 `hasFTaylorSeriesUpToOn_pi`

English:
theorem hasFTaylorSeriesUpToOn_pi
  given: {n : Nat∞ω}
  proof: by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  set L : forall m : Nat, (forall i, E [×m]->L[𝕜] F' i) ≃ₗᵢ[𝕜] E [×m]->L[𝕜] forall i, F' i := fun m =>
    ContinuousMultilinearMap.piₗᵢ _ _
  refine ⟨fun h i => ?_, fun h => ⟨fun x hx => ?_, ?_, ?_⟩⟩
  · exact h.continuousLinearMap_comp (pr i)

中文:
定理 hasFTaylorSeriesUpToOn_pi
  条件: {n : 自然数∞ω}
  证明: by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  set L : forall m : Nat, (forall i, E [×m]->L[𝕜] F' i) ≃ₗᵢ[𝕜] E [×m]->L[𝕜] forall i, F' i := fun m =>
    ContinuousMultilinearMap.piₗᵢ _ _
  refine ⟨fun h i => ?_, fun h => ⟨fun x hx => ?_, ?_, ?_⟩⟩
  · exact h.continuousLinearMap_comp (pr i)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.proj, ContinuousMultilinearMap, ContinuousMultilinearMap.pi, comp_continuo, comp_hasFDerivWithinAt, continuous, continuous.comp_continuo, continuousLinearMap_comp, fderivWithin, h.continuousLinearMap_comp, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt, hasFDerivWithinAt_pi, zero_eq
-/
theorem hasFTaylorSeriesUpToOn_pi {n : Nat∞ω} :
    HasFTaylorSeriesUpToOn n (fun x i => φ i x)
        (fun x m => ContinuousMultilinearMap.pi fun i => p' i x m) s ↔
      forall i, HasFTaylorSeriesUpToOn n (φ i) (p' i) s := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  set L : forall m : Nat, (forall i, E [×m]->L[𝕜] F' i) ≃ₗᵢ[𝕜] E [×m]->L[𝕜] forall i, F' i := fun m =>
    ContinuousMultilinearMap.piₗᵢ _ _
  refine ⟨fun h i => ?_, fun h => ⟨fun x hx => ?_, ?_, ?_⟩⟩
  · exact h.continuousLinearMap_comp (pr i)
  · ext1 i
    exact (h i).zero_eq x hx
  · intro m hm x hx
exact (L m).hasFDerivAt.comp_hasFDerivWithinAt x
      hasFDerivWithinAt_pi.2 fun i => (h i).fderivWithin m hm x hx
  · intro m hm
exact (L m).continuous.comp_continuousOn continuousOn_pi.2 fun i => (h i).cont m hm

@[simp]
/--
theorem `hasFTaylorSeriesUpToOn_pi'` / 定理 `hasFTaylorSeriesUpToOn_pi'`

English:
theorem hasFTaylorSeriesUpToOn_pi'
  given: {n : Nat∞ω}
  proof: by
  convert! hasFTaylorSeriesUpToOn_pi (𝕜 := 𝕜) (φ := fun i x => Φ x i); ext; rfl

中文:
定理 hasFTaylorSeriesUpToOn_pi'
  条件: {n : 自然数∞ω}
  证明: by
  convert! hasFTaylorSeriesUpToOn_pi (𝕜 := 𝕜) (φ := fun i x => Φ x i); ext; rfl

Depends on / 依赖: convert, hasFTaylorSeriesUpToOn_pi
-/
theorem hasFTaylorSeriesUpToOn_pi' {n : Nat∞ω} :
    HasFTaylorSeriesUpToOn n Φ P' s ↔
      forall i, HasFTaylorSeriesUpToOn n (fun x => Φ x i)
        (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap
          (P' x m)) s := by
  convert! hasFTaylorSeriesUpToOn_pi (𝕜 := 𝕜) (φ := fun i x => Φ x i); ext; rfl

/--
theorem `contDiffWithinAt_pi` / 定理 `contDiffWithinAt_pi`

English:
theorem contDiffWithinAt_pi
  proof: by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine ⟨fun h i => h.continuousLinearMap_comp (pr i), fun h => ?_⟩
  match n with
  | ω =>
    choose u hux p hp h'p using h
    refine ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono iInter_subset _ _,

中文:
定理 contDiffWithinAt_pi
  证明: by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine ⟨fun h i => h.continuousLinearMap_comp (pr i), fun h => ?_⟩
  match n with
  | ω =>
    choose u hux p hp h'p using h
    refine ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono iInter_subset _ _,

Depends on / 依赖: AnalyticOn, ContinuousLinearMap, ContinuousLinearMap.proj, ContinuousMultilinearMap, ContinuousMultilinearMap.pi, Filter, Filter.iInter_mem, L.analyticOnNhd, analyticOnNhd, continuousLinearMap_comp, h.continuousLinearMap_comp, hasFTaylorSeriesUpToOn_pi, iInter_mem, iInter_subset
-/
theorem contDiffWithinAt_pi :
    ContDiffWithinAt 𝕜 n Φ s x ↔ forall i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine ⟨fun h i => h.continuousLinearMap_comp (pr i), fun h => ?_⟩
  match n with
  | ω =>
    choose u hux p hp h'p using h
    refine ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono iInter_subset _ _, fun m => ?_⟩
    set L : (forall i, E [×m]->L[𝕜] F' i) ≃ₗᵢ[𝕜] E [×m]->L[𝕜] forall i, F' i :=
      ContinuousMultilinearMap.piₗᵢ _ _
    change AnalyticOn 𝕜 (fun x => L (fun i => p i x m)) (⋂ i, u i)
    apply (L.analyticOnNhd univ).comp_analyticOn ?_ (mapsTo_univ _ _)
    exact AnalyticOn.pi (fun i => (h'p i m).mono (iInter_subset _ _))
  | (n : Nat∞) =>
    intro m hm
    choose u hux p hp using fun i => h i m hm
    exact ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono iInter_subset _ _⟩

/--
theorem `contDiffOn_pi` / 定理 `contDiffOn_pi`

English:
theorem contDiffOn_pi
  statement: ContDiffOn 𝕜 n Φ s ↔ forall i, ContDiffOn 𝕜 n (fun x => Φ x i) s
  proof: ⟨fun h _ x hx => contDiffWithinAt_pi.1 (h x hx) _, fun h x hx =>
    contDiffWithinAt_pi.2 fun i => h i x hx⟩

中文:
定理 contDiffOn_pi
  结论: ContDiffOn 𝕜 n Φ s ↔ 对任意 i, ContDiffOn 𝕜 n (fun x => Φ x i) s
  证明: ⟨fun h _ x hx => contDiffWithinAt_pi.1 (h x hx) _, fun h x hx =>
    contDiffWithinAt_pi.2 fun i => h i x hx⟩

Depends on / 依赖: contDiffWithinAt_pi
-/
theorem contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ forall i, ContDiffOn 𝕜 n (fun x => Φ x i) s :=
  ⟨fun h _ x hx => contDiffWithinAt_pi.1 (h x hx) _, fun h x hx =>
    contDiffWithinAt_pi.2 fun i => h i x hx⟩

/--
theorem `contDiffAt_pi` / 定理 `contDiffAt_pi`

English:
theorem contDiffAt_pi
  statement: ContDiffAt 𝕜 n Φ x ↔ forall i, ContDiffAt 𝕜 n (fun x => Φ x i) x
  proof: contDiffWithinAt_pi

中文:
定理 contDiffAt_pi
  结论: ContDiffAt 𝕜 n Φ x ↔ 对任意 i, ContDiffAt 𝕜 n (fun x => Φ x i) x
  证明: contDiffWithinAt_pi

Depends on / 依赖: contDiffWithinAt_pi
-/
theorem contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ forall i, ContDiffAt 𝕜 n (fun x => Φ x i) x :=
  contDiffWithinAt_pi

/--
theorem `contDiff_pi` / 定理 `contDiff_pi`

English:
theorem contDiff_pi
  statement: ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x => Φ x i
  proof: by
  simp only [← contDiffOn_univ, contDiffOn_pi]

@[fun_prop]

中文:
定理 contDiff_pi
  结论: 连续可微 𝕜 n Φ ↔ 对任意 i, 连续可微 𝕜 n fun x => Φ x i
  证明: by
  simp only [← contDiffOn_univ, contDiffOn_pi]

@[fun_prop]

Depends on / 依赖: contDiffOn_pi, contDiffOn_univ
-/
theorem contDiff_pi : ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x => Φ x i := by
  simp only [← contDiffOn_univ, contDiffOn_pi]

@[fun_prop]
/--
theorem `contDiff_pi'` / 定理 `contDiff_pi'`

English:
theorem contDiff_pi'
  given: (hΦ : forall i, ContDiff 𝕜 n fun x => Φ x i)
  statement: ContDiff 𝕜 n Φ
  proof: contDiff_pi.2 hΦ

@[fun_prop]

中文:
定理 contDiff_pi'
  条件: (hΦ : 对任意 i, 连续可微 𝕜 n fun x => Φ x i)
  结论: 连续可微 𝕜 n Φ
  证明: contDiff_pi.2 hΦ

@[fun_prop]

Depends on / 依赖: contDiff_pi
-/
theorem contDiff_pi' (hΦ : forall i, ContDiff 𝕜 n fun x => Φ x i) : ContDiff 𝕜 n Φ :=
  contDiff_pi.2 hΦ

@[fun_prop]
/--
theorem `contDiffOn_pi'` / 定理 `contDiffOn_pi'`

English:
theorem contDiffOn_pi'
  given: (hΦ : forall i, ContDiffOn 𝕜 n (fun x => Φ x i) s)
  statement: ContDiffOn 𝕜 n Φ s
  proof: contDiffOn_pi.2 hΦ

@[fun_prop]

中文:
定理 contDiffOn_pi'
  条件: (hΦ : 对任意 i, ContDiffOn 𝕜 n (fun x => Φ x i) s)
  结论: ContDiffOn 𝕜 n Φ s
  证明: contDiffOn_pi.2 hΦ

@[fun_prop]

Depends on / 依赖: contDiffOn_pi
-/
theorem contDiffOn_pi' (hΦ : forall i, ContDiffOn 𝕜 n (fun x => Φ x i) s) : ContDiffOn 𝕜 n Φ s :=
  contDiffOn_pi.2 hΦ

@[fun_prop]
/--
theorem `contDiffAt_pi'` / 定理 `contDiffAt_pi'`

English:
theorem contDiffAt_pi'
  given: (hΦ : forall i, ContDiffAt 𝕜 n (fun x => Φ x i) x)
  statement: ContDiffAt 𝕜 n Φ x
  proof: contDiffAt_pi.2 hΦ

中文:
定理 contDiffAt_pi'
  条件: (hΦ : 对任意 i, ContDiffAt 𝕜 n (fun x => Φ x i) x)
  结论: ContDiffAt 𝕜 n Φ x
  证明: contDiffAt_pi.2 hΦ

Depends on / 依赖: contDiffAt_pi
-/
theorem contDiffAt_pi' (hΦ : forall i, ContDiffAt 𝕜 n (fun x => Φ x i) x) : ContDiffAt 𝕜 n Φ x :=
  contDiffAt_pi.2 hΦ

/--
theorem `contDiff_update` / 定理 `contDiff_update`

English:
theorem contDiff_update
  given: [DecidableEq ι] (k : Nat∞ω) (x : forall i, F' i) (i : ι)
  proof: by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

中文:
定理 contDiff_update
  条件: [DecidableEq ι] (k : 自然数∞ω) (x : 对任意 i, F' i) (i : ι)
  证明: by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

Depends on / 依赖: Function, Function.update, contDiff_const, contDiff_id, contDiff_pi, split_ifs, update
-/
theorem contDiff_update [DecidableEq ι] (k : Nat∞ω) (x : forall i, F' i) (i : ι) :
    ContDiff 𝕜 k (update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

variable (F') in
/--
theorem `contDiff_single` / 定理 `contDiff_single`

English:
theorem contDiff_single
  given: [DecidableEq ι] (k : Nat∞ω) (i : ι)
  proof: contDiff_update k 0 i

中文:
定理 contDiff_single
  条件: [DecidableEq ι] (k : 自然数∞ω) (i : ι)
  证明: contDiff_update k 0 i

Depends on / 依赖: contDiff_update
-/
theorem contDiff_single [DecidableEq ι] (k : Nat∞ω) (i : ι) :
    ContDiff 𝕜 k (Pi.single i : F' i -> forall i, F' i) :=
  contDiff_update k 0 i

variable (𝕜 E)

@[fun_prop]
/--
theorem `contDiff_apply` / 定理 `contDiff_apply`

English:
theorem contDiff_apply
  given: (i : ι)
  statement: ContDiff 𝕜 n fun f : ι -> E => f i
  proof: contDiff_pi.mp contDiff_id i

@[fun_prop]

中文:
定理 contDiff_apply
  条件: (i : ι)
  结论: 连续可微 𝕜 n fun f : ι -> E => f i
  证明: contDiff_pi.mp contDiff_id i

@[fun_prop]

Depends on / 依赖: contDiff_id, contDiff_pi, contDiff_pi.mp
-/
theorem contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι -> E => f i :=
  contDiff_pi.mp contDiff_id i

@[fun_prop]
/--
theorem `contDiffAt_apply` / 定理 `contDiffAt_apply`

English:
theorem contDiffAt_apply
  given: (i : ι) (f : ι -> E)
  statement: ContDiffAt 𝕜 n (fun f : ι -> E => f i) f
  proof: (contDiff_apply 𝕜 E i).contDiffAt

@[fun_prop]

中文:
定理 contDiffAt_apply
  条件: (i : ι) (f : ι -> E)
  结论: ContDiffAt 𝕜 n (fun f : ι -> E => f i) f
  证明: (contDiff_apply 𝕜 E i).contDiffAt

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiff_apply
-/
theorem contDiffAt_apply (i : ι) (f : ι -> E) : ContDiffAt 𝕜 n (fun f : ι -> E => f i) f :=
  (contDiff_apply 𝕜 E i).contDiffAt

@[fun_prop]
/--
theorem `contDiffOn_apply` / 定理 `contDiffOn_apply`

English:
theorem contDiffOn_apply
  given: (i : ι) (s : Set (ι -> E))
  statement: ContDiffOn 𝕜 n (fun f : ι -> E => f i) s
  proof: (contDiff_apply 𝕜 E i).contDiffOn

中文:
定理 contDiffOn_apply
  条件: (i : ι) (s : 集合 (ι -> E))
  结论: ContDiffOn 𝕜 n (fun f : ι -> E => f i) s
  证明: (contDiff_apply 𝕜 E i).contDiffOn

Depends on / 依赖: contDiffOn, contDiff_apply
-/
theorem contDiffOn_apply (i : ι) (s : Set (ι -> E)) : ContDiffOn 𝕜 n (fun f : ι -> E => f i) s :=
  (contDiff_apply 𝕜 E i).contDiffOn

/--
theorem `contDiff_apply_apply` / 定理 `contDiff_apply_apply`

English:
theorem contDiff_apply_apply
  given: (i : ι) (j : ι')
  statement: ContDiff 𝕜 n fun f : ι -> ι' -> E => f i j
  proof: contDiff_pi.mp (contDiff_apply 𝕜 (ι' -> E) i) j

中文:
定理 contDiff_apply_apply
  条件: (i : ι) (j : ι')
  结论: 连续可微 𝕜 n fun f : ι -> ι' -> E => f i j
  证明: contDiff_pi.mp (contDiff_apply 𝕜 (ι' -> E) i) j

Depends on / 依赖: contDiff_apply, contDiff_pi, contDiff_pi.mp
-/
theorem contDiff_apply_apply (i : ι) (j : ι') : ContDiff 𝕜 n fun f : ι -> ι' -> E => f i j :=
  contDiff_pi.mp (contDiff_apply 𝕜 (ι' -> E) i) j

end Pi

/-! ### Sum of two functions -/

section Add

/--
theorem `HasFTaylorSeriesUpToOn.add` / 定理 `HasFTaylorSeriesUpToOn.add`

English:
theorem HasFTaylorSeriesUpToOn.add
  statement: {n : Nat∞ω} {q g} (hf : HasFTaylorSeriesUpToOn n f p s)
  proof: by
  exact HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    (ContinuousLinearMap.fst 𝕜 F F + .snd 𝕜 F F) (hf.prodMk hg)

中文:
定理 有FTaylorSeriesUpToOn.add
  结论: {n : 自然数∞ω} {q g} (hf : 有FTaylorSeriesUpToOn n f p s)
  证明: by
  exact HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    (ContinuousLinearMap.fst 𝕜 F F + .snd 𝕜 F F) (hf.prodMk hg)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst, HasFTaylorSeriesUpToOn, HasFTaylorSeriesUpToOn.continuousLinearMap_comp, continuousLinearMap_comp, hf.prodMk, prodMk
-/
theorem HasFTaylorSeriesUpToOn.add {n : Nat∞ω} {q g} (hf : HasFTaylorSeriesUpToOn n f p s)
    (hg : HasFTaylorSeriesUpToOn n g q s) : HasFTaylorSeriesUpToOn n (f + g) (p + q) s := by
  exact HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    (ContinuousLinearMap.fst 𝕜 F F + .snd 𝕜 F F) (hf.prodMk hg)

-- The sum is smooth.
@[fun_prop]
/--
theorem `contDiff_add` / 定理 `contDiff_add`

English:
theorem contDiff_add
  statement: ContDiff 𝕜 n fun p : F × F => p.1 + p.2
  proof: (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).contDiff

中文:
定理 contDiff_add
  结论: 连续可微 𝕜 n fun p : F × F => p.1 + p.2
  证明: (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).contDiff

Depends on / 依赖: IsBoundedLinearMap, IsBoundedLinearMap.fst.add, IsBoundedLinearMap.snd, contDiff
-/
theorem contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2 :=
  (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).contDiff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.add` / 定理 `ContDiffWithinAt.add`

English:
theorem ContDiffWithinAt.add
  statement: {s : Set E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: contDiff_add.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

中文:
定理 ContDiffWithinAt.add
  结论: {s : 集合 E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: contDiff_add.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

Depends on / 依赖: contDiffWithinAt, contDiff_add, contDiff_add.contDiffWithinAt.comp, hf.prodMk, prodMk, subset_preimage_univ
-/
theorem ContDiffWithinAt.add {s : Set E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x + g x) s x :=
  contDiff_add.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
/--
theorem `ContDiffAt.add` / 定理 `ContDiffAt.add`

English:
theorem ContDiffAt.add
  given: {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  proof: by
  rw [← contDiffWithinAt_univ] at *; exact hf.add hg

中文:
定理 ContDiffAt.add
  条件: {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  证明: by
  rw [← contDiffWithinAt_univ] at *; exact hf.add hg

Depends on / 依赖: contDiffWithinAt_univ, hf.add
-/
theorem ContDiffAt.add {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x + g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.add hg

/-- The sum of two `C^n` functions is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.add` / 定理 `ContDiff.add`

English:
theorem ContDiff.add
  given: {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
  proof: contDiff_add.comp (hf.prodMk hg)

中文:
定理 连续可微.add
  条件: {f g : E -> F} (hf : 连续可微 𝕜 n f) (hg : 连续可微 𝕜 n g)
  证明: contDiff_add.comp (hf.prodMk hg)

Depends on / 依赖: contDiff_add, contDiff_add.comp, hf.prodMk, prodMk
-/
theorem ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x + g x :=
  contDiff_add.comp (hf.prodMk hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffOn.add` / 定理 `ContDiffOn.add`

English:
theorem ContDiffOn.add
  statement: {s : Set E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  proof: fun x hx =>
  (hf x hx).add (hg x hx)

中文:
定理 ContDiffOn.add
  结论: {s : 集合 E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  证明: fun x hx =>
  (hf x hx).add (hg x hx)
-/
theorem ContDiffOn.add {s : Set E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x + g x) s := fun x hx =>
  (hf x hx).add (hg x hx)

variable {i : Nat}

/--
theorem `iteratedFDerivWithin_add_apply` / 定理 `iteratedFDerivWithin_add_apply`

English:
theorem iteratedFDerivWithin_add_apply
  statement: {f g : E -> F} (hf : ContDiffWithinAt 𝕜 i f s x)
  proof: by
  have := (hf.eventually (by simp)).and (hg.eventually (by simp))
  obtain ⟨t, ht, hxt, h⟩ := mem_nhdsWithin.mp this
  have hft : ContDiffOn 𝕜 i f (s inter t) := fun a ha => (h (by simp_all)).1.mono inter_subset_left
  have hgt : ContDiffOn 𝕜 i g (s inter t) := fun a ha => (h (by simp_all)).2.mon

中文:
定理 iteratedFDerivWithin_add_apply
  结论: {f g : E -> F} (hf : ContDiffWithinAt 𝕜 i f s x)
  证明: by
  have := (hf.eventually (by simp)).and (hg.eventually (by simp))
  obtain ⟨t, ht, hxt, h⟩ := mem_nhdsWithin.mp this
  have hft : ContDiffOn 𝕜 i f (s inter t) := fun a ha => (h (by simp_all)).1.mono inter_subset_left
  have hgt : ContDiffOn 𝕜 i g (s inter t) := fun a ha => (h (by simp_all)).2.mon
-/
@[to_fun] theorem iteratedFDerivWithin_add_apply {f g : E -> F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x in s) :
    iteratedFDerivWithin 𝕜 i (f + g) s x =
      iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x := by
  have := (hf.eventually (by simp)).and (hg.eventually (by simp))
  obtain ⟨t, ht, hxt, h⟩ := mem_nhdsWithin.mp this
  have hft : ContDiffOn 𝕜 i f (s inter t) := fun a ha => (h (by simp_all)).1.mono inter_subset_left
  have hgt : ContDiffOn 𝕜 i g (s inter t) := fun a ha => (h (by simp_all)).2.mono inter_subset_left
  have hut : UniqueDiffOn 𝕜 (s inter t) := hu.inter ht
  have H : ↑(s inter t) =ᶠ[𝓝 x] s :=
    inter_eventuallyEq_left.mpr (eventually_of_mem (ht.mem_nhds hxt) (fun _ h _ => h))
  rw [← iteratedFDerivWithin_congr_set H]; rw [← iteratedFDerivWithin_congr_set H]; rw [← iteratedFDerivWithin_congr_set H]
  exact .symm (((hft.ftaylorSeriesWithin hut).add
      (hgt.ftaylorSeriesWithin hut)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hut ⟨hx, hxt⟩)

@[deprecated (since := "2026-02-13")]
alias iteratedFDerivWithin_add_apply' := fun_iteratedFDerivWithin_add_apply

/--
theorem `iteratedFDeriv_add_apply` / 定理 `iteratedFDeriv_add_apply`

English:
theorem iteratedFDeriv_add_apply
  statement: {i : Nat} {f g : E -> F}
  proof: by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_add_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

@[deprecated (since := "2026-02-13")]
alias iteratedFDeriv_add_apply' := fun_iteratedFDeriv_add_apply

中文:
定理 iteratedFDeriv_add_apply
  结论: {i : 自然数} {f g : E -> F}
  证明: by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_add_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

@[deprecated (since := "2026-02-13")]
alias iteratedFDeriv_add_apply' := fun_iteratedFDeriv_add_apply
-/
@[to_fun] theorem iteratedFDeriv_add_apply {i : Nat} {f g : E -> F}
    (hf : ContDiffAt 𝕜 i f x) (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (f + g) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_add_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

@[deprecated (since := "2026-02-13")]
alias iteratedFDeriv_add_apply' := fun_iteratedFDeriv_add_apply

/--
theorem `iteratedFDeriv_add` / 定理 `iteratedFDeriv_add`

English:
theorem iteratedFDeriv_add
  statement: {i : Nat} {f g : E -> F} (hf : ContDiff 𝕜 i f)
  proof: funext fun _ => iteratedFDeriv_add_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)

中文:
定理 iteratedFDeriv_add
  结论: {i : 自然数} {f g : E -> F} (hf : 连续可微 𝕜 i f)
  证明: funext fun _ => iteratedFDeriv_add_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)
-/
@[to_fun] theorem iteratedFDeriv_add {i : Nat} {f g : E -> F} (hf : ContDiff 𝕜 i f)
    (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (f + g) = iteratedFDeriv 𝕜 i f + iteratedFDeriv 𝕜 i g :=
  funext fun _ => iteratedFDeriv_add_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)

end Add

/-! ### Negative -/

section Neg

-- The negative is smooth.
@[fun_prop]
/--
theorem `contDiff_neg` / 定理 `contDiff_neg`

English:
theorem contDiff_neg
  statement: ContDiff 𝕜 n fun p : F => -p
  proof: IsBoundedLinearMap.id.neg.contDiff

中文:
定理 contDiff_neg
  结论: 连续可微 𝕜 n fun p : F => -p
  证明: IsBoundedLinearMap.id.neg.contDiff

Depends on / 依赖: IsBoundedLinearMap, IsBoundedLinearMap.id.neg.contDiff, contDiff
-/
theorem contDiff_neg : ContDiff 𝕜 n fun p : F => -p :=
  IsBoundedLinearMap.id.neg.contDiff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.neg` / 定理 `ContDiffWithinAt.neg`

English:
theorem ContDiffWithinAt.neg
  given: {s : Set E} {f : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: contDiff_neg.contDiffWithinAt.comp x hf subset_preimage_univ

中文:
定理 ContDiffWithinAt.neg
  条件: {s : 集合 E} {f : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: contDiff_neg.contDiffWithinAt.comp x hf subset_preimage_univ

Depends on / 依赖: contDiffWithinAt, contDiff_neg, contDiff_neg.contDiffWithinAt.comp, subset_preimage_univ
-/
theorem ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => -f x) s x :=
  contDiff_neg.contDiffWithinAt.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
@[fun_prop]
/--
theorem `ContDiffAt.neg` / 定理 `ContDiffAt.neg`

English:
theorem ContDiffAt.neg
  given: {f : E -> F} (hf : ContDiffAt 𝕜 n f x)
  proof: by rw [← contDiffWithinAt_univ] at *; exact hf.neg

中文:
定理 ContDiffAt.neg
  条件: {f : E -> F} (hf : ContDiffAt 𝕜 n f x)
  证明: by rw [← contDiffWithinAt_univ] at *; exact hf.neg

Depends on / 依赖: contDiffWithinAt_univ, hf.neg
-/
theorem ContDiffAt.neg {f : E -> F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => -f x) x := by rw [← contDiffWithinAt_univ] at *; exact hf.neg

/-- The negative of a `C^n` function is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.neg` / 定理 `ContDiff.neg`

English:
theorem ContDiff.neg
  given: {f : E -> F} (hf : ContDiff 𝕜 n f)
  statement: ContDiff 𝕜 n fun x => -f x
  proof: contDiff_neg.comp hf

中文:
定理 连续可微.neg
  条件: {f : E -> F} (hf : 连续可微 𝕜 n f)
  结论: 连续可微 𝕜 n fun x => -f x
  证明: contDiff_neg.comp hf

Depends on / 依赖: contDiff_neg, contDiff_neg.comp
-/
theorem ContDiff.neg {f : E -> F} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => -f x :=
  contDiff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffOn.neg` / 定理 `ContDiffOn.neg`

English:
theorem ContDiffOn.neg
  given: {s : Set E} {f : E -> F} (hf : ContDiffOn 𝕜 n f s)
  proof: fun x hx => (hf x hx).neg

中文:
定理 ContDiffOn.neg
  条件: {s : 集合 E} {f : E -> F} (hf : ContDiffOn 𝕜 n f s)
  证明: fun x hx => (hf x hx).neg
-/
theorem ContDiffOn.neg {s : Set E} {f : E -> F} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => -f x) s := fun x hx => (hf x hx).neg

variable {i : Nat}

-- TODO: define `Neg` instance on `ContinuousLinearEquiv`,
-- prove it from `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`
/--
theorem `iteratedFDerivWithin_neg_apply` / 定理 `iteratedFDerivWithin_neg_apply`

English:
theorem iteratedFDerivWithin_neg_apply
  given: {f : E -> F} (hu : UniqueDiffOn 𝕜 s) (hx : x in s)
  proof: by
  induction i generalizing x with ext h
  | zero => simp
  | succ i hi =>
    calc
      iteratedFDerivWithin 𝕜 (i + 1) (-f) s x h =
          fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (-f) s) s x (h 0) (Fin.tail h) :=
        iteratedFDerivWithin_succ_apply_left _
      _ = fderivWithin 𝕜 (-itera

中文:
定理 iteratedFDerivWithin_neg_apply
  条件: {f : E -> F} (hu : UniqueDiffOn 𝕜 s) (hx : x in s)
  证明: by
  induction i generalizing x with ext h
  | zero => simp
  | succ i hi =>
    calc
      iteratedFDerivWithin 𝕜 (i + 1) (-f) s x h =
          fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (-f) s) s x (h 0) (Fin.tail h) :=
        iteratedFDerivWithin_succ_apply_left _
      _ = fderivWithin 𝕜 (-itera

Depends on / 依赖: Fin.tail, Pi.neg_def, fderivWithin, fderivWithin_congr, fderivWithin_neg, generalizing, iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left, neg_apply, neg_def
-/
theorem iteratedFDerivWithin_neg_apply {f : E -> F} (hu : UniqueDiffOn 𝕜 s) (hx : x in s) :
    iteratedFDerivWithin 𝕜 i (-f) s x = -iteratedFDerivWithin 𝕜 i f s x := by
  induction i generalizing x with ext h
  | zero => simp
  | succ i hi =>
    calc
      iteratedFDerivWithin 𝕜 (i + 1) (-f) s x h =
          fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (-f) s) s x (h 0) (Fin.tail h) :=
        iteratedFDerivWithin_succ_apply_left _
      _ = fderivWithin 𝕜 (-iteratedFDerivWithin 𝕜 i f s) s x (h 0) (Fin.tail h) := by
        rw [fderivWithin_congr' (@hi) hx]; rw [Pi.neg_def]
      _ = -(fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i f s) s) x (h 0) (Fin.tail h) := by
        rw [fderivWithin_neg (hu x hx)]; rw [neg_apply]; rw [neg_apply]
      _ = -(iteratedFDerivWithin 𝕜 (i + 1) f s) x h := by
        rw [iteratedFDerivWithin_succ_apply_left]

/--
theorem `iteratedFDeriv_neg_apply` / 定理 `iteratedFDeriv_neg_apply`

English:
theorem iteratedFDeriv_neg_apply
  given: {i : Nat} {f : E -> F}
  proof: by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_neg_apply uniqueDiffOn_univ (Set.mem_univ _)

中文:
定理 iteratedFDeriv_neg_apply
  条件: {i : 自然数} {f : E -> F}
  证明: by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_neg_apply uniqueDiffOn_univ (Set.mem_univ _)

Depends on / 依赖: Set.mem_univ, iteratedFDerivWithin_neg_apply, iteratedFDerivWithin_univ, mem_univ, simp_rw, uniqueDiffOn_univ
-/
theorem iteratedFDeriv_neg_apply {i : Nat} {f : E -> F} :
    iteratedFDeriv 𝕜 i (-f) x = -iteratedFDeriv 𝕜 i f x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_neg_apply uniqueDiffOn_univ (Set.mem_univ _)

/--
theorem `iteratedFDeriv_neg` / 定理 `iteratedFDeriv_neg`

English:
theorem iteratedFDeriv_neg
  given: {i : Nat} {f : E -> F}
  proof: funext fun _ => iteratedFDeriv_neg_apply

中文:
定理 iteratedFDeriv_neg
  条件: {i : 自然数} {f : E -> F}
  证明: funext fun _ => iteratedFDeriv_neg_apply

Depends on / 依赖: iteratedFDeriv_neg_apply
-/
theorem iteratedFDeriv_neg {i : Nat} {f : E -> F} :
    iteratedFDeriv 𝕜 i (-f) = -iteratedFDeriv 𝕜 i f :=
  funext fun _ => iteratedFDeriv_neg_apply

end Neg

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.sub` / 定理 `ContDiffWithinAt.sub`

English:
theorem ContDiffWithinAt.sub
  statement: {s : Set E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 ContDiffWithinAt.sub
  结论: {s : 集合 E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem ContDiffWithinAt.sub {s : Set E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x - g x) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
/--
theorem `ContDiffAt.sub` / 定理 `ContDiffAt.sub`

English:
theorem ContDiffAt.sub
  given: {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  proof: by simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 ContDiffAt.sub
  条件: {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  证明: by simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem ContDiffAt.sub {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x - g x) x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffOn.sub` / 定理 `ContDiffOn.sub`

English:
theorem ContDiffOn.sub
  statement: {s : Set E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 ContDiffOn.sub
  结论: {s : 集合 E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem ContDiffOn.sub {s : Set E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.sub` / 定理 `ContDiff.sub`

English:
theorem ContDiff.sub
  given: {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
  proof: by simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 连续可微.sub
  条件: {f g : E -> F} (hf : 连续可微 𝕜 n f) (hg : 连续可微 𝕜 n g)
  证明: by simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x - g x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

variable {i : Nat}

/--
theorem `iteratedFDerivWithin_sub_apply` / 定理 `iteratedFDerivWithin_sub_apply`

English:
theorem iteratedFDerivWithin_sub_apply
  statement: {f g : E -> F} (hf : ContDiffWithinAt 𝕜 i f s x)
  proof: by
  rw [sub_eq_add_neg]; rw [iteratedFDerivWithin_add_apply hf _ hu hx]; rw [iteratedFDerivWithin_neg_apply hu hx]; rw [sub_eq_add_neg]
  exact hg.neg

中文:
定理 iteratedFDerivWithin_sub_apply
  结论: {f g : E -> F} (hf : ContDiffWithinAt 𝕜 i f s x)
  证明: by
  rw [sub_eq_add_neg]; rw [iteratedFDerivWithin_add_apply hf _ hu hx]; rw [iteratedFDerivWithin_neg_apply hu hx]; rw [sub_eq_add_neg]
  exact hg.neg
-/
@[to_fun] theorem iteratedFDerivWithin_sub_apply {f g : E -> F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x in s) :
    iteratedFDerivWithin 𝕜 i (f - g) s x =
      iteratedFDerivWithin 𝕜 i f s x - iteratedFDerivWithin 𝕜 i g s x := by
  rw [sub_eq_add_neg]; rw [iteratedFDerivWithin_add_apply hf _ hu hx]; rw [iteratedFDerivWithin_neg_apply hu hx]; rw [sub_eq_add_neg]
  exact hg.neg

/--
theorem `iteratedFDeriv_sub_apply` / 定理 `iteratedFDeriv_sub_apply`

English:
theorem iteratedFDeriv_sub_apply
  statement: {i : Nat} {f g : E -> F}
  proof: by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_sub_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

中文:
定理 iteratedFDeriv_sub_apply
  结论: {i : 自然数} {f g : E -> F}
  证明: by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_sub_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)
-/
@[to_fun] theorem iteratedFDeriv_sub_apply {i : Nat} {f g : E -> F}
    (hf : ContDiffAt 𝕜 i f x) (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (f - g) x = iteratedFDeriv 𝕜 i f x - iteratedFDeriv 𝕜 i g x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_sub_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

/--
theorem `iteratedFDeriv_sub` / 定理 `iteratedFDeriv_sub`

English:
theorem iteratedFDeriv_sub
  statement: {i : Nat} {f g : E -> F} (hf : ContDiff 𝕜 i f)
  proof: funext fun _ => iteratedFDeriv_sub_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)

中文:
定理 iteratedFDeriv_sub
  结论: {i : 自然数} {f g : E -> F} (hf : 连续可微 𝕜 i f)
  证明: funext fun _ => iteratedFDeriv_sub_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)
-/
@[to_fun] theorem iteratedFDeriv_sub {i : Nat} {f g : E -> F} (hf : ContDiff 𝕜 i f)
    (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (f - g) = iteratedFDeriv 𝕜 i f - iteratedFDeriv 𝕜 i g :=
  funext fun _ => iteratedFDeriv_sub_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)

/-! ### Sum of finitely many functions -/

@[fun_prop]
/--
theorem `ContDiffWithinAt.sum` / 定理 `ContDiffWithinAt.sum`

English:
theorem ContDiffWithinAt.sum
  statement: {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {t : Set E} {x : E}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [contDiffWithinAt_const]
  | insert i s is IH =>
    simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add
      (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))

@[fun_prop]

中文:
定理 ContDiffWithinAt.求和
  结论: {ι : 类型} {f : ι -> E -> F} {s : 有限集 ι} {t : 集合 E} {x : E}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [contDiffWithinAt_const]
  | insert i s is IH =>
    simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add
      (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))

@[fun_prop]

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_insert, classical, contDiffWithinAt_const, induction_on, insert, mem_insert_of_mem, mem_insert_self, not_false_iff, sum_insert
-/
theorem ContDiffWithinAt.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {t : Set E} {x : E}
    (h : forall i in s, ContDiffWithinAt 𝕜 n (fun x => f i x) t x) :
    ContDiffWithinAt 𝕜 n (fun x => ∑ i in s, f i x) t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [contDiffWithinAt_const]
  | insert i s is IH =>
    simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add
      (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))

@[fun_prop]
/--
theorem `ContDiffAt.sum` / 定理 `ContDiffAt.sum`

English:
theorem ContDiffAt.sum
  statement: {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {x : E}
  proof: by
  rw [← contDiffWithinAt_univ] at *; exact ContDiffWithinAt.sum h

@[fun_prop]

中文:
定理 ContDiffAt.求和
  结论: {ι : 类型} {f : ι -> E -> F} {s : 有限集 ι} {x : E}
  证明: by
  rw [← contDiffWithinAt_univ] at *; exact ContDiffWithinAt.sum h

@[fun_prop]

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.sum, contDiffWithinAt_univ
-/
theorem ContDiffAt.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {x : E}
    (h : forall i in s, ContDiffAt 𝕜 n (fun x => f i x) x) :
    ContDiffAt 𝕜 n (fun x => ∑ i in s, f i x) x := by
  rw [← contDiffWithinAt_univ] at *; exact ContDiffWithinAt.sum h

@[fun_prop]
/--
theorem `ContDiffOn.sum` / 定理 `ContDiffOn.sum`

English:
theorem ContDiffOn.sum
  statement: {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {t : Set E}
  proof: fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx

@[fun_prop]

中文:
定理 ContDiffOn.求和
  结论: {ι : 类型} {f : ι -> E -> F} {s : 有限集 ι} {t : 集合 E}
  证明: fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx

@[fun_prop]
-/
theorem ContDiffOn.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {t : Set E}
    (h : forall i in s, ContDiffOn 𝕜 n (fun x => f i x) t) :
    ContDiffOn 𝕜 n (fun x => ∑ i in s, f i x) t := fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx

@[fun_prop]
/--
theorem `ContDiff.sum` / 定理 `ContDiff.sum`

English:
theorem ContDiff.sum
  statement: {ι : Type*} {f : ι -> E -> F} {s : Finset ι}
  proof: by
  simp only [← contDiffOn_univ] at *; exact ContDiffOn.sum h

中文:
定理 连续可微.求和
  结论: {ι : 类型} {f : ι -> E -> F} {s : 有限集 ι}
  证明: by
  simp only [← contDiffOn_univ] at *; exact ContDiffOn.sum h

Depends on / 依赖: ContDiffOn, ContDiffOn.sum, contDiffOn_univ
-/
theorem ContDiff.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι}
    (h : forall i in s, ContDiff 𝕜 n fun x => f i x) : ContDiff 𝕜 n fun x => ∑ i in s, f i x := by
  simp only [← contDiffOn_univ] at *; exact ContDiffOn.sum h

/--
theorem `iteratedFDerivWithin_sum_apply` / 定理 `iteratedFDerivWithin_sum_apply`

English:
theorem iteratedFDerivWithin_sum_apply
  statement: {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat} {x : E}
  proof: by
  rw [(by aesop : (∑ j in u]; rw [f j) = (fun x => ∑ j in u]; rw [f j x))]
  induction u using Finset.cons_induction with
  | empty => simp
  | cons a u ha IH =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    simp only [Finset.sum_cons]
    rw [fun_iteratedFDerivWithin_add_apply h.1 (

中文:
定理 iteratedFDerivWithin_sum_apply
  结论: {ι : 类型} {f : ι -> E -> F} {u : 有限集 ι} {i : 自然数} {x : E}
  证明: by
  rw [(by aesop : (∑ j in u]; rw [f j) = (fun x => ∑ j in u]; rw [f j x))]
  induction u using Finset.cons_induction with
  | empty => simp
  | cons a u ha IH =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    simp only [Finset.sum_cons]
    rw [fun_iteratedFDerivWithin_add_apply h.1 (

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.sum, Finset, Finset.cons_induction, Finset.mem_cons, Finset.sum_cons, cons_induction, forall_eq_or_imp, fun_iteratedFDerivWithin_add_apply, mem_cons, sum_cons
-/
theorem iteratedFDerivWithin_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (h : forall j in u, ContDiffWithinAt 𝕜 i (f j) s x) :
    iteratedFDerivWithin 𝕜 i (∑ j in u, f j) s x =
      ∑ j in u, iteratedFDerivWithin 𝕜 i (f j) s x := by
  rw [(by aesop : (∑ j in u]; rw [f j) = (fun x => ∑ j in u]; rw [f j x))]
  induction u using Finset.cons_induction with
  | empty => simp
  | cons a u ha IH =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    simp only [Finset.sum_cons]
    rw [fun_iteratedFDerivWithin_add_apply h.1 (ContDiffWithinAt.sum h.2) hs hx]; rw [IH h.2]

/--
theorem `iteratedFDerivWithin_fun_sum_apply` / 定理 `iteratedFDerivWithin_fun_sum_apply`

English:
theorem iteratedFDerivWithin_fun_sum_apply
  statement: {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat}
  proof: by
  convert! iteratedFDerivWithin_sum_apply hs hx h
  rw [Finset.sum_apply]

中文:
定理 iteratedFDerivWithin_fun_sum_apply
  结论: {ι : 类型} {f : ι -> E -> F} {u : 有限集 ι} {i : 自然数}
  证明: by
  convert! iteratedFDerivWithin_sum_apply hs hx h
  rw [Finset.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, convert, iteratedFDerivWithin_sum_apply, sum_apply
-/
theorem iteratedFDerivWithin_fun_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat}
    {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (h : forall j in u, ContDiffWithinAt 𝕜 i (f j) s x) :
    iteratedFDerivWithin 𝕜 i (fun z => ∑ j in u, f j z) s x =
      ∑ j in u, iteratedFDerivWithin 𝕜 i (f j) s x := by
  convert! iteratedFDerivWithin_sum_apply hs hx h
  rw [Finset.sum_apply]

/--
theorem `iteratedFDeriv_sum_apply` / 定理 `iteratedFDeriv_sum_apply`

English:
theorem iteratedFDeriv_sum_apply
  statement: {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {n : Nat} {x : E}
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  apply iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (Set.mem_univ x)
    (h · · |>.contDiffWithinAt)

中文:
定理 iteratedFDeriv_sum_apply
  结论: {ι : 类型} {f : ι -> E -> F} {u : 有限集 ι} {n : 自然数} {x : E}
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  apply iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (Set.mem_univ x)
    (h · · |>.contDiffWithinAt)

Depends on / 依赖: Set.mem_univ, contDiffWithinAt, iteratedFDerivWithin_sum_apply, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedFDeriv_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {n : Nat} {x : E}
    (h : forall j in u, ContDiffAt 𝕜 n (f j) x) :
    iteratedFDeriv 𝕜 n (∑ j in u, f j) x = ∑ j in u, iteratedFDeriv 𝕜 n (f j) x := by
  simp only [← iteratedFDerivWithin_univ]
  apply iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (Set.mem_univ x)
    (h · · |>.contDiffWithinAt)

/--
theorem `iteratedFDeriv_fun_sum_apply` / 定理 `iteratedFDeriv_fun_sum_apply`

English:
theorem iteratedFDeriv_fun_sum_apply
  statement: {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {n : Nat} {x : E}
  proof: by
  convert! iteratedFDeriv_sum_apply h
  rw [Finset.sum_apply]

中文:
定理 iteratedFDeriv_fun_sum_apply
  结论: {ι : 类型} {f : ι -> E -> F} {u : 有限集 ι} {n : 自然数} {x : E}
  证明: by
  convert! iteratedFDeriv_sum_apply h
  rw [Finset.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, convert, iteratedFDeriv_sum_apply, sum_apply
-/
theorem iteratedFDeriv_fun_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {n : Nat} {x : E}
    (h : forall j in u, ContDiffAt 𝕜 n (f j) x) :
    iteratedFDeriv 𝕜 n (fun z => ∑ j in u, f j z) x = ∑ j in u, iteratedFDeriv 𝕜 n (f j) x := by
  convert! iteratedFDeriv_sum_apply h
  rw [Finset.sum_apply]

/--
theorem `iteratedFDeriv_sum` / 定理 `iteratedFDeriv_sum`

English:
theorem iteratedFDeriv_sum
  statement: {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat}
  proof: funext fun x => by simpa [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) (h · · |>.contDiffWithinAt)

中文:
定理 iteratedFDeriv_sum
  结论: {ι : 类型} {f : ι -> E -> F} {u : 有限集 ι} {i : 自然数}
  证明: funext fun x => by simpa [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) (h · · |>.contDiffWithinAt)

Depends on / 依赖: contDiffWithinAt, iteratedFDerivWithin_fun_sum_apply, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedFDeriv_sum {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat}
    (h : forall j in u, ContDiff 𝕜 i (f j)) :
    iteratedFDeriv 𝕜 i (∑ j in u, f j ·) = ∑ j in u, iteratedFDeriv 𝕜 i (f j) :=
  funext fun x => by simpa [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) (h · · |>.contDiffWithinAt)

/-! ### Product of two functions -/

section MulProd

variable {𝔸 𝔸' ι 𝕜' : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [NormedCommRing 𝔸']
  [NormedAlgebra 𝕜 𝔸'] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

-- The product is smooth.
@[fun_prop]
/--
theorem `contDiff_mul` / 定理 `contDiff_mul`

English:
theorem contDiff_mul
  statement: ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2
  proof: (ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.contDiff

中文:
定理 contDiff_mul
  结论: 连续可微 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2
  证明: (ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.contDiff

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, contDiff, isBoundedBilinearMap, isBoundedBilinearMap.contDiff
-/
theorem contDiff_mul : ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2 :=
  (ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.contDiff

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.mul` / 定理 `ContDiffWithinAt.mul`

English:
theorem ContDiffWithinAt.mul
  statement: {s : Set E} {f g : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: contDiff_mul.comp_contDiffWithinAt (hf.prodMk hg)

中文:
定理 ContDiffWithinAt.mul
  结论: {s : 集合 E} {f g : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: contDiff_mul.comp_contDiffWithinAt (hf.prodMk hg)

Depends on / 依赖: comp_contDiffWithinAt, contDiff_mul, contDiff_mul.comp_contDiffWithinAt, hf.prodMk, prodMk
-/
theorem ContDiffWithinAt.mul {s : Set E} {f g : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x * g x) s x :=
  contDiff_mul.comp_contDiffWithinAt (hf.prodMk hg)

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
nonrec theorem ContDiffAt.mul {f g : E -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x * g x) x :=
  hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffOn.mul` / 定理 `ContDiffOn.mul`

English:
theorem ContDiffOn.mul
  given: {f g : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s)
  proof: fun x hx => (hf x hx).mul (hg x hx)

中文:
定理 ContDiffOn.mul
  条件: {f g : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s)
  证明: fun x hx => (hf x hx).mul (hg x hx)
-/
theorem ContDiffOn.mul {f g : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x * g x) s := fun x hx => (hf x hx).mul (hg x hx)

/-- The product of two `C^n` functions is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.mul` / 定理 `ContDiff.mul`

English:
theorem ContDiff.mul
  given: {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
  proof: contDiff_mul.comp (hf.prodMk hg)

@[fun_prop]

中文:
定理 连续可微.mul
  条件: {f g : E -> 𝔸} (hf : 连续可微 𝕜 n f) (hg : 连续可微 𝕜 n g)
  证明: contDiff_mul.comp (hf.prodMk hg)

@[fun_prop]

Depends on / 依赖: contDiff_mul, contDiff_mul.comp, hf.prodMk, prodMk
-/
theorem ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x * g x :=
  contDiff_mul.comp (hf.prodMk hg)

@[fun_prop]
/--
theorem `contDiffWithinAt_prod'` / 定理 `contDiffWithinAt_prod'`

English:
theorem contDiffWithinAt_prod'
  statement: {t : Finset ι} {f : ι -> E -> 𝔸'}
  proof: Finset.prod_induction f (fun f => ContDiffWithinAt 𝕜 n f s x) (fun _ _ => ContDiffWithinAt.mul)
    (contDiffWithinAt_const (c := 1)) h

@[fun_prop]

中文:
定理 contDiffWithinAt_prod'
  结论: {t : 有限集 ι} {f : ι -> E -> 𝔸'}
  证明: Finset.prod_induction f (fun f => ContDiffWithinAt 𝕜 n f s x) (fun _ _ => ContDiffWithinAt.mul)
    (contDiffWithinAt_const (c := 1)) h

@[fun_prop]

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.mul, Finset, Finset.prod_induction, contDiffWithinAt_const, prod_induction
-/
theorem contDiffWithinAt_prod' {t : Finset ι} {f : ι -> E -> 𝔸'}
    (h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 n (∏ i in t, f i) s x :=
  Finset.prod_induction f (fun f => ContDiffWithinAt 𝕜 n f s x) (fun _ _ => ContDiffWithinAt.mul)
    (contDiffWithinAt_const (c := 1)) h

@[fun_prop]
/--
theorem `contDiffWithinAt_prod` / 定理 `contDiffWithinAt_prod`

English:
theorem contDiffWithinAt_prod
  statement: {t : Finset ι} {f : ι -> E -> 𝔸'}
  proof: by
  simpa only [← Finset.prod_apply] using contDiffWithinAt_prod' h

@[fun_prop]

中文:
定理 contDiffWithinAt_prod
  结论: {t : 有限集 ι} {f : ι -> E -> 𝔸'}
  证明: by
  simpa only [← Finset.prod_apply] using contDiffWithinAt_prod' h

@[fun_prop]

Depends on / 依赖: Finset, Finset.prod_apply, contDiffWithinAt_prod, prod_apply
-/
theorem contDiffWithinAt_prod {t : Finset ι} {f : ι -> E -> 𝔸'}
    (h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x) :
    ContDiffWithinAt 𝕜 n (fun y => ∏ i in t, f i y) s x := by
  simpa only [← Finset.prod_apply] using contDiffWithinAt_prod' h

@[fun_prop]
/--
theorem `contDiffAt_prod'` / 定理 `contDiffAt_prod'`

English:
theorem contDiffAt_prod'
  given: {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffAt 𝕜 n (f i) x)
  proof: contDiffWithinAt_prod' h

@[fun_prop]

中文:
定理 contDiffAt_prod'
  条件: {t : 有限集 ι} {f : ι -> E -> 𝔸'} (h : 对任意 i in t, ContDiffAt 𝕜 n (f i) x)
  证明: contDiffWithinAt_prod' h

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_prod
-/
theorem contDiffAt_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (∏ i in t, f i) x :=
  contDiffWithinAt_prod' h

@[fun_prop]
/--
theorem `contDiffAt_prod` / 定理 `contDiffAt_prod`

English:
theorem contDiffAt_prod
  given: {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffAt 𝕜 n (f i) x)
  proof: contDiffWithinAt_prod h

@[fun_prop]

中文:
定理 contDiffAt_prod
  条件: {t : 有限集 ι} {f : ι -> E -> 𝔸'} (h : 对任意 i in t, ContDiffAt 𝕜 n (f i) x)
  证明: contDiffWithinAt_prod h

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_prod
-/
theorem contDiffAt_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (fun y => ∏ i in t, f i y) x :=
  contDiffWithinAt_prod h

@[fun_prop]
/--
theorem `contDiffOn_prod'` / 定理 `contDiffOn_prod'`

English:
theorem contDiffOn_prod'
  given: {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffOn 𝕜 n (f i) s)
  proof: fun x hx => contDiffWithinAt_prod' fun i hi => h i hi x hx

@[fun_prop]

中文:
定理 contDiffOn_prod'
  条件: {t : 有限集 ι} {f : ι -> E -> 𝔸'} (h : 对任意 i in t, ContDiffOn 𝕜 n (f i) s)
  证明: fun x hx => contDiffWithinAt_prod' fun i hi => h i hi x hx

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_prod
-/
theorem contDiffOn_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (∏ i in t, f i) s := fun x hx => contDiffWithinAt_prod' fun i hi => h i hi x hx

@[fun_prop]
/--
theorem `contDiffOn_prod` / 定理 `contDiffOn_prod`

English:
theorem contDiffOn_prod
  given: {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffOn 𝕜 n (f i) s)
  proof: fun x hx =>
  contDiffWithinAt_prod fun i hi => h i hi x hx

@[fun_prop]

中文:
定理 contDiffOn_prod
  条件: {t : 有限集 ι} {f : ι -> E -> 𝔸'} (h : 对任意 i in t, ContDiffOn 𝕜 n (f i) s)
  证明: fun x hx =>
  contDiffWithinAt_prod fun i hi => h i hi x hx

@[fun_prop]
-/
theorem contDiffOn_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (fun y => ∏ i in t, f i y) s := fun x hx =>
  contDiffWithinAt_prod fun i hi => h i hi x hx

@[fun_prop]
/--
theorem `contDiff_prod'` / 定理 `contDiff_prod'`

English:
theorem contDiff_prod'
  given: {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiff 𝕜 n (f i))
  proof: contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod' fun i hi => (h i hi).contDiffAt

@[fun_prop]

中文:
定理 contDiff_prod'
  条件: {t : 有限集 ι} {f : ι -> E -> 𝔸'} (h : 对任意 i in t, 连续可微 𝕜 n (f i))
  证明: contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod' fun i hi => (h i hi).contDiffAt

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiffAt_prod, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr
-/
theorem contDiff_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n (∏ i in t, f i) :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod' fun i hi => (h i hi).contDiffAt

@[fun_prop]
/--
theorem `contDiff_prod` / 定理 `contDiff_prod`

English:
theorem contDiff_prod
  given: {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiff 𝕜 n (f i))
  proof: contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod fun i hi => (h i hi).contDiffAt

@[fun_prop]

中文:
定理 contDiff_prod
  条件: {t : 有限集 ι} {f : ι -> E -> 𝔸'} (h : 对任意 i in t, 连续可微 𝕜 n (f i))
  证明: contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod fun i hi => (h i hi).contDiffAt

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiffAt_prod, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr
-/
theorem contDiff_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n fun y => ∏ i in t, f i y :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod fun i hi => (h i hi).contDiffAt

@[fun_prop]
/--
theorem `ContDiff.pow` / 定理 `ContDiff.pow`

English:
theorem ContDiff.pow
  given: {f : E -> 𝔸} (hf : ContDiff 𝕜 n f)
  statement: forall m : Nat, ContDiff 𝕜 n fun x => f x ^ m

中文:
定理 连续可微.pow
  条件: {f : E -> 𝔸} (hf : 连续可微 𝕜 n f)
  结论: 对任意 m : 自然数, 连续可微 𝕜 n fun x => f x ^ m
-/
theorem ContDiff.pow {f : E -> 𝔸} (hf : ContDiff 𝕜 n f) : forall m : Nat, ContDiff 𝕜 n fun x => f x ^ m
  | 0 => by simpa using contDiff_const
  | m + 1 => by simpa [pow_succ] using (hf.pow m).mul hf

@[fun_prop]
/--
theorem `ContDiffWithinAt.pow` / 定理 `ContDiffWithinAt.pow`

English:
theorem ContDiffWithinAt.pow
  given: {f : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : Nat)
  proof: (contDiff_id.pow m).comp_contDiffWithinAt hf

@[fun_prop]
nonrec theorem ContDiffAt.pow {f : E -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (m : Nat) :
    ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  hf.pow m

@[fun_prop]

中文:
定理 ContDiffWithinAt.pow
  条件: {f : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : 自然数)
  证明: (contDiff_id.pow m).comp_contDiffWithinAt hf

@[fun_prop]
nonrec theorem ContDiffAt.pow {f : E -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (m : Nat) :
    ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  hf.pow m

@[fun_prop]

Depends on / 依赖: comp_contDiffWithinAt, contDiff_id, contDiff_id.pow
-/
theorem ContDiffWithinAt.pow {f : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : Nat) :
    ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x :=
  (contDiff_id.pow m).comp_contDiffWithinAt hf

@[fun_prop]
nonrec theorem ContDiffAt.pow {f : E -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (m : Nat) :
    ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  hf.pow m

@[fun_prop]
/--
theorem `ContDiffOn.pow` / 定理 `ContDiffOn.pow`

English:
theorem ContDiffOn.pow
  given: {f : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : Nat)
  proof: fun y hy => (hf y hy).pow m

@[fun_prop]

中文:
定理 ContDiffOn.pow
  条件: {f : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : 自然数)
  证明: fun y hy => (hf y hy).pow m

@[fun_prop]
-/
theorem ContDiffOn.pow {f : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : Nat) :
    ContDiffOn 𝕜 n (fun y => f y ^ m) s := fun y hy => (hf y hy).pow m

@[fun_prop]
/--
theorem `ContDiffWithinAt.div_const` / 定理 `ContDiffWithinAt.div_const`

English:
theorem ContDiffWithinAt.div_const
  given: {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜')
  proof: by
  simpa only [div_eq_mul_inv] using hf.mul contDiffWithinAt_const

@[fun_prop]
nonrec theorem ContDiffAt.div_const {f : E -> 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (c : 𝕜') :
    ContDiffAt 𝕜 n (fun x => f x / c) x :=
  hf.div_const c

@[fun_prop]

中文:
定理 ContDiffWithinAt.div_const
  条件: {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜')
  证明: by
  simpa only [div_eq_mul_inv] using hf.mul contDiffWithinAt_const

@[fun_prop]
nonrec theorem ContDiffAt.div_const {f : E -> 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (c : 𝕜') :
    ContDiffAt 𝕜 n (fun x => f x / c) x :=
  hf.div_const c

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_const, div_eq_mul_inv, hf.mul
-/
theorem ContDiffWithinAt.div_const {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') :
    ContDiffWithinAt 𝕜 n (fun x => f x / c) s x := by
  simpa only [div_eq_mul_inv] using hf.mul contDiffWithinAt_const

@[fun_prop]
nonrec theorem ContDiffAt.div_const {f : E -> 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (c : 𝕜') :
    ContDiffAt 𝕜 n (fun x => f x / c) x :=
  hf.div_const c

@[fun_prop]
/--
theorem `ContDiffOn.div_const` / 定理 `ContDiffOn.div_const`

English:
theorem ContDiffOn.div_const
  given: {f : E -> 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜')
  proof: fun x hx => (hf x hx).div_const c

@[fun_prop]

中文:
定理 ContDiffOn.div_const
  条件: {f : E -> 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜')
  证明: fun x hx => (hf x hx).div_const c

@[fun_prop]

Depends on / 依赖: div_const
-/
theorem ContDiffOn.div_const {f : E -> 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜') :
    ContDiffOn 𝕜 n (fun x => f x / c) s := fun x hx => (hf x hx).div_const c

@[fun_prop]
/--
theorem `ContDiff.div_const` / 定理 `ContDiff.div_const`

English:
theorem ContDiff.div_const
  given: {f : E -> 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜')
  proof: by simpa only [div_eq_mul_inv] using hf.mul contDiff_const

中文:
定理 连续可微.div_const
  条件: {f : E -> 𝕜'} {n} (hf : 连续可微 𝕜 n f) (c : 𝕜')
  证明: by simpa only [div_eq_mul_inv] using hf.mul contDiff_const

Depends on / 依赖: contDiff_const, div_eq_mul_inv, hf.mul
-/
theorem ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜') :
    ContDiff 𝕜 n fun x => f x / c := by simpa only [div_eq_mul_inv] using hf.mul contDiff_const


end MulProd

/-! ### Scalar multiplication -/

section SMul

variable {𝕜' : Type*} [NormedRing 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

-- The scalar multiplication is smooth.
@[fun_prop]
/--
theorem `contDiff_smul` / 定理 `contDiff_smul`

English:
theorem contDiff_smul
  statement: ContDiff 𝕜 n fun p : 𝕜' × F => p.1 • p.2
  proof: isBoundedBilinearMap_smul.contDiff

中文:
定理 contDiff_smul
  结论: 连续可微 𝕜 n fun p : 𝕜' × F => p.1 • p.2
  证明: isBoundedBilinearMap_smul.contDiff

Depends on / 依赖: contDiff, isBoundedBilinearMap_smul, isBoundedBilinearMap_smul.contDiff
-/
theorem contDiff_smul : ContDiff 𝕜 n fun p : 𝕜' × F => p.1 • p.2 :=
  isBoundedBilinearMap_smul.contDiff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
@[to_fun (attr := fun_prop)]
/--
theorem `ContDiffWithinAt.smul` / 定理 `ContDiffWithinAt.smul`

English:
theorem ContDiffWithinAt.smul
  statement: {s : Set E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: contDiff_smul.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

中文:
定理 ContDiffWithinAt.smul
  结论: {s : 集合 E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: contDiff_smul.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

Depends on / 依赖: contDiffWithinAt, contDiff_smul, contDiff_smul.contDiffWithinAt.comp, hf.prodMk, prodMk, subset_preimage_univ
-/
theorem ContDiffWithinAt.smul {s : Set E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (f • g) s x :=
  contDiff_smul.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
@[to_fun (attr := fun_prop)]
/--
theorem `ContDiffAt.smul` / 定理 `ContDiffAt.smul`

English:
theorem ContDiffAt.smul
  statement: {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffAt 𝕜 n f x)
  proof: by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul hg

中文:
定理 ContDiffAt.smul
  结论: {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffAt 𝕜 n f x)
  证明: by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul hg

Depends on / 依赖: contDiffWithinAt_univ, hf.smul
-/
theorem ContDiffAt.smul {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (f • g) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
@[to_fun (attr := fun_prop)]
/--
theorem `ContDiff.smul` / 定理 `ContDiff.smul`

English:
theorem ContDiff.smul
  given: {f : E -> 𝕜'} {g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
  proof: contDiff_smul.comp (hf.prodMk hg)

中文:
定理 连续可微.smul
  条件: {f : E -> 𝕜'} {g : E -> F} (hf : 连续可微 𝕜 n f) (hg : 连续可微 𝕜 n g)
  证明: contDiff_smul.comp (hf.prodMk hg)

Depends on / 依赖: contDiff_smul, contDiff_smul.comp, hf.prodMk, prodMk
-/
theorem ContDiff.smul {f : E -> 𝕜'} {g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (f • g) :=
  contDiff_smul.comp (hf.prodMk hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
@[to_fun (attr := fun_prop)]
/--
theorem `ContDiffOn.smul` / 定理 `ContDiffOn.smul`

English:
theorem ContDiffOn.smul
  statement: {s : Set E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  proof: fun x hx =>
  (hf x hx).smul (hg x hx)

中文:
定理 ContDiffOn.smul
  结论: {s : 集合 E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  证明: fun x hx =>
  (hf x hx).smul (hg x hx)
-/
theorem ContDiffOn.smul {s : Set E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (f • g) s := fun x hx =>
  (hf x hx).smul (hg x hx)

end SMul

/-! ### Constant scalar multiplication

TODO: generalize results in this section -- if `c` is a unit (or `R` is a group), then one can
drop `ContDiff*` assumptions in some lemmas about `iteratedFDeriv` and `iteratedFDerivWithin`.
-/

section ConstSMul

variable {R A : Type*} [DistribSMul R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  [NormedRing A] [NormedAlgebra 𝕜 A] [Module A F] [IsScalarTower 𝕜 A F] [IsBoundedSMul A F]

/-- Scalar multiplication is smooth (as a function of the vector variable). -/
@[fun_prop]
/--
theorem `contDiff_const_smul` / 定理 `contDiff_const_smul`

English:
theorem contDiff_const_smul
  given: (c : R)
  statement: ContDiff 𝕜 n fun p : F => c • p
  proof: (c • ContinuousLinearMap.id 𝕜 F).contDiff

中文:
定理 contDiff_const_smul
  条件: (c : R)
  结论: 连续可微 𝕜 n fun p : F => c • p
  证明: (c • ContinuousLinearMap.id 𝕜 F).contDiff

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, contDiff
-/
theorem contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : F => c • p :=
  (c • ContinuousLinearMap.id 𝕜 F).contDiff

/-- Scalar multiplication is smooth (as a function of the scalar variable). -/
@[fun_prop]
/--
theorem `contDiff_smul_const` / 定理 `contDiff_smul_const`

English:
theorem contDiff_smul_const
  given: (v : F)
  statement: ContDiff 𝕜 n fun a : A => a • v
  proof: ((ContinuousLinearMap.id 𝕜 A).smulRight v).contDiff

中文:
定理 contDiff_smul_const
  条件: (v : F)
  结论: 连续可微 𝕜 n fun a : A => a • v
  证明: ((ContinuousLinearMap.id 𝕜 A).smulRight v).contDiff

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, contDiff, smulRight
-/
theorem contDiff_smul_const (v : F) : ContDiff 𝕜 n fun a : A => a • v :=
  ((ContinuousLinearMap.id 𝕜 A).smulRight v).contDiff

/-- The scalar multiplication of a constant and a `C^n` function within a set at a point is `C^n`
within this set at this point. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.const_smul` / 定理 `ContDiffWithinAt.const_smul`

English:
theorem ContDiffWithinAt.const_smul
  statement: {s : Set E} {f : E -> F} {x : E} (c : R)
  proof: (contDiff_const_smul c).contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.const_smul
  结论: {s : 集合 E} {f : E -> F} {x : E} (c : R)
  证明: (contDiff_const_smul c).contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt, contDiffAt.comp_contDiffWithinAt, contDiff_const_smul
-/
theorem ContDiffWithinAt.const_smul {s : Set E} {f : E -> F} {x : E} (c : R)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun y => c • f y) s x :=
  (contDiff_const_smul c).contDiffAt.comp_contDiffWithinAt x hf

/-- The scalar multiplication of `C^n` function within a set at a point and a constant and is `C^n`
within this set at this point. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.smul_const` / 定理 `ContDiffWithinAt.smul_const`

English:
theorem ContDiffWithinAt.smul_const
  statement: {s : Set E} {f : E -> A} {x : E}
  proof: (contDiff_smul_const v).contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.smul_const
  结论: {s : 集合 E} {f : E -> A} {x : E}
  证明: (contDiff_smul_const v).contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt, contDiffAt.comp_contDiffWithinAt, contDiff_smul_const
-/
theorem ContDiffWithinAt.smul_const {s : Set E} {f : E -> A} {x : E}
    (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) : ContDiffWithinAt 𝕜 n (fun y => f y • v) s x :=
  (contDiff_smul_const v).contDiffAt.comp_contDiffWithinAt x hf

/-- The scalar multiplication of a constant and a `C^n` function at a point is `C^n` at this
point. -/
@[fun_prop]
/--
theorem `ContDiffAt.const_smul` / 定理 `ContDiffAt.const_smul`

English:
theorem ContDiffAt.const_smul
  given: {f : E -> F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f x)
  proof: by
  rw [← contDiffWithinAt_univ] at *; exact hf.const_smul c

中文:
定理 ContDiffAt.const_smul
  条件: {f : E -> F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f x)
  证明: by
  rw [← contDiffWithinAt_univ] at *; exact hf.const_smul c

Depends on / 依赖: const_smul, contDiffWithinAt_univ, hf.const_smul
-/
theorem ContDiffAt.const_smul {f : E -> F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun y => c • f y) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.const_smul c

/-- The scalar multiplication of a `C^n` function at a point and a constant is `C^n` at this
point. -/
@[fun_prop]
/--
theorem `ContDiffAt.smul_const` / 定理 `ContDiffAt.smul_const`

English:
theorem ContDiffAt.smul_const
  given: {f : E -> A} {x : E} (hf : ContDiffAt 𝕜 n f x) (v : F)
  proof: by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul_const v

中文:
定理 ContDiffAt.smul_const
  条件: {f : E -> A} {x : E} (hf : ContDiffAt 𝕜 n f x) (v : F)
  证明: by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul_const v

Depends on / 依赖: contDiffWithinAt_univ, hf.smul_const, smul_const
-/
theorem ContDiffAt.smul_const {f : E -> A} {x : E} (hf : ContDiffAt 𝕜 n f x) (v : F) :
    ContDiffAt 𝕜 n (fun y => f y • v) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul_const v

/-- The scalar multiplication of a constant and a `C^n` function is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.const_smul` / 定理 `ContDiff.const_smul`

English:
theorem ContDiff.const_smul
  given: {f : E -> F} (c : R) (hf : ContDiff 𝕜 n f)
  proof: (contDiff_const_smul c).comp hf

中文:
定理 连续可微.const_smul
  条件: {f : E -> F} (c : R) (hf : 连续可微 𝕜 n f)
  证明: (contDiff_const_smul c).comp hf

Depends on / 依赖: contDiff_const_smul
-/
theorem ContDiff.const_smul {f : E -> F} (c : R) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun y => c • f y :=
  (contDiff_const_smul c).comp hf

/-- The scalar multiplication of a `C^n` function and a constant is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.smul_const` / 定理 `ContDiff.smul_const`

English:
theorem ContDiff.smul_const
  given: {f : E -> A} (hf : ContDiff 𝕜 n f) (v : F)
  proof: (contDiff_smul_const v).comp hf

中文:
定理 连续可微.smul_const
  条件: {f : E -> A} (hf : 连续可微 𝕜 n f) (v : F)
  证明: (contDiff_smul_const v).comp hf

Depends on / 依赖: contDiff_smul_const
-/
theorem ContDiff.smul_const {f : E -> A} (hf : ContDiff 𝕜 n f) (v : F) :
    ContDiff 𝕜 n fun y => f y • v :=
  (contDiff_smul_const v).comp hf

/-- The scalar multiplication of a constant and a `C^n` function on a domain is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffOn.const_smul` / 定理 `ContDiffOn.const_smul`

English:
theorem ContDiffOn.const_smul
  given: {s : Set E} {f : E -> F} (c : R) (hf : ContDiffOn 𝕜 n f s)
  proof: fun x hx => (hf x hx).const_smul c

中文:
定理 ContDiffOn.const_smul
  条件: {s : 集合 E} {f : E -> F} (c : R) (hf : ContDiffOn 𝕜 n f s)
  证明: fun x hx => (hf x hx).const_smul c

Depends on / 依赖: const_smul
-/
theorem ContDiffOn.const_smul {s : Set E} {f : E -> F} (c : R) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun y => c • f y) s := fun x hx => (hf x hx).const_smul c

/-- The scalar multiplication of a `C^n` function on a domain and a constant is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffOn.smul_const` / 定理 `ContDiffOn.smul_const`

English:
theorem ContDiffOn.smul_const
  given: {s : Set E} {f : E -> A} (hf : ContDiffOn 𝕜 n f s) (v : F)
  proof: fun x hx => (hf x hx).smul_const v

中文:
定理 ContDiffOn.smul_const
  条件: {s : 集合 E} {f : E -> A} (hf : ContDiffOn 𝕜 n f s) (v : F)
  证明: fun x hx => (hf x hx).smul_const v

Depends on / 依赖: smul_const
-/
theorem ContDiffOn.smul_const {s : Set E} {f : E -> A} (hf : ContDiffOn 𝕜 n f s) (v : F) :
    ContDiffOn 𝕜 n (fun y => f y • v) s := fun x hx => (hf x hx).smul_const v

variable {i : Nat} {a : R} {v : F}

/--
theorem `iteratedFDerivWithin_const_smul_apply` / 定理 `iteratedFDerivWithin_const_smul_apply`

English:
theorem iteratedFDerivWithin_const_smul_apply
  statement: (hf : ContDiffWithinAt 𝕜 i f s x)
  proof: (a • (1 : F ->L[𝕜] F)).iteratedFDerivWithin_comp_left hf hu hx le_rfl

中文:
定理 iteratedFDerivWithin_const_smul_apply
  结论: (hf : ContDiffWithinAt 𝕜 i f s x)
  证明: (a • (1 : F ->L[𝕜] F)).iteratedFDerivWithin_comp_left hf hu hx le_rfl

Depends on / 依赖: iteratedFDerivWithin_comp_left, le_rfl
-/
theorem iteratedFDerivWithin_const_smul_apply (hf : ContDiffWithinAt 𝕜 i f s x)
    (hu : UniqueDiffOn 𝕜 s) (hx : x in s) :
    iteratedFDerivWithin 𝕜 i (a • f) s x = a • iteratedFDerivWithin 𝕜 i f s x :=
  (a • (1 : F ->L[𝕜] F)).iteratedFDerivWithin_comp_left hf hu hx le_rfl

/--
theorem `iteratedFDerivWithin_smul_const_apply` / 定理 `iteratedFDerivWithin_smul_const_apply`

English:
theorem iteratedFDerivWithin_smul_const_apply
  statement: {f : E -> A} (hf : ContDiffWithinAt 𝕜 i f s x)
  proof: .iteratedFDerivWithin_comp_left hf hu hx le_rfl (ContinuousLinearMap.id 𝕜 A).smulRight v

中文:
定理 iteratedFDerivWithin_smul_const_apply
  结论: {f : E -> A} (hf : ContDiffWithinAt 𝕜 i f s x)
  证明: .iteratedFDerivWithin_comp_left hf hu hx le_rfl (ContinuousLinearMap.id 𝕜 A).smulRight v

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, iteratedFDerivWithin_comp_left, le_rfl, smulRight
-/
theorem iteratedFDerivWithin_smul_const_apply {f : E -> A} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hu : UniqueDiffOn 𝕜 s) (hx : x in s) :
    iteratedFDerivWithin 𝕜 i (fun y => f y • v) s x =
      ((ContinuousLinearMap.id 𝕜 A).smulRight v).compContinuousMultilinearMap
        (iteratedFDerivWithin 𝕜 i f s x) :=
.iteratedFDerivWithin_comp_left hf hu hx le_rfl (ContinuousLinearMap.id 𝕜 A).smulRight v

/--
theorem `iteratedFDeriv_const_smul_apply` / 定理 `iteratedFDeriv_const_smul_apply`

English:
theorem iteratedFDeriv_const_smul_apply
  given: (hf : ContDiffAt 𝕜 i f x)
  proof: (a • (1 : F ->L[𝕜] F)).iteratedFDeriv_comp_left hf le_rfl

中文:
定理 iteratedFDeriv_const_smul_apply
  条件: (hf : ContDiffAt 𝕜 i f x)
  证明: (a • (1 : F ->L[𝕜] F)).iteratedFDeriv_comp_left hf le_rfl

Depends on / 依赖: iteratedFDeriv_comp_left, le_rfl
-/
theorem iteratedFDeriv_const_smul_apply (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x :=
  (a • (1 : F ->L[𝕜] F)).iteratedFDeriv_comp_left hf le_rfl

/--
theorem `iteratedFDeriv_const_smul_apply'` / 定理 `iteratedFDeriv_const_smul_apply'`

English:
theorem iteratedFDeriv_const_smul_apply'
  given: (hf : ContDiffAt 𝕜 i f x)
  proof: iteratedFDeriv_const_smul_apply hf

中文:
定理 iteratedFDeriv_const_smul_apply'
  条件: (hf : ContDiffAt 𝕜 i f x)
  证明: iteratedFDeriv_const_smul_apply hf

Depends on / 依赖: iteratedFDeriv_const_smul_apply
-/
theorem iteratedFDeriv_const_smul_apply' (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (fun x => a • f x) x = a • iteratedFDeriv 𝕜 i f x :=
  iteratedFDeriv_const_smul_apply hf

/--
theorem `iteratedFDeriv_smul_const_apply` / 定理 `iteratedFDeriv_smul_const_apply`

English:
theorem iteratedFDeriv_smul_const_apply
  given: {f : E -> A} (hf : ContDiffAt 𝕜 i f x)
  proof: .iteratedFDeriv_comp_left hf le_rfl (ContinuousLinearMap.id 𝕜 A).smulRight v

中文:
定理 iteratedFDeriv_smul_const_apply
  条件: {f : E -> A} (hf : ContDiffAt 𝕜 i f x)
  证明: .iteratedFDeriv_comp_left hf le_rfl (ContinuousLinearMap.id 𝕜 A).smulRight v

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, iteratedFDeriv_comp_left, le_rfl, smulRight
-/
theorem iteratedFDeriv_smul_const_apply {f : E -> A} (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (fun y => f y • v) x =
      ((ContinuousLinearMap.id 𝕜 A).smulRight v).compContinuousMultilinearMap
        (iteratedFDeriv 𝕜 i f x) :=
.iteratedFDeriv_comp_left hf le_rfl (ContinuousLinearMap.id 𝕜 A).smulRight v

/--
theorem `iteratedFDeriv_comp_const_smul` / 定理 `iteratedFDeriv_comp_const_smul`

English:
theorem iteratedFDeriv_comp_const_smul
  given: (a : 𝕜) (hf : ContDiff 𝕜 i f)
  proof: by
  induction i with
  | zero => ext; simp
  | succ i hi =>
    ext v
    rw [iteratedFDeriv_succ_eq_comp_left]; rw [iteratedFDeriv_succ_eq_comp_left]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, self_le_add_right, hf.of_le, hi,
      comp_apply, continuousMultilinearCurryLeftEqu

中文:
定理 iteratedFDeriv_comp_const_smul
  条件: (a : 𝕜) (hf : 连续可微 𝕜 i f)
  证明: by
  induction i with
  | zero => ext; simp
  | succ i hi =>
    ext v
    rw [iteratedFDeriv_succ_eq_comp_left]; rw [iteratedFDeriv_succ_eq_comp_left]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, self_le_add_right, hf.of_le, hi,
      comp_apply, continuousMultilinearCurryLeftEqu

Depends on / 依赖: DifferentiableAt, DifferentiableAt.comp, Function, Function.comp_def, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, cast_add, cast_one, comp_apply, comp_def, contDiffAt, continuousMultilinearCurryLeftEquiv_symm_apply, differentiableAt_, fderiv_comp_smul, fderiv_fun_const_smul, hf.contDiffAt.differentiableAt_, hf.of_le, iteratedFDeriv_succ_eq_comp_left, of_le
-/
theorem iteratedFDeriv_comp_const_smul (a : 𝕜) (hf : ContDiff 𝕜 i f) :
    iteratedFDeriv 𝕜 i (fun z => f (a • z)) = fun x => a ^ i • iteratedFDeriv 𝕜 i f (a • x) := by
  induction i with
  | zero => ext; simp
  | succ i hi =>
    ext v
    rw [iteratedFDeriv_succ_eq_comp_left]; rw [iteratedFDeriv_succ_eq_comp_left]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, self_le_add_right, hf.of_le, hi,
      comp_apply, continuousMultilinearCurryLeftEquiv_symm_apply, smul_apply]
    rw [fderiv_fun_const_smul]; rw [fderiv_comp_smul]; rw [smul_smul]; rw [← pow_succ]
    · simp
    rw [← Function.comp_def (g := (a • ·))]
    apply DifferentiableAt.comp
    · exact hf.contDiffAt.differentiableAt_iteratedFDeriv (Nat.cast_lt.2 i.lt_succ_self)
    · exact differentiableAt_id.const_smul _

end ConstSMul

/-! ### Cartesian product of two functions -/

section prodMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.prodMap'` / 定理 `ContDiffWithinAt.prodMap'`

English:
theorem ContDiffWithinAt.prodMap'
  statement: {s : Set E} {t : Set E'} {f : E -> F} {g : E' -> F'} {p : E × E'}
  proof: (hf.comp p contDiffWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp p contDiffWithinAt_snd (prod_subset_preimage_snd _ _))

@[fun_prop]

中文:
定理 ContDiffWithinAt.prodMap'
  结论: {s : 集合 E} {t : 集合 E'} {f : E -> F} {g : E' -> F'} {p : E × E'}
  证明: (hf.comp p contDiffWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp p contDiffWithinAt_snd (prod_subset_preimage_snd _ _))

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_fst, contDiffWithinAt_snd, hf.comp, hg.comp, prodMk, prod_subset_preimage_fst, prod_subset_preimage_snd
-/
theorem ContDiffWithinAt.prodMap' {s : Set E} {t : Set E'} {f : E -> F} {g : E' -> F'} {p : E × E'}
    (hf : ContDiffWithinAt 𝕜 n f s p.1) (hg : ContDiffWithinAt 𝕜 n g t p.2) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) p :=
  (hf.comp p contDiffWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp p contDiffWithinAt_snd (prod_subset_preimage_snd _ _))

@[fun_prop]
/--
theorem `ContDiffWithinAt.prodMap` / 定理 `ContDiffWithinAt.prodMap`

English:
theorem ContDiffWithinAt.prodMap
  statement: {s : Set E} {t : Set E'} {f : E -> F} {g : E' -> F'} {x : E} {y : E'}
  proof: ContDiffWithinAt.prodMap' hf hg

中文:
定理 ContDiffWithinAt.prodMap
  结论: {s : 集合 E} {t : 集合 E'} {f : E -> F} {g : E' -> F'} {x : E} {y : E'}
  证明: ContDiffWithinAt.prodMap' hf hg

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.prodMap, prodMap
-/
theorem ContDiffWithinAt.prodMap {s : Set E} {t : Set E'} {f : E -> F} {g : E' -> F'} {x : E} {y : E'}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g t y) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) (x, y) :=
  ContDiffWithinAt.prodMap' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
@[fun_prop]
/--
theorem `ContDiffOn.prodMap` / 定理 `ContDiffOn.prodMap`

English:
theorem ContDiffOn.prodMap
  statement: {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
  proof: (hf.comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp contDiffOn_snd (prod_subset_preimage_snd _ _))

中文:
定理 ContDiffOn.prodMap
  结论: {E' : 类型} [赋范交换加群 E'] [赋范空间 𝕜 E'] {F' : 类型}
  证明: (hf.comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp contDiffOn_snd (prod_subset_preimage_snd _ _))

Depends on / 依赖: contDiffOn_fst, contDiffOn_snd, hf.comp, hg.comp, prodMk, prod_subset_preimage_fst, prod_subset_preimage_snd
-/
theorem ContDiffOn.prodMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'} {f : E -> F} {g : E' -> F'}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g t) : ContDiffOn 𝕜 n (Prod.map f g) (s ×ˢ t) :=
  (hf.comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp contDiffOn_snd (prod_subset_preimage_snd _ _))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
/--
theorem `ContDiffAt.prodMap` / 定理 `ContDiffAt.prodMap`

English:
theorem ContDiffAt.prodMap
  statement: {f : E -> F} {g : E' -> F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
  proof: by
  rw [ContDiffAt] at *
  simpa only [univ_prod_univ] using hf.prodMap hg

中文:
定理 ContDiffAt.prodMap
  结论: {f : E -> F} {g : E' -> F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
  证明: by
  rw [ContDiffAt] at *
  simpa only [univ_prod_univ] using hf.prodMap hg

Depends on / 依赖: ContDiffAt, hf.prodMap, prodMap, univ_prod_univ
-/
theorem ContDiffAt.prodMap {f : E -> F} {g : E' -> F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n (Prod.map f g) (x, y) := by
  rw [ContDiffAt] at *
  simpa only [univ_prod_univ] using hf.prodMap hg

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
/--
theorem `ContDiffAt.prodMap'` / 定理 `ContDiffAt.prodMap'`

English:
theorem ContDiffAt.prodMap'
  statement: {f : E -> F} {g : E' -> F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
  proof: hf.prodMap hg

中文:
定理 ContDiffAt.prodMap'
  结论: {f : E -> F} {g : E' -> F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
  证明: hf.prodMap hg

Depends on / 依赖: hf.prodMap, prodMap
-/
theorem ContDiffAt.prodMap' {f : E -> F} {g : E' -> F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
    (hg : ContDiffAt 𝕜 n g p.2) : ContDiffAt 𝕜 n (Prod.map f g) p :=
  hf.prodMap hg

/-- The product map of two `C^n` functions is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.prodMap` / 定理 `ContDiff.prodMap`

English:
theorem ContDiff.prodMap
  given: {f : E -> F} {g : E' -> F'} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
  proof: by
  rw [contDiff_iff_contDiffAt] at *
  exact fun ⟨x, y⟩ => (hf x).prodMap (hg y)

@[fun_prop]

中文:
定理 连续可微.prodMap
  条件: {f : E -> F} {g : E' -> F'} (hf : 连续可微 𝕜 n f) (hg : 连续可微 𝕜 n g)
  证明: by
  rw [contDiff_iff_contDiffAt] at *
  exact fun ⟨x, y⟩ => (hf x).prodMap (hg y)

@[fun_prop]

Depends on / 依赖: contDiff_iff_contDiffAt, prodMap
-/
theorem ContDiff.prodMap {f : E -> F} {g : E' -> F'} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (Prod.map f g) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun ⟨x, y⟩ => (hf x).prodMap (hg y)

@[fun_prop]
/--
theorem `contDiff_prodMk_left` / 定理 `contDiff_prodMk_left`

English:
theorem contDiff_prodMk_left
  given: (f₀ : F)
  statement: ContDiff 𝕜 n fun e : E => (e, f₀)
  proof: contDiff_id.prodMk contDiff_const

@[fun_prop]

中文:
定理 contDiff_prodMk_left
  条件: (f₀ : F)
  结论: 连续可微 𝕜 n fun e : E => (e, f₀)
  证明: contDiff_id.prodMk contDiff_const

@[fun_prop]

Depends on / 依赖: contDiff_const, contDiff_id, contDiff_id.prodMk, prodMk
-/
theorem contDiff_prodMk_left (f₀ : F) : ContDiff 𝕜 n fun e : E => (e, f₀) :=
  contDiff_id.prodMk contDiff_const

@[fun_prop]
/--
theorem `contDiff_prodMk_right` / 定理 `contDiff_prodMk_right`

English:
theorem contDiff_prodMk_right
  given: (e₀ : E)
  statement: ContDiff 𝕜 n fun f : F => (e₀, f)
  proof: contDiff_const.prodMk contDiff_id

中文:
定理 contDiff_prodMk_right
  条件: (e₀ : E)
  结论: 连续可微 𝕜 n fun f : F => (e₀, f)
  证明: contDiff_const.prodMk contDiff_id

Depends on / 依赖: contDiff_const, contDiff_const.prodMk, contDiff_id, prodMk
-/
theorem contDiff_prodMk_right (e₀ : E) : ContDiff 𝕜 n fun f : F => (e₀, f) :=
  contDiff_const.prodMk contDiff_id

end prodMap

/-!
### Inversion in a complete normed algebra (or more generally with summable geometric series)
-/

section AlgebraInverse

variable (𝕜)
variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element, as it is analytic. -/
@[fun_prop]
/--
theorem `contDiffAt_ringInverse` / 定理 `contDiffAt_ringInverse`

English:
theorem contDiffAt_ringInverse
  given: [HasSummableGeomSeries R] (x : Rˣ)
  proof: by
  have := AnalyticOnNhd.contDiffOn (analyticOnNhd_inverse (𝕜 := 𝕜) (A := R)) (n := n)
    Units.isOpen.uniqueDiffOn x x.isUnit
  exact this.contDiffAt (Units.isOpen.mem_nhds x.isUnit)

中文:
定理 contDiffAt_ringInverse
  条件: [有SummableGeomSeries R] (x : Rˣ)
  证明: by
  have := AnalyticOnNhd.contDiffOn (analyticOnNhd_inverse (𝕜 := 𝕜) (A := R)) (n := n)
    Units.isOpen.uniqueDiffOn x x.isUnit
  exact this.contDiffAt (Units.isOpen.mem_nhds x.isUnit)

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.contDiffOn, RCLike, RCLike.instTietzeExtension, Units.isOpen.mem_nhds, Units.isOpen.uniqueDiffOn, analyticOnNhd_inverse, contDiffAt, contDiffOn, instTietzeExtension, isOpen, isUnit, mem_nhds, this.contDiffAt, uniqueDiffOn, x.isUnit
-/
theorem contDiffAt_ringInverse [HasSummableGeomSeries R] (x : Rˣ) :
    ContDiffAt 𝕜 n Ring.inverse (x : R) := by
  have := AnalyticOnNhd.contDiffOn (analyticOnNhd_inverse (𝕜 := 𝕜) (A := R)) (n := n)
    Units.isOpen.uniqueDiffOn x x.isUnit
  exact this.contDiffAt (Units.isOpen.mem_nhds x.isUnit)

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

@[fun_prop]
/--
theorem `contDiffAt_inv` / 定理 `contDiffAt_inv`

English:
theorem contDiffAt_inv
  given: {x : 𝕜'} (hx : x != 0) {n}
  statement: ContDiffAt 𝕜 n Inv.inv x
  proof: by
  simpa only [Ring.inverse_eq_inv'] using! contDiffAt_ringInverse 𝕜 (Units.mk0 x hx)

@[fun_prop]

中文:
定理 contDiffAt_inv
  条件: {x : 𝕜'} (hx : x != 0) {n}
  结论: ContDiffAt 𝕜 n 取逆.inv x
  证明: by
  simpa only [Ring.inverse_eq_inv'] using! contDiffAt_ringInverse 𝕜 (Units.mk0 x hx)

@[fun_prop]

Depends on / 依赖: Ring.inverse_eq_inv, Units.mk0, contDiffAt_ringInverse, inverse_eq_inv
-/
theorem contDiffAt_inv {x : 𝕜'} (hx : x != 0) {n} : ContDiffAt 𝕜 n Inv.inv x := by
  simpa only [Ring.inverse_eq_inv'] using! contDiffAt_ringInverse 𝕜 (Units.mk0 x hx)

@[fun_prop]
/--
theorem `contDiffOn_inv` / 定理 `contDiffOn_inv`

English:
theorem contDiffOn_inv
  given: {n}
  statement: ContDiffOn 𝕜 n (Inv.inv : 𝕜' -> 𝕜') {0}ᶜ
  proof: fun _ hx =>
  (contDiffAt_inv 𝕜 hx).contDiffWithinAt

中文:
定理 contDiffOn_inv
  条件: {n}
  结论: ContDiffOn 𝕜 n (取逆.inv : 𝕜' -> 𝕜') {0}ᶜ
  证明: fun _ hx =>
  (contDiffAt_inv 𝕜 hx).contDiffWithinAt
-/
theorem contDiffOn_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' -> 𝕜') {0}ᶜ := fun _ hx =>
  (contDiffAt_inv 𝕜 hx).contDiffWithinAt

variable {𝕜}

@[to_fun (attr := fun_prop)]
/--
theorem `ContDiffWithinAt.inv` / 定理 `ContDiffWithinAt.inv`

English:
theorem ContDiffWithinAt.inv
  given: {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x != 0)
  proof: (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf

@[to_fun (attr := fun_prop)]

中文:
定理 ContDiffWithinAt.inv
  条件: {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x != 0)
  证明: (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf

@[to_fun (attr := fun_prop)]

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt_inv
-/
theorem ContDiffWithinAt.inv {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x != 0) :
    ContDiffWithinAt 𝕜 n f⁻¹ s x :=
  (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf

@[to_fun (attr := fun_prop)]
/--
theorem `ContDiffOn.inv` / 定理 `ContDiffOn.inv`

English:
theorem ContDiffOn.inv
  given: {f : E -> 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : forall x in s, f x != 0)
  proof: fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.inv {f : E -> 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hx : f x != 0) :
    ContDiffAt 𝕜 n f⁻¹ x :=
  hf.inv hx

@[to_fun (attr := fun_prop)]

中文:
定理 ContDiffOn.inv
  条件: {f : E -> 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.inv {f : E -> 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hx : f x != 0) :
    ContDiffAt 𝕜 n f⁻¹ x :=
  hf.inv hx

@[to_fun (attr := fun_prop)]

Depends on / 依赖: contDiffWithinAt, hf.contDiffWithinAt
-/
theorem ContDiffOn.inv {f : E -> 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : forall x in s, f x != 0) :
    ContDiffOn 𝕜 n f⁻¹ s := fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.inv {f : E -> 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hx : f x != 0) :
    ContDiffAt 𝕜 n f⁻¹ x :=
  hf.inv hx

@[to_fun (attr := fun_prop)]
/--
theorem `ContDiff.inv` / 定理 `ContDiff.inv`

English:
theorem ContDiff.inv
  given: {f : E -> 𝕜'} (hf : ContDiff 𝕜 n f) (h : forall x, f x != 0)
  proof: by
  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)

中文:
定理 连续可微.inv
  条件: {f : E -> 𝕜'} (hf : 连续可微 𝕜 n f) (h : 对任意 x, f x != 0)
  证明: by
  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, hf.contDiffAt.inv
-/
theorem ContDiff.inv {f : E -> 𝕜'} (hf : ContDiff 𝕜 n f) (h : forall x, f x != 0) :
    ContDiff 𝕜 n f⁻¹ := by
  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)

-- TODO: generalize to `f g : E → 𝕜'`
@[to_fun (attr := fun_prop)]
/--
theorem `ContDiffWithinAt.div` / 定理 `ContDiffWithinAt.div`

English:
theorem ContDiffWithinAt.div
  statement: {f g : E -> 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: by
  change ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x
  simpa only [div_eq_mul_inv] using hf.mul (hg.fun_inv hx)

@[to_fun (attr := fun_prop)]

中文:
定理 ContDiffWithinAt.div
  结论: {f g : E -> 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: by
  change ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x
  simpa only [div_eq_mul_inv] using hf.mul (hg.fun_inv hx)

@[to_fun (attr := fun_prop)]

Depends on / 依赖: ContDiffWithinAt, div_eq_mul_inv, fun_inv, hf.mul, hg.fun_inv
-/
theorem ContDiffWithinAt.div {f g : E -> 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x != 0) :
    ContDiffWithinAt 𝕜 n (f / g) s x := by
  change ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x
  simpa only [div_eq_mul_inv] using hf.mul (hg.fun_inv hx)

@[to_fun (attr := fun_prop)]
/--
theorem `ContDiffOn.div` / 定理 `ContDiffOn.div`

English:
theorem ContDiffOn.div
  statement: {f g : E -> 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
  proof: fun x hx =>
  (hf x hx).div (hg x hx) (h₀ x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.div {f g : E -> 𝕜} {n} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) (hx : g x != 0) : ContDiffAt 𝕜 n (f / g) x :=
  hf.div hg hx

@[to_fun (attr := fun_prop)]

中文:
定理 ContDiffOn.div
  结论: {f g : E -> 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
  证明: fun x hx =>
  (hf x hx).div (hg x hx) (h₀ x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.div {f g : E -> 𝕜} {n} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) (hx : g x != 0) : ContDiffAt 𝕜 n (f / g) x :=
  hf.div hg hx

@[to_fun (attr := fun_prop)]
-/
theorem ContDiffOn.div {f g : E -> 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) (h₀ : forall x in s, g x != 0) : ContDiffOn 𝕜 n (f / g) s := fun x hx =>
  (hf x hx).div (hg x hx) (h₀ x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.div {f g : E -> 𝕜} {n} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) (hx : g x != 0) : ContDiffAt 𝕜 n (f / g) x :=
  hf.div hg hx

@[to_fun (attr := fun_prop)]
/--
theorem `ContDiff.div` / 定理 `ContDiff.div`

English:
theorem ContDiff.div
  statement: {f g : E -> 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
  proof: by
  simp only [contDiff_iff_contDiffAt] at *
  exact fun x => (hf x).div (hg x) (h0 x)

中文:
定理 连续可微.div
  结论: {f g : E -> 𝕜} {n} (hf : 连续可微 𝕜 n f) (hg : 连续可微 𝕜 n g)
  证明: by
  simp only [contDiff_iff_contDiffAt] at *
  exact fun x => (hf x).div (hg x) (h0 x)

Depends on / 依赖: contDiff_iff_contDiffAt
-/
theorem ContDiff.div {f g : E -> 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (h0 : forall x, g x != 0) : ContDiff 𝕜 n (f / g) := by
  simp only [contDiff_iff_contDiffAt] at *
  exact fun x => (hf x).div (hg x) (h0 x)

end AlgebraInverse

/-! ### Inversion of continuous linear maps between Banach spaces -/

section MapInverse

open ContinuousLinearMap

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
@[fun_prop]
/--
theorem `contDiffAt_map_inverse` / 定理 `contDiffAt_map_inverse`

English:
theorem contDiffAt_map_inverse
  given: [CompleteSpace E] (e : E ≃L[𝕜] F)
  proof: by
  nontriviality E
  -- first, we use the lemma `inverse_eq_ringInverse` to rewrite in terms of `Ring.inverse` in the
  -- ring `E →L[𝕜] E`
  let O₁ : (E ->L[𝕜] E) -> F ->L[𝕜] E := fun f => f.comp (e.symm : F ->L[𝕜] E)
  let O₂ : (E ->L[𝕜] F) -> E ->L[𝕜] E := fun f => (e.symm : F ->L[𝕜] E).comp f


中文:
定理 contDiffAt_map_inverse
  条件: [完备空间 E] (e : E ≃L[𝕜] F)
  证明: by
  nontriviality E
  -- first, we use the lemma `inverse_eq_ringInverse` to rewrite in terms of `Ring.inverse` in the
  -- ring `E →L[𝕜] E`
  let O₁ : (E ->L[𝕜] E) -> F ->L[𝕜] E := fun f => f.comp (e.symm : F ->L[𝕜] E)
  let O₂ : (E ->L[𝕜] F) -> E ->L[𝕜] E := fun f => (e.symm : F ->L[𝕜] E).comp f


Depends on / 依赖: nontriviality
-/
theorem contDiffAt_map_inverse [CompleteSpace E] (e : E ≃L[𝕜] F) :
    ContDiffAt 𝕜 n inverse (e : E ->L[𝕜] F) := by
  nontriviality E
  -- first, we use the lemma `inverse_eq_ringInverse` to rewrite in terms of `Ring.inverse` in the
  -- ring `E →L[𝕜] E`
  let O₁ : (E ->L[𝕜] E) -> F ->L[𝕜] E := fun f => f.comp (e.symm : F ->L[𝕜] E)
  let O₂ : (E ->L[𝕜] F) -> E ->L[𝕜] E := fun f => (e.symm : F ->L[𝕜] E).comp f
  have : ContinuousLinearMap.inverse = O₁ ∘ Ring.inverse ∘ O₂ := funext (inverse_eq_ringInverse e)
  rw [this]
  -- `O₁` and `O₂` are `ContDiff`,
  -- so we reduce to proving that `Ring.inverse` is `ContDiff`
  have h₁ : ContDiff 𝕜 n O₁ := contDiff_id.clm_comp contDiff_const
  have h₂ : ContDiff 𝕜 n O₂ := contDiff_const.clm_comp contDiff_id
  refine h₁.contDiffAt.comp _ (ContDiffAt.comp _ ?_ h₂.contDiffAt)
  convert! contDiffAt_ringInverse 𝕜 (1 : (E ->L[𝕜] E)ˣ)
  simp [O₂, one_def]

/--
theorem `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse` / 定理 `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`

English:
theorem ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
  statement: [CompleteSpace E] {e : E ->L[𝕜] F}
  proof: by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

中文:
定理 连续线性映射.IsInvertible.contDiffAt_map_inverse
  结论: [完备空间 E] {e : E ->L[𝕜] F}
  证明: by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

Depends on / 依赖: _root_, _root_.contDiffAt_map_inverse, contDiffAt_map_inverse
-/
theorem ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse [CompleteSpace E] {e : E ->L[𝕜] F}
    (he : e.IsInvertible) : ContDiffAt 𝕜 n inverse e := by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

end MapInverse

section FunctionInverse

open ContinuousLinearMap

/--
theorem `OpenPartialHomeomorph.contDiffAt_symm` / 定理 `OpenPartialHomeomorph.contDiffAt_symm`

English:
theorem OpenPartialHomeomorph.contDiffAt_symm
  statement: [CompleteSpace E] (f : OpenPartialHomeomorph E F)
  proof: by
  match n with
  | ω =>
    apply AnalyticAt.contDiffAt
    exact f.analyticAt_symm ha hf.analyticAt hf₀'.fderiv
  | (n : Nat∞) =>
    -- We prove this by induction on `n`
    induction n using ENat.nat_induction with
    | zero =>
      apply contDiffAt_zero.2
      exact ⟨f.target, IsOpen.mem_n

中文:
定理 OpenPartialHomeomorph.contDiffAt_symm
  结论: [完备空间 E] (f : OpenPartialHomeomorph E F)
  证明: by
  match n with
  | ω =>
    apply AnalyticAt.contDiffAt
    exact f.analyticAt_symm ha hf.analyticAt hf₀'.fderiv
  | (n : Nat∞) =>
    -- We prove this by induction on `n`
    induction n using ENat.nat_induction with
    | zero =>
      apply contDiffAt_zero.2
      exact ⟨f.target, IsOpen.mem_n

Depends on / 依赖: AnalyticAt, AnalyticAt.contDiffAt, analyticAt, analyticAt_symm, contDiffAt, f.analyticAt_symm, fderiv, hf.analyticAt
-/
theorem OpenPartialHomeomorph.contDiffAt_symm [CompleteSpace E] (f : OpenPartialHomeomorph E F)
    {f₀' : E ≃L[𝕜] F} {a : F} (ha : a in f.target)
    (hf₀' : HasFDerivAt f (f₀' : E ->L[𝕜] F) (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a := by
  match n with
  | ω =>
    apply AnalyticAt.contDiffAt
    exact f.analyticAt_symm ha hf.analyticAt hf₀'.fderiv
  | (n : Nat∞) =>
    -- We prove this by induction on `n`
    induction n using ENat.nat_induction with
    | zero =>
      apply contDiffAt_zero.2
      exact ⟨f.target, IsOpen.mem_nhds f.open_target ha, f.continuousOn_invFun⟩
    | succ n IH =>
      obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := contDiffAt_succ_iff_hasFDerivAt.mp hf
      apply contDiffAt_succ_iff_hasFDerivAt.2
      -- For showing `n.succ` times continuous differentiability (the main inductive step), it
      -- suffices to produce the derivative and show that it is `n` times continuously
      -- differentiable
      have eq_f₀' : f' (f.symm a) = f₀' := (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀'
      -- This follows by a bootstrapping formula expressing the derivative as a
      -- function of `f` itself
      refine ⟨inverse ∘ f' ∘ f.symm, ?_, ?_⟩
      · -- We first check that the derivative of `f` is that formula
        have h_nhds : { y : E | exists e : E ≃L[𝕜] F, ↑e = f' y } in 𝓝 (f.symm a) := by
          have hf₀' := f₀'.nhds
          rw [← eq_f₀'] at hf₀'
          exact hf'.continuousAt.preimage_mem_nhds hf₀'
        obtain ⟨t, htu, ht, htf⟩ := mem_nhds_iff.mp (Filter.inter_mem hu h_nhds)
        use f.target inter f.symm ⁻¹' t
        refine ⟨IsOpen.mem_nhds ?_ ?_, ?_⟩
        · exact f.isOpen_inter_preimage_symm ht
        · exact mem_inter ha (mem_preimage.mpr htf)
        intro x hx
        obtain ⟨hxu, e, he⟩ := htu hx.2
        have h_deriv : HasFDerivAt f (e : E ->L[𝕜] F) (f.symm x) := by
          rw [he]
          exact hff' (f.symm x) hxu
        convert! f.hasFDerivAt_symm hx.1 h_deriv
        simp [← he]
      · -- Then we check that the formula, being a composition of `ContDiff` pieces, is
        -- itself `ContDiff`
        have h_deriv₁ : ContDiffAt 𝕜 n inverse (f' (f.symm a)) := by
          rw [eq_f₀']
          exact contDiffAt_map_inverse _
        have h_deriv₂ : ContDiffAt 𝕜 n f.symm a := by
          refine IH (hf.of_le ?_)
          norm_cast
          exact Nat.le_succ n
        exact (h_deriv₁.comp _ hf').comp _ h_deriv₂
    | top Itop => exact contDiffAt_infty.mpr fun n => Itop n (contDiffAt_infty.mp hf n)

/--
theorem `Homeomorph.contDiff_symm` / 定理 `Homeomorph.contDiff_symm`

English:
theorem Homeomorph.contDiff_symm
  statement: [CompleteSpace E] (f : E ≃ₜ F) {f₀' : E -> E ≃L[𝕜] F}
  proof: contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) (hf₀' _) hf.contDiffAt

中文:
定理 同胚.contDiff_symm
  结论: [完备空间 E] (f : E ≃ₜ F) {f₀' : E -> E ≃L[𝕜] F}
  证明: contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) (hf₀' _) hf.contDiffAt

Depends on / 依赖: contDiffAt, contDiffAt_symm, contDiff_iff_contDiffAt, f.toOpenPartialHomeomorph.contDiffAt_symm, hf.contDiffAt, mem_univ, toOpenPartialHomeomorph
-/
theorem Homeomorph.contDiff_symm [CompleteSpace E] (f : E ≃ₜ F) {f₀' : E -> E ≃L[𝕜] F}
    (hf₀' : forall a, HasFDerivAt f (f₀' a : E ->L[𝕜] F) a) (hf : ContDiff 𝕜 n (f : E -> F)) :
    ContDiff 𝕜 n (f.symm : F -> E) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) (hf₀' _) hf.contDiffAt

/--
theorem `OpenPartialHomeomorph.contDiffAt_symm_deriv` / 定理 `OpenPartialHomeomorph.contDiffAt_symm_deriv`

English:
theorem OpenPartialHomeomorph.contDiffAt_symm_deriv
  statement: [CompleteSpace 𝕜]
  proof: f.contDiffAt_symm ha (hf₀'.hasFDerivAt_equiv h₀) hf

中文:
定理 OpenPartialHomeomorph.contDiffAt_symm_deriv
  结论: [完备空间 𝕜]
  证明: f.contDiffAt_symm ha (hf₀'.hasFDerivAt_equiv h₀) hf

Depends on / 依赖: contDiffAt_symm, f.contDiffAt_symm, hasFDerivAt_equiv
-/
theorem OpenPartialHomeomorph.contDiffAt_symm_deriv [CompleteSpace 𝕜]
    (f : OpenPartialHomeomorph 𝕜 𝕜) {f₀' a : 𝕜} (h₀ : f₀' != 0) (ha : a in f.target)
    (hf₀' : HasDerivAt f f₀' (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a :=
  f.contDiffAt_symm ha (hf₀'.hasFDerivAt_equiv h₀) hf

/--
theorem `Homeomorph.contDiff_symm_deriv` / 定理 `Homeomorph.contDiff_symm_deriv`

English:
theorem Homeomorph.contDiff_symm_deriv
  statement: [CompleteSpace 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 -> 𝕜}
  proof: contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.contDiffAt

中文:
定理 同胚.contDiff_symm_deriv
  结论: [完备空间 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 -> 𝕜}
  证明: contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.contDiffAt

Depends on / 依赖: contDiffAt, contDiffAt_symm_deriv, contDiff_iff_contDiffAt, f.toOpenPartialHomeomorph.contDiffAt_symm_deriv, hf.contDiffAt, mem_univ, toOpenPartialHomeomorph
-/
theorem Homeomorph.contDiff_symm_deriv [CompleteSpace 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 -> 𝕜}
    (h₀ : forall x, f' x != 0) (hf' : forall x, HasDerivAt f (f' x) x) (hf : ContDiff 𝕜 n (f : 𝕜 -> 𝕜)) :
    ContDiff 𝕜 n (f.symm : 𝕜 -> 𝕜) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.contDiffAt

namespace OpenPartialHomeomorph

variable (𝕜)

/-- Restrict an open partial homeomorphism to the subsets of the source and target
that consist of points `x ∈ f.source`, `y = f x ∈ f.target`
such that `f` is `C^n` at `x` and `f.symm` is `C^n` at `y`.

Note that `n` is a natural number or `ω`, but not `∞`,
because the set of points of `C^∞`-smoothness of `f` is not guaranteed to be open. -/
@[simps! apply symm_apply source target]
/--
Definition of `restrContDiff` / `restrContDiff` 的定义

English:
definition restrContDiff
  signature: (f : OpenPartialHomeomorph E F) (n : Nat∞ω) (hn : n != ∞)
  body: haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx => by
    simp [hx, and_comm]
H.restr isOpen_iff_mem_nhds.2 fun _ ⟨hxs, hxf, hxf'⟩ =>
inter_mem (f.open_source.mem_nhds hxs) (hxf.eventually hn).an

中文:
定义 restrContDiff
  签名: (f : OpenPartialHomeomorph E F) (n : 自然数∞ω) (hn : n != ∞)
  定义体: haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx => by
    simp [hx, and_comm]
H.restr isOpen_iff_mem_nhds.2 fun _ ⟨hxs, hxf, hxf'⟩ =>
inter_mem (f.open_source.mem_nhds hxs) (hxf.eventually hn).an

Depends on / 依赖: ContDiffAt, H.restr, IsImage, and_comm, continuousAt, eventually, f.IsImage, f.continuousAt, f.open_source.mem_nhds, f.symm, hxf.eventually, inter_mem, isOpen_iff_mem_nhds, mem_nhds, open_source
-/
def restrContDiff (f : OpenPartialHomeomorph E F) (n : Nat∞ω) (hn : n != ∞) :
    OpenPartialHomeomorph E F :=
  haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx => by
    simp [hx, and_comm]
H.restr isOpen_iff_mem_nhds.2 fun _ ⟨hxs, hxf, hxf'⟩ =>
inter_mem (f.open_source.mem_nhds hxs) (hxf.eventually hn).and
    f.continuousAt hxs (hxf'.eventually hn)

/--
lemma `contDiffOn_restrContDiff_source` / 引理 `contDiffOn_restrContDiff_source`

English:
lemma contDiffOn_restrContDiff_source
  statement: (f : OpenPartialHomeomorph E F) {n : Nat∞ω}
  proof: fun _x hx => hx.2.1.contDiffWithinAt

中文:
引理 contDiffOn_restrContDiff_source
  结论: (f : OpenPartialHomeomorph E F) {n : 自然数∞ω}
  证明: fun _x hx => hx.2.1.contDiffWithinAt

Depends on / 依赖: contDiffWithinAt
-/
lemma contDiffOn_restrContDiff_source (f : OpenPartialHomeomorph E F) {n : Nat∞ω}
    (hn : n != ∞) : ContDiffOn 𝕜 n f (f.restrContDiff 𝕜 n hn).source :=
  fun _x hx => hx.2.1.contDiffWithinAt

/--
lemma `contDiffOn_restrContDiff_target` / 引理 `contDiffOn_restrContDiff_target`

English:
lemma contDiffOn_restrContDiff_target
  statement: (f : OpenPartialHomeomorph E F) {n : Nat∞ω}
  proof: fun _x hx => hx.2.1.contDiffWithinAt

中文:
引理 contDiffOn_restrContDiff_target
  结论: (f : OpenPartialHomeomorph E F) {n : 自然数∞ω}
  证明: fun _x hx => hx.2.1.contDiffWithinAt

Depends on / 依赖: contDiffWithinAt
-/
lemma contDiffOn_restrContDiff_target (f : OpenPartialHomeomorph E F) {n : Nat∞ω}
    (hn : n != ∞) : ContDiffOn 𝕜 n f.symm (f.restrContDiff 𝕜 n hn).target :=
  fun _x hx => hx.2.1.contDiffWithinAt

end OpenPartialHomeomorph

end FunctionInverse

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/


variable (𝕜)
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
variable {p' : E -> FormalMultilinearSeries 𝕜' E F}

/--
theorem `HasFTaylorSeriesUpToOn.restrictScalars` / 定理 `HasFTaylorSeriesUpToOn.restrictScalars`

English:
theorem HasFTaylorSeriesUpToOn.restrictScalars
  statement: {n : Nat∞ω}
  proof: h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x <|
        (h.fderivWithin m hm x hx).restrictScalars 𝕜 :)
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

中文:
定理 有FTaylorSeriesUpToOn.restrictScalars
  结论: {n : 自然数∞ω}
  证明: h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x <|
        (h.fderivWithin m hm x hx).restrictScalars 𝕜 :)
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

Depends on / 依赖: h.zero_eq, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.restrictScalars {n : Nat∞ω}
    (h : HasFTaylorSeriesUpToOn n f p' s) :
    HasFTaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x <|
        (h.fderivWithin m hm x hx).restrictScalars 𝕜 :)
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

/--
theorem `ContDiffWithinAt.restrict_scalars` / 定理 `ContDiffWithinAt.restrict_scalars`

English:
theorem ContDiffWithinAt.restrict_scalars
  given: (h : ContDiffWithinAt 𝕜' n f s x)
  proof: by
  match n with
  | ω =>
    obtain ⟨u, u_mem, p', hp', Hp'⟩ := h
    refine ⟨u, u_mem, _, hp'.restrictScalars _, fun i => ?_⟩
    change AnalyticOn 𝕜 (fun x => ContinuousMultilinearMap.restrictScalarsLinear 𝕜 (p' x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (Hp' i).restrictScalars (Set.mapsT

中文:
定理 ContDiffWithinAt.restrict_scalars
  条件: (h : ContDiffWithinAt 𝕜' n f s x)
  证明: by
  match n with
  | ω =>
    obtain ⟨u, u_mem, p', hp', Hp'⟩ := h
    refine ⟨u, u_mem, _, hp'.restrictScalars _, fun i => ?_⟩
    change AnalyticOn 𝕜 (fun x => ContinuousMultilinearMap.restrictScalarsLinear 𝕜 (p' x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (Hp' i).restrictScalars (Set.mapsT

Depends on / 依赖: AnalyticOn, AnalyticOnNhd, AnalyticOnNhd.comp_analyticOn, ContinuousLinearMap, ContinuousLinearMap.analyticOnNhd, ContinuousMultilinearMap, ContinuousMultilinearMap.restrictScalarsLinear, Set.mapsTo_univ, analyticOnNhd, comp_analyticOn, mapsTo_univ, restrictScalars, restrictScalarsLinear, u_mem
-/
theorem ContDiffWithinAt.restrict_scalars (h : ContDiffWithinAt 𝕜' n f s x) :
    ContDiffWithinAt 𝕜 n f s x := by
  match n with
  | ω =>
    obtain ⟨u, u_mem, p', hp', Hp'⟩ := h
    refine ⟨u, u_mem, _, hp'.restrictScalars _, fun i => ?_⟩
    change AnalyticOn 𝕜 (fun x => ContinuousMultilinearMap.restrictScalarsLinear 𝕜 (p' x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (Hp' i).restrictScalars (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : Nat∞) =>
    intro m hm
    rcases h m hm with ⟨u, u_mem, p', hp'⟩
    exact ⟨u, u_mem, _, hp'.restrictScalars _⟩

/--
theorem `ContDiffOn.restrict_scalars` / 定理 `ContDiffOn.restrict_scalars`

English:
theorem ContDiffOn.restrict_scalars
  given: (h : ContDiffOn 𝕜' n f s)
  statement: ContDiffOn 𝕜 n f s
  proof: fun x hx =>
  (h x hx).restrict_scalars _

中文:
定理 ContDiffOn.restrict_scalars
  条件: (h : ContDiffOn 𝕜' n f s)
  结论: ContDiffOn 𝕜 n f s
  证明: fun x hx =>
  (h x hx).restrict_scalars _
-/
theorem ContDiffOn.restrict_scalars (h : ContDiffOn 𝕜' n f s) : ContDiffOn 𝕜 n f s := fun x hx =>
  (h x hx).restrict_scalars _

/--
theorem `ContDiffAt.restrict_scalars` / 定理 `ContDiffAt.restrict_scalars`

English:
theorem ContDiffAt.restrict_scalars
  given: (h : ContDiffAt 𝕜' n f x)
  statement: ContDiffAt 𝕜 n f x
  proof: contDiffWithinAt_univ.1 h.contDiffWithinAt.restrict_scalars _

中文:
定理 ContDiffAt.restrict_scalars
  条件: (h : ContDiffAt 𝕜' n f x)
  结论: ContDiffAt 𝕜 n f x
  证明: contDiffWithinAt_univ.1 h.contDiffWithinAt.restrict_scalars _

Depends on / 依赖: contDiffWithinAt, contDiffWithinAt_univ, h.contDiffWithinAt.restrict_scalars, restrict_scalars
-/
theorem ContDiffAt.restrict_scalars (h : ContDiffAt 𝕜' n f x) : ContDiffAt 𝕜 n f x :=
contDiffWithinAt_univ.1 h.contDiffWithinAt.restrict_scalars _

/--
theorem `ContDiff.restrict_scalars` / 定理 `ContDiff.restrict_scalars`

English:
theorem ContDiff.restrict_scalars
  given: (h : ContDiff 𝕜' n f)
  statement: ContDiff 𝕜 n f
  proof: contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.restrict_scalars _

中文:
定理 连续可微.restrict_scalars
  条件: (h : 连续可微 𝕜' n f)
  结论: 连续可微 𝕜 n f
  证明: contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.restrict_scalars _

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, h.contDiffAt.restrict_scalars, restrict_scalars
-/
theorem ContDiff.restrict_scalars (h : ContDiff 𝕜' n f) : ContDiff 𝕜 n f :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.restrict_scalars _

end RestrictScalars
