/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Inverse function theorem, the "easy half"

In this file we prove several versions of the following theorem.
Consider three functions `f : F → G`, `g : E → F`, and `h : E → G`,
together with "candidate derivatives" `f' : F →L[𝕜] G`, `g' : E →L[𝕜] F`, and `h' : E →L[𝕜] G`.
Suppose that

- `f ∘ g = h` in a neighborhood of `a`;
- `h` has derivative `h'` at `a`;
- `f` has derivative `f'` at `g a`;
- `g` is continuous at `a`;
- either `f'` has a right inverse `f'⁻¹` and `g' = f'⁻¹ ∘ h'`,
  or `f'` is a topological embedding and `h' = f' ∘ g'`.

Then `g` has derivative `g'` at `a`.
We prove these theorems for different differentiability predicates,
then specialize it to the cases when `f'` is a linear equivalence and/or `h = id`.
-/

open Filter
open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

public section

section OfComp

variable {g : E -> F} {f : F -> G} {h : E -> G}
  {g' : E ->L[𝕜] F} {f' : F ->L[𝕜] G} {h' : E ->L[𝕜] G} {f'symm : G ->L[𝕜] F}
  {lE : Filter (E × E)} {lF : Filter (F × F)}
  {a : E} {s : Set E} {t : Set F}

/--
theorem `HasFDerivAtFilter.of_comp_aux` / 定理 `HasFDerivAtFilter.of_comp_aux`

English:
theorem HasFDerivAtFilter.of_comp_aux
  statement: (hf_emb : Topology.IsEmbedding f')
  proof: by
refine .of_isLittleOTVS ho.trans_isLittleOTVS .triangle (.symm ?_) hh.isLittleOTVS
.trans_isBigOTVS ?_ refine (hf.isLittleOTVS.comp_tendsto htendsto).congr' ?_ .rfl
  · refine hcomp.mono ?_
    simp +contextual
.trans ?_ .symm.isBigOTVS.comp_tendsto htendsto · refine hf.isThetaTVS_sub hf_emb.isIn

中文:
定理 HasFDerivAtFilter.of_comp_aux
  结论: (hf_emb : Topology.IsEmbedding f')
  证明: by
refine .of_isLittleOTVS ho.trans_isLittleOTVS .triangle (.symm ?_) hh.isLittleOTVS
.trans_isBigOTVS ?_ refine (hf.isLittleOTVS.comp_tendsto htendsto).congr' ?_ .rfl
  · refine hcomp.mono ?_
    simp +contextual
.trans ?_ .symm.isBigOTVS.comp_tendsto htendsto · refine hf.isThetaTVS_sub hf_emb.isIn
-/
private theorem HasFDerivAtFilter.of_comp_aux (hf_emb : Topology.IsEmbedding f')
    (htendsto : Tendsto (Prod.map g g) lE lF)
    (hh : HasFDerivAtFilter h h' lE)
    (hf : HasFDerivAtFilter f f' lF)
    (hcomp : Prod.map (f ∘ g) (f ∘ g) =ᶠ[lE] Prod.map h h)
    (ho : (fun (x, y) => g x - g y - g' (x - y)) =O[𝕜; lE]
      (fun (x, y) => f' (g x - g y) - h' (x - y))) :
    HasFDerivAtFilter g g' lE := by
refine .of_isLittleOTVS ho.trans_isLittleOTVS .triangle (.symm ?_) hh.isLittleOTVS
.trans_isBigOTVS ?_ refine (hf.isLittleOTVS.comp_tendsto htendsto).congr' ?_ .rfl
  · refine hcomp.mono ?_
    simp +contextual
.trans ?_ .symm.isBigOTVS.comp_tendsto htendsto · refine hf.isThetaTVS_sub hf_emb.isInducing
    refine hh.isBigOTVS_sub.congr' (hcomp.mono ?_) .rfl
    simp +contextual


/--
theorem `HasFDerivAtFilter.of_comp_of_leftInverse` / 定理 `HasFDerivAtFilter.of_comp_of_leftInverse`

English:
theorem HasFDerivAtFilter.of_comp_of_leftInverse
  proof: by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
  · exact Topology.IsEmbedding.of_leftInverse hf'symm (map_continuous _) (map_continuous _)
  · refine f'symm.isBigOTVS_comp.congr_left ?_
    simp [hf'symm _]

中文:
定理 HasFDerivAtFilter.of_comp_of_leftInverse
  证明: by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
  · exact Topology.IsEmbedding.of_leftInverse hf'symm (map_continuous _) (map_continuous _)
  · refine f'symm.isBigOTVS_comp.congr_left ?_
    simp [hf'symm _]

Depends on / 依赖: IsEmbedding, Topology, Topology.IsEmbedding.of_leftInverse, congr_left, isBigOTVS_comp, map_continuous, of_comp_aux, of_leftInverse, symm.isBigOTVS_comp.congr_left
-/
theorem HasFDerivAtFilter.of_comp_of_leftInverse
    (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF)
    (hh : HasFDerivAtFilter h h' lE) (hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasFDerivAtFilter g (f'symm ∘L h') lE := by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
  · exact Topology.IsEmbedding.of_leftInverse hf'symm (map_continuous _) (map_continuous _)
  · refine f'symm.isBigOTVS_comp.congr_left ?_
    simp [hf'symm _]

/--
theorem `HasFDerivWithinAt.of_comp_of_leftInverse` / 定理 `HasFDerivWithinAt.of_comp_of_leftInverse`

English:
theorem HasFDerivWithinAt.of_comp_of_leftInverse
  proof: by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hst.prodMap (by simp)
  · exact hcomp.prodMap (hcomp.self_of_nhdsWithin ha)

中文:
定理 HasFDerivWithinAt.of_comp_of_leftInverse
  证明: by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hst.prodMap (by simp)
  · exact hcomp.prodMap (hcomp.self_of_nhdsWithin ha)

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.of_comp_of_leftInverse, hcomp.prodMap, hcomp.self_of_nhdsWithin, hst.prodMap, of_comp_of_leftInverse, prodMap, self_of_nhdsWithin
-/
theorem HasFDerivWithinAt.of_comp_of_leftInverse
    (hst : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f f' t (g a))
    (hh : HasFDerivWithinAt h h' s a) (hcomp : f ∘ g =ᶠ[𝓝[s] a] h)
    (hf'symm : Function.LeftInverse f'symm f') (ha : a in s) :
    HasFDerivWithinAt g (f'symm ∘L h') s a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hst.prodMap (by simp)
  · exact hcomp.prodMap (hcomp.self_of_nhdsWithin ha)

/--
theorem `HasFDerivAt.of_comp_of_leftInverse` / 定理 `HasFDerivAt.of_comp_of_leftInverse`

English:
theorem HasFDerivAt.of_comp_of_leftInverse
  proof: by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hgc.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

中文:
定理 HasFDerivAt.of_comp_of_leftInverse
  证明: by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hgc.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.of_comp_of_leftInverse, hcomp.prodMap, hcomp.self_of_nhds, hgc.tendsto.prodMap, of_comp_of_leftInverse, prodMap, self_of_nhds, tendsto
-/
theorem HasFDerivAt.of_comp_of_leftInverse
    (hgc : ContinuousAt g a) (hf : HasFDerivAt f f' (g a))
    (hh : HasFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 a] h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasFDerivAt g (f'symm ∘L h') a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hgc.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

/--
theorem `HasStrictFDerivAt.of_comp_of_leftInverse` / 定理 `HasStrictFDerivAt.of_comp_of_leftInverse`

English:
theorem HasStrictFDerivAt.of_comp_of_leftInverse
  proof: HasFDerivAtFilter.of_comp_of_leftInverse (hgc.prodMap_nhds hgc) hf hh
    (hcomp.prodMap_nhds hcomp) hf'symm

中文:
定理 HasStrictFDerivAt.of_comp_of_leftInverse
  证明: HasFDerivAtFilter.of_comp_of_leftInverse (hgc.prodMap_nhds hgc) hf hh
    (hcomp.prodMap_nhds hcomp) hf'symm

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.of_comp_of_leftInverse, hcomp.prodMap_nhds, hgc.prodMap_nhds, of_comp_of_leftInverse, prodMap_nhds
-/
theorem HasStrictFDerivAt.of_comp_of_leftInverse
    (hgc : ContinuousAt g a) (hf : HasStrictFDerivAt f f' (g a))
    (hh : HasStrictFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 a] h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasStrictFDerivAt g (f'symm ∘L h') a :=
  HasFDerivAtFilter.of_comp_of_leftInverse (hgc.prodMap_nhds hgc) hf hh
    (hcomp.prodMap_nhds hcomp) hf'symm



/--
theorem `HasFDerivAtFilter.of_comp_of_isEmbedding` / 定理 `HasFDerivAtFilter.of_comp_of_isEmbedding`

English:
theorem HasFDerivAtFilter.of_comp_of_isEmbedding
  proof: by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
.symm.isBigOTVS.congr_right ?_ refine f'.isThetaTVS_comp hf'.isInducing
  simp

中文:
定理 HasFDerivAtFilter.of_comp_of_isEmbedding
  证明: by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
.symm.isBigOTVS.congr_right ?_ refine f'.isThetaTVS_comp hf'.isInducing
  simp

Depends on / 依赖: congr_right, isBigOTVS, isInducing, isThetaTVS_comp, of_comp_aux, symm.isBigOTVS.congr_right
-/
theorem HasFDerivAtFilter.of_comp_of_isEmbedding
    (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF)
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivAtFilter h (f' ∘L g') lE)
    (hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h) :
    HasFDerivAtFilter g g' lE := by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
.symm.isBigOTVS.congr_right ?_ refine f'.isThetaTVS_comp hf'.isInducing
  simp

/--
theorem `HasFDerivWithinAt.of_comp_of_isEmbedding` / 定理 `HasFDerivWithinAt.of_comp_of_isEmbedding`

English:
theorem HasFDerivWithinAt.of_comp_of_isEmbedding
  proof: by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.prodMap (by simp)
· exact hcomp.prodMap hcomp.self_of_nhdsWithin ha

中文:
定理 HasFDerivWithinAt.of_comp_of_isEmbedding
  证明: by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.prodMap (by simp)
· exact hcomp.prodMap hcomp.self_of_nhdsWithin ha

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.of_comp_of_isEmbedding, hcomp.prodMap, hcomp.self_of_nhdsWithin, hg.prodMap, of_comp_of_isEmbedding, prodMap, self_of_nhdsWithin
-/
theorem HasFDerivWithinAt.of_comp_of_isEmbedding
    (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f f' t (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivWithinAt h (f' ∘L g') s a)
    (hcomp : (f ∘ g) =ᶠ[𝓝[s] a] h) (ha : a in s) :
    HasFDerivWithinAt g g' s a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.prodMap (by simp)
· exact hcomp.prodMap hcomp.self_of_nhdsWithin ha

/--
theorem `HasFDerivAt.of_comp_of_isEmbedding` / 定理 `HasFDerivAt.of_comp_of_isEmbedding`

English:
theorem HasFDerivAt.of_comp_of_isEmbedding
  proof: by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

中文:
定理 HasFDerivAt.of_comp_of_isEmbedding
  证明: by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.of_comp_of_isEmbedding, hcomp.prodMap, hcomp.self_of_nhds, hg.tendsto.prodMap, of_comp_of_isEmbedding, prodMap, self_of_nhds, tendsto
-/
theorem HasFDerivAt.of_comp_of_isEmbedding
    (hg : ContinuousAt g a) (hf : HasFDerivAt f f' (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivAt h (f' ∘L g') a)
    (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) :
    HasFDerivAt g g' a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

/--
theorem `HasStrictFDerivAt.of_comp_of_isEmbedding` / 定理 `HasStrictFDerivAt.of_comp_of_isEmbedding`

English:
theorem HasStrictFDerivAt.of_comp_of_isEmbedding
  proof: HasFDerivAtFilter.of_comp_of_isEmbedding (hg.prodMap hg) hf hf' hh (hcomp.prodMap_nhds hcomp)

中文:
定理 HasStrictFDerivAt.of_comp_of_isEmbedding
  证明: HasFDerivAtFilter.of_comp_of_isEmbedding (hg.prodMap hg) hf hf' hh (hcomp.prodMap_nhds hcomp)

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.of_comp_of_isEmbedding, hcomp.prodMap_nhds, hg.prodMap, of_comp_of_isEmbedding, prodMap, prodMap_nhds
-/
theorem HasStrictFDerivAt.of_comp_of_isEmbedding
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f f' (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasStrictFDerivAt h (f' ∘L g') a)
    (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) :
    HasStrictFDerivAt g g' a :=
  HasFDerivAtFilter.of_comp_of_isEmbedding (hg.prodMap hg) hf hf' hh (hcomp.prodMap_nhds hcomp)

end OfComp

/-!
### Local left inverse (equivalence)
-/

section LeftInverse

variable {g : E -> F} {f : F -> E} {f' : F ≃L[𝕜] E} {a : E} {s : Set E} {t : Set F}

/--
theorem `HasFDerivAt.of_local_left_inverse` / 定理 `HasFDerivAt.of_local_left_inverse`

English:
theorem HasFDerivAt.of_local_left_inverse
  proof: hf.of_comp_of_leftInverse (f'symm := (f'.symm : E ->L[𝕜] F)) hg (hasFDerivAt_id _) hfg
    f'.symm_apply_apply

中文:
定理 HasFDerivAt.of_local_left_inverse
  证明: hf.of_comp_of_leftInverse (f'symm := (f'.symm : E ->L[𝕜] F)) hg (hasFDerivAt_id _) hfg
    f'.symm_apply_apply

Depends on / 依赖: hasFDerivAt_id, hf.of_comp_of_leftInverse, of_comp_of_leftInverse, symm_apply_apply
-/
theorem HasFDerivAt.of_local_left_inverse
    (hg : ContinuousAt g a) (hf : HasFDerivAt f (f' : F ->L[𝕜] E) (g a))
    (hfg : forallᶠ y in 𝓝 a, f (g y) = y) : HasFDerivAt g (f'.symm : E ->L[𝕜] F) a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : E ->L[𝕜] F)) hg (hasFDerivAt_id _) hfg
    f'.symm_apply_apply

/--
theorem `HasFDerivWithinAt.of_local_left_inverse` / 定理 `HasFDerivWithinAt.of_local_left_inverse`

English:
theorem HasFDerivWithinAt.of_local_left_inverse
  proof: hf.of_comp_of_leftInverse (f'symm := (f'.symm : E ->L[𝕜] F)) hg (hasFDerivWithinAt_id _ _) hfg
    f'.symm_apply_apply ha

中文:
定理 HasFDerivWithinAt.of_local_left_inverse
  证明: hf.of_comp_of_leftInverse (f'symm := (f'.symm : E ->L[𝕜] F)) hg (hasFDerivWithinAt_id _ _) hfg
    f'.symm_apply_apply ha

Depends on / 依赖: hasFDerivWithinAt_id, hf.of_comp_of_leftInverse, of_comp_of_leftInverse, symm_apply_apply
-/
theorem HasFDerivWithinAt.of_local_left_inverse
    (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f (f' : F ->L[𝕜] E) t (g a))
    (ha : a in s) (hfg : forallᶠ x in 𝓝[s] a, f (g x) = x) :
    HasFDerivWithinAt g (f'.symm : E ->L[𝕜] F) s a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : E ->L[𝕜] F)) hg (hasFDerivWithinAt_id _ _) hfg
    f'.symm_apply_apply ha

/--
theorem `HasStrictFDerivAt.of_local_left_inverse` / 定理 `HasStrictFDerivAt.of_local_left_inverse`

English:
theorem HasStrictFDerivAt.of_local_left_inverse
  statement: {f : E -> F} {f' : E ≃L[𝕜] F} {g : F -> E} {a : F}
  proof: hf.of_comp_of_leftInverse (f'symm := (f'.symm : F ->L[𝕜] E)) hg (hasStrictFDerivAt_id _) hfg
    f'.symm_apply_apply

中文:
定理 HasStrictFDerivAt.of_local_left_inverse
  结论: {f : E -> F} {f' : E ≃L[𝕜] F} {g : F -> E} {a : F}
  证明: hf.of_comp_of_leftInverse (f'symm := (f'.symm : F ->L[𝕜] E)) hg (hasStrictFDerivAt_id _) hfg
    f'.symm_apply_apply

Depends on / 依赖: hasStrictFDerivAt_id, hf.of_comp_of_leftInverse, of_comp_of_leftInverse, symm_apply_apply
-/
theorem HasStrictFDerivAt.of_local_left_inverse {f : E -> F} {f' : E ≃L[𝕜] F} {g : F -> E} {a : F}
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) (g a))
    (hfg : forallᶠ y in 𝓝 a, f (g y) = y) : HasStrictFDerivAt g (f'.symm : F ->L[𝕜] E) a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : F ->L[𝕜] E)) hg (hasStrictFDerivAt_id _) hfg
    f'.symm_apply_apply

/--
theorem `OpenPartialHomeomorph.hasStrictFDerivAt_symm` / 定理 `OpenPartialHomeomorph.hasStrictFDerivAt_symm`

English:
theorem OpenPartialHomeomorph.hasStrictFDerivAt_symm
  statement: (f : OpenPartialHomeomorph E F)
  proof: htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

中文:
定理 OpenPartialHomeomorph.hasStrictFDerivAt_symm
  结论: (f : OpenPartialHomeomorph E F)
  证明: htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

Depends on / 依赖: continuousAt, eventually_right_inverse, f.eventually_right_inverse, f.symm.continuousAt, of_local_left_inverse
-/
theorem OpenPartialHomeomorph.hasStrictFDerivAt_symm (f : OpenPartialHomeomorph E F)
    {f' : E ≃L[𝕜] F} {a : F} (ha : a in f.target)
    (htff' : HasStrictFDerivAt f (f' : E ->L[𝕜] F) (f.symm a)) :
    HasStrictFDerivAt f.symm (f'.symm : F ->L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

/--
theorem `OpenPartialHomeomorph.hasFDerivAt_symm` / 定理 `OpenPartialHomeomorph.hasFDerivAt_symm`

English:
theorem OpenPartialHomeomorph.hasFDerivAt_symm
  statement: (f : OpenPartialHomeomorph E F) {f' : E ≃L[𝕜] F}
  proof: htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

中文:
定理 OpenPartialHomeomorph.hasFDerivAt_symm
  结论: (f : OpenPartialHomeomorph E F) {f' : E ≃L[𝕜] F}
  证明: htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

Depends on / 依赖: continuousAt, eventually_right_inverse, f.eventually_right_inverse, f.symm.continuousAt, of_local_left_inverse
-/
theorem OpenPartialHomeomorph.hasFDerivAt_symm (f : OpenPartialHomeomorph E F) {f' : E ≃L[𝕜] F}
    {a : F} (ha : a in f.target) (htff' : HasFDerivAt f (f' : E ->L[𝕜] F) (f.symm a)) :
    HasFDerivAt f.symm (f'.symm : F ->L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)
