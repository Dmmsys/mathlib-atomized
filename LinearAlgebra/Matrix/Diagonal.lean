/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear map
-/

public section


noncomputable section

open LinearMap Matrix Set Submodule Matrix

universe u v w

namespace Matrix

section CommSemiring

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type v} [CommSemiring R]

/--
theorem `proj_diagonal` / 定理 `proj_diagonal`

English:
theorem proj_diagonal
  given: (i : n) (w : n -> R)
  statement: (proj i).comp (toLin' (diagonal w)) = w i • proj i
  proof: LinearMap.ext fun _ => mulVec_diagonal _ _ _

中文:
定理 proj_diagonal
  条件: (i : n) (w : n -> R)
  结论: (proj i).comp (toLin' (diagonal w)) = w i • proj i
  证明: LinearMap.ext fun _ => mulVec_diagonal _ _ _

Depends on / 依赖: LinearMap, LinearMap.ext, mulVec_diagonal
-/
theorem proj_diagonal (i : n) (w : n -> R) : (proj i).comp (toLin' (diagonal w)) = w i • proj i :=
  LinearMap.ext fun _ => mulVec_diagonal _ _ _

/--
theorem `diagonal_comp_single` / 定理 `diagonal_comp_single`

English:
theorem diagonal_comp_single
  given: (w : n -> R) (i : n)
  proof: LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)

中文:
定理 diagonal_comp_single
  条件: (w : n -> R) (i : n)
  证明: LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)

Depends on / 依赖: LinearMap, LinearMap.ext, Pi.single_smul, diagonal_mulVec_single, single_smul
-/
theorem diagonal_comp_single (w : n -> R) (i : n) :
    (diagonal w).toLin'.comp (LinearMap.single R (fun _ : n => R) i) =
      w i • LinearMap.single R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)

/--
theorem `diagonal_toLin'` / 定理 `diagonal_toLin'`

English:
theorem diagonal_toLin'
  given: (w : n -> R)
  proof: LinearMap.ext fun _ => funext fun _ => mulVec_diagonal _ _ _

中文:
定理 diagonal_toLin'
  条件: (w : n -> R)
  证明: LinearMap.ext fun _ => funext fun _ => mulVec_diagonal _ _ _

Depends on / 依赖: LinearMap, LinearMap.ext, mulVec_diagonal
-/
theorem diagonal_toLin' (w : n -> R) :
    toLin' (diagonal w) = LinearMap.pi fun i => w i • LinearMap.proj i :=
  LinearMap.ext fun _ => funext fun _ => mulVec_diagonal _ _ _

end CommSemiring

section Semifield

variable {m : Type*} [Fintype m] {K : Type u} [Semifield K]

-- maybe try to relax the universe constraint
/--
theorem `ker_diagonal_toLin'` / 定理 `ker_diagonal_toLin'`

English:
theorem ker_diagonal_toLin'
  given: [DecidableEq m] (w : m -> K)
  proof: by
  rw [← comap_bot]
  simpa [← ker_comp, proj_diagonal, ker_smul', ← iInf_ker_proj] using
    (iSup_range_single_eq_iInf_ker_proj K _ isCompl_compl {i | w i = 0}.toFinite).symm

中文:
定理 ker_diagonal_toLin'
  条件: [DecidableEq m] (w : m -> K)
  证明: by
  rw [← comap_bot]
  simpa [← ker_comp, proj_diagonal, ker_smul', ← iInf_ker_proj] using
    (iSup_range_single_eq_iInf_ker_proj K _ isCompl_compl {i | w i = 0}.toFinite).symm

Depends on / 依赖: comap_bot, iInf_ker_proj, iSup_range_single_eq_iInf_ker_proj, isCompl_compl, ker_comp, ker_smul, proj_diagonal, toFinite
-/
theorem ker_diagonal_toLin' [DecidableEq m] (w : m -> K) :
    ker (toLin' (diagonal w)) =
      ⨆ i in { i | w i = 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) := by
  rw [← comap_bot]
  simpa [← ker_comp, proj_diagonal, ker_smul', ← iInf_ker_proj] using
    (iSup_range_single_eq_iInf_ker_proj K _ isCompl_compl {i | w i = 0}.toFinite).symm

/--
theorem `range_diagonal` / 定理 `range_diagonal`

English:
theorem range_diagonal
  given: [DecidableEq m] (w : m -> K)
  proof: by
  dsimp only [mem_ofPred_eq]
  rw [← Submodule.map_top]; rw [← iSup_range_single]; rw [Submodule.map_iSup]
  congr; funext i
  rw [← LinearMap.range_comp]; rw [diagonal_comp_single]; rw [← range_smul']

中文:
定理 range_diagonal
  条件: [DecidableEq m] (w : m -> K)
  证明: by
  dsimp only [mem_ofPred_eq]
  rw [← Submodule.map_top]; rw [← iSup_range_single]; rw [Submodule.map_iSup]
  congr; funext i
  rw [← LinearMap.range_comp]; rw [diagonal_comp_single]; rw [← range_smul']

Depends on / 依赖: LinearMap, LinearMap.range_comp, Submodule, Submodule.map_iSup, Submodule.map_top, diagonal_comp_single, iSup_range_single, map_iSup, map_top, mem_ofPred_eq, range_comp, range_smul
-/
theorem range_diagonal [DecidableEq m] (w : m -> K) :
    LinearMap.range (toLin' (diagonal w)) =
      ⨆ i in { i | w i != 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) := by
  dsimp only [mem_ofPred_eq]
  rw [← Submodule.map_top]; rw [← iSup_range_single]; rw [Submodule.map_iSup]
  congr; funext i
  rw [← LinearMap.range_comp]; rw [diagonal_comp_single]; rw [← range_smul']

end Semifield

end Matrix

namespace LinearMap

section Field

variable {m : Type*} [Fintype m] {K : Type u} [Field K]

/--
theorem `rank_diagonal` / 定理 `rank_diagonal`

English:
theorem rank_diagonal
  given: [DecidableEq m] [DecidableEq K] (w : m -> K)
  proof: by
  have hIJ : IsCompl { i : m | w i != 0 } { i : m | w i = 0 } := isCompl_compl.symm
  have B₁ := iSup_range_single_eq_iInf_ker_proj K (fun _ : m => K) hIJ (Set.toFinite _)
  rw [LinearMap.rank]; rw [range_diagonal]; rw [B₁]; rw [← @rank_fun' K]
.rank_eq exact iInfKerProjEquiv K (fun _ => K) hIJ.disjoint hIJ.codisjoint.top_le

中文:
定理 rank_diagonal
  条件: [DecidableEq m] [DecidableEq K] (w : m -> K)
  证明: by
  have hIJ : IsCompl { i : m | w i != 0 } { i : m | w i = 0 } := isCompl_compl.symm
  have B₁ := iSup_range_single_eq_iInf_ker_proj K (fun _ : m => K) hIJ (Set.toFinite _)
  rw [LinearMap.rank]; rw [range_diagonal]; rw [B₁]; rw [← @rank_fun' K]
.rank_eq exact iInfKerProjEquiv K (fun _ => K) hIJ.disjoint hIJ.codisjoint.top_le

Depends on / 依赖: IsCompl, LinearMap, LinearMap.rank, Set.toFinite, codisjoint, disjoint, hIJ.codisjoint.top_le, hIJ.disjoint, iInfKerProjEquiv, iSup_range_single_eq_iInf_ker_proj, isCompl_compl, isCompl_compl.symm, range_diagonal, rank_eq, rank_fun, toFinite, top_le
-/
theorem rank_diagonal [DecidableEq m] [DecidableEq K] (w : m -> K) :
    LinearMap.rank (toLin' (diagonal w)) = Fintype.card { i // w i != 0 } := by
  have hIJ : IsCompl { i : m | w i != 0 } { i : m | w i = 0 } := isCompl_compl.symm
  have B₁ := iSup_range_single_eq_iInf_ker_proj K (fun _ : m => K) hIJ (Set.toFinite _)
  rw [LinearMap.rank]; rw [range_diagonal]; rw [B₁]; rw [← @rank_fun' K]
.rank_eq exact iInfKerProjEquiv K (fun _ => K) hIJ.disjoint hIJ.codisjoint.top_le

end Field

end LinearMap
