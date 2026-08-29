/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Anatole Dedecker, Yongxi Lin, Patrick Massot, Oliver Nash, Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite

/-!
# Fredholm operators between topological vector spaces

Fix `𝕜` a complete `NontriviallyNormedField`, and let `E`, `F` be two Hausdorff topological vector
spaces over `𝕜`.

We say that a continuous linear map `T : E →L[𝕜] F` is a **Fredholm operator** if it satisfies
the following four equivalent conditions:

1. `T` is strict, its range is closed and has finite codimension, and its kernel is (topologically)
  complemented and has finite dimension. This is chosen as the definition, see `IsFredholm`.
2. `T` admits a continuous **quasi-inverse**, in the sense of `LinearMap.IsQuasiInverse`.
3. There are closed finite-codimension subspaces `E₁` and `F₁` of `E` and `F` between which `T`
  induces an isomorphism.
4. `T` admits a `FredholmPackage`: there are topological decompositions `E = E₁ ⊕ E₀`,
  `F = F₁ ⊕ F₀`, where `E₀` and `F₀` are finite dimensional, and an isomorphism `Φ : E₁ ≃L[𝕜] F₁`
  such that `T` is zero on `E₀` and coincides with `Φ` on `E₁`; in other words, in these
  decompositions, `T` is given by the matrix $\begin{pmatrix} Φ & 0 \cr 0 & 0 \end{pmatrix}$.

## Main definitions

* `ContinuousLinearMap.IsFredholm`: a continuous linear map `u : E →L[𝕜] F` is a
  **Fredholm operator** if it is strict, its range is closed and has finite codimension, and its
  kernel is (topologically) complemented and has finite dimension.
* `FredholmDecomposition`: a **Fredholm decomposition** of a topological vector space `E` is the
  data of two subspaces `X₀` and `X₁` which are topological complements, and where `X₀` is finite
  dimensional.
* `ContinuousLinearMap.FredholmPackage`: a **Fredholm package** for `u : E →L[𝕜] F` is the data of
  Fredholm decompositions `decDom` and `decCodom` of `E` and `F` respectively, together with
  a continuous linear equivalence `equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁` between the "essential"
  (i.e. finite codimension) parts of these decompositions, such that `u` equals the composition
  `decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj`.

Note that the data of a `FredholmPackage` for an operator is morally the strongest of the
equivalent ways to assume that `u` is Fredholm (for example, it is clear how to build a canonical
continuous quasi-inverse of `u` from such a package).

Hence, you should not typically prove that an operator is Fredholm by building a Fredholm package
(consider using `IsFredholm.of_isInvertible_restrict`); instead, when you know that an operator is
Fredholm, you can obtain a `FredholmPackage` from `IsFredholm.nonempty_fredholmPackage`
in order to conveniently use the full strength of Fredholmness.

## Main statements

### Equivalent criteria

* `ContinuousLinearMap.isFredholm_tfae`: the equivalence between conditions 1, 2, 3 and 4 above.
  In practice, most of the interesting directions should be covered by specific API lemmas.
* `ContinuousLinearMap.FredholmPackage.isQuasiInverse`: given a `FredholmPackage` for `u`,
  one can build a canonical continuous quasi-inverse of `u`.
* `ContinuousLinearMap.IsFredholm.of_isInvertible_restrict`: if a continuous linear map induces
  an isomorphism between finite codimension subspaces, then it is Fredholm.
* `ContinuousLinearMap.IsFredholm.of_restrict` (not in Mathlib yet) is a generalization
  of the above: if a continuous linear map induces a Fredholm operator between finite codimension
  subspaces, then the original map is Fredholm as well.
* `IsFredholm.nonempty_fredholmPackage`: every Fredholm operator admits a Fredholm package.
  This is the primary way to obtain Fredholm packages.

## Implementation details

We largely follow [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 2][bourbaki2023],
in particular for the proof of equivalence of the four conditions above.
Here are some notable changes:

* Bourbaki restricts itself to locally convex spaces over `ℝ` or `ℂ`. Yet, under close inspection,
  this assumption plays very little role in the beginning of the theory. In fact, at the very mild
  cost of assuming that the kernel is complemented in the definition of `IsFredholm` (which follows
  from the finiteness assumption if Hahn-Banach is available), we generalize the beginning of the
  theory to topological vector spaces over any complete nontrivially normed field. In particular,
  our theory naturally captures p-adic Fredholm operators.
* Bourbaki chooses the existence of a continuous quasi-inverse as the definition of being Fredholm.
  Our choice differs for a very practical reason: it is much simpler to spell out formally
  "`u` has a continuous quasi-inverse" than "`u` is strict, its range is closed and has finite
  codimension, and its kernel is complemented and has finite dimension". Hence we prefer to give
  a name to the latter.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 2][bourbaki2023]
-/

@[expose] public noncomputable section

open Topology Submodule LinearMap
open Set (MapsTo)
open LinearMap.FiniteRangeSetoid

namespace ContinuousLinearMap
section TVS

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [TopologicalSpace E] [TopologicalSpace F]

/-!
## Definition and equivalent conditions
-/

section DefTFAE

section IsFredholm

/--
Definition of `IsFredholm` / `IsFredholm` 的定义

English:
structure IsFredholm
  parameters: (u : E ->L[𝕜] F)
  axioms and operations (5):
    - isStrictMap : IsStrictMap u
    - isClosed_range : IsClosed (u.range : Set F)
    - finite_ker : FiniteDimensional 𝕜 u.ker
    - finite_coker : u.range.CoFG
    - closedComplemented_ker : u.ker.ClosedComplemented

中文:
结构 IsFredholm
  参数: (u : E ->L[𝕜] F)
  公理与运算 (5 个):
    - isStrictMap : IsStrictMap u
    - isClosed_range : IsClosed (u.range : Set F)
    - finite_ker : FiniteDimensional 𝕜 u.ker
    - finite_coker : u.range.CoFG
    - closedComplemented_ker : u.ker.ClosedComplemented
-/
structure IsFredholm (u : E ->L[𝕜] F) : Prop where
  isStrictMap : IsStrictMap u
  isClosed_range : IsClosed (u.range : Set F)
  finite_ker : FiniteDimensional 𝕜 u.ker
  finite_coker : u.range.CoFG
  closedComplemented_ker : u.ker.ClosedComplemented

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
/--
lemma `IsFredholm.closedComplemented_range` / 引理 `IsFredholm.closedComplemented_range`

English:
lemma IsFredholm.closedComplemented_range
  given: {u : E ->L[𝕜] F} (u_fred : IsFredholm u)
  proof: have := u_fred.finite_coker
  ClosedComplemented.of_finiteDimensional_quotient u_fred.isClosed_range

中文:
引理 IsFredholm.closedComplemented_range
  条件: {u : E ->L[𝕜] F} (u_fred : IsFredholm u)
  证明: have := u_fred.finite_coker
  ClosedComplemented.of_finiteDimensional_quotient u_fred.isClosed_range

Depends on / 依赖: ClosedComplemented, ClosedComplemented.of_finiteDimensional_quotient, finite_coker, isClosed_range, of_finiteDimensional_quotient, u_fred, u_fred.finite_coker, u_fred.isClosed_range
-/
lemma IsFredholm.closedComplemented_range {u : E ->L[𝕜] F} (u_fred : IsFredholm u) :
    u.range.ClosedComplemented :=
  have := u_fred.finite_coker
  ClosedComplemented.of_finiteDimensional_quotient u_fred.isClosed_range

end IsFredholm

section FredholmPackage

variable (𝕜 E) in
/--
Definition of `_root_.FredholmDecomposition` / `_root_.FredholmDecomposition` 的定义

English:
structure _root_.FredholmDecomposition
  parameters: where
  axioms and operations (4):
    - X₀ : Submodule 𝕜 E
    - X₁ : Submodule 𝕜 E
    - isTopCompl : IsTopCompl X₁ X₀
    - finite_X₀ : FiniteDimensional 𝕜 X₀

中文:
结构 _root_.FredholmDecomposition
  参数: where
  公理与运算 (4 个):
    - X₀ : Submodule 𝕜 E
    - X₁ : Submodule 𝕜 E
    - isTopCompl : IsTopCompl X₁ X₀
    - finite_X₀ : FiniteDimensional 𝕜 X₀
-/
structure _root_.FredholmDecomposition where
  /-- The inessential (i.e. finite dimensional) part of a Fredholm decomposition. -/
  X₀ : Submodule 𝕜 E
  /-- The essential (i.e. finite codimensional) part of a Fredholm decomposition. -/
  X₁ : Submodule 𝕜 E
  isTopCompl : IsTopCompl X₁ X₀
  finite_X₀ : FiniteDimensional 𝕜 X₀

/--
Definition of `_root_.FredholmDecomposition.proj` / `_root_.FredholmDecomposition.proj` 的定义

English:
abbreviation _root_.FredholmDecomposition.proj
  signature: (dec : FredholmDecomposition 𝕜 E)
  body: dec.X₁.projectionOntoL dec.X₀ dec.isTopCompl

中文:
缩写 _root_.FredholmDecomposition.proj
  签名: (dec : FredholmDecomposition 𝕜 E)
  定义体: dec.X₁.projectionOntoL dec.X₀ dec.isTopCompl

Depends on / 依赖: dec.X, dec.isTopCompl, isTopCompl, projectionOntoL
-/
abbrev _root_.FredholmDecomposition.proj (dec : FredholmDecomposition 𝕜 E) :
    E ->L[𝕜] dec.X₁ := dec.X₁.projectionOntoL dec.X₀ dec.isTopCompl

/--
Definition of `FredholmPackage` / `FredholmPackage` 的定义

English:
structure FredholmPackage
  parameters: (u : E ->L[𝕜] F)
  axioms and operations (4):
    - decDom : FredholmDecomposition 𝕜 E
    - decCodom : FredholmDecomposition 𝕜 F
    - equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁
    - eq_equiv : u = decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj

中文:
结构 FredholmPackage
  参数: (u : E ->L[𝕜] F)
  公理与运算 (4 个):
    - decDom : FredholmDecomposition 𝕜 E
    - decCodom : FredholmDecomposition 𝕜 F
    - equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁
    - eq_equiv : u = decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj
-/
structure FredholmPackage (u : E ->L[𝕜] F) where
  /-- A `FredholmDecomposition` of the domain. -/
  decDom : FredholmDecomposition 𝕜 E
  /-- A `FredholmDecomposition` of the codomain. -/
  decCodom : FredholmDecomposition 𝕜 F
  /-- An isomorphism between the essential parts of `decDom` and `decCodom`. -/
  equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁
  eq_equiv : u = decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj

/--
lemma `FredholmPackage.ker_eq` / 引理 `FredholmPackage.ker_eq`

English:
lemma FredholmPackage.ker_eq
  given: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  proof: by simp [pkg.eq_equiv, ker_comp]

中文:
引理 FredholmPackage.ker_eq
  条件: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  证明: by simp [pkg.eq_equiv, ker_comp]

Depends on / 依赖: eq_equiv, ker_comp, pkg.eq_equiv
-/
lemma FredholmPackage.ker_eq {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
    u.ker = pkg.decDom.X₀ := by simp [pkg.eq_equiv, ker_comp]

/--
lemma `FredholmPackage.range_eq` / 引理 `FredholmPackage.range_eq`

English:
lemma FredholmPackage.range_eq
  given: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  proof: by
  simp [pkg.eq_equiv, range_comp]

中文:
引理 FredholmPackage.range_eq
  条件: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  证明: by
  simp [pkg.eq_equiv, range_comp]

Depends on / 依赖: eq_equiv, pkg.eq_equiv, range_comp
-/
lemma FredholmPackage.range_eq {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
    u.range = pkg.decCodom.X₁ := by
  simp [pkg.eq_equiv, range_comp]

/--
lemma `FredholmPackage.mapsTo` / 引理 `FredholmPackage.mapsTo`

English:
lemma FredholmPackage.mapsTo
  given: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  proof: by
  simpa [← FredholmPackage.range_eq, LinearMap.coe_range] using Set.mapsTo_range _ _

中文:
引理 FredholmPackage.mapsTo
  条件: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  证明: by
  simpa [← FredholmPackage.range_eq, LinearMap.coe_range] using Set.mapsTo_range _ _

Depends on / 依赖: FredholmPackage, FredholmPackage.range_eq, LinearMap, LinearMap.coe_range, Set.mapsTo_range, coe_range, mapsTo_range, range_eq
-/
lemma FredholmPackage.mapsTo {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
    MapsTo u pkg.decDom.X₁ pkg.decCodom.X₁ := by
  simpa [← FredholmPackage.range_eq, LinearMap.coe_range] using Set.mapsTo_range _ _

/--
lemma `FredholmPackage.equiv_eq_restrict` / 引理 `FredholmPackage.equiv_eq_restrict`

English:
lemma FredholmPackage.equiv_eq_restrict
  given: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  proof: by
  ext x
  simp [pkg.eq_equiv]

中文:
引理 FredholmPackage.equiv_eq_restrict
  条件: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  证明: by
  ext x
  simp [pkg.eq_equiv]

Depends on / 依赖: eq_equiv, pkg.eq_equiv
-/
lemma FredholmPackage.equiv_eq_restrict {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
    pkg.equiv = u.restrict pkg.mapsTo := by
  ext x
  simp [pkg.eq_equiv]

/--
lemma `FredholmPackage.isInvertible_restrict` / 引理 `FredholmPackage.isInvertible_restrict`

English:
lemma FredholmPackage.isInvertible_restrict
  given: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  proof: u.restrict pkg.mapsTo
  ⟨pkg.equiv, pkg.equiv_eq_restrict⟩

中文:
引理 FredholmPackage.isInvertible_restrict
  条件: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  证明: u.restrict pkg.mapsTo
  ⟨pkg.equiv, pkg.equiv_eq_restrict⟩

Depends on / 依赖: mapsTo, pkg.mapsTo, restrict, u.restrict
-/
lemma FredholmPackage.isInvertible_restrict {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
.IsInvertible := u.restrict pkg.mapsTo
  ⟨pkg.equiv, pkg.equiv_eq_restrict⟩

/--
Definition of `FredholmPackage.quasiInverse` / `FredholmPackage.quasiInverse` 的定义

English:
definition FredholmPackage.quasiInverse
  signature: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  body: pkg.decDom.X₁.subtypeL ∘L pkg.equiv.symm ∘L pkg.decCodom.proj

中文:
定义 FredholmPackage.quasiInverse
  签名: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  定义体: pkg.decDom.X₁.subtypeL ∘L pkg.equiv.symm ∘L pkg.decCodom.proj

Depends on / 依赖: decCodom, decDom, pkg.decCodom.proj, pkg.decDom.X, pkg.equiv.symm, subtypeL
-/
def FredholmPackage.quasiInverse {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
    F ->L[𝕜] E :=
  pkg.decDom.X₁.subtypeL ∘L pkg.equiv.symm ∘L pkg.decCodom.proj

/--
lemma `FredholmPackage.isQuasiInverse` / 引理 `FredholmPackage.isQuasiInverse`

English:
lemma FredholmPackage.isQuasiInverse
  given: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  proof: by
  nth_rw 2 [pkg.eq_equiv]
  have hdom : IsQuasiInverse pkg.decDom.X₁.subtype pkg.decDom.proj :=
    have := pkg.decDom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  have hcodom : IsQuasiInverse pkg.decCodom.X₁.subtype pkg.decCodom.proj :=
    have := pkg.decCodom.finite_X₀
    isQuasiIn

中文:
引理 FredholmPackage.isQuasiInverse
  条件: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  证明: by
  nth_rw 2 [pkg.eq_equiv]
  have hdom : IsQuasiInverse pkg.decDom.X₁.subtype pkg.decDom.proj :=
    have := pkg.decDom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  have hcodom : IsQuasiInverse pkg.decCodom.X₁.subtype pkg.decCodom.proj :=
    have := pkg.decCodom.finite_X₀
    isQuasiIn

Depends on / 依赖: IsQuasiInverse, decCodom, decDom, eq_equiv, hcodom, isQuasiInverse_subtype_projectionOnto, nth_rw, pkg.decCodom.X, pkg.decCodom.finite_X, pkg.decCodom.proj, pkg.decDom.X, pkg.decDom.finite_X, pkg.decDom.proj, pkg.eq_equiv, subtype
-/
lemma FredholmPackage.isQuasiInverse {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
    pkg.quasiInverse.IsQuasiInverse u := by
  nth_rw 2 [pkg.eq_equiv]
  have hdom : IsQuasiInverse pkg.decDom.X₁.subtype pkg.decDom.proj :=
    have := pkg.decDom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  have hcodom : IsQuasiInverse pkg.decCodom.X₁.subtype pkg.decCodom.proj :=
    have := pkg.decCodom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  -- For some reason `exact` and `refine` are slow here!
  apply hdom.comp (pkg.equiv.isQuasiInverse.comp hcodom.symm)

end FredholmPackage

variable [T2Space E] [T2Space F] in
/--
theorem `exists_restrict_isInvertible_of_isQuasiInverse` / 定理 `exists_restrict_isInvertible_of_isQuasiInverse`

English:
theorem exists_restrict_isInvertible_of_isQuasiInverse
  statement: {u : E ->L[𝕜] F}
  proof: by
  obtain ⟨hvu, huv⟩ := hvu
  rw [IsRightQuasiInverse]; rw [Setoid.comm]; rw [equiv_iff_eqLocus_coFG] at huv
  rw [IsLeftQuasiInverse]; rw [Setoid.comm]; rw [equiv_iff_eqLocus_coFG] at hvu
  set E₁ := (ContinuousLinearMap.id 𝕜 E).eqLocus (v ∘L u)
  set F₁ := (ContinuousLinearMap.id 𝕜 F).eqLocus (u

中文:
定理 exists_restrict_isInvertible_of_isQuasiInverse
  结论: {u : E ->L[𝕜] F}
  证明: by
  obtain ⟨hvu, huv⟩ := hvu
  rw [IsRightQuasiInverse]; rw [Setoid.comm]; rw [equiv_iff_eqLocus_coFG] at huv
  rw [IsLeftQuasiInverse]; rw [Setoid.comm]; rw [equiv_iff_eqLocus_coFG] at hvu
  set E₁ := (ContinuousLinearMap.id 𝕜 E).eqLocus (v ∘L u)
  set F₁ := (ContinuousLinearMap.id 𝕜 F).eqLocus (u
-/
private theorem exists_restrict_isInvertible_of_isQuasiInverse {u : E ->L[𝕜] F}
    {v : F ->L[𝕜] E} (hvu : v.IsQuasiInverse u) :
    exists (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
      IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
      E₁.CoFG ∧ F₁.CoFG ∧
      exists h : MapsTo u E₁ F₁, (u.restrict h).IsInvertible := by
  obtain ⟨hvu, huv⟩ := hvu
  rw [IsRightQuasiInverse]; rw [Setoid.comm]; rw [equiv_iff_eqLocus_coFG] at huv
  rw [IsLeftQuasiInverse]; rw [Setoid.comm]; rw [equiv_iff_eqLocus_coFG] at hvu
  set E₁ := (ContinuousLinearMap.id 𝕜 E).eqLocus (v ∘L u)
  set F₁ := (ContinuousLinearMap.id 𝕜 F).eqLocus (u ∘L v)
  have u_mapsto : MapsTo u E₁ F₁ := fun x hx => congr(u $hx)
  have v_mapsto : MapsTo v F₁ E₁ := fun x hx => congr(v $hx)
  refine ⟨E₁, F₁, isClosed_eqLocus _ _, isClosed_eqLocus _ _, hvu, huv, u_mapsto, ?_⟩
  refine .of_inverse (g := v.restrict v_mapsto) ?_ ?_
  · ext ⟨x, hx : x = u (v x)⟩
    simp [coe_restrict_apply u_mapsto, coe_restrict_apply v_mapsto, ← hx]
  · ext ⟨x, hx : x = v (u x)⟩
    simp [coe_restrict_apply u_mapsto, coe_restrict_apply v_mapsto, ← hx]

variable [CompleteSpace 𝕜]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

/--
theorem `IsFredholm.of_isInvertible_restrict` / 定理 `IsFredholm.of_isInvertible_restrict`

English:
theorem IsFredholm.of_isInvertible_restrict
  statement: {u : E ->L[𝕜] F}
  proof: by
  obtain ⟨e, he⟩ := h_inv
  have eqL : u.domRestrict E₁ = F₁.subtypeL ∘L e := congr(F₁.subtypeL ∘L $he).symm
  have eqₗ : u.toLinearMap.domRestrict E₁ = F₁.subtype ∘ₗ e := congr(($eqL).toLinearMap)
  have h : Topology.IsStrictMap u ∧ IsClosed (u.range : Set F) := by
    rw [u.isStrictMap_isClosed

中文:
定理 IsFredholm.of_isInvertible_restrict
  结论: {u : E ->L[𝕜] F}
  证明: by
  obtain ⟨e, he⟩ := h_inv
  have eqL : u.domRestrict E₁ = F₁.subtypeL ∘L e := congr(F₁.subtypeL ∘L $he).symm
  have eqₗ : u.toLinearMap.domRestrict E₁ = F₁.subtype ∘ₗ e := congr(($eqL).toLinearMap)
  have h : Topology.IsStrictMap u ∧ IsClosed (u.range : Set F) := by
    rw [u.isStrictMap_isClosed

Depends on / 依赖: Disjoint, IsClosed, IsStrictMap, LinearMa, Topology, Topology.IsStrictMap, disjoint_iff_comap_eq_bot, domRestrict, e.isHomeomorph.isEmbedding, h_inv, isEmbedding, isEmbedding_subtype, isEmbedding_subtype.comp, isHomeomorph, isStrictMap, isStrictMap_isClosed_range_iff_restrict, subtype, subtypeL, toLinearMap, u.domRestrict
-/
theorem IsFredholm.of_isInvertible_restrict {u : E ->L[𝕜] F}
    {E₁ : Submodule 𝕜 E} (E₁_closed : IsClosed (E₁ : Set E)) [E₁_coFG : E₁.CoFG]
    {F₁ : Submodule 𝕜 F} (F₁_closed : IsClosed (F₁ : Set F)) [F₁_coFG : F₁.CoFG]
    (h_mapsto : MapsTo u E₁ F₁) (h_inv : (u.restrict h_mapsto).IsInvertible) :
    IsFredholm u := by
  obtain ⟨e, he⟩ := h_inv
  have eqL : u.domRestrict E₁ = F₁.subtypeL ∘L e := congr(F₁.subtypeL ∘L $he).symm
  have eqₗ : u.toLinearMap.domRestrict E₁ = F₁.subtype ∘ₗ e := congr(($eqL).toLinearMap)
  have h : Topology.IsStrictMap u ∧ IsClosed (u.range : Set F) := by
    rw [u.isStrictMap_isClosed_range_iff_restrict E₁ E₁_closed]; rw [eqL]
.isStrictMap, by simpa⟩ exact ⟨F₁.isEmbedding_subtype.comp e.isHomeomorph.isEmbedding
  have disj : Disjoint E₁ u.ker := by
    rw [disjoint_iff_comap_eq_bot]; rw [← LinearMap.ker_domRestrict]; rw [eqₗ]; rw [LinearMap.ker_comp]; rw [ker_subtype]; rw [comap_bot]; rw [LinearEquiv.ker]
  refine ⟨h.1, h.2, ?_, ?_, ?_⟩
  · rw [← Submodule.fg_iff_finiteDimensional]
    exact E₁_coFG.fg_of_disjoint disj.symm
  · refine F₁_coFG.of_le (le_trans ?_ (u.range_domRestrict_le_range E₁))
    rw [eqₗ]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [Submodule.map_top]; rw [range_subtype]
  · exact .of_disjoint_of_finiteDimensional_quotient E₁_closed disj.symm

omit [ContinuousSMul 𝕜 E] in
/--
Definition of `IsFredholm.fredholmPackage` / `IsFredholm.fredholmPackage` 的定义

English:
definition IsFredholm.fredholmPackage
  signature: {u : E ->L[𝕜] F}
  body: { X₀ := u.ker
      X₁ := dom₁
      isTopCompl := h_dom.symm
      finite_X₀ := u_fred.finite_ker }
  decCodom :=
    { X₀ := codom₀
      X₁ := u.range
      isTopCompl := h_codom
finite_X₀ := .of_fg u_fred.finite_coker.fg_of_isCompl h_codom.isCompl }
  equiv :=
.symm letI Φ : dom₁ ≃L[𝕜] E ⧸ u.ker

中文:
定义 IsFredholm.fredholmPackage
  签名: {u : E ->L[𝕜] F}
  定义体: { X₀ := u.ker
      X₁ := dom₁
      isTopCompl := h_dom.symm
      finite_X₀ := u_fred.finite_ker }
  decCodom :=
    { X₀ := codom₀
      X₁ := u.range
      isTopCompl := h_codom
finite_X₀ := .of_fg u_fred.finite_coker.fg_of_isCompl h_codom.isCompl }
  equiv :=
.symm letI Φ : dom₁ ≃L[𝕜] E ⧸ u.ker

Depends on / 依赖: LinearMap, LinearMap.ext_on_codisjoint, codisjoint, decCodom, eq_equiv, ext_on_codisjoint, fg_of_isCompl, finite_coker, finite_ker, h_codom, h_codom.isCompl, h_dom, h_dom.isCompl.codisjoint, h_dom.symm, isCompl, isStrictMap, isTopCompl, of_fg, quotKerEquivRange, quotientEquivOfIsTopCompl
-/
def IsFredholm.fredholmPackage {u : E ->L[𝕜] F}
    (u_fred : IsFredholm u) {dom₁ : Submodule 𝕜 E} {codom₀ : Submodule 𝕜 F}
    (h_dom : IsTopCompl u.ker dom₁) (h_codom : IsTopCompl u.range codom₀) :
    FredholmPackage u where
  decDom :=
    { X₀ := u.ker
      X₁ := dom₁
      isTopCompl := h_dom.symm
      finite_X₀ := u_fred.finite_ker }
  decCodom :=
    { X₀ := codom₀
      X₁ := u.range
      isTopCompl := h_codom
finite_X₀ := .of_fg u_fred.finite_coker.fg_of_isCompl h_codom.isCompl }
  equiv :=
.symm letI Φ : dom₁ ≃L[𝕜] E ⧸ u.ker := u.ker.quotientEquivOfIsTopCompl dom₁ h_dom
    letI Ψ : (E ⧸ u.ker) ≃L[𝕜] u.range := .quotKerEquivRange u_fred.isStrictMap
    Φ.trans Ψ
  eq_equiv := by
    refine LinearMap.ext_on_codisjoint h_dom.isCompl.codisjoint ?_ ?_
    · intro x (hx : u x = 0)
      simp [hx, projection_apply_of_mem_right]
    · intro x (hx : x in dom₁)
      simp [hx, projection_apply_of_mem_left, ContinuousLinearEquiv.quotKerEquivRange]

omit [ContinuousSMul 𝕜 E] in
/--
theorem `IsFredholm.nonempty_fredholmPackage` / 定理 `IsFredholm.nonempty_fredholmPackage`

English:
theorem IsFredholm.nonempty_fredholmPackage
  statement: {u : E ->L[𝕜] F}
  proof: by
  obtain ⟨codom₀, h_codom⟩ := u_fred.closedComplemented_range.exists_isTopCompl
  obtain ⟨dom₁, h_dom⟩ := u_fred.closedComplemented_ker.exists_isTopCompl
  exact ⟨u_fred.fredholmPackage h_dom h_codom⟩

中文:
定理 IsFredholm.nonempty_fredholmPackage
  结论: {u : E ->L[𝕜] F}
  证明: by
  obtain ⟨codom₀, h_codom⟩ := u_fred.closedComplemented_range.exists_isTopCompl
  obtain ⟨dom₁, h_dom⟩ := u_fred.closedComplemented_ker.exists_isTopCompl
  exact ⟨u_fred.fredholmPackage h_dom h_codom⟩

Depends on / 依赖: closedComplemented_ker, closedComplemented_range, exists_isTopCompl, fredholmPackage, h_codom, h_dom, u_fred, u_fred.closedComplemented_ker.exists_isTopCompl, u_fred.closedComplemented_range.exists_isTopCompl, u_fred.fredholmPackage
-/
theorem IsFredholm.nonempty_fredholmPackage {u : E ->L[𝕜] F}
    (u_fred : IsFredholm u) : Nonempty (FredholmPackage u) := by
  obtain ⟨codom₀, h_codom⟩ := u_fred.closedComplemented_range.exists_isTopCompl
  obtain ⟨dom₁, h_dom⟩ := u_fred.closedComplemented_ker.exists_isTopCompl
  exact ⟨u_fred.fredholmPackage h_dom h_codom⟩

variable [T2Space E] [T2Space F]

/--
theorem `isFredholm_tfae` / 定理 `isFredholm_tfae`

English:
theorem isFredholm_tfae
  given: (u : E ->L[𝕜] F)
  proof: by
  tfae_have 1 -> 4 := IsFredholm.nonempty_fredholmPackage
  tfae_have 4 -> 2 := by
    rintro ⟨dec⟩
    exact ⟨dec.quasiInverse, dec.isQuasiInverse⟩
  tfae_have 2 -> 3 := by
    rintro ⟨v, huv⟩
    exact exists_restrict_isInvertible_of_isQuasiInverse huv
  tfae_have 3 -> 1 := by
    rintro ⟨E₁, F

中文:
定理 isFredholm_tfae
  条件: (u : E ->L[𝕜] F)
  证明: by
  tfae_have 1 -> 4 := IsFredholm.nonempty_fredholmPackage
  tfae_have 4 -> 2 := by
    rintro ⟨dec⟩
    exact ⟨dec.quasiInverse, dec.isQuasiInverse⟩
  tfae_have 2 -> 3 := by
    rintro ⟨v, huv⟩
    exact exists_restrict_isInvertible_of_isQuasiInverse huv
  tfae_have 3 -> 1 := by
    rintro ⟨E₁, F

Depends on / 依赖: IsFredholm, IsFredholm.nonempty_fredholmPackage, dec.isQuasiInverse, dec.quasiInverse, exists_restrict_isInvertible_of_isQuasiInverse, isQuasiInverse, nonempty_fredholmPackage, of_isInvertible_restrict, quasiInverse, tfae_finish, tfae_have, u_invertible, u_mapsto
-/
theorem isFredholm_tfae (u : E ->L[𝕜] F) :
    [ IsFredholm u,
      exists v : F ->L[𝕜] E, v.IsQuasiInverse u,
      exists (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
        IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
        E₁.CoFG ∧ F₁.CoFG ∧
        exists h : MapsTo u E₁ F₁, (u.restrict h).IsInvertible,
      Nonempty (FredholmPackage u) ].TFAE := by
  tfae_have 1 -> 4 := IsFredholm.nonempty_fredholmPackage
  tfae_have 4 -> 2 := by
    rintro ⟨dec⟩
    exact ⟨dec.quasiInverse, dec.isQuasiInverse⟩
  tfae_have 2 -> 3 := by
    rintro ⟨v, huv⟩
    exact exists_restrict_isInvertible_of_isQuasiInverse huv
  tfae_have 3 -> 1 := by
    rintro ⟨E₁, F₁, E₁_closed, F₁_closed, E₁_coFG, F₁_coFG, u_mapsto, u_invertible⟩
    exact .of_isInvertible_restrict E₁_closed F₁_closed u_mapsto u_invertible
  tfae_finish

/--
theorem `FredholmPackage.isFredholm` / 定理 `FredholmPackage.isFredholm`

English:
theorem FredholmPackage.isFredholm
  given: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  proof: .mp (Nonempty.intro pkg) .out 3 0 isFredholm_tfae u

中文:
定理 FredholmPackage.isFredholm
  条件: {u : E ->L[𝕜] F} (pkg : FredholmPackage u)
  证明: .mp (Nonempty.intro pkg) .out 3 0 isFredholm_tfae u

Depends on / 依赖: Nonempty, Nonempty.intro, isFredholm_tfae
-/
theorem FredholmPackage.isFredholm {u : E ->L[𝕜] F} (pkg : FredholmPackage u) :
    IsFredholm u :=
.mp (Nonempty.intro pkg) .out 3 0 isFredholm_tfae u

/--
theorem `isFredholm_iff_exists_isQuasiInverse` / 定理 `isFredholm_iff_exists_isQuasiInverse`

English:
theorem isFredholm_iff_exists_isQuasiInverse
  given: {u : E ->L[𝕜] F}
  proof: .out 0 1 isFredholm_tfae u

alias ⟨IsFredholm.exists_isQuasiInverse, _⟩ := isFredholm_iff_exists_isQuasiInverse

中文:
定理 isFredholm_iff_exists_isQuasiInverse
  条件: {u : E ->L[𝕜] F}
  证明: .out 0 1 isFredholm_tfae u

alias ⟨IsFredholm.exists_isQuasiInverse, _⟩ := isFredholm_iff_exists_isQuasiInverse

Depends on / 依赖: isFredholm_tfae
-/
theorem isFredholm_iff_exists_isQuasiInverse {u : E ->L[𝕜] F} :
    IsFredholm u ↔ exists v : F ->L[𝕜] E, v.IsQuasiInverse u :=
.out 0 1 isFredholm_tfae u

alias ⟨IsFredholm.exists_isQuasiInverse, _⟩ := isFredholm_iff_exists_isQuasiInverse

/--
theorem `IsFredholm.of_isQuasiInverse` / 定理 `IsFredholm.of_isQuasiInverse`

English:
theorem IsFredholm.of_isQuasiInverse
  given: {u : E ->L[𝕜] F} {v : F ->L[𝕜] E} (h : v.IsQuasiInverse u)
  proof: isFredholm_iff_exists_isQuasiInverse.mpr ⟨v, h⟩

中文:
定理 IsFredholm.of_isQuasiInverse
  条件: {u : E ->L[𝕜] F} {v : F ->L[𝕜] E} (h : v.IsQuasiInverse u)
  证明: isFredholm_iff_exists_isQuasiInverse.mpr ⟨v, h⟩

Depends on / 依赖: isFredholm_iff_exists_isQuasiInverse, isFredholm_iff_exists_isQuasiInverse.mpr
-/
theorem IsFredholm.of_isQuasiInverse {u : E ->L[𝕜] F} {v : F ->L[𝕜] E} (h : v.IsQuasiInverse u) :
    IsFredholm u :=
  isFredholm_iff_exists_isQuasiInverse.mpr ⟨v, h⟩

end DefTFAE

end TVS
end ContinuousLinearMap

end
