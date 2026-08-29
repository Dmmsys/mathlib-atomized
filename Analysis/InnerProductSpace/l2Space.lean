/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Bases

/-!
# Hilbert sum of a family of inner product spaces

Given a family `(G : ι → Type*) [Π i, InnerProductSpace 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ‖f i‖ ^ 2`, the sum of the norms-squared, is
summable. This construction is sometimes called the *Hilbert sum* of the family `G`. By choosing
`G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this construction.

We also define a *predicate* `IsHilbertSum 𝕜 G V`, where `V : Π i, G i →ₗᵢ[𝕜] E`, expressing that
`V` is an `OrthogonalFamily` and that the associated map `lp G 2 →ₗᵢ[𝕜] E` is surjective.

## Main definitions

* `OrthogonalFamily.linearIsometry`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with
  mutually-orthogonal images, there is an induced isometric embedding of the Hilbert sum of `G`
  into `E`.

* `IsHilbertSum`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E`,
  `IsHilbertSum 𝕜 G V` means that `V` is an `OrthogonalFamily` and that the above
  linear isometry is surjective.

* `IsHilbertSum.linearIsometryEquiv`: If a Hilbert space `E` is a Hilbert sum of the
  inner product spaces `G i` with respect to the family `V : Π i, G i →ₗᵢ[𝕜] E`, then the
  corresponding `OrthogonalFamily.linearIsometry` can be upgraded to a `LinearIsometryEquiv`.

* `HilbertBasis`: We define a *Hilbert basis* of a Hilbert space `E` to be a structure whose single
  field `HilbertBasis.repr` is an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)` (i.e., the Hilbert
  sum of `ι` copies of `𝕜`). This parallels the definition of `Basis`, in `LinearAlgebra.Basis`,
  as an isomorphism of an `R`-module with `ι →₀ R`.

* `HilbertBasis.instCoeFun`: More conventionally a Hilbert basis is thought of as a family
  `ι → E` of vectors in `E` satisfying certain properties (orthonormality, completeness). We obtain
  this interpretation of a Hilbert basis `b` by defining `⇑b`, of type `ι → E`, to be the image
  under `b.repr` of `lp.single 2 i (1:𝕜)`. This parallels the definition `Basis.coeFun` in
  `LinearAlgebra.Basis`.

* `HilbertBasis.mk`: Make a Hilbert basis of `E` from an orthonormal family `v : ι → E` of vectors
  in `E` whose span is dense. This parallels the definition `Basis.mk` in `LinearAlgebra.Basis`.

* `HilbertBasis.mkOfOrthogonalEqBot`: Make a Hilbert basis of `E` from an orthonormal family
  `v : ι → E` of vectors in `E` whose span has trivial orthogonal complement.

* `HilbertBasis.toUnconditionalSchauderBasis`: Convert a Hilbert basis of `E` into an unconditional
  Schauder basis (`UnconditionalSchauderBasis`), with coordinate functionals `x ↦ ⟪b i, x⟫`.

* `HilbertBasis.toSchauderBasis`: Convert a Hilbert basis of `E` indexed by `ℕ` into a classical
  Schauder basis (`SchauderBasis`).

## Main results

* `lp.instInnerProductSpace`: Construction of the inner product space instance on the Hilbert sum
  `lp G 2`. Note that from the file `Mathlib/Analysis/Normed/Lp/lpSpace.lean`, the space `lp G 2`
  already held a normed space instance (`lp.normedSpace`), and if each `G i` is a Hilbert space
  (i.e., complete), then `lp G 2` was already known to be complete (`lp.completeSpace`). So the work
  here is to define the inner product and show it is compatible.

* `OrthogonalFamily.range_linearIsometry`: Given a family `G` of inner product spaces and a family
  `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with mutually-orthogonal
  images, the image of the embedding `OrthogonalFamily.linearIsometry` of the Hilbert sum of `G`
  into `E` is the closure of the span of the images of the `G i`.

* `HilbertBasis.repr_apply_apply`: Given a Hilbert basis `b` of `E`, the entry `b.repr x i` of
  `x`'s representation in `ℓ²(ι, 𝕜)` is the inner product `⟪b i, x⟫`.

* `HilbertBasis.hasSum_repr`: Given a Hilbert basis `b` of `E`, a vector `x` in `E` can be
  expressed as the "infinite linear combination" `∑' i, b.repr x i • b i` of the basis vectors
  `b i`, with coefficients given by the entries `b.repr x i` of `x`'s representation in `ℓ²(ι, 𝕜)`.

* `exists_hilbertBasis`: A Hilbert space admits a Hilbert basis.

## Keywords

Hilbert space, Hilbert sum, l2, Hilbert basis, unitary equivalence, isometric isomorphism
-/

@[expose] public section

open RCLike Submodule Filter
open scoped NNReal ENNReal ComplexConjugate Topology lp

noncomputable section

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {G : ι -> Type*} [forall i, NormedAddCommGroup (G i)] [forall i, InnerProductSpace 𝕜 (G i)]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Inner product space structure on `lp G 2` -/


namespace lp

/--
theorem `summable_inner` / 定理 `summable_inner`

English:
theorem summable_inner
  given: (f g : lp G 2)
  statement: Summable fun i => ⟪f i, g i⟫
  proof: by
  -- Apply the Direct Comparison Test, comparing with ∑' i, ‖f i‖ * ‖g i‖ (summable by Hölder)
  refine .of_norm_bounded (lp.summable_mul ?_ f g) ?_
  · rw [Real.holderConjugate_iff]; norm_num
  intro i
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm (𝕜 := 𝕜) _ _

中文:
定理 summable_inner
  条件: (f g : lp G 2)
  结论: Summable fun i => ⟪f i, g i⟫
  证明: by
  -- Apply the Direct Comparison Test, comparing with ∑' i, ‖f i‖ * ‖g i‖ (summable by Hölder)
  refine .of_norm_bounded (lp.summable_mul ?_ f g) ?_
  · rw [Real.holderConjugate_iff]; norm_num
  intro i
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm (𝕜 := 𝕜) _ _
-/
theorem summable_inner (f g : lp G 2) : Summable fun i => ⟪f i, g i⟫ := by
  -- Apply the Direct Comparison Test, comparing with ∑' i, ‖f i‖ * ‖g i‖ (summable by Hölder)
  refine .of_norm_bounded (lp.summable_mul ?_ f g) ?_
  · rw [Real.holderConjugate_iff]; norm_num
  intro i
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm (𝕜 := 𝕜) _ _

/--
Instance `instInnerProductSpace` / 实例 `instInnerProductSpace`

English:
instance instInnerProductSpace
  signature: : InnerProductSpace 𝕜 (lp G 2)
  body: { lp.normedAddCommGroup (E := G) (p := 2) with
    inner := fun f g => ∑' i, ⟪f i, g i⟫
    norm_sq_eq_re_inner := fun f => by
      calc
        ‖f‖ ^ 2 = ‖f‖ ^ (2 : Real>=0∞).toReal := by norm_cast
        _ = ∑' i, ‖f i‖ ^ (2 : Real>=0∞).toReal := lp.norm_rpow_eq_tsum ?_ f
        _ = ∑' i, ‖f i‖ ^ (2 : Nat) := by norm_cast
        _ = ∑' i, re ⟪f i, f i⟫ := by simp
        _ = re (∑' i, ⟪f i, f i⟫) := (RCLike.reCLM.map_tsum ?_).symm
      · norm_num
      · exact summable_inner f f
    conj_inner_symm := fun f g => by
      calc
        conj _ = conj (∑' i, ⟪g i, f i⟫) := by congr
        _ = ∑' i, conj ⟪g i, f i⟫ := RCLike.conjCLE.map_tsum
        _ = ∑' i, ⟪f i, g i⟫ := by simp only [inner_conj_symm]
        _ = _ := by congr
    add_left := fun f₁ f₂ g => by
      calc
        _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ := ?_
        _ = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) := by
          simp only [inner_add_left, Pi.add_apply, coeFn_add]
        _ = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ := Summable.tsum_add ?_ ?_
        _ = _ := by congr
      · congr
      · exact summable_inner f₁ g
      · exact summable_inner f₂ g
    smul_left := fun f g c => by
      calc
        _ = ∑' i, ⟪c • f i, g i⟫ := ?_
        _ = ∑' i, conj c * ⟪f i, g i⟫ := by simp only [inner_smul_left]
        _ = conj c * ∑' i, ⟪f i, g i⟫ := tsum_mul_left
        _ = _ := ?_
      · simp only [coeFn_smul, Pi.smul_apply]
      · congr }

中文:
实例 instInnerProductSpace
  签名: : 内积空间 𝕜 (lp G 2)
  定义体: { lp.normedAddCommGroup (E := G) (p := 2) with
    inner := fun f g => ∑' i, ⟪f i, g i⟫
    norm_sq_eq_re_inner := fun f => by
      calc
        ‖f‖ ^ 2 = ‖f‖ ^ (2 : Real>=0∞).toReal := by norm_cast
        _ = ∑' i, ‖f i‖ ^ (2 : Real>=0∞).toReal := lp.norm_rpow_eq_tsum ?_ f
        _ = ∑' i, ‖f i‖ ^ (2 : Nat) := by norm_cast
        _ = ∑' i, re ⟪f i, f i⟫ := by simp
        _ = re (∑' i, ⟪f i, f i⟫) := (RCLike.reCLM.map_tsum ?_).symm
      · norm_num
      · exact summable_inner f f
    conj_inner_symm := fun f g => by
      calc
        conj _ = conj (∑' i, ⟪g i, f i⟫) := by congr
        _ = ∑' i, conj ⟪g i, f i⟫ := RCLike.conjCLE.map_tsum
        _ = ∑' i, ⟪f i, g i⟫ := by simp only [inner_conj_symm]
        _ = _ := by congr
    add_left := fun f₁ f₂ g => by
      calc
        _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ := ?_
        _ = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) := by
          simp only [inner_add_left, Pi.add_apply, coeFn_add]
        _ = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ := Summable.tsum_add ?_ ?_
        _ = _ := by congr
      · congr
      · exact summable_inner f₁ g
      · exact summable_inner f₂ g
    smul_left := fun f g c => by
      calc
        _ = ∑' i, ⟪c • f i, g i⟫ := ?_
        _ = ∑' i, conj c * ⟪f i, g i⟫ := by simp only [inner_smul_left]
        _ = conj c * ∑' i, ⟪f i, g i⟫ := tsum_mul_left
        _ = _ := ?_
      · simp only [coeFn_smul, Pi.smul_apply]
      · congr }

Depends on / 依赖: RCLike, RCLike.reCLM.map_tsum, conj_inner_symm, lp.norm_rpow_eq_tsum, lp.normedAddCommGroup, map_tsum, norm_rpow_eq_tsum, norm_sq_eq_re_inner, normedAddCommGroup, summable_inner, toReal
-/
instance instInnerProductSpace : InnerProductSpace 𝕜 (lp G 2) :=
  { lp.normedAddCommGroup (E := G) (p := 2) with
    inner := fun f g => ∑' i, ⟪f i, g i⟫
    norm_sq_eq_re_inner := fun f => by
      calc
        ‖f‖ ^ 2 = ‖f‖ ^ (2 : Real>=0∞).toReal := by norm_cast
        _ = ∑' i, ‖f i‖ ^ (2 : Real>=0∞).toReal := lp.norm_rpow_eq_tsum ?_ f
        _ = ∑' i, ‖f i‖ ^ (2 : Nat) := by norm_cast
        _ = ∑' i, re ⟪f i, f i⟫ := by simp
        _ = re (∑' i, ⟪f i, f i⟫) := (RCLike.reCLM.map_tsum ?_).symm
      · norm_num
      · exact summable_inner f f
    conj_inner_symm := fun f g => by
      calc
        conj _ = conj (∑' i, ⟪g i, f i⟫) := by congr
        _ = ∑' i, conj ⟪g i, f i⟫ := RCLike.conjCLE.map_tsum
        _ = ∑' i, ⟪f i, g i⟫ := by simp only [inner_conj_symm]
        _ = _ := by congr
    add_left := fun f₁ f₂ g => by
      calc
        _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ := ?_
        _ = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) := by
          simp only [inner_add_left, Pi.add_apply, coeFn_add]
        _ = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ := Summable.tsum_add ?_ ?_
        _ = _ := by congr
      · congr
      · exact summable_inner f₁ g
      · exact summable_inner f₂ g
    smul_left := fun f g c => by
      calc
        _ = ∑' i, ⟪c • f i, g i⟫ := ?_
        _ = ∑' i, conj c * ⟪f i, g i⟫ := by simp only [inner_smul_left]
        _ = conj c * ∑' i, ⟪f i, g i⟫ := tsum_mul_left
        _ = _ := ?_
      · simp only [coeFn_smul, Pi.smul_apply]
      · congr }

/--
theorem `inner_eq_tsum` / 定理 `inner_eq_tsum`

English:
theorem inner_eq_tsum
  given: (f g : lp G 2)
  statement: ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫
  proof: rfl

中文:
定理 inner_eq_tsum
  条件: (f g : lp G 2)
  结论: ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫
  证明: rfl
-/
theorem inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ :=
  rfl

/--
theorem `hasSum_inner` / 定理 `hasSum_inner`

English:
theorem hasSum_inner
  given: (f g : lp G 2)
  statement: HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫
  proof: (summable_inner f g).hasSum

中文:
定理 hasSum_inner
  条件: (f g : lp G 2)
  结论: HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫
  证明: (summable_inner f g).hasSum

Depends on / 依赖: hasSum, summable_inner
-/
theorem hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫ :=
  (summable_inner f g).hasSum

/--
theorem `inner_single_left` / 定理 `inner_single_left`

English:
theorem inner_single_left
  given: [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2)
  proof: by
  refine (hasSum_inner (lp.single 2 i a) f).unique ?_
  simp_rw [lp.coeFn_single]
  convert! hasSum_ite_eq i ⟪a, f i⟫ using 1
  ext j
  split_ifs with h
  · subst h; rw [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

中文:
定理 inner_single_left
  条件: [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2)
  证明: by
  refine (hasSum_inner (lp.single 2 i a) f).unique ?_
  simp_rw [lp.coeFn_single]
  convert! hasSum_ite_eq i ⟪a, f i⟫ using 1
  ext j
  split_ifs with h
  · subst h; rw [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

Depends on / 依赖: Pi.single_eq_of_ne, Pi.single_eq_same, coeFn_single, convert, hasSum_inner, hasSum_ite_eq, lp.coeFn_single, lp.single, simp_rw, single, single_eq_of_ne, single_eq_same, split_ifs, unique
-/
theorem inner_single_left [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫ := by
  refine (hasSum_inner (lp.single 2 i a) f).unique ?_
  simp_rw [lp.coeFn_single]
  convert! hasSum_ite_eq i ⟪a, f i⟫ using 1
  ext j
  split_ifs with h
  · subst h; rw [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

/--
theorem `inner_single_right` / 定理 `inner_single_right`

English:
theorem inner_single_right
  given: [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2)
  proof: by
  simpa [inner_conj_symm] using congr_arg conj (inner_single_left (𝕜 := 𝕜) i a f)

中文:
定理 inner_single_right
  条件: [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2)
  证明: by
  simpa [inner_conj_symm] using congr_arg conj (inner_single_left (𝕜 := 𝕜) i a f)

Depends on / 依赖: congr_arg, inner_conj_symm, inner_single_left
-/
theorem inner_single_right [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪f, lp.single 2 i a⟫ = ⟪f i, a⟫ := by
  simpa [inner_conj_symm] using congr_arg conj (inner_single_left (𝕜 := 𝕜) i a f)

end lp

/-! ### Identification of a general Hilbert space `E` with a Hilbert sum -/


namespace OrthogonalFamily

variable [CompleteSpace E] {V : forall i, G i ->ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 G V)
include hV

/--
theorem `summable_of_lp` / 定理 `summable_of_lp`

English:
theorem summable_of_lp
  given: (f : lp G 2)
  proof: by
  rw [hV.summable_iff_norm_sq_summable]
  convert! (lp.memℓp f).summable _
  · norm_cast
  · norm_num

中文:
定理 summable_of_lp
  条件: (f : lp G 2)
  证明: by
  rw [hV.summable_iff_norm_sq_summable]
  convert! (lp.memℓp f).summable _
  · norm_cast
  · norm_num
-/
protected theorem summable_of_lp (f : lp G 2) :
    Summable fun i => V i (f i) := by
  rw [hV.summable_iff_norm_sq_summable]
  convert! (lp.memℓp f).summable _
  · norm_cast
  · norm_num

/--
Definition of `linearIsometry` / `linearIsometry` 的定义

English:
definition linearIsometry
  signature: (hV : OrthogonalFamily 𝕜 G V)
  body: ∑' i, V i (f i)
  map_add' f g := by
    simp only [(hV.summable_of_lp f).tsum_add (hV.summable_of_lp g), lp.coeFn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coeFn_smul] using!
      (hV.summable_of_lp f).tsum_const_smul c
  norm_map' f := by
    -- needed for lattice instance on `Finset ι`, for `Filter.atTop_neBot`
    have H : 0 < (2 : Real>=0∞).toReal := by simp
    suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : Real>=0∞).toReal = ‖f‖ ^ (2 : Real>=0∞).toReal by
      exact Real.rpow_left_injOn H.ne' (norm_nonneg _) (norm_nonneg _) this
    refine tendsto_nhds_unique ?_ (lp.hasSum_norm H f)
    convert! (hV.summable_of_lp f).hasSum.norm.rpow_const (Or.inr H.le) using 1
    ext s
    exact mod_cast (hV.norm_sum f s).symm

中文:
定义 linearIsometry
  签名: (hV : OrthogonalFamily 𝕜 G V)
  定义体: ∑' i, V i (f i)
  map_add' f g := by
    simp only [(hV.summable_of_lp f).tsum_add (hV.summable_of_lp g), lp.coeFn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coeFn_smul] using!
      (hV.summable_of_lp f).tsum_const_smul c
  norm_map' f := by
    -- needed for lattice instance on `Finset ι`, for `Filter.atTop_neBot`
    have H : 0 < (2 : Real>=0∞).toReal := by simp
    suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : Real>=0∞).toReal = ‖f‖ ^ (2 : Real>=0∞).toReal by
      exact Real.rpow_left_injOn H.ne' (norm_nonneg _) (norm_nonneg _) this
    refine tendsto_nhds_unique ?_ (lp.hasSum_norm H f)
    convert! (hV.summable_of_lp f).hasSum.norm.rpow_const (Or.inr H.le) using 1
    ext s
    exact mod_cast (hV.norm_sum f s).symm
-/
protected def linearIsometry (hV : OrthogonalFamily 𝕜 G V) : lp G 2 ->ₗᵢ[𝕜] E where
  toFun f := ∑' i, V i (f i)
  map_add' f g := by
    simp only [(hV.summable_of_lp f).tsum_add (hV.summable_of_lp g), lp.coeFn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coeFn_smul] using!
      (hV.summable_of_lp f).tsum_const_smul c
  norm_map' f := by
    -- needed for lattice instance on `Finset ι`, for `Filter.atTop_neBot`
    have H : 0 < (2 : Real>=0∞).toReal := by simp
    suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : Real>=0∞).toReal = ‖f‖ ^ (2 : Real>=0∞).toReal by
      exact Real.rpow_left_injOn H.ne' (norm_nonneg _) (norm_nonneg _) this
    refine tendsto_nhds_unique ?_ (lp.hasSum_norm H f)
    convert! (hV.summable_of_lp f).hasSum.norm.rpow_const (Or.inr H.le) using 1
    ext s
    exact mod_cast (hV.norm_sum f s).symm

/--
theorem `linearIsometry_apply` / 定理 `linearIsometry_apply`

English:
theorem linearIsometry_apply
  given: (f : lp G 2)
  statement: hV.linearIsometry f = ∑' i, V i (f i)
  proof: rfl

中文:
定理 linearIsometry_apply
  条件: (f : lp G 2)
  结论: hV.linearIsometry f = ∑' i, V i (f i)
  证明: rfl
-/
protected theorem linearIsometry_apply (f : lp G 2) : hV.linearIsometry f = ∑' i, V i (f i) :=
  rfl

/--
theorem `hasSum_linearIsometry` / 定理 `hasSum_linearIsometry`

English:
theorem hasSum_linearIsometry
  given: (f : lp G 2)
  proof: (hV.summable_of_lp f).hasSum

@[simp]

中文:
定理 hasSum_linearIsometry
  条件: (f : lp G 2)
  证明: (hV.summable_of_lp f).hasSum

@[simp]
-/
protected theorem hasSum_linearIsometry (f : lp G 2) :
    HasSum (fun i => V i (f i)) (hV.linearIsometry f) :=
  (hV.summable_of_lp f).hasSum

@[simp]
/--
theorem `linearIsometry_apply_single` / 定理 `linearIsometry_apply_single`

English:
theorem linearIsometry_apply_single
  given: [DecidableEq ι] {i : ι} (x : G i)
  proof: by
  rw [hV.linearIsometry_apply]; rw [← tsum_ite_eq i (fun _ => V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [h]

中文:
定理 linearIsometry_apply_single
  条件: [DecidableEq ι] {i : ι} (x : G i)
  证明: by
  rw [hV.linearIsometry_apply]; rw [← tsum_ite_eq i (fun _ => V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [h]
-/
protected theorem linearIsometry_apply_single [DecidableEq ι] {i : ι} (x : G i) :
    hV.linearIsometry (lp.single 2 i x) = V i x := by
  rw [hV.linearIsometry_apply]; rw [← tsum_ite_eq i (fun _ => V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [h]

/--
theorem `linearIsometry_apply_dfinsupp_sum_single` / 定理 `linearIsometry_apply_dfinsupp_sum_single`

English:
theorem linearIsometry_apply_dfinsupp_sum_single
  statement: [DecidableEq ι] [forall i, DecidableEq (G i)]
  proof: by
  simp

中文:
定理 linearIsometry_apply_dfinsupp_sum_single
  结论: [DecidableEq ι] [对任意 i, DecidableEq (G i)]
  证明: by
  simp
-/
protected theorem linearIsometry_apply_dfinsupp_sum_single [DecidableEq ι] [forall i, DecidableEq (G i)]
    (W₀ : Π₀ i : ι, G i) : hV.linearIsometry (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp

/--
theorem `range_linearIsometry` / 定理 `range_linearIsometry`

English:
theorem range_linearIsometry
  given: [forall i, CompleteSpace (G i)]
  proof: by
  classical
  refine le_antisymm ?_ ?_
  · rintro x ⟨f, rfl⟩
    refine mem_closure_of_tendsto (hV.hasSum_linearIsometry f) (Eventually.of_forall ?_)
    intro s
    rw [SetLike.mem_coe]
    refine sum_mem ?_
    intro i _
    refine mem_iSup_of_mem i ?_
    exact LinearMap.mem_range_self _ (f i)
  · apply topologicalClosure_minimal
    · refine iSup_le ?_
      rintro i x ⟨x, rfl⟩
      use lp.single 2 i x
      exact hV.linearIsometry_apply_single x
    exact hV.linearIsometry.isometry.isUniformInducing.isComplete_range.isClosed

中文:
定理 range_linearIsometry
  条件: [对任意 i, 完备空间 (G i)]
  证明: by
  classical
  refine le_antisymm ?_ ?_
  · rintro x ⟨f, rfl⟩
    refine mem_closure_of_tendsto (hV.hasSum_linearIsometry f) (Eventually.of_forall ?_)
    intro s
    rw [SetLike.mem_coe]
    refine sum_mem ?_
    intro i _
    refine mem_iSup_of_mem i ?_
    exact LinearMap.mem_range_self _ (f i)
  · apply topologicalClosure_minimal
    · refine iSup_le ?_
      rintro i x ⟨x, rfl⟩
      use lp.single 2 i x
      exact hV.linearIsometry_apply_single x
    exact hV.linearIsometry.isometry.isUniformInducing.isComplete_range.isClosed
-/
protected theorem range_linearIsometry [forall i, CompleteSpace (G i)] :
    LinearMap.range hV.linearIsometry.toLinearMap =
      (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure := by
  classical
  refine le_antisymm ?_ ?_
  · rintro x ⟨f, rfl⟩
    refine mem_closure_of_tendsto (hV.hasSum_linearIsometry f) (Eventually.of_forall ?_)
    intro s
    rw [SetLike.mem_coe]
    refine sum_mem ?_
    intro i _
    refine mem_iSup_of_mem i ?_
    exact LinearMap.mem_range_self _ (f i)
  · apply topologicalClosure_minimal
    · refine iSup_le ?_
      rintro i x ⟨x, rfl⟩
      use lp.single 2 i x
      exact hV.linearIsometry_apply_single x
    exact hV.linearIsometry.isometry.isUniformInducing.isComplete_range.isClosed

end OrthogonalFamily

section IsHilbertSum

variable (𝕜 G)
variable [CompleteSpace E] (V : forall i, G i ->ₗᵢ[𝕜] E) (F : ι -> Submodule 𝕜 E)

/--
Definition of `IsHilbertSum` / `IsHilbertSum` 的定义

English:
structure IsHilbertSum
  parameters: : Prop where
  axioms and operations (3):
    - ofSurjective : :
    - OrthogonalFamily : OrthogonalFamily 𝕜 G V
    - surjective_isometry : Function.Surjective OrthogonalFamily.linearIsometry

中文:
结构 是HilbertSum
  参数: : 命题 where
  公理与运算 (3 个):
    - ofSurjective : :
    - OrthogonalFamily : OrthogonalFamily 𝕜 G V
    - surjective_isometry : 函数.满射 OrthogonalFamily.linearIsometry
-/
structure IsHilbertSum : Prop where
  ofSurjective ::
  /-- The orthogonal family constituting the summands in the Hilbert sum. -/
  protected OrthogonalFamily : OrthogonalFamily 𝕜 G V
  /-- The isometry `lp G 2 → E` induced by the orthogonal family is surjective. -/
  protected surjective_isometry : Function.Surjective OrthogonalFamily.linearIsometry

variable {𝕜 G V}

/--
theorem `IsHilbertSum.mk` / 定理 `IsHilbertSum.mk`

English:
theorem IsHilbertSum.mk
  statement: [forall i, CompleteSpace <| G i] (hVortho : OrthogonalFamily 𝕜 G V)
  proof: { OrthogonalFamily := hVortho
    surjective_isometry := by
      rw [← LinearIsometry.coe_toLinearMap]
      exact LinearMap.range_eq_top.mp
        (eq_top_iff.mpr <| hVtotal.trans_eq hVortho.range_linearIsometry.symm) }

中文:
定理 是HilbertSum.mk
  结论: [对任意 i, 完备空间 <| G i] (hVortho : OrthogonalFamily 𝕜 G V)
  证明: { OrthogonalFamily := hVortho
    surjective_isometry := by
      rw [← LinearIsometry.coe_toLinearMap]
      exact LinearMap.range_eq_top.mp
        (eq_top_iff.mpr <| hVtotal.trans_eq hVortho.range_linearIsometry.symm) }

Depends on / 依赖: LinearIsometry, LinearIsometry.coe_toLinearMap, LinearMap, LinearMap.range_eq_top.mp, OrthogonalFamily, coe_toLinearMap, eq_top_iff, eq_top_iff.mpr, hVortho, hVortho.range_linearIsometry.symm, hVtotal, hVtotal.trans_eq, range_eq_top, range_linearIsometry, surjective_isometry, trans_eq
-/
theorem IsHilbertSum.mk [forall i, CompleteSpace <| G i] (hVortho : OrthogonalFamily 𝕜 G V)
    (hVtotal : ⊤ <= (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure) :
    IsHilbertSum 𝕜 G V :=
  { OrthogonalFamily := hVortho
    surjective_isometry := by
      rw [← LinearIsometry.coe_toLinearMap]
      exact LinearMap.range_eq_top.mp
        (eq_top_iff.mpr <| hVtotal.trans_eq hVortho.range_linearIsometry.symm) }

/--
theorem `IsHilbertSum.mkInternal` / 定理 `IsHilbertSum.mkInternal`

English:
theorem IsHilbertSum.mkInternal
  statement: [forall i, CompleteSpace <| F i]
  proof: IsHilbertSum.mk hFortho (by simpa [subtypeₗᵢ_toLinearMap, range_subtype] using hFtotal)

中文:
定理 是HilbertSum.mk整数ernal
  结论: [对任意 i, 完备空间 <| F i]
  证明: IsHilbertSum.mk hFortho (by simpa [subtypeₗᵢ_toLinearMap, range_subtype] using hFtotal)

Depends on / 依赖: IsHilbertSum, IsHilbertSum.mk, hFortho, hFtotal, range_subtype
-/
theorem IsHilbertSum.mkInternal [forall i, CompleteSpace <| F i]
    (hFortho : OrthogonalFamily 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ)
    (hFtotal : ⊤ <= (⨆ i, F i).topologicalClosure) :
    IsHilbertSum 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ :=
  IsHilbertSum.mk hFortho (by simpa [subtypeₗᵢ_toLinearMap, range_subtype] using hFtotal)

/--
Definition of `IsHilbertSum.linearIsometryEquiv` / `IsHilbertSum.linearIsometryEquiv` 的定义

English:
definition IsHilbertSum.linearIsometryEquiv
  signature: (hV : IsHilbertSum 𝕜 G V)
  body: LinearIsometryEquiv.symm
    LinearIsometryEquiv.ofSurjective hV.OrthogonalFamily.linearIsometry hV.surjective_isometry

中文:
定义 是HilbertSum.linearIsometryEquiv
  签名: (hV : 是HilbertSum 𝕜 G V)
  定义体: LinearIsometryEquiv.symm
    LinearIsometryEquiv.ofSurjective hV.OrthogonalFamily.linearIsometry hV.surjective_isometry

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ofSurjective, LinearIsometryEquiv.symm, OrthogonalFamily, hV.OrthogonalFamily.linearIsometry, hV.surjective_isometry, linearIsometry, ofSurjective, surjective_isometry
-/
noncomputable def IsHilbertSum.linearIsometryEquiv (hV : IsHilbertSum 𝕜 G V) : E ≃ₗᵢ[𝕜] lp G 2 :=
LinearIsometryEquiv.symm
    LinearIsometryEquiv.ofSurjective hV.OrthogonalFamily.linearIsometry hV.surjective_isometry

/--
theorem `IsHilbertSum.linearIsometryEquiv_symm_apply` / 定理 `IsHilbertSum.linearIsometryEquiv_symm_apply`

English:
theorem IsHilbertSum.linearIsometryEquiv_symm_apply
  statement: (hV : IsHilbertSum 𝕜 G V)
  proof: by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply]

中文:
定理 是HilbertSum.linearIsometryEquiv_symm_apply
  结论: (hV : 是HilbertSum 𝕜 G V)
  证明: by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply]
-/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : hV.linearIsometryEquiv.symm w = ∑' i, V i (w i) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply]

/--
theorem `IsHilbertSum.hasSum_linearIsometryEquiv_symm` / 定理 `IsHilbertSum.hasSum_linearIsometryEquiv_symm`

English:
theorem IsHilbertSum.hasSum_linearIsometryEquiv_symm
  statement: (hV : IsHilbertSum 𝕜 G V)
  proof: by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.hasSum_linearIsometry]

中文:
定理 是HilbertSum.hasSum_linearIsometryEquiv_symm
  结论: (hV : 是HilbertSum 𝕜 G V)
  证明: by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.hasSum_linearIsometry]
-/
protected theorem IsHilbertSum.hasSum_linearIsometryEquiv_symm (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : HasSum (fun i => V i (w i)) (hV.linearIsometryEquiv.symm w) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.hasSum_linearIsometry]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, an "elementary basis vector" in `lp G 2` supported at `i : ι` is the image of the
associated element in `E`. -/
@[simp]
/--
theorem `IsHilbertSum.linearIsometryEquiv_symm_apply_single` / 定理 `IsHilbertSum.linearIsometryEquiv_symm_apply_single`

English:
theorem IsHilbertSum.linearIsometryEquiv_symm_apply_single
  proof: by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply_single]

中文:
定理 是HilbertSum.linearIsometryEquiv_symm_apply_single
  证明: by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply_single]
-/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_single
    [DecidableEq ι] (hV : IsHilbertSum 𝕜 G V) {i : ι} (x : G i) :
    hV.linearIsometryEquiv.symm (lp.single 2 i x) = V i x := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply_single]

/--
theorem `IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single` / 定理 `IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single`

English:
theorem IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single
  proof: by
  simp only [map_dfinsuppSum, IsHilbertSum.linearIsometryEquiv_symm_apply_single]

中文:
定理 是HilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single
  证明: by
  simp only [map_dfinsuppSum, IsHilbertSum.linearIsometryEquiv_symm_apply_single]
-/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single
    [DecidableEq ι] [forall i, DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    hV.linearIsometryEquiv.symm (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp only [map_dfinsuppSum, IsHilbertSum.linearIsometryEquiv_symm_apply_single]

set_option backward.isDefEq.respectTransparency false in
/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp]
/--
theorem `IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single` / 定理 `IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single`

English:
theorem IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single
  proof: by
  rw [← map_dfinsuppSum]
  rw [← hV.linearIsometryEquiv_symm_apply_dfinsupp_sum_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp +contextual [DFinsupp.sum, lp.single_apply]

中文:
定理 是HilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single
  证明: by
  rw [← map_dfinsuppSum]
  rw [← hV.linearIsometryEquiv_symm_apply_dfinsupp_sum_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp +contextual [DFinsupp.sum, lp.single_apply]
-/
protected theorem IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single
    [DecidableEq ι] [forall i, DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    ((W₀.sum (γ := lp G 2) fun a b => hV.linearIsometryEquiv (V a b)) : forall i, G i) = W₀ := by
  rw [← map_dfinsuppSum]
  rw [← hV.linearIsometryEquiv_symm_apply_dfinsupp_sum_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp +contextual [DFinsupp.sum, lp.single_apply]

/--
theorem `Orthonormal.isHilbertSum` / 定理 `Orthonormal.isHilbertSum`

English:
theorem Orthonormal.isHilbertSum
  statement: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  proof: IsHilbertSum.mk hv.orthogonalFamily (by
    convert! hsp
    simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion])

中文:
定理 Orthonormal.isHilbertSum
  结论: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  证明: IsHilbertSum.mk hv.orthogonalFamily (by
    convert! hsp
    simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion])

Depends on / 依赖: IsHilbertSum, IsHilbertSum.mk, LinearMap, LinearMap.span_singleton_eq_range, Submodule, Submodule.span_iUnion, convert, hv.orthogonalFamily, orthogonalFamily, span_iUnion, span_singleton_eq_range
-/
theorem Orthonormal.isHilbertSum {v : ι -> E} (hv : Orthonormal 𝕜 v)
    (hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure) :
    IsHilbertSum 𝕜 (fun _ : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  IsHilbertSum.mk hv.orthogonalFamily (by
    convert! hsp
    simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion])

/--
theorem `Submodule.isHilbertSumOrthogonal` / 定理 `Submodule.isHilbertSumOrthogonal`

English:
theorem Submodule.isHilbertSumOrthogonal
  given: (K : Submodule 𝕜 E) [hK : CompleteSpace K]
  proof: by
  have : forall b, CompleteSpace (↥(cond b K Kᗮ)) := by
    intro b
    cases b <;> first | exact instOrthogonalCompleteSpace K | assumption
  refine IsHilbertSum.mkInternal _ K.orthogonalFamily_self ?_
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  rw [iSup_bool_eq]; rw [cond]; rw [cond]
  refine Codisjoint.top_le ?_
  exact K.isCompl_orthogonal.codisjoint

中文:
定理 子模.isHilbertSumOrthogonal
  条件: (K : 子模 𝕜 E) [hK : 完备空间 K]
  证明: by
  have : forall b, CompleteSpace (↥(cond b K Kᗮ)) := by
    intro b
    cases b <;> first | exact instOrthogonalCompleteSpace K | assumption
  refine IsHilbertSum.mkInternal _ K.orthogonalFamily_self ?_
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  rw [iSup_bool_eq]; rw [cond]; rw [cond]
  refine Codisjoint.top_le ?_
  exact K.isCompl_orthogonal.codisjoint

Depends on / 依赖: Codisjoint, Codisjoint.top_le, CompleteSpace, IsHilbertSum, IsHilbertSum.mkInternal, K.isCompl_orthogonal.codisjoint, K.orthogonalFamily_self, Submodule, Submodule.le_topologicalClosure, codisjoint, iSup_bool_eq, instOrthogonalCompleteSpace, isCompl_orthogonal, le_topologicalClosure, le_trans, mkInternal, orthogonalFamily_self, top_le
-/
theorem Submodule.isHilbertSumOrthogonal (K : Submodule 𝕜 E) [hK : CompleteSpace K] :
    IsHilbertSum 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ := by
  have : forall b, CompleteSpace (↥(cond b K Kᗮ)) := by
    intro b
    cases b <;> first | exact instOrthogonalCompleteSpace K | assumption
  refine IsHilbertSum.mkInternal _ K.orthogonalFamily_self ?_
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  rw [iSup_bool_eq]; rw [cond]; rw [cond]
  refine Codisjoint.top_le ?_
  exact K.isCompl_orthogonal.codisjoint

end IsHilbertSum

/-! ### Hilbert bases -/


section

variable (ι) (𝕜) (E)

/--
Definition of `HilbertBasis` / `HilbertBasis` 的定义

English:
structure HilbertBasis
  parameters: where ofRepr
  (no additional axioms)

中文:
结构 Hilbert基
  参数: where ofRepr
  (无附加公理)
-/
structure HilbertBasis where ofRepr ::
  /-- The linear isometric equivalence implementing identifying the Hilbert space with `ℓ²`. -/
  repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)

end

namespace HilbertBasis

instance {ι : Type*} : Inhabited (HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) :=
  ⟨ofRepr (LinearIsometryEquiv.refl 𝕜 _)⟩

open scoped Classical in
/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (HilbertBasis ι 𝕜 E) ι E where
  body: b.repr.symm (lp.single 2 i (1 : 𝕜))
  coe_injective
  | ⟨b₁⟩, ⟨b₂⟩, h => by
    congr
    apply LinearIsometryEquiv.symm_bijective.injective
    apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
    apply ContinuousLinearEquiv.coe_injective
    refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun i => ?_
    ext
    exact congr_fun h i

@[simp]

中文:
实例 instFunLike
  签名: : 函数状 (Hilbert基 ι 𝕜 E) ι E where
  定义体: b.repr.symm (lp.single 2 i (1 : 𝕜))
  coe_injective
  | ⟨b₁⟩, ⟨b₂⟩, h => by
    congr
    apply LinearIsometryEquiv.symm_bijective.injective
    apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
    apply ContinuousLinearEquiv.coe_injective
    refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun i => ?_
    ext
    exact congr_fun h i

@[simp]

Depends on / 依赖: b.repr.symm, lp.single, single
-/
instance instFunLike : FunLike (HilbertBasis ι 𝕜 E) ι E where
  coe b i := b.repr.symm (lp.single 2 i (1 : 𝕜))
  coe_injective
  | ⟨b₁⟩, ⟨b₂⟩, h => by
    congr
    apply LinearIsometryEquiv.symm_bijective.injective
    apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
    apply ContinuousLinearEquiv.coe_injective
    refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun i => ?_
    ext
    exact congr_fun h i

@[simp]
/--
theorem `repr_symm_single` / 定理 `repr_symm_single`

English:
theorem repr_symm_single
  given: [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι)
  proof: by
  dsimp +instances [instFunLike]
  convert! rfl

中文:
定理 repr_symm_single
  条件: [DecidableEq ι] (b : Hilbert基 ι 𝕜 E) (i : ι)
  证明: by
  dsimp +instances [instFunLike]
  convert! rfl
-/
protected theorem repr_symm_single [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (lp.single 2 i (1 : 𝕜)) = b i := by
  dsimp +instances [instFunLike]
  convert! rfl


/--
theorem `repr_self` / 定理 `repr_self`

English:
theorem repr_self
  given: [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι)
  proof: by
  simp only [LinearIsometryEquiv.apply_symm_apply, ← b.repr_symm_single]

中文:
定理 repr_self
  条件: [DecidableEq ι] (b : Hilbert基 ι 𝕜 E) (i : ι)
  证明: by
  simp only [LinearIsometryEquiv.apply_symm_apply, ← b.repr_symm_single]
-/
protected theorem repr_self [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = lp.single 2 i (1 : 𝕜) := by
  simp only [LinearIsometryEquiv.apply_symm_apply, ← b.repr_symm_single]

/--
theorem `repr_apply_apply` / 定理 `repr_apply_apply`

English:
theorem repr_apply_apply
  given: (b : HilbertBasis ι 𝕜 E) (v : E) (i : ι)
  proof: by
  classical
  rw [← b.repr.inner_map_map (b i) v]; rw [b.repr_self]; rw [lp.inner_single_left]
  simp

@[simp]

中文:
定理 repr_apply_apply
  条件: (b : Hilbert基 ι 𝕜 E) (v : E) (i : ι)
  证明: by
  classical
  rw [← b.repr.inner_map_map (b i) v]; rw [b.repr_self]; rw [lp.inner_single_left]
  simp

@[simp]
-/
protected theorem repr_apply_apply (b : HilbertBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  classical
  rw [← b.repr.inner_map_map (b i) v]; rw [b.repr_self]; rw [lp.inner_single_left]
  simp

@[simp]
/--
theorem `orthonormal` / 定理 `orthonormal`

English:
theorem orthonormal
  given: (b : HilbertBasis ι 𝕜 E)
  statement: Orthonormal 𝕜 b
  proof: by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j)]; rw [b.repr_self]; rw [b.repr_self]; rw [lp.inner_single_left]; rw [lp.single_apply]; rw [Pi.single_apply]
  simp

中文:
定理 orthonormal
  条件: (b : Hilbert基 ι 𝕜 E)
  结论: Orthonormal 𝕜 b
  证明: by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j)]; rw [b.repr_self]; rw [b.repr_self]; rw [lp.inner_single_left]; rw [lp.single_apply]; rw [Pi.single_apply]
  simp
-/
protected theorem orthonormal (b : HilbertBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j)]; rw [b.repr_self]; rw [b.repr_self]; rw [lp.inner_single_left]; rw [lp.single_apply]; rw [Pi.single_apply]
  simp

/--
theorem `hasSum_repr_symm` / 定理 `hasSum_repr_symm`

English:
theorem hasSum_repr_symm
  given: (b : HilbertBasis ι 𝕜 E) (f : ℓ²(ι, 𝕜))
  proof: by
  classical
suffices H : (fun i : ι => f i • b i) = fun b_1 : ι => b.repr.symm.toContinuousLinearEquiv
      (fun i : ι => lp.single 2 i (f i) (E := (fun _ : ι => 𝕜))) b_1 by
    rw [H]
    have : HasSum (fun i : ι => lp.single 2 i (f i)) f := lp.hasSum_single ENNReal.ofNat_ne_top f
    exact (↑b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, 𝕜) ->L[𝕜] E).hasSum this
  ext i
  apply b.repr.injective
  let : NormedSpace 𝕜 (lp (fun _i : ι => 𝕜) 2) := by infer_instance
  have : lp.single (E := (fun _ : ι => 𝕜)) 2 i (f i * 1) = f i • lp.single 2 i 1 :=
    lp.single_smul (E := (fun _ : ι => 𝕜)) 2 i (f i) (1 : 𝕜)
  rw [mul_one] at this
  rw [map_smul]; rw [b.repr_self]; rw [← this]; rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm

中文:
定理 hasSum_repr_symm
  条件: (b : Hilbert基 ι 𝕜 E) (f : ℓ²(ι, 𝕜))
  证明: by
  classical
suffices H : (fun i : ι => f i • b i) = fun b_1 : ι => b.repr.symm.toContinuousLinearEquiv
      (fun i : ι => lp.single 2 i (f i) (E := (fun _ : ι => 𝕜))) b_1 by
    rw [H]
    have : HasSum (fun i : ι => lp.single 2 i (f i)) f := lp.hasSum_single ENNReal.ofNat_ne_top f
    exact (↑b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, 𝕜) ->L[𝕜] E).hasSum this
  ext i
  apply b.repr.injective
  let : NormedSpace 𝕜 (lp (fun _i : ι => 𝕜) 2) := by infer_instance
  have : lp.single (E := (fun _ : ι => 𝕜)) 2 i (f i * 1) = f i • lp.single 2 i 1 :=
    lp.single_smul (E := (fun _ : ι => 𝕜)) 2 i (f i) (1 : 𝕜)
  rw [mul_one] at this
  rw [map_smul]; rw [b.repr_self]; rw [← this]; rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm
-/
protected theorem hasSum_repr_symm (b : HilbertBasis ι 𝕜 E) (f : ℓ²(ι, 𝕜)) :
    HasSum (fun i => f i • b i) (b.repr.symm f) := by
  classical
suffices H : (fun i : ι => f i • b i) = fun b_1 : ι => b.repr.symm.toContinuousLinearEquiv
      (fun i : ι => lp.single 2 i (f i) (E := (fun _ : ι => 𝕜))) b_1 by
    rw [H]
    have : HasSum (fun i : ι => lp.single 2 i (f i)) f := lp.hasSum_single ENNReal.ofNat_ne_top f
    exact (↑b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, 𝕜) ->L[𝕜] E).hasSum this
  ext i
  apply b.repr.injective
  let : NormedSpace 𝕜 (lp (fun _i : ι => 𝕜) 2) := by infer_instance
  have : lp.single (E := (fun _ : ι => 𝕜)) 2 i (f i * 1) = f i • lp.single 2 i 1 :=
    lp.single_smul (E := (fun _ : ι => 𝕜)) 2 i (f i) (1 : 𝕜)
  rw [mul_one] at this
  rw [map_smul]; rw [b.repr_self]; rw [← this]; rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm

/--
theorem `hasSum_repr` / 定理 `hasSum_repr`

English:
theorem hasSum_repr
  given: (b : HilbertBasis ι 𝕜 E) (x : E)
  proof: by simpa using b.hasSum_repr_symm (b.repr x)

@[simp]

中文:
定理 hasSum_repr
  条件: (b : Hilbert基 ι 𝕜 E) (x : E)
  证明: by simpa using b.hasSum_repr_symm (b.repr x)

@[simp]
-/
protected theorem hasSum_repr (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => b.repr x i • b i) x := by simpa using b.hasSum_repr_symm (b.repr x)

@[simp]
/--
theorem `dense_span` / 定理 `dense_span`

English:
theorem dense_span
  given: (b : HilbertBasis ι 𝕜 E)
  proof: by
  rw [eq_top_iff]
  rintro x -
  refine mem_closure_of_tendsto (b.hasSum_repr x) (Eventually.of_forall ?_)
  intro s
  simp only [SetLike.mem_coe]
  refine sum_mem ?_
  rintro i -
  refine smul_mem _ _ ?_
  exact subset_span ⟨i, rfl⟩

中文:
定理 dense_span
  条件: (b : Hilbert基 ι 𝕜 E)
  证明: by
  rw [eq_top_iff]
  rintro x -
  refine mem_closure_of_tendsto (b.hasSum_repr x) (Eventually.of_forall ?_)
  intro s
  simp only [SetLike.mem_coe]
  refine sum_mem ?_
  rintro i -
  refine smul_mem _ _ ?_
  exact subset_span ⟨i, rfl⟩
-/
protected theorem dense_span (b : HilbertBasis ι 𝕜 E) :
    (span 𝕜 (Set.range b)).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  refine mem_closure_of_tendsto (b.hasSum_repr x) (Eventually.of_forall ?_)
  intro s
  simp only [SetLike.mem_coe]
  refine sum_mem ?_
  rintro i -
  refine smul_mem _ _ ?_
  exact subset_span ⟨i, rfl⟩

/--
theorem `hasSum_inner_mul_inner` / 定理 `hasSum_inner_mul_inner`

English:
theorem hasSum_inner_mul_inner
  given: (b : HilbertBasis ι 𝕜 E) (x y : E)
  proof: by
  convert! (b.hasSum_repr y).mapL (innerSL 𝕜 x) using 1
  ext i
  rw [innerSL_apply_apply]; rw [b.repr_apply_apply]; rw [inner_smul_right]; rw [mul_comm]

中文:
定理 hasSum_inner_mul_inner
  条件: (b : Hilbert基 ι 𝕜 E) (x y : E)
  证明: by
  convert! (b.hasSum_repr y).mapL (innerSL 𝕜 x) using 1
  ext i
  rw [innerSL_apply_apply]; rw [b.repr_apply_apply]; rw [inner_smul_right]; rw [mul_comm]
-/
protected theorem hasSum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    HasSum (fun i => ⟪x, b i⟫ * ⟪b i, y⟫) ⟪x, y⟫ := by
  convert! (b.hasSum_repr y).mapL (innerSL 𝕜 x) using 1
  ext i
  rw [innerSL_apply_apply]; rw [b.repr_apply_apply]; rw [inner_smul_right]; rw [mul_comm]

/--
theorem `summable_inner_mul_inner` / 定理 `summable_inner_mul_inner`

English:
theorem summable_inner_mul_inner
  given: (b : HilbertBasis ι 𝕜 E) (x y : E)
  proof: (b.hasSum_inner_mul_inner x y).summable

中文:
定理 summable_inner_mul_inner
  条件: (b : Hilbert基 ι 𝕜 E) (x y : E)
  证明: (b.hasSum_inner_mul_inner x y).summable
-/
protected theorem summable_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    Summable fun i => ⟪x, b i⟫ * ⟪b i, y⟫ :=
  (b.hasSum_inner_mul_inner x y).summable

/--
theorem `tsum_inner_mul_inner` / 定理 `tsum_inner_mul_inner`

English:
theorem tsum_inner_mul_inner
  given: (b : HilbertBasis ι 𝕜 E) (x y : E)
  proof: (b.hasSum_inner_mul_inner x y).tsum_eq

中文:
定理 tsum_inner_mul_inner
  条件: (b : Hilbert基 ι 𝕜 E) (x y : E)
  证明: (b.hasSum_inner_mul_inner x y).tsum_eq
-/
protected theorem tsum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    ∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ :=
  (b.hasSum_inner_mul_inner x y).tsum_eq

-- Note: this should be `b.repr` composed with an identification of `lp (fun i : ι => 𝕜) p` with
-- `PiLp p (fun i : ι => 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/--
Definition of `toOrthonormalBasis` / `toOrthonormalBasis` 的定义

English:
definition toOrthonormalBasis
  signature: [Fintype ι] (b : HilbertBasis ι 𝕜 E)
  body: OrthonormalBasis.mk b.orthonormal
    (by
      refine Eq.ge ?_
      classical
      have := (span 𝕜 (Finset.univ.image b : Set E)).closed_of_finiteDimensional
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, HilbertBasis.dense_span] using
        this.submodule_topologicalClosure_eq.symm)

@[simp]

中文:
定义 toOrthonormalBasis
  签名: [有限类型 ι] (b : Hilbert基 ι 𝕜 E)
  定义体: OrthonormalBasis.mk b.orthonormal
    (by
      refine Eq.ge ?_
      classical
      have := (span 𝕜 (Finset.univ.image b : Set E)).closed_of_finiteDimensional
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, HilbertBasis.dense_span] using
        this.submodule_topologicalClosure_eq.symm)

@[simp]
-/
protected def toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk b.orthonormal
    (by
      refine Eq.ge ?_
      classical
      have := (span 𝕜 (Finset.univ.image b : Set E)).closed_of_finiteDimensional
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, HilbertBasis.dense_span] using
        this.submodule_topologicalClosure_eq.symm)

@[simp]
/--
theorem `coe_toOrthonormalBasis` / 定理 `coe_toOrthonormalBasis`

English:
theorem coe_toOrthonormalBasis
  given: [Fintype ι] (b : HilbertBasis ι 𝕜 E)
  proof: OrthonormalBasis.coe_mk _ _

中文:
定理 coe_toOrthonormalBasis
  条件: [有限类型 ι] (b : Hilbert基 ι 𝕜 E)
  证明: OrthonormalBasis.coe_mk _ _

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.coe_mk, coe_mk
-/
theorem coe_toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    (b.toOrthonormalBasis : ι -> E) = b :=
  OrthonormalBasis.coe_mk _ _

/-- A Hilbert basis of is an unconditional Schauder basis (`UnconditionalSchauderBasis`),
with coordinate functionals `x ↦ ⟪b i, x⟫`. The basis expansion `x = ∑' i, ⟪b i, x⟫ • b i`
converges unconditionally. -/
@[simps]
/--
Definition of `toUnconditionalSchauderBasis` / `toUnconditionalSchauderBasis` 的定义

English:
definition toUnconditionalSchauderBasis
  signature: (b : HilbertBasis ι 𝕜 E)
  body: b
  coord i := innerSL 𝕜 (b i)
  ortho i j := by
    classical
    simpa [innerSL_apply_apply, Pi.single_apply] using orthonormal_iff_ite.mp b.orthonormal i j
  expansion x := by
    simpa only [innerSL_apply_apply, ← b.repr_apply_apply] using b.hasSum_repr x

中文:
定义 toUnconditionalSchauderBasis
  签名: (b : Hilbert基 ι 𝕜 E)
  定义体: b
  coord i := innerSL 𝕜 (b i)
  ortho i j := by
    classical
    simpa [innerSL_apply_apply, Pi.single_apply] using orthonormal_iff_ite.mp b.orthonormal i j
  expansion x := by
    simpa only [innerSL_apply_apply, ← b.repr_apply_apply] using b.hasSum_repr x
-/
protected def toUnconditionalSchauderBasis (b : HilbertBasis ι 𝕜 E) :
    UnconditionalSchauderBasis ι 𝕜 E where
  basis := b
  coord i := innerSL 𝕜 (b i)
  ortho i j := by
    classical
    simpa [innerSL_apply_apply, Pi.single_apply] using orthonormal_iff_ite.mp b.orthonormal i j
  expansion x := by
    simpa only [innerSL_apply_apply, ← b.repr_apply_apply] using b.hasSum_repr x

/-- Every Hilbert basis indexed by `ℕ` is a Schauder basis (`SchauderBasis`) with
coordinate functionals `x ↦ ⟪b i, x⟫`. The expansion `x = ∑ i, ⟪b i, x⟫ • b i` converges. -/
@[simps]
/--
Definition of `toSchauderBasis` / `toSchauderBasis` 的定义

English:
definition toSchauderBasis
  signature: (b : HilbertBasis Nat 𝕜 E)
  body: ⇑b
  coord i := innerSL 𝕜 (b i)
  ortho := b.toUnconditionalSchauderBasis.ortho
  expansion x := (b.toUnconditionalSchauderBasis.expansion x).mono_left SummationFilter.le_atTop

中文:
定义 toSchauderBasis
  签名: (b : Hilbert基 自然数 𝕜 E)
  定义体: ⇑b
  coord i := innerSL 𝕜 (b i)
  ortho := b.toUnconditionalSchauderBasis.ortho
  expansion x := (b.toUnconditionalSchauderBasis.expansion x).mono_left SummationFilter.le_atTop
-/
protected def toSchauderBasis (b : HilbertBasis Nat 𝕜 E) : SchauderBasis 𝕜 E where
  basis := ⇑b
  coord i := innerSL 𝕜 (b i)
  ortho := b.toUnconditionalSchauderBasis.ortho
  expansion x := (b.toUnconditionalSchauderBasis.expansion x).mono_left SummationFilter.le_atTop

/--
theorem `hasSum_orthogonalProjectionOnto` / 定理 `hasSum_orthogonalProjectionOnto`

English:
theorem hasSum_orthogonalProjectionOnto
  statement: {U : Submodule 𝕜 E} [CompleteSpace U]
  proof: by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    b.hasSum_repr (U.orthogonalProjectionOnto x)

@[deprecated (since := "2026-05-05")] alias hasSum_orthogonalProjection :=
  HilbertBasis.hasSum_orthogonalProjectionOnto

中文:
定理 hasSum_orthogonalProjectionOnto
  结论: {U : 子模 𝕜 E} [完备空间 U]
  证明: by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    b.hasSum_repr (U.orthogonalProjectionOnto x)

@[deprecated (since := "2026-05-05")] alias hasSum_orthogonalProjection :=
  HilbertBasis.hasSum_orthogonalProjectionOnto
-/
protected theorem hasSum_orthogonalProjectionOnto {U : Submodule 𝕜 E} [CompleteSpace U]
    (b : HilbertBasis ι 𝕜 U) (x : E) :
    HasSum (fun i => ⟪(b i : E), x⟫ • b i) (U.orthogonalProjectionOnto x) := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    b.hasSum_repr (U.orthogonalProjectionOnto x)

@[deprecated (since := "2026-05-05")] alias hasSum_orthogonalProjection :=
  HilbertBasis.hasSum_orthogonalProjectionOnto

/--
theorem `finite_spans_dense` / 定理 `finite_spans_dense`

English:
theorem finite_spans_dense
  given: [DecidableEq E] (b : HilbertBasis ι 𝕜 E)
  proof: eq_top_iff.mpr b.dense_span.ge.trans (by
    simp_rw [← Submodule.span_iUnion]
    exact topologicalClosure_mono (span_mono <| Set.range_subset_iff.mpr fun i =>
Set.mem_iUnion_of_mem {i} Finset.mem_coe.mpr Finset.mem_image_of_mem _
      Finset.mem_singleton_self i))

中文:
定理 finite_spans_dense
  条件: [DecidableEq E] (b : Hilbert基 ι 𝕜 E)
  证明: eq_top_iff.mpr b.dense_span.ge.trans (by
    simp_rw [← Submodule.span_iUnion]
    exact topologicalClosure_mono (span_mono <| Set.range_subset_iff.mpr fun i =>
Set.mem_iUnion_of_mem {i} Finset.mem_coe.mpr Finset.mem_image_of_mem _
      Finset.mem_singleton_self i))

Depends on / 依赖: Finset, Finset.mem_coe.mpr, Finset.mem_image_of_mem, Finset.mem_singleton_self, Set.mem_iUnion_of_mem, Set.range_subset_iff.mpr, Submodule, Submodule.span_iUnion, b.dense_span.ge.trans, dense_span, eq_top_iff, eq_top_iff.mpr, mem_coe, mem_iUnion_of_mem, mem_image_of_mem, mem_singleton_self, range_subset_iff, simp_rw, span_iUnion, span_mono
-/
theorem finite_spans_dense [DecidableEq E] (b : HilbertBasis ι 𝕜 E) :
    (⨆ J : Finset ι, span 𝕜 (J.image b : Set E)).topologicalClosure = ⊤ :=
eq_top_iff.mpr b.dense_span.ge.trans (by
    simp_rw [← Submodule.span_iUnion]
    exact topologicalClosure_mono (span_mono <| Set.range_subset_iff.mpr fun i =>
Set.mem_iUnion_of_mem {i} Finset.mem_coe.mpr Finset.mem_image_of_mem _
      Finset.mem_singleton_self i))

variable [CompleteSpace E]

section
variable {v : ι -> E} (hv : Orthonormal 𝕜 v)
include hv

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure)
  body: HilbertBasis.ofRepr (hv.isHilbertSum hsp).linearIsometryEquiv

中文:
定义 mk
  签名: (hsp : ⊤ <= (span 𝕜 (集合.range v)).topologicalClosure)
  定义体: HilbertBasis.ofRepr (hv.isHilbertSum hsp).linearIsometryEquiv
-/
protected def mk (hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure) : HilbertBasis ι 𝕜 E :=
HilbertBasis.ofRepr (hv.isHilbertSum hsp).linearIsometryEquiv

/--
theorem `_root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one` / 定理 `_root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one`

English:
theorem _root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one
  given: [DecidableEq ι] (h i)
  proof: by
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single]; rw [LinearIsometry.toSpanSingleton_apply]; rw [one_smul]

@[simp]

中文:
定理 _root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one
  条件: [DecidableEq ι] (h i)
  证明: by
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single]; rw [LinearIsometry.toSpanSingleton_apply]; rw [one_smul]

@[simp]

Depends on / 依赖: IsHilbertSum, IsHilbertSum.linearIsometryEquiv_symm_apply_single, LinearIsometry, LinearIsometry.toSpanSingleton_apply, linearIsometryEquiv_symm_apply_single, one_smul, toSpanSingleton_apply
-/
theorem _root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one [DecidableEq ι] (h i) :
    (hv.isHilbertSum h).linearIsometryEquiv.symm (lp.single 2 i 1) = v i := by
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single]; rw [LinearIsometry.toSpanSingleton_apply]; rw [one_smul]

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure)
  proof: by
  classical
apply funext Orthonormal.linearIsometryEquiv_symm_apply_single_one hv hsp

中文:
定理 coe_mk
  条件: (hsp : ⊤ <= (span 𝕜 (集合.range v)).topologicalClosure)
  证明: by
  classical
apply funext Orthonormal.linearIsometryEquiv_symm_apply_single_one hv hsp

Depends on / 依赖: NormedSpace, NormedSpace.instPathConnectedSpace, PathConnectedSpace, instPathConnectedSpace
-/
protected theorem coe_mk (hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure) :
    ⇑(HilbertBasis.mk hv hsp) = v := by
  classical
apply funext Orthonormal.linearIsometryEquiv_symm_apply_single_one hv hsp

/--
Definition of `mkOfOrthogonalEqBot` / `mkOfOrthogonalEqBot` 的定义

English:
definition mkOfOrthogonalEqBot
  signature: (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥)
  body: HilbertBasis.mk hv
    (by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])

@[simp]

中文:
定义 mkOfOrthogonalEqBot
  签名: (hsp : (span 𝕜 (集合.range v))ᗮ = ⊥)
  定义体: HilbertBasis.mk hv
    (by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])

@[simp]
-/
protected def mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk hv
    (by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])

@[simp]
/--
theorem `coe_mkOfOrthogonalEqBot` / 定理 `coe_mkOfOrthogonalEqBot`

English:
theorem coe_mkOfOrthogonalEqBot
  given: (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥)
  proof: HilbertBasis.coe_mk hv _

中文:
定理 coe_mkOfOrthogonalEqBot
  条件: (hsp : (span 𝕜 (集合.range v))ᗮ = ⊥)
  证明: HilbertBasis.coe_mk hv _
-/
protected theorem coe_mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    ⇑(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v :=
  HilbertBasis.coe_mk hv _

-- Note : this should be `b.repr` composed with an identification of `lp (fun i : ι => 𝕜) p` with
-- `PiLp p (fun i : ι => 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/--
Definition of `_root_.OrthonormalBasis.toHilbertBasis` / `_root_.OrthonormalBasis.toHilbertBasis` 的定义

English:
definition _root_.OrthonormalBasis.toHilbertBasis
  signature: [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
  body: HilbertBasis.mk b.orthonormal by
    simpa only [← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq, eq_top_iff] using!
      @subset_closure E _ _

中文:
定义 _root_.正交标准基.toHilbertBasis
  签名: [有限类型 ι] (b : 正交标准基 ι 𝕜 E)
  定义体: HilbertBasis.mk b.orthonormal by
    simpa only [← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq, eq_top_iff] using!
      @subset_closure E _ _
-/
protected def _root_.OrthonormalBasis.toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    HilbertBasis ι 𝕜 E :=
HilbertBasis.mk b.orthonormal by
    simpa only [← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq, eq_top_iff] using!
      @subset_closure E _ _

end

@[simp]
/--
theorem `_root_.OrthonormalBasis.coe_toHilbertBasis` / 定理 `_root_.OrthonormalBasis.coe_toHilbertBasis`

English:
theorem _root_.OrthonormalBasis.coe_toHilbertBasis
  given: [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
  proof: HilbertBasis.coe_mk _ _

中文:
定理 _root_.正交标准基.coe_toHilbertBasis
  条件: [有限类型 ι] (b : 正交标准基 ι 𝕜 E)
  证明: HilbertBasis.coe_mk _ _

Depends on / 依赖: HilbertBasis, HilbertBasis.coe_mk, coe_mk
-/
theorem _root_.OrthonormalBasis.coe_toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    (b.toHilbertBasis : ι -> E) = b :=
  HilbertBasis.coe_mk _ _

/--
theorem `_root_.Orthonormal.exists_hilbertBasis_extension` / 定理 `_root_.Orthonormal.exists_hilbertBasis_extension`

English:
theorem _root_.Orthonormal.exists_hilbertBasis_extension
  statement: {s : Set E}
  proof: let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs
  ⟨w, HilbertBasis.mkOfOrthogonalEqBot hw_ortho
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq,
      maximal_orthonormal_iff_orthogonalComplement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_mkOfOrthogonalEqBot _ _⟩

中文:
定理 _root_.Orthonormal.存在_hilbertBasis_extension
  结论: {s : 集合 E}
  证明: let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs
  ⟨w, HilbertBasis.mkOfOrthogonalEqBot hw_ortho
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq,
      maximal_orthonormal_iff_orthogonalComplement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_mkOfOrthogonalEqBot _ _⟩

Depends on / 依赖: HilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot, HilbertBasis.mkOfOrthogonalEqBot, Set.ofPred_mem_eq, Subtype, Subtype.range_coe_subtype, coe_mkOfOrthogonalEqBot, exists_maximal_orthonormal, hw_max, hw_ortho, maximal_orthonormal_iff_orthogonalComplement_eq_bot, mkOfOrthogonalEqBot, ofPred_mem_eq, range_coe_subtype
-/
theorem _root_.Orthonormal.exists_hilbertBasis_extension {s : Set E}
    (hs : Orthonormal 𝕜 ((↑) : s -> E)) :
    exists (w : Set E) (b : HilbertBasis w 𝕜 E), s subseteq w ∧ ⇑b = ((↑) : w -> E) :=
  let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs
  ⟨w, HilbertBasis.mkOfOrthogonalEqBot hw_ortho
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq,
      maximal_orthonormal_iff_orthogonalComplement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_mkOfOrthogonalEqBot _ _⟩

variable (𝕜 E)

/--
theorem `_root_.exists_hilbertBasis` / 定理 `_root_.exists_hilbertBasis`

English:
theorem _root_.exists_hilbertBasis
  statement: exists (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w -> E)
  proof: let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbertBasis_extension
  ⟨w, hw, hw''⟩

中文:
定理 _root_.存在_hilbertBasis
  结论: 存在 (w : 集合 E) (b : Hilbert基 w 𝕜 E), ⇑b = ((↑) : w -> E)
  证明: let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbertBasis_extension
  ⟨w, hw, hw''⟩

Depends on / 依赖: exists_hilbertBasis_extension, orthonormal_empty
-/
theorem _root_.exists_hilbertBasis : exists (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w -> E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbertBasis_extension
  ⟨w, hw, hw''⟩

end HilbertBasis
