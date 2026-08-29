/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Kalle Kytölä
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Polar set

In this file we define the polar set. There are different notions of the polar, we will define the
*absolute polar*. The advantage over the real polar is that we can define the absolute polar for
any bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, where `𝕜` is a normed commutative ring and
`E` and `F` are modules over `𝕜`.

## Main definitions

* `LinearMap.polar`: The polar of a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.

## Main statements

* `LinearMap.polar_eq_iInter`: The polar as an intersection.
* `LinearMap.subset_bipolar`: The polar is a subset of the bipolar.
* `LinearMap.polar_isClosed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/

@[expose] public section

variable {𝕜 E F : Type*}

open Topology

namespace LinearMap

section NormedRing

variable [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)

/--
Definition of `polar` / `polar` 的定义

English:
definition polar
  signature: (s : Set E)
  body: { y : F | forall x in s, ‖B x y‖ <= 1 }

中文:
定义 polar
  签名: (s : Set E)
  定义体: { y : F | forall x in s, ‖B x y‖ <= 1 }
-/
def polar (s : Set E) : Set F :=
  { y : F | forall x in s, ‖B x y‖ <= 1 }

/--
theorem `polar_mem_iff` / 定理 `polar_mem_iff`

English:
theorem polar_mem_iff
  given: (s : Set E) (y : F)
  statement: y in B.polar s ↔ forall x in s, ‖B x y‖ <= 1
  proof: Iff.rfl

中文:
定理 polar_mem_iff
  条件: (s : Set E) (y : F)
  结论: y in B.polar s ↔ 对任意 x in s, ‖B x y‖ <= 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem polar_mem_iff (s : Set E) (y : F) : y in B.polar s ↔ forall x in s, ‖B x y‖ <= 1 :=
  Iff.rfl

/--
theorem `polar_mem` / 定理 `polar_mem`

English:
theorem polar_mem
  given: (s : Set E) (y : F) (hy : y in B.polar s)
  statement: forall x in s, ‖B x y‖ <= 1
  proof: hy

中文:
定理 polar_mem
  条件: (s : Set E) (y : F) (hy : y in B.polar s)
  结论: 对任意 x in s, ‖B x y‖ <= 1
  证明: hy
-/
theorem polar_mem (s : Set E) (y : F) (hy : y in B.polar s) : forall x in s, ‖B x y‖ <= 1 :=
  hy

/--
theorem `polar_eq_biInter_preimage` / 定理 `polar_eq_biInter_preimage`

English:
theorem polar_eq_biInter_preimage
  given: (s : Set E)
  proof: by aesop

中文:
定理 polar_eq_biInter_preimage
  条件: (s : Set E)
  证明: by aesop
-/
theorem polar_eq_biInter_preimage (s : Set E) :
    B.polar s = ⋂ x in s, ((B x) ⁻¹' Metric.closedBall (0 : 𝕜) 1) := by aesop

-- TODO: this theorem is abusing defeq between F and WeakBilin B.flip
/--
theorem `polar_isClosed` / 定理 `polar_isClosed`

English:
theorem polar_isClosed
  given: (s : Set E)
  statement: IsClosed (X := WeakBilin B.flip) (B.polar s)
  proof: by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ => Metric.isClosed_closedBall.preimage (WeakBilin.eval_continuous B.flip _)

@[simp]

中文:
定理 polar_isClosed
  条件: (s : Set E)
  结论: IsClosed (X := WeakBilin B.flip) (B.polar s)
  证明: by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ => Metric.isClosed_closedBall.preimage (WeakBilin.eval_continuous B.flip _)

@[simp]

Depends on / 依赖: B.flip, B.polar, Metric, Metric.isClosed_closedBall.preimage, WeakBilin, WeakBilin.eval_continuous, eval_continuous, isClosed_biInter, isClosed_closedBall, polar_eq_biInter_preimage, preimage
-/
theorem polar_isClosed (s : Set E) : IsClosed (X := WeakBilin B.flip) (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ => Metric.isClosed_closedBall.preimage (WeakBilin.eval_continuous B.flip _)

@[simp]
/--
theorem `zero_mem_polar` / 定理 `zero_mem_polar`

English:
theorem zero_mem_polar
  given: (s : Set E)
  statement: (0 : F) in B.polar s
  proof: fun _ _ => by
  simp only [map_zero, norm_zero, zero_le_one]

中文:
定理 zero_mem_polar
  条件: (s : Set E)
  结论: (0 : F) in B.polar s
  证明: fun _ _ => by
  simp only [map_zero, norm_zero, zero_le_one]

Depends on / 依赖: map_zero, norm_zero, zero_le_one
-/
theorem zero_mem_polar (s : Set E) : (0 : F) in B.polar s := fun _ _ => by
  simp only [map_zero, norm_zero, zero_le_one]

/--
theorem `polar_nonempty` / 定理 `polar_nonempty`

English:
theorem polar_nonempty
  given: (s : Set E)
  statement: Set.Nonempty (B.polar s)
  proof: by
  use 0
  exact zero_mem_polar B s

中文:
定理 polar_nonempty
  条件: (s : Set E)
  结论: Set.Nonempty (B.polar s)
  证明: by
  use 0
  exact zero_mem_polar B s

Depends on / 依赖: zero_mem_polar
-/
theorem polar_nonempty (s : Set E) : Set.Nonempty (B.polar s) := by
  use 0
  exact zero_mem_polar B s

/--
theorem `polar_eq_iInter` / 定理 `polar_eq_iInter`

English:
theorem polar_eq_iInter
  given: {s : Set E}
  statement: B.polar s = ⋂ x in s, { y : F | ‖B x y‖ <= 1 }
  proof: by
  ext
  simp only [polar_mem_iff, Set.mem_iInter, Set.mem_ofPred_eq]

中文:
定理 polar_eq_iInter
  条件: {s : Set E}
  结论: B.polar s = ⋂ x in s, { y : F | ‖B x y‖ <= 1 }
  证明: by
  ext
  simp only [polar_mem_iff, Set.mem_iInter, Set.mem_ofPred_eq]

Depends on / 依赖: Set.mem_iInter, Set.mem_ofPred_eq, mem_iInter, mem_ofPred_eq, polar_mem_iff
-/
theorem polar_eq_iInter {s : Set E} : B.polar s = ⋂ x in s, { y : F | ‖B x y‖ <= 1 } := by
  ext
  simp only [polar_mem_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/--
theorem `polar_gc` / 定理 `polar_gc`

English:
theorem polar_gc
  proof: fun _ _ =>
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hx _ hy => h hy _ hx⟩

@[simp]

中文:
定理 polar_gc
  证明: fun _ _ =>
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hx _ hy => h hy _ hx⟩

@[simp]
-/
theorem polar_gc :
    GaloisConnection (OrderDual.toDual ∘ B.polar) (B.flip.polar ∘ OrderDual.ofDual) := fun _ _ =>
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hx _ hy => h hy _ hx⟩

@[simp]
/--
theorem `polar_iUnion` / 定理 `polar_iUnion`

English:
theorem polar_iUnion
  given: {ι} {s : ι -> Set E}
  statement: B.polar (⋃ i, s i) = ⋂ i, B.polar (s i)
  proof: B.polar_gc.l_iSup

@[simp]

中文:
定理 polar_iUnion
  条件: {ι} {s : ι -> Set E}
  结论: B.polar (⋃ i, s i) = ⋂ i, B.polar (s i)
  证明: B.polar_gc.l_iSup

@[simp]

Depends on / 依赖: B.polar_gc.l_iSup, l_iSup, polar_gc
-/
theorem polar_iUnion {ι} {s : ι -> Set E} : B.polar (⋃ i, s i) = ⋂ i, B.polar (s i) :=
  B.polar_gc.l_iSup

@[simp]
/--
theorem `polar_union` / 定理 `polar_union`

English:
theorem polar_union
  given: {s t : Set E}
  statement: B.polar (s union t) = B.polar s inter B.polar t
  proof: B.polar_gc.l_sup

中文:
定理 polar_union
  条件: {s t : Set E}
  结论: B.polar (s union t) = B.polar s inter B.polar t
  证明: B.polar_gc.l_sup

Depends on / 依赖: B.polar_gc.l_sup, l_sup, polar_gc
-/
theorem polar_union {s t : Set E} : B.polar (s union t) = B.polar s inter B.polar t :=
  B.polar_gc.l_sup

/--
theorem `polar_antitone` / 定理 `polar_antitone`

English:
theorem polar_antitone
  statement: Antitone (B.polar : Set E -> Set F)
  proof: B.polar_gc.monotone_l

@[simp]

中文:
定理 polar_antitone
  结论: Antitone (B.polar : Set E -> Set F)
  证明: B.polar_gc.monotone_l

@[simp]

Depends on / 依赖: B.polar_gc.monotone_l, monotone_l, polar_gc
-/
theorem polar_antitone : Antitone (B.polar : Set E -> Set F) :=
  B.polar_gc.monotone_l

@[simp]
/--
theorem `polar_empty` / 定理 `polar_empty`

English:
theorem polar_empty
  statement: B.polar ∅ = Set.univ
  proof: B.polar_gc.l_bot

@[simp]

中文:
定理 polar_empty
  结论: B.polar ∅ = Set.univ
  证明: B.polar_gc.l_bot

@[simp]

Depends on / 依赖: B.polar_gc.l_bot, l_bot, polar_gc
-/
theorem polar_empty : B.polar ∅ = Set.univ :=
  B.polar_gc.l_bot

@[simp]
/--
theorem `polar_singleton` / 定理 `polar_singleton`

English:
theorem polar_singleton
  given: {a : E}
  statement: B.polar {a} = { y | ‖B a y‖ <= 1 }
  proof: le_antisymm
  (fun _ hy => hy _ rfl)
  (fun y hy => (polar_mem_iff _ _ _).mp (fun _ hb => by rw [Set.mem_singleton_iff.mp hb]; exact hy))

中文:
定理 polar_singleton
  条件: {a : E}
  结论: B.polar {a} = { y | ‖B a y‖ <= 1 }
  证明: le_antisymm
  (fun _ hy => hy _ rfl)
  (fun y hy => (polar_mem_iff _ _ _).mp (fun _ hb => by rw [Set.mem_singleton_iff.mp hb]; exact hy))

Depends on / 依赖: le_antisymm
-/
theorem polar_singleton {a : E} : B.polar {a} = { y | ‖B a y‖ <= 1 } := le_antisymm
  (fun _ hy => hy _ rfl)
  (fun y hy => (polar_mem_iff _ _ _).mp (fun _ hb => by rw [Set.mem_singleton_iff.mp hb]; exact hy))

/--
theorem `mem_polar_singleton` / 定理 `mem_polar_singleton`

English:
theorem mem_polar_singleton
  given: {x : E} (y : F)
  statement: y in B.polar {x} ↔ ‖B x y‖ <= 1
  proof: by
  simp only [polar_singleton, Set.mem_ofPred_eq]

中文:
定理 mem_polar_singleton
  条件: {x : E} (y : F)
  结论: y in B.polar {x} ↔ ‖B x y‖ <= 1
  证明: by
  simp only [polar_singleton, Set.mem_ofPred_eq]

Depends on / 依赖: Set.mem_ofPred_eq, mem_ofPred_eq, polar_singleton
-/
theorem mem_polar_singleton {x : E} (y : F) : y in B.polar {x} ↔ ‖B x y‖ <= 1 := by
  simp only [polar_singleton, Set.mem_ofPred_eq]

/--
theorem `polar_zero` / 定理 `polar_zero`

English:
theorem polar_zero
  statement: B.polar ({0} : Set E) = Set.univ
  proof: by
  simp only [polar_singleton, map_zero, zero_apply, norm_zero, zero_le_one, Set.ofPred_true]

中文:
定理 polar_zero
  结论: B.polar ({0} : Set E) = Set.univ
  证明: by
  simp only [polar_singleton, map_zero, zero_apply, norm_zero, zero_le_one, Set.ofPred_true]

Depends on / 依赖: Set.ofPred_true, map_zero, norm_zero, ofPred_true, polar_singleton, zero_apply, zero_le_one
-/
theorem polar_zero : B.polar ({0} : Set E) = Set.univ := by
  simp only [polar_singleton, map_zero, zero_apply, norm_zero, zero_le_one, Set.ofPred_true]

/--
theorem `subset_bipolar` / 定理 `subset_bipolar`

English:
theorem subset_bipolar
  given: (s : Set E)
  statement: s subseteq B.flip.polar (B.polar s)
  proof: fun x hx y hy => by
  rw [B.flip_apply]
  exact hy x hx

@[simp]

中文:
定理 subset_bipolar
  条件: (s : Set E)
  结论: s subseteq B.flip.polar (B.polar s)
  证明: fun x hx y hy => by
  rw [B.flip_apply]
  exact hy x hx

@[simp]

Depends on / 依赖: B.flip_apply, flip_apply
-/
theorem subset_bipolar (s : Set E) : s subseteq B.flip.polar (B.polar s) := fun x hx y hy => by
  rw [B.flip_apply]
  exact hy x hx

@[simp]
/--
theorem `tripolar_eq_polar` / 定理 `tripolar_eq_polar`

English:
theorem tripolar_eq_polar
  given: (s : Set E)
  statement: B.polar (B.flip.polar (B.polar s)) = B.polar s
  proof: (B.polar_antitone (B.subset_bipolar s)).antisymm (subset_bipolar B.flip (B.polar s))

中文:
定理 tripolar_eq_polar
  条件: (s : Set E)
  结论: B.polar (B.flip.polar (B.polar s)) = B.polar s
  证明: (B.polar_antitone (B.subset_bipolar s)).antisymm (subset_bipolar B.flip (B.polar s))

Depends on / 依赖: B.flip, B.polar, B.polar_antitone, B.subset_bipolar, antisymm, polar_antitone, subset_bipolar
-/
theorem tripolar_eq_polar (s : Set E) : B.polar (B.flip.polar (B.polar s)) = B.polar s :=
  (B.polar_antitone (B.subset_bipolar s)).antisymm (subset_bipolar B.flip (B.polar s))

/--
theorem `sInter_polar_finite_subset_eq_polar` / 定理 `sInter_polar_finite_subset_eq_polar`

English:
theorem sInter_polar_finite_subset_eq_polar
  given: (s : Set E)
  proof: by
  ext x
  simp only [Set.sInter_image, Set.mem_ofPred_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha => ?_, fun hx F _ hF₂ => polar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

中文:
定理 sInter_polar_finite_subset_eq_polar
  条件: (s : Set E)
  证明: by
  ext x
  simp only [Set.sInter_image, Set.mem_ofPred_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha => ?_, fun hx F _ hF₂ => polar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

Depends on / 依赖: Set.finite_singleton, Set.mem_iInter, Set.mem_ofPred_eq, Set.sInter_image, Set.singleton_subset_iff.mpr, and_imp, finite_singleton, mem_iInter, mem_ofPred_eq, mem_polar_singleton, polar_antitone, sInter_image, singleton_subset_iff
-/
theorem sInter_polar_finite_subset_eq_polar (s : Set E) :
    ⋂₀ (B.polar '' { F | F.Finite ∧ F subseteq s }) = B.polar s := by
  ext x
  simp only [Set.sInter_image, Set.mem_ofPred_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha => ?_, fun hx F _ hF₂ => polar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

end NormedRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)

/--
theorem `polar_univ` / 定理 `polar_univ`

English:
theorem polar_univ
  given: (h : SeparatingRight B)
  statement: B.polar Set.univ = {(0 : F)}
  proof: by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨by simp only [zero_mem_polar], fun y hy => h _ fun x => ?_⟩
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  rcases NormedField.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩
  calc
    ‖B x y‖ = ‖c‖ * ‖B (c⁻¹ • x) y‖ := by
  

中文:
定理 polar_univ
  条件: (h : SeparatingRight B)
  结论: B.polar Set.univ = {(0 : F)}
  证明: by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨by simp only [zero_mem_polar], fun y hy => h _ fun x => ?_⟩
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  rcases NormedField.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩
  calc
    ‖B x y‖ = ‖c‖ * ‖B (c⁻¹ • x) y‖ := by
  

Depends on / 依赖: B.map_smul, LinearMap, LinearMap.smul_apply, NormedField, NormedField.exists_norm_lt, Set.eq_singleton_iff_unique_mem, eq_singleton_iff_unique_mem, exists_norm_lt, hc.ne, le_of_forall_gt_imp_ge_of_dense, map_smul, mul_one, norm_inv, norm_le_zero_iff, norm_le_zero_iff.mp, norm_mul, smul_apply, smul_eq_mul, zero_mem_polar
-/
theorem polar_univ (h : SeparatingRight B) : B.polar Set.univ = {(0 : F)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨by simp only [zero_mem_polar], fun y hy => h _ fun x => ?_⟩
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  rcases NormedField.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩
  calc
    ‖B x y‖ = ‖c‖ * ‖B (c⁻¹ • x) y‖ := by
      rw [B.map_smul]; rw [LinearMap.smul_apply]; rw [smul_eq_mul]; rw [norm_mul]; rw [norm_inv]; rw [mul_inv_cancel_left₀ hc.ne']
    _ <= ε * 1 := by gcongr; exact hy _ trivial
    _ = ε := mul_one _

/--
theorem `polar_subMulAction` / 定理 `polar_subMulAction`

English:
theorem polar_subMulAction
  given: {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  proof: by
  ext y
  constructor
  · intro hy x hx
    obtain ⟨r, hr⟩ := NormedField.exists_lt_norm 𝕜 ‖B x y‖⁻¹
    contrapose! hr
    rw [← one_div]; rw [le_div_iff₀ (norm_pos_iff.2 hr)]
    simpa using hy _ (SMulMemClass.smul_mem r hx)
  · intro h x hx
    simp [h x hx]

中文:
定理 polar_subMulAction
  条件: {S : 类型} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  证明: by
  ext y
  constructor
  · intro hy x hx
    obtain ⟨r, hr⟩ := NormedField.exists_lt_norm 𝕜 ‖B x y‖⁻¹
    contrapose! hr
    rw [← one_div]; rw [le_div_iff₀ (norm_pos_iff.2 hr)]
    simpa using hy _ (SMulMemClass.smul_mem r hx)
  · intro h x hx
    simp [h x hx]

Depends on / 依赖: NormedField, NormedField.exists_lt_norm, SMulMemClass, SMulMemClass.smul_mem, contrapose, exists_lt_norm, norm_pos_iff, one_div, smul_mem
-/
theorem polar_subMulAction {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    B.polar m = { y | forall x in m, B x y = 0 } := by
  ext y
  constructor
  · intro hy x hx
    obtain ⟨r, hr⟩ := NormedField.exists_lt_norm 𝕜 ‖B x y‖⁻¹
    contrapose! hr
    rw [← one_div]; rw [le_div_iff₀ (norm_pos_iff.2 hr)]
    simpa using hy _ (SMulMemClass.smul_mem r hx)
  · intro h x hx
    simp [h x hx]

/--
Definition of `polarSubmodule` / `polarSubmodule` 的定义

English:
definition polarSubmodule
  signature: {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  body: .copy (⨅ x in m, LinearMap.ker (B x)) (B.polar m) by ext; simp [polar_subMulAction]

中文:
定义 polarSubmodule
  签名: {S : 类型} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  定义体: .copy (⨅ x in m, LinearMap.ker (B x)) (B.polar m) by ext; simp [polar_subMulAction]

Depends on / 依赖: B.polar, LinearMap, LinearMap.ker, polar_subMulAction
-/
def polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : Submodule 𝕜 F :=
.copy (⨅ x in m, LinearMap.ker (B x)) (B.polar m) by ext; simp [polar_subMulAction]

end NontriviallyNormedField

end LinearMap

namespace StrongDual

section

variable (R M : Type*) [SeminormedCommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

/--
theorem `dualPairing_separatingLeft` / 定理 `dualPairing_separatingLeft`

English:
theorem dualPairing_separatingLeft
  statement: (topDualPairing R M).SeparatingLeft
  proof: by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot]; rw [LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

中文:
定理 dualPairing_separatingLeft
  结论: (topDualPairing R M).SeparatingLeft
  证明: by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot]; rw [LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_injective, LinearMap, LinearMap.ker_eq_bot, LinearMap.separatingLeft_iff_ker_eq_bot, coe_injective, ker_eq_bot, separatingLeft_iff_ker_eq_bot
-/
theorem dualPairing_separatingLeft : (topDualPairing R M).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot]; rw [LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

end

section

/--
Definition of `polar` / `polar` 的定义

English:
definition polar
  signature: (R : Type*) [NormedCommRing R] {M : Type*} [AddCommMonoid M]
  body: (topDualPairing R M).flip.polar

中文:
定义 polar
  签名: (R : 类型) [NormedCommRing R] {M : 类型} [AddCommMonoid M]
  定义体: (topDualPairing R M).flip.polar

Depends on / 依赖: flip.polar, topDualPairing
-/
def polar (R : Type*) [NormedCommRing R] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module R M] : Set M -> Set (StrongDual R M) :=
  (topDualPairing R M).flip.polar

/--
Definition of `polarSubmodule` / `polarSubmodule` 的定义

English:
definition polarSubmodule
  signature: (𝕜 : Type*) [NontriviallyNormedField 𝕜] {M : Type*} [AddCommMonoid M]
  body: (topDualPairing 𝕜 M).flip.polarSubmodule m

中文:
定义 polarSubmodule
  签名: (𝕜 : 类型) [NontriviallyNormedField 𝕜] {M : 类型} [AddCommMonoid M]
  定义体: (topDualPairing 𝕜 M).flip.polarSubmodule m

Depends on / 依赖: flip.polarSubmodule, polarSubmodule, topDualPairing
-/
def polarSubmodule (𝕜 : Type*) [NontriviallyNormedField 𝕜] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module 𝕜 M] {S : Type*} [SetLike S M] [SMulMemClass S 𝕜 M] (m : S) :
    Submodule 𝕜 (StrongDual 𝕜 M) := (topDualPairing 𝕜 M).flip.polarSubmodule m

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]

/--
lemma `polarSubmodule_eq_polar` / 引理 `polarSubmodule_eq_polar`

English:
lemma polarSubmodule_eq_polar
  given: (m : SubMulAction 𝕜 E)
  proof: rfl

中文:
引理 polarSubmodule_eq_polar
  条件: (m : SubMulAction 𝕜 E)
  证明: rfl
-/
lemma polarSubmodule_eq_polar (m : SubMulAction 𝕜 E) :
    (polarSubmodule 𝕜 m : Set (StrongDual 𝕜 E)) = polar 𝕜 m := rfl

/--
theorem `mem_polar_iff` / 定理 `mem_polar_iff`

English:
theorem mem_polar_iff
  given: {x' : StrongDual 𝕜 E} (s : Set E)
  statement: x' in polar 𝕜 s ↔ forall z in s, ‖x' z‖ <= 1
  proof: Iff.rfl

中文:
定理 mem_polar_iff
  条件: {x' : StrongDual 𝕜 E} (s : Set E)
  结论: x' in polar 𝕜 s ↔ 对任意 z in s, ‖x' z‖ <= 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_polar_iff {x' : StrongDual 𝕜 E} (s : Set E) : x' in polar 𝕜 s ↔ forall z in s, ‖x' z‖ <= 1 :=
  Iff.rfl

/--
lemma `polarSubmodule_eq_setOfPred` / 引理 `polarSubmodule_eq_setOfPred`

English:
lemma polarSubmodule_eq_setOfPred
  given: {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  proof: (topDualPairing 𝕜 E).flip.polar_subMulAction _

@[deprecated (since := "2026-07-09")]
alias polarSubmodule_eq_setOf := polarSubmodule_eq_setOfPred

中文:
引理 polarSubmodule_eq_setOfPred
  条件: {S : 类型} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  证明: (topDualPairing 𝕜 E).flip.polar_subMulAction _

@[deprecated (since := "2026-07-09")]
alias polarSubmodule_eq_setOf := polarSubmodule_eq_setOfPred

Depends on / 依赖: flip.polar_subMulAction, polar_subMulAction, topDualPairing
-/
lemma polarSubmodule_eq_setOfPred {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    polarSubmodule 𝕜 m = { y : StrongDual 𝕜 E | forall x in m, y x = 0 } :=
  (topDualPairing 𝕜 E).flip.polar_subMulAction _

@[deprecated (since := "2026-07-09")]
alias polarSubmodule_eq_setOf := polarSubmodule_eq_setOfPred

/--
lemma `mem_polarSubmodule` / 引理 `mem_polarSubmodule`

English:
lemma mem_polarSubmodule
  statement: {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  proof: propext_iff.mp congr($(polarSubmodule_eq_setOfPred 𝕜 m) y)

@[simp]

中文:
引理 mem_polarSubmodule
  结论: {S : 类型} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
  证明: propext_iff.mp congr($(polarSubmodule_eq_setOfPred 𝕜 m) y)

@[simp]

Depends on / 依赖: polarSubmodule_eq_setOfPred, propext_iff, propext_iff.mp
-/
lemma mem_polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
    (y : StrongDual 𝕜 E) : y in polarSubmodule 𝕜 m ↔ forall x in m, y x = 0 :=
  propext_iff.mp congr($(polarSubmodule_eq_setOfPred 𝕜 m) y)

@[simp]
/--
theorem `zero_mem_polar` / 定理 `zero_mem_polar`

English:
theorem zero_mem_polar
  given: (s : Set E)
  statement: (0 : StrongDual 𝕜 E) in polar 𝕜 s
  proof: LinearMap.zero_mem_polar _ s

中文:
定理 zero_mem_polar
  条件: (s : Set E)
  结论: (0 : StrongDual 𝕜 E) in polar 𝕜 s
  证明: LinearMap.zero_mem_polar _ s

Depends on / 依赖: LinearMap, LinearMap.zero_mem_polar, zero_mem_polar
-/
theorem zero_mem_polar (s : Set E) : (0 : StrongDual 𝕜 E) in polar 𝕜 s :=
  LinearMap.zero_mem_polar _ s

/--
theorem `polar_nonempty` / 定理 `polar_nonempty`

English:
theorem polar_nonempty
  given: (s : Set E)
  statement: Set.Nonempty (polar 𝕜 s)
  proof: LinearMap.polar_nonempty _ _

中文:
定理 polar_nonempty
  条件: (s : Set E)
  结论: Set.Nonempty (polar 𝕜 s)
  证明: LinearMap.polar_nonempty _ _

Depends on / 依赖: LinearMap, LinearMap.polar_nonempty, polar_nonempty
-/
theorem polar_nonempty (s : Set E) : Set.Nonempty (polar 𝕜 s) :=
  LinearMap.polar_nonempty _ _

open Set

@[simp]
/--
theorem `polar_empty` / 定理 `polar_empty`

English:
theorem polar_empty
  statement: polar 𝕜 (∅ : Set E) = Set.univ
  proof: LinearMap.polar_empty _

@[simp]

中文:
定理 polar_empty
  结论: polar 𝕜 (∅ : Set E) = Set.univ
  证明: LinearMap.polar_empty _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.polar_empty, polar_empty
-/
theorem polar_empty : polar 𝕜 (∅ : Set E) = Set.univ :=
  LinearMap.polar_empty _

@[simp]
/--
theorem `polar_singleton` / 定理 `polar_singleton`

English:
theorem polar_singleton
  given: {a : E}
  statement: polar 𝕜 {a} = { x | ‖x a‖ <= 1 }
  proof: by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, topDualPairing_apply]

中文:
定理 polar_singleton
  条件: {a : E}
  结论: polar 𝕜 {a} = { x | ‖x a‖ <= 1 }
  证明: by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, topDualPairing_apply]

Depends on / 依赖: LinearMap, LinearMap.flip_apply, LinearMap.polar_singleton, flip_apply, polar_singleton, topDualPairing_apply
-/
theorem polar_singleton {a : E} : polar 𝕜 {a} = { x | ‖x a‖ <= 1 } := by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, topDualPairing_apply]

/--
theorem `mem_polar_singleton` / 定理 `mem_polar_singleton`

English:
theorem mem_polar_singleton
  given: {a : E} (y : StrongDual 𝕜 E)
  statement: y in polar 𝕜 {a} ↔ ‖y a‖ <= 1
  proof: by
  simp only [polar_singleton, mem_ofPred_eq]

中文:
定理 mem_polar_singleton
  条件: {a : E} (y : StrongDual 𝕜 E)
  结论: y in polar 𝕜 {a} ↔ ‖y a‖ <= 1
  证明: by
  simp only [polar_singleton, mem_ofPred_eq]

Depends on / 依赖: mem_ofPred_eq, polar_singleton
-/
theorem mem_polar_singleton {a : E} (y : StrongDual 𝕜 E) : y in polar 𝕜 {a} ↔ ‖y a‖ <= 1 := by
  simp only [polar_singleton, mem_ofPred_eq]

/--
theorem `polar_zero` / 定理 `polar_zero`

English:
theorem polar_zero
  statement: polar 𝕜 ({0} : Set E) = Set.univ
  proof: LinearMap.polar_zero _

中文:
定理 polar_zero
  结论: polar 𝕜 ({0} : Set E) = Set.univ
  证明: LinearMap.polar_zero _

Depends on / 依赖: LinearMap, LinearMap.polar_zero, polar_zero
-/
theorem polar_zero : polar 𝕜 ({0} : Set E) = Set.univ :=
  LinearMap.polar_zero _

end

section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

open Set

@[simp]
/--
theorem `polar_univ` / 定理 `polar_univ`

English:
theorem polar_univ
  statement: polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)}
  proof: (topDualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

中文:
定理 polar_univ
  结论: polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)}
  证明: (topDualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

Depends on / 依赖: LinearMap, LinearMap.flip_separatingRight.mpr, dualPairing_separatingLeft, flip.polar_univ, flip_separatingRight, polar_univ, topDualPairing
-/
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)} :=
  (topDualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

end

end StrongDual
