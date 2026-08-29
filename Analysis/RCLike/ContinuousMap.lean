/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.Units

/-! # Mapping `C(X, ℝ)` to `C(X, 𝕜)` and back

This file contains the definitions for `ContinuousMap.realToRCLike` and
`ContinuousMap.rclikeToReal`, which map `C(X, ℝ)` to `C(X, 𝕜)` and back for any `RCLike 𝕜`. -/

@[expose] public section

namespace ContinuousMap
variable {X : Type*} (𝕜 : Type*) [TopologicalSpace X] [RCLike 𝕜]

/--
Definition of `realToRCLike` / `realToRCLike` 的定义

English:
definition realToRCLike
  signature: (f : C(X, Real))
  body: RCLike.ofReal (f x)

中文:
定义 realToRCLike
  签名: (f : C(X, 实数))
  定义体: RCLike.ofReal (f x)
-/
@[simps] def realToRCLike (f : C(X, Real)) : C(X, 𝕜) where toFun x := RCLike.ofReal (f x)

/--
lemma `isSelfAdjoint_realToRCLike` / 引理 `isSelfAdjoint_realToRCLike`

English:
lemma isSelfAdjoint_realToRCLike
  given: {f : C(X, Real)}
  proof: by ext; simp

中文:
引理 isSelfAdjoint_realToRCLike
  条件: {f : C(X, 实数)}
  证明: by ext; simp
-/
@[simp, grind .] lemma isSelfAdjoint_realToRCLike {f : C(X, Real)} :
    IsSelfAdjoint (f.realToRCLike 𝕜) := by ext; simp

/--
lemma `spectrum_realToRCLike` / 引理 `spectrum_realToRCLike`

English:
lemma spectrum_realToRCLike
  given: (f : C(X, Real))
  proof: by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]

中文:
引理 spectrum_realToRCLike
  条件: (f : C(X, 实数))
  证明: by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]
-/
@[simp] lemma spectrum_realToRCLike (f : C(X, Real)) :
    spectrum Real (f.realToRCLike 𝕜) = spectrum Real f := by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]

open ComplexOrder

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/--
Definition of `realToRCLikeOrderEmbedding` / `realToRCLikeOrderEmbedding` 的定义

English:
definition realToRCLikeOrderEmbedding
  signature: : C(X, Real) ↪o C(X, 𝕜) where
  body: realToRCLike 𝕜
  inj' f g hfg := by ext x; simpa using congr($hfg x)
  map_rel_iff' := by simp [le_def]

中文:
定义 realToRCLikeOrderEmbedding
  签名: : C(X, 实数) ↪o C(X, 𝕜) where
  定义体: realToRCLike 𝕜
  inj' f g hfg := by ext x; simpa using congr($hfg x)
  map_rel_iff' := by simp [le_def]
-/
@[simps] def realToRCLikeOrderEmbedding : C(X, Real) ↪o C(X, 𝕜) where
  toFun := realToRCLike 𝕜
  inj' f g hfg := by ext x; simpa using congr($hfg x)
  map_rel_iff' := by simp [le_def]

variable (X) in
/--
lemma `realToRCLike_monotone` / 引理 `realToRCLike_monotone`

English:
lemma realToRCLike_monotone
  statement: Monotone (realToRCLike (X := X) 𝕜)
  proof: .monotone realToRCLikeOrderEmbedding X 𝕜

中文:
引理 realToRCLike_monotone
  结论: Monotone (realToRCLike (X := X) 𝕜)
  证明: .monotone realToRCLikeOrderEmbedding X 𝕜
-/
lemma realToRCLike_monotone : Monotone (realToRCLike (X := X) 𝕜) :=
.monotone realToRCLikeOrderEmbedding X 𝕜

variable (X) in
/--
lemma `realToRCLike_strictMono` / 引理 `realToRCLike_strictMono`

English:
lemma realToRCLike_strictMono
  statement: StrictMono (realToRCLike (X := X) 𝕜)
  proof: .strictMono realToRCLikeOrderEmbedding X 𝕜

中文:
引理 realToRCLike_strictMono
  结论: StrictMono (realToRCLike (X := X) 𝕜)
  证明: .strictMono realToRCLikeOrderEmbedding X 𝕜
-/
lemma realToRCLike_strictMono : StrictMono (realToRCLike (X := X) 𝕜) :=
.strictMono realToRCLikeOrderEmbedding X 𝕜

variable (X) in
/--
lemma `realToRCLike_injective` / 引理 `realToRCLike_injective`

English:
lemma realToRCLike_injective
  statement: (realToRCLike (X := X) 𝕜).Injective
  proof: .injective realToRCLikeOrderEmbedding X 𝕜

中文:
引理 realToRCLike_injective
  结论: (realToRCLike (X := X) 𝕜).Injective
  证明: .injective realToRCLikeOrderEmbedding X 𝕜
-/
@[simp] lemma realToRCLike_injective : (realToRCLike (X := X) 𝕜).Injective :=
.injective realToRCLikeOrderEmbedding X 𝕜

/--
lemma `realToRCLike_inj` / 引理 `realToRCLike_inj`

English:
lemma realToRCLike_inj
  given: {f g : C(X, Real)}
  proof: .eq_iff_eq realToRCLikeOrderEmbedding X 𝕜

中文:
引理 realToRCLike_inj
  条件: {f g : C(X, 实数)}
  证明: .eq_iff_eq realToRCLikeOrderEmbedding X 𝕜
-/
@[simp] lemma realToRCLike_inj {f g : C(X, Real)} :
    realToRCLike 𝕜 f = realToRCLike 𝕜 g ↔ f = g :=
.eq_iff_eq realToRCLikeOrderEmbedding X 𝕜

/--
lemma `realToRCLike_le_realToRCLike_iff` / 引理 `realToRCLike_le_realToRCLike_iff`

English:
lemma realToRCLike_le_realToRCLike_iff
  given: {f g : C(X, Real)}
  proof: .le_iff_le realToRCLikeOrderEmbedding X 𝕜

中文:
引理 realToRCLike_le_realToRCLike_iff
  条件: {f g : C(X, 实数)}
  证明: .le_iff_le realToRCLikeOrderEmbedding X 𝕜
-/
@[simp] lemma realToRCLike_le_realToRCLike_iff {f g : C(X, Real)} :
    realToRCLike 𝕜 f <= realToRCLike 𝕜 g ↔ f <= g :=
.le_iff_le realToRCLikeOrderEmbedding X 𝕜

/--
lemma `realToRCLike_lt_realToRCLike_iff` / 引理 `realToRCLike_lt_realToRCLike_iff`

English:
lemma realToRCLike_lt_realToRCLike_iff
  given: {f g : C(X, Real)}
  proof: .lt_iff_lt realToRCLikeOrderEmbedding X 𝕜

中文:
引理 realToRCLike_lt_realToRCLike_iff
  条件: {f g : C(X, 实数)}
  证明: .lt_iff_lt realToRCLikeOrderEmbedding X 𝕜
-/
@[simp] lemma realToRCLike_lt_realToRCLike_iff {f g : C(X, Real)} :
    realToRCLike 𝕜 f < realToRCLike 𝕜 g ↔ f < g :=
.lt_iff_lt realToRCLikeOrderEmbedding X 𝕜

variable (X) in
/--
theorem `isometry_realToRCLike` / 定理 `isometry_realToRCLike`

English:
theorem isometry_realToRCLike
  given: [CompactSpace X]
  statement: Isometry (realToRCLike 𝕜 (X := X))
  proof: .of_dist_eq fun f g => by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]

中文:
定理 isometry_realToRCLike
  条件: [CompactSpace X]
  结论: Isometry (realToRCLike 𝕜 (X := X))
  证明: .of_dist_eq fun f g => by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]
-/
@[simp] theorem isometry_realToRCLike [CompactSpace X] : Isometry (realToRCLike 𝕜 (X := X)) :=
  .of_dist_eq fun f g => by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]

variable (X) in
/--
lemma `continuous_realToRCLike` / 引理 `continuous_realToRCLike`

English:
lemma continuous_realToRCLike
  statement: Continuous (realToRCLike 𝕜 (X := X))
  proof: continuous_postcomp { toFun x := RCLike.ofReal x }

中文:
引理 continuous_realToRCLike
  结论: Continuous (realToRCLike 𝕜 (X := X))
  证明: continuous_postcomp { toFun x := RCLike.ofReal x }
-/
@[simp, fun_prop] lemma continuous_realToRCLike : Continuous (realToRCLike 𝕜 (X := X)) :=
  continuous_postcomp { toFun x := RCLike.ofReal x }

variable (X) in
/--
Definition of `realToRCLikeStarAlgHom` / `realToRCLikeStarAlgHom` 的定义

English:
definition realToRCLikeStarAlgHom
  signature: : C(X, Real) ->⋆ₐ[Real] C(X, 𝕜)
  body: compStarAlgHom X (RCLike.ofRealStarAlgHom 𝕜) RCLike.continuous_ofReal

中文:
定义 realToRCLikeStarAlgHom
  签名: : C(X, 实数) ->⋆ₐ[实数] C(X, 𝕜)
  定义体: compStarAlgHom X (RCLike.ofRealStarAlgHom 𝕜) RCLike.continuous_ofReal

Depends on / 依赖: RCLike, RCLike.continuous_ofReal, RCLike.ofRealStarAlgHom, compStarAlgHom, continuous_ofReal, ofRealStarAlgHom
-/
noncomputable def realToRCLikeStarAlgHom : C(X, Real) ->⋆ₐ[Real] C(X, 𝕜) :=
  compStarAlgHom X (RCLike.ofRealStarAlgHom 𝕜) RCLike.continuous_ofReal

/--
lemma `realToRCLikeStarAlgHom_apply` / 引理 `realToRCLikeStarAlgHom_apply`

English:
lemma realToRCLikeStarAlgHom_apply
  given: (f : C(X, Real))
  proof: rfl

中文:
引理 realToRCLikeStarAlgHom_apply
  条件: (f : C(X, 实数))
  证明: rfl
-/
@[simp] lemma realToRCLikeStarAlgHom_apply (f : C(X, Real)) :
    realToRCLikeStarAlgHom X 𝕜 f = f.realToRCLike 𝕜 := rfl

/--
lemma `realToRCLike_star` / 引理 `realToRCLike_star`

English:
lemma realToRCLike_star
  given: (f : C(X, Real))
  statement: (star f).realToRCLike 𝕜 = star (f.realToRCLike 𝕜)
  proof: map_star (realToRCLikeStarAlgHom X 𝕜) f

中文:
引理 realToRCLike_star
  条件: (f : C(X, 实数))
  结论: (star f).realToRCLike 𝕜 = star (f.realToRCLike 𝕜)
  证明: map_star (realToRCLikeStarAlgHom X 𝕜) f

Depends on / 依赖: map_star, realToRCLikeStarAlgHom
-/
lemma realToRCLike_star (f : C(X, Real)) : (star f).realToRCLike 𝕜 = star (f.realToRCLike 𝕜) :=
  map_star (realToRCLikeStarAlgHom X 𝕜) f

/--
lemma `realToRCLike_mul` / 引理 `realToRCLike_mul`

English:
lemma realToRCLike_mul
  given: (f g : C(X, Real))
  proof: map_mul (realToRCLikeStarAlgHom X 𝕜) f g

中文:
引理 realToRCLike_mul
  条件: (f g : C(X, 实数))
  证明: map_mul (realToRCLikeStarAlgHom X 𝕜) f g
-/
@[simp] lemma realToRCLike_mul (f g : C(X, Real)) :
    (f * g).realToRCLike 𝕜 = f.realToRCLike 𝕜 * g.realToRCLike 𝕜 :=
  map_mul (realToRCLikeStarAlgHom X 𝕜) f g

variable {𝕜} in
/--
Definition of `rclikeToReal` / `rclikeToReal` 的定义

English:
definition rclikeToReal
  signature: (f : C(X, 𝕜))
  body: RCLike.re (f x)

中文:
定义 rclikeToReal
  签名: (f : C(X, 𝕜))
  定义体: RCLike.re (f x)
-/
@[simps] def rclikeToReal (f : C(X, 𝕜)) : C(X, Real) where toFun x := RCLike.re (f x)

variable (X) in
/--
lemma `rclikeToReal_monotone` / 引理 `rclikeToReal_monotone`

English:
lemma rclikeToReal_monotone
  statement: Monotone (rclikeToReal (X := X) (𝕜 := 𝕜))
  proof: by
  intro a b; simp_all [le_def, RCLike.le_iff_re_im (K := 𝕜)]

中文:
引理 rclikeToReal_monotone
  结论: Monotone (rclikeTo实数 (X := X) (𝕜 := 𝕜))
  证明: by
  intro a b; simp_all [le_def, RCLike.le_iff_re_im (K := 𝕜)]

Depends on / 依赖: RCLike, RCLike.le_iff_re_im, le_def, le_iff_re_im
-/
lemma rclikeToReal_monotone : Monotone (rclikeToReal (X := X) (𝕜 := 𝕜)) := by
  intro a b; simp_all [le_def, RCLike.le_iff_re_im (K := 𝕜)]

variable (X) in
/--
lemma `continuous_rclikeToReal` / 引理 `continuous_rclikeToReal`

English:
lemma continuous_rclikeToReal
  statement: Continuous (rclikeToReal (X := X) (𝕜 := 𝕜))
  proof: continuous_postcomp { toFun x := RCLike.re x }

中文:
引理 continuous_rclikeToReal
  结论: Continuous (rclikeTo实数 (X := X) (𝕜 := 𝕜))
  证明: continuous_postcomp { toFun x := RCLike.re x }
-/
@[simp, fun_prop] lemma continuous_rclikeToReal : Continuous (rclikeToReal (X := X) (𝕜 := 𝕜)) :=
  continuous_postcomp { toFun x := RCLike.re x }

/--
theorem `rclikeToReal_realToRCLike` / 定理 `rclikeToReal_realToRCLike`

English:
theorem rclikeToReal_realToRCLike
  given: (f : C(X, Real))
  proof: by ext; simp

中文:
定理 rclikeToReal_realToRCLike
  条件: (f : C(X, 实数))
  证明: by ext; simp
-/
@[simp] theorem rclikeToReal_realToRCLike (f : C(X, Real)) :
    (f.realToRCLike 𝕜).rclikeToReal = f := by ext; simp

variable {𝕜} in
@[aesop safe apply, grind =]
/--
theorem `IsSelfAdjoint.realToRCLike_rclikeToReal` / 定理 `IsSelfAdjoint.realToRCLike_rclikeToReal`

English:
theorem IsSelfAdjoint.realToRCLike_rclikeToReal
  given: {f : C(X, 𝕜)} (hf : IsSelfAdjoint f)
  proof: by
  ext
  simp only [realToRCLike_apply, rclikeToReal_apply, ← RCLike.conj_eq_iff_re]
  conv_rhs => rw [← hf.star_eq]
  simp

中文:
定理 IsSelfAdjoint.realToRCLike_rclikeToReal
  条件: {f : C(X, 𝕜)} (hf : IsSelfAdjoint f)
  证明: by
  ext
  simp only [realToRCLike_apply, rclikeToReal_apply, ← RCLike.conj_eq_iff_re]
  conv_rhs => rw [← hf.star_eq]
  simp

Depends on / 依赖: RCLike, RCLike.conj_eq_iff_re, conj_eq_iff_re, conv_rhs, hf.star_eq, rclikeToReal_apply, realToRCLike_apply, star_eq
-/
theorem IsSelfAdjoint.realToRCLike_rclikeToReal {f : C(X, 𝕜)} (hf : IsSelfAdjoint f) :
    f.rclikeToReal.realToRCLike 𝕜 = f := by
  ext
  simp only [realToRCLike_apply, rclikeToReal_apply, ← RCLike.conj_eq_iff_re]
  conv_rhs => rw [← hf.star_eq]
  simp

variable (X) in
open ContinuousMap in
/--
theorem `range_realToRCLike_eq_isSelfAdjoint` / 定理 `range_realToRCLike_eq_isSelfAdjoint`

English:
theorem range_realToRCLike_eq_isSelfAdjoint
  proof: le_antisymm (fun _ ⟨_, h⟩ => by simp [← h]) fun f hf =>
    ⟨f.rclikeToReal, hf.realToRCLike_rclikeToReal⟩

中文:
定理 range_realToRCLike_eq_isSelfAdjoint
  证明: le_antisymm (fun _ ⟨_, h⟩ => by simp [← h]) fun f hf =>
    ⟨f.rclikeToReal, hf.realToRCLike_rclikeToReal⟩

Depends on / 依赖: f.rclikeToReal, hf.realToRCLike_rclikeToReal, le_antisymm, rclikeToReal, realToRCLike_rclikeToReal
-/
theorem range_realToRCLike_eq_isSelfAdjoint :
    .range (realToRCLike 𝕜) = {f : C(X, 𝕜) | IsSelfAdjoint f} :=
  le_antisymm (fun _ ⟨_, h⟩ => by simp [← h]) fun f hf =>
    ⟨f.rclikeToReal, hf.realToRCLike_rclikeToReal⟩

end ContinuousMap
