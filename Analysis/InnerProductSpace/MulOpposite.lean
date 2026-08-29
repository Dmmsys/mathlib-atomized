/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Basis.MulOpposite

/-!
# Inner product space on `Hᵐᵒᵖ`

This file defines the inner product space structure on `Hᵐᵒᵖ` where we define
the inner product naturally. We also define `OrthonormalBasis.mulOpposite`.
-/

@[expose] public section

namespace MulOpposite
variable {𝕜 H : Type*}

open MulOpposite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inner
  signature: 𝕜 H] : Inner 𝕜 Hᵐᵒᵖ where inner x y
  body: inner 𝕜 x.unop y.unop

中文:
实例 [Inner
  签名: 𝕜 H] : Inner 𝕜 Hᵐᵒᵖ where inner x y
  定义体: inner 𝕜 x.unop y.unop

Depends on / 依赖: x.unop, y.unop
-/
instance [Inner 𝕜 H] : Inner 𝕜 Hᵐᵒᵖ where inner x y := inner 𝕜 x.unop y.unop

/--
theorem `inner_unop` / 定理 `inner_unop`

English:
theorem inner_unop
  given: [Inner 𝕜 H] (x y : Hᵐᵒᵖ)
  statement: inner 𝕜 x.unop y.unop = inner 𝕜 x y
  proof: rfl

中文:
定理 inner_unop
  条件: [Inner 𝕜 H] (x y : Hᵐᵒᵖ)
  结论: inner 𝕜 x.unop y.unop = inner 𝕜 x y
  证明: rfl
-/
@[simp] theorem inner_unop [Inner 𝕜 H] (x y : Hᵐᵒᵖ) : inner 𝕜 x.unop y.unop = inner 𝕜 x y := rfl

/--
theorem `inner_op` / 定理 `inner_op`

English:
theorem inner_op
  given: [Inner 𝕜 H] (x y : H)
  statement: inner 𝕜 (op x) (op y) = inner 𝕜 x y
  proof: rfl

中文:
定理 inner_op
  条件: [Inner 𝕜 H] (x y : H)
  结论: inner 𝕜 (op x) (op y) = inner 𝕜 x y
  证明: rfl
-/
@[simp] theorem inner_op [Inner 𝕜 H] (x y : H) : inner 𝕜 (op x) (op y) = inner 𝕜 x y := rfl

section InnerProductSpace
variable [RCLike 𝕜] [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InnerProductSpace 𝕜 Hᵐᵒᵖ
  body: (inner_self_eq_norm_sq x.unop).symm
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.unop y.unop
  add_left x y z := InnerProductSpace.add_left x.unop y.unop z.unop
  smul_left x y r := InnerProductSpace.smul_left x.unop y.unop r

中文:
实例 :
  签名: InnerProductSpace 𝕜 Hᵐᵒᵖ
  定义体: (inner_self_eq_norm_sq x.unop).symm
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.unop y.unop
  add_left x y z := InnerProductSpace.add_left x.unop y.unop z.unop
  smul_left x y r := InnerProductSpace.smul_left x.unop y.unop r

Depends on / 依赖: inner_self_eq_norm_sq, x.unop
-/
instance : InnerProductSpace 𝕜 Hᵐᵒᵖ where
  norm_sq_eq_re_inner x := (inner_self_eq_norm_sq x.unop).symm
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.unop y.unop
  add_left x y z := InnerProductSpace.add_left x.unop y.unop z.unop
  smul_left x y r := InnerProductSpace.smul_left x.unop y.unop r

section orthonormal

/--
theorem `_root_.Module.Basis.mulOpposite_is_orthonormal_iff` / 定理 `_root_.Module.Basis.mulOpposite_is_orthonormal_iff`

English:
theorem _root_.Module.Basis.mulOpposite_is_orthonormal_iff
  given: {ι : Type*} (b : Module.Basis ι 𝕜 H)
  proof: Iff.rfl

中文:
定理 _root_.Module.Basis.mulOpposite_is_orthonormal_iff
  条件: {ι : 类型} (b : Module.Basis ι 𝕜 H)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem _root_.Module.Basis.mulOpposite_is_orthonormal_iff {ι : Type*} (b : Module.Basis ι 𝕜 H) :
    Orthonormal 𝕜 b.mulOpposite ↔ Orthonormal 𝕜 b := Iff.rfl

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Fintype ι]

/--
Definition of `_root_.OrthonormalBasis.mulOpposite` / `_root_.OrthonormalBasis.mulOpposite` 的定义

English:
definition _root_.OrthonormalBasis.mulOpposite
  signature: (b : OrthonormalBasis ι 𝕜 H)
  body: b.toBasis.mulOpposite.toOrthonormalBasis b.orthonormal

中文:
定义 _root_.OrthonormalBasis.mulOpposite
  签名: (b : OrthonormalBasis ι 𝕜 H)
  定义体: b.toBasis.mulOpposite.toOrthonormalBasis b.orthonormal

Depends on / 依赖: b.orthonormal, b.toBasis.mulOpposite.toOrthonormalBasis, mulOpposite, orthonormal, toBasis, toOrthonormalBasis
-/
noncomputable def _root_.OrthonormalBasis.mulOpposite (b : OrthonormalBasis ι 𝕜 H) :
    OrthonormalBasis ι 𝕜 Hᵐᵒᵖ := b.toBasis.mulOpposite.toOrthonormalBasis b.orthonormal

/--
lemma `_root_.OrthonormalBasis.toBasis_mulOpposite` / 引理 `_root_.OrthonormalBasis.toBasis_mulOpposite`

English:
lemma _root_.OrthonormalBasis.toBasis_mulOpposite
  given: (b : OrthonormalBasis ι 𝕜 H)
  proof: rfl

中文:
引理 _root_.OrthonormalBasis.toBasis_mulOpposite
  条件: (b : OrthonormalBasis ι 𝕜 H)
  证明: rfl
-/
@[simp] lemma _root_.OrthonormalBasis.toBasis_mulOpposite (b : OrthonormalBasis ι 𝕜 H) :
    b.mulOpposite.toBasis = b.toBasis.mulOpposite := rfl

end orthonormal

end InnerProductSpace

end MulOpposite
