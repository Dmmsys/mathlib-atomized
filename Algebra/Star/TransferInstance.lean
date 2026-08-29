/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Ring.TransferInstance

/-! # Transfer star (algebraic) structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

variable {R S : Type*}

@[expose] public section

namespace Equiv

variable (e : R ≃ S)

-- See note [instance transfer via equivalence]
/--
Definition of `star` / `star` 的定义

English:
abbreviation star
  signature: [Star S]
  body: e.invFun (star (e.toFun r))

中文:
缩写 star
  签名: [对合 S]
  定义体: e.invFun (star (e.toFun r))
-/
protected abbrev star [Star S] : Star R where
  star r := e.invFun (star (e.toFun r))

/--
Definition of `involutiveStar` / `involutiveStar` 的定义

English:
abbreviation involutiveStar
  signature: [InvolutiveStar S]
  body: let _ := e.star
  e.injective.involutiveStar _ fun _ => e.apply_symm_apply _

中文:
缩写 involutiveStar
  签名: [InvolutiveStar S]
  定义体: let _ := e.star
  e.injective.involutiveStar _ fun _ => e.apply_symm_apply _
-/
protected abbrev involutiveStar [InvolutiveStar S] : InvolutiveStar R :=
  let _ := e.star
  e.injective.involutiveStar _ fun _ => e.apply_symm_apply _

/--
Definition of `starMul` / `starMul` 的定义

English:
abbreviation starMul
  signature: [Mul S] [StarMul S]
  body: e.mul
    StarMul R := by
  let := e.star
  let := e.mul
  apply e.injective.starMul <;> (intros; exact e.apply_symm_apply _)

中文:
缩写 starMul
  签名: [乘法 S] [StarMul S]
  定义体: e.mul
    StarMul R := by
  let := e.star
  let := e.mul
  apply e.injective.starMul <;> (intros; exact e.apply_symm_apply _)
-/
protected abbrev starMul [Mul S] [StarMul S] :
    letI := e.mul
    StarMul R := by
  let := e.star
  let := e.mul
  apply e.injective.starMul <;> (intros; exact e.apply_symm_apply _)

/--
Definition of `starAddMonoid` / `starAddMonoid` 的定义

English:
abbreviation starAddMonoid
  signature: [AddMonoid S] [StarAddMonoid S]
  body: e.addMonoid
    StarAddMonoid R := by
  let := e.star
  let := e.addMonoid
  apply e.injective.starAddMonoid <;> (intros; exact e.apply_symm_apply _)

中文:
缩写 starAddMonoid
  签名: [加法幺半群 S] [StarAdd幺半群 S]
  定义体: e.addMonoid
    StarAddMonoid R := by
  let := e.star
  let := e.addMonoid
  apply e.injective.starAddMonoid <;> (intros; exact e.apply_symm_apply _)
-/
protected abbrev starAddMonoid [AddMonoid S] [StarAddMonoid S] :
    letI := e.addMonoid
    StarAddMonoid R := by
  let := e.star
  let := e.addMonoid
  apply e.injective.starAddMonoid <;> (intros; exact e.apply_symm_apply _)

/--
Definition of `starRing` / `starRing` 的定义

English:
abbreviation starRing
  signature: [NonUnitalNonAssocSemiring S] [StarRing S]
  body: e.nonUnitalNonAssocSemiring
    StarRing R := by
  let := e.star
  let := e.nonUnitalNonAssocSemiring
  apply e.injective.starRing <;> (intros; exact e.apply_symm_apply _)

中文:
缩写 starRing
  签名: [非幺非结合半环 S] [对合环 S]
  定义体: e.nonUnitalNonAssocSemiring
    StarRing R := by
  let := e.star
  let := e.nonUnitalNonAssocSemiring
  apply e.injective.starRing <;> (intros; exact e.apply_symm_apply _)
-/
protected abbrev starRing [NonUnitalNonAssocSemiring S] [StarRing S] :
    letI := e.nonUnitalNonAssocSemiring
    StarRing R := by
  let := e.star
  let := e.nonUnitalNonAssocSemiring
  apply e.injective.starRing <;> (intros; exact e.apply_symm_apply _)

/--
lemma `starModule` / 引理 `starModule`

English:
lemma starModule
  statement: (𝕜 : Type*)
  proof: e.star
    letI := e.smul 𝕜
    StarModule 𝕜 R := by
  let := e.star
  let := e.smul 𝕜
  apply e.injective.starModule _ 𝕜 <;> (intros; exact e.apply_symm_apply _)

中文:
引理 starModule
  结论: (𝕜 : 类型)
  证明: e.star
    letI := e.smul 𝕜
    StarModule 𝕜 R := by
  let := e.star
  let := e.smul 𝕜
  apply e.injective.starModule _ 𝕜 <;> (intros; exact e.apply_symm_apply _)
-/
protected lemma starModule (𝕜 : Type*)
    [Star 𝕜] [Star S] [SMul 𝕜 S] [StarModule 𝕜 S] :
    letI := e.star
    letI := e.smul 𝕜
    StarModule 𝕜 R := by
  let := e.star
  let := e.smul 𝕜
  apply e.injective.starModule _ 𝕜 <;> (intros; exact e.apply_symm_apply _)

end Equiv
