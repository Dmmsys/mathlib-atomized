/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Lifting bilinear forms to quotients
-/

@[expose] public section

namespace LinearMap

section Asymmetric -- "asymmetric" case of a form `M × N → P`

variable {R R₂ S S₂ M N P : Type*} [Ring R] [Ring R₂] [Ring S] [Ring S₂]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module S N] [Module R₂ P]
    [Module S₂ P] [SMulCommClass R₂ S₂ P] {ρ : R ->+* R₂} {σ : S ->+* S₂}

attribute [local instance] SMulCommClass.symm

/--
Definition of `liftQ₂` / `liftQ₂` 的定义

English:
definition liftQ₂
  signature: (M' : Submodule R M) (N' : Submodule S N) (f : M ->ₛₗ[ρ] N ->ₛₗ[σ] P)
  body: have : forall n in N', n in (M'.liftQ f hM').flip.ker := fun n hn => by
    simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply, Submodule.Quotient.forall,
      Submodule.liftQ_apply, ← f.flip_apply, show f.flip n = 0 from hN' hn, LinearMap.zero_apply,
      forall_true_iff]
  (N'.liftQ (M'.liftQ f hM').flip this).flip

@[simp]

中文:
定义 liftQ₂
  签名: (M' : 子模 R M) (N' : 子模 S N) (f : M ->ₛₗ[ρ] N ->ₛₗ[σ] P)
  定义体: have : forall n in N', n in (M'.liftQ f hM').flip.ker := fun n hn => by
    simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply, Submodule.Quotient.forall,
      Submodule.liftQ_apply, ← f.flip_apply, show f.flip n = 0 from hN' hn, LinearMap.zero_apply,
      forall_true_iff]
  (N'.liftQ (M'.liftQ f hM').flip this).flip

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, LinearMap.flip_apply, LinearMap.mem_ker, LinearMap.zero_apply, Quotient, Submodule, Submodule.Quotient.forall, Submodule.liftQ_apply, ext_iff, f.flip, f.flip_apply, flip.ker, flip_apply, forall_true_iff, liftQ_apply, mem_ker, simp_rw, zero_apply
-/
def liftQ₂ (M' : Submodule R M) (N' : Submodule S N) (f : M ->ₛₗ[ρ] N ->ₛₗ[σ] P)
    (hM' : M' <= f.ker) (hN' : N' <= f.flip.ker) :
    M ⧸ M' ->ₛₗ[ρ] N ⧸ N' ->ₛₗ[σ] P :=
  have : forall n in N', n in (M'.liftQ f hM').flip.ker := fun n hn => by
    simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply, Submodule.Quotient.forall,
      Submodule.liftQ_apply, ← f.flip_apply, show f.flip n = 0 from hN' hn, LinearMap.zero_apply,
      forall_true_iff]
  (N'.liftQ (M'.liftQ f hM').flip this).flip

@[simp]
/--
lemma `liftQ₂_mk` / 引理 `liftQ₂_mk`

English:
lemma liftQ₂_mk
  statement: {M' : Submodule R M} {N' : Submodule S N} {f : M ->ₛₗ[ρ] N ->ₛₗ[σ] P}
  proof: rfl

中文:
引理 liftQ₂_mk
  结论: {M' : 子模 R M} {N' : 子模 S N} {f : M ->ₛₗ[ρ] N ->ₛₗ[σ] P}
  证明: rfl
-/
lemma liftQ₂_mk {M' : Submodule R M} {N' : Submodule S N} {f : M ->ₛₗ[ρ] N ->ₛₗ[σ] P}
    (hM' : M' <= f.ker) (hN' : N' <= f.flip.ker) (m : M) (n : N) :
    f.liftQ₂ M' N' hM' hN' (Submodule.Quotient.mk m) (Submodule.Quotient.mk n) = f m n :=
  rfl

end Asymmetric

section Symmetric -- "symmetric" case of a form `M × M → P`

variable {R S M P : Type*} [AddCommGroup M] [CommRing R] [CommRing S]
    [Module R M] [AddCommGroup P] [Module S P] {I₁ I₂ : R ->+* S}

/--
Definition of `IsRefl.liftQ₂` / `IsRefl.liftQ₂` 的定义

English:
abbreviation IsRefl.liftQ₂
  signature: (f : M ->ₛₗ[I₁] M ->ₛₗ[I₂] P)
  body: f.liftQ₂ N N hN (hf.ker_flip ▸ hN)

中文:
缩写 IsRefl.liftQ₂
  签名: (f : M ->ₛₗ[I₁] M ->ₛₗ[I₂] P)
  定义体: f.liftQ₂ N N hN (hf.ker_flip ▸ hN)

Depends on / 依赖: f.liftQ, hf.ker_flip, ker_flip
-/
abbrev IsRefl.liftQ₂ (f : M ->ₛₗ[I₁] M ->ₛₗ[I₂] P)
    (N : Submodule R M) (hf : f.IsRefl) (hN : N <= f.ker) :
    M ⧸ N ->ₛₗ[I₁] M ⧸ N ->ₛₗ[I₂] P :=
  f.liftQ₂ N N hN (hf.ker_flip ▸ hN)

end Symmetric

end LinearMap
