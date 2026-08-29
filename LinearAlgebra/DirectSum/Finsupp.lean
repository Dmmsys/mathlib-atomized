/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Results on finitely supported functions.

* `TensorProduct.finsuppLeft`, the tensor product of `ι →₀ M` and `N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarLeft`, the tensor product of `ι →₀ R` and `N`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppRight`, the tensor product of `M` and `ι →₀ N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarRight`, the tensor product of `M` and `ι →₀ R`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppLeft'`, if `M` is an `S`-module,
  then the tensor product of `ι →₀ M` and `N` is `S`-linearly equivalent
  to `ι →₀ M ⊗[R] N`

* `finsuppTensorFinsupp`, the tensor product of `ι →₀ M` and `κ →₀ N`
  is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`.

-/

@[expose] public section


noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

section TensorProduct

variable (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (N : Type*) [AddCommMonoid N] [Module R N]

namespace TensorProduct

variable (ι : Type*) [DecidableEq ι]

/--
Definition of `finsuppLeft` / `finsuppLeft` 的定义

English:
definition finsuppLeft
  signature: :
  body: AlgebraTensorModule.congr (finsuppLEquivDirectSum S M ι) (.refl R N) ≪≫ₗ
    directSumLeft _ S (fun _ => M) N ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

中文:
定义 finsuppLeft
  签名: :
  定义体: AlgebraTensorModule.congr (finsuppLEquivDirectSum S M ι) (.refl R N) ≪≫ₗ
    directSumLeft _ S (fun _ => M) N ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.congr, directSumLeft, finsuppLEquivDirectSum
-/
noncomputable def finsuppLeft :
    (ι ->₀ M) otimes[R] N ≃ₗ[S] ι ->₀ M otimes[R] N :=
  AlgebraTensorModule.congr (finsuppLEquivDirectSum S M ι) (.refl R N) ≪≫ₗ
    directSumLeft _ S (fun _ => M) N ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

variable {R S M N ι}

/--
lemma `finsuppLeft_apply_tmul` / 引理 `finsuppLeft_apply_tmul`

English:
lemma finsuppLeft_apply_tmul
  given: (p : ι ->₀ M) (n : N)
  proof: by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_tmul, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppLeft]

@[simp]

中文:
引理 finsuppLeft_apply_tmul
  条件: (p : ι ->₀ M) (n : N)
  证明: by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_tmul, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppLeft]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.induction_linear, Finsupp.sum_add_index, add_tmul, finsuppLeft, induction_linear, map_add, single, sum_add_index
-/
lemma finsuppLeft_apply_tmul (p : ι ->₀ M) (n : N) :
    finsuppLeft R S M N ι (p otimesₜ[R] n) = p.sum fun i m => Finsupp.single i (m otimesₜ[R] n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_tmul, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppLeft]

@[simp]
/--
lemma `finsuppLeft_apply_tmul_apply` / 引理 `finsuppLeft_apply_tmul_apply`

English:
lemma finsuppLeft_apply_tmul_apply
  given: (p : ι ->₀ M) (n : N) (i : ι)
  proof: by
  rw [finsuppLeft_apply_tmul]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

中文:
引理 finsuppLeft_apply_tmul_apply
  条件: (p : ι ->₀ M) (n : N) (i : ι)
  证明: by
  rw [finsuppLeft_apply_tmul]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

Depends on / 依赖: Finsupp, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, Finsupp.sum_apply, Finsupp.sum_eq_single, finsuppLeft_apply_tmul, single_eq_of_ne, single_eq_same, sum_apply, sum_eq_single
-/
lemma finsuppLeft_apply_tmul_apply (p : ι ->₀ M) (n : N) (i : ι) :
    finsuppLeft R S M N ι (p otimesₜ[R] n) i = p i otimesₜ[R] n := by
  rw [finsuppLeft_apply_tmul]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

/--
theorem `finsuppLeft_apply` / 定理 `finsuppLeft_apply`

English:
theorem finsuppLeft_apply
  given: (t : (ι ->₀ M) otimes[R] N) (i : ι)
  proof: by
  induction t with
  | zero => simp
  | tmul f n => simp only [finsuppLeft_apply_tmul_apply, rTensor_tmul, Finsupp.lapply_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]

中文:
定理 finsuppLeft_apply
  条件: (t : (ι ->₀ M) otimes[R] N) (i : ι)
  证明: by
  induction t with
  | zero => simp
  | tmul f n => simp only [finsuppLeft_apply_tmul_apply, rTensor_tmul, Finsupp.lapply_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.lapply_apply, finsuppLeft_apply_tmul_apply, lapply_apply, map_add, rTensor_tmul
-/
theorem finsuppLeft_apply (t : (ι ->₀ M) otimes[R] N) (i : ι) :
    finsuppLeft R S M N ι t i = rTensor N (Finsupp.lapply i) t := by
  induction t with
  | zero => simp
  | tmul f n => simp only [finsuppLeft_apply_tmul_apply, rTensor_tmul, Finsupp.lapply_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
/--
lemma `finsuppLeft_symm_apply_single` / 引理 `finsuppLeft_symm_apply_single`

English:
lemma finsuppLeft_symm_apply_single
  given: (i : ι) (m : M) (n : N)
  proof: by
  simp [finsuppLeft]

中文:
引理 finsuppLeft_symm_apply_single
  条件: (i : ι) (m : M) (n : N)
  证明: by
  simp [finsuppLeft]

Depends on / 依赖: finsuppLeft
-/
lemma finsuppLeft_symm_apply_single (i : ι) (m : M) (n : N) :
    (finsuppLeft R S M N ι).symm (Finsupp.single i (m otimesₜ[R] n)) =
      Finsupp.single i m otimesₜ[R] n := by
  simp [finsuppLeft]

variable (R S M N ι) in
/--
Definition of `finsuppRight` / `finsuppRight` 的定义

English:
definition finsuppRight
  signature: :
  body: AlgebraTensorModule.congr (.refl S M) (finsuppLEquivDirectSum R N ι) ≪≫ₗ
    directSumRight R S M (fun _ : ι => N) ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

中文:
定义 finsuppRight
  签名: :
  定义体: AlgebraTensorModule.congr (.refl S M) (finsuppLEquivDirectSum R N ι) ≪≫ₗ
    directSumRight R S M (fun _ : ι => N) ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.congr, directSumRight, finsuppLEquivDirectSum
-/
noncomputable def finsuppRight :
    M otimes[R] (ι ->₀ N) ≃ₗ[S] ι ->₀ M otimes[R] N :=
  AlgebraTensorModule.congr (.refl S M) (finsuppLEquivDirectSum R N ι) ≪≫ₗ
    directSumRight R S M (fun _ : ι => N) ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

/--
lemma `finsuppRight_apply_tmul` / 引理 `finsuppRight_apply_tmul`

English:
lemma finsuppRight_apply_tmul
  given: (m : M) (p : ι ->₀ N)
  proof: by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [tmul_add, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppRight]

@[simp]

中文:
引理 finsuppRight_apply_tmul
  条件: (m : M) (p : ι ->₀ N)
  证明: by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [tmul_add, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppRight]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.induction_linear, Finsupp.sum_add_index, finsuppRight, induction_linear, map_add, single, sum_add_index, tmul_add
-/
lemma finsuppRight_apply_tmul (m : M) (p : ι ->₀ N) :
    finsuppRight R S M N ι (m otimesₜ[R] p) = p.sum fun i n => Finsupp.single i (m otimesₜ[R] n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [tmul_add, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppRight]

@[simp]
/--
lemma `finsuppRight_apply_tmul_apply` / 引理 `finsuppRight_apply_tmul_apply`

English:
lemma finsuppRight_apply_tmul_apply
  given: (m : M) (p : ι ->₀ N) (i : ι)
  proof: by
  rw [finsuppRight_apply_tmul]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

中文:
引理 finsuppRight_apply_tmul_apply
  条件: (m : M) (p : ι ->₀ N) (i : ι)
  证明: by
  rw [finsuppRight_apply_tmul]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

Depends on / 依赖: Finsupp, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, Finsupp.sum_apply, Finsupp.sum_eq_single, finsuppRight_apply_tmul, single_eq_of_ne, single_eq_same, sum_apply, sum_eq_single
-/
lemma finsuppRight_apply_tmul_apply (m : M) (p : ι ->₀ N) (i : ι) :
    finsuppRight R S M N ι (m otimesₜ[R] p) i = m otimesₜ[R] p i := by
  rw [finsuppRight_apply_tmul]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

/--
theorem `finsuppRight_apply` / 定理 `finsuppRight_apply`

English:
theorem finsuppRight_apply
  given: (t : M otimes[R] (ι ->₀ N)) (i : ι)
  proof: by
  induction t with
  | zero => simp
  | tmul m f => simp [finsuppRight_apply_tmul_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]

中文:
定理 finsuppRight_apply
  条件: (t : M otimes[R] (ι ->₀ N)) (i : ι)
  证明: by
  induction t with
  | zero => simp
  | tmul m f => simp [finsuppRight_apply_tmul_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]

Depends on / 依赖: finsuppRight_apply_tmul_apply, map_add
-/
theorem finsuppRight_apply (t : M otimes[R] (ι ->₀ N)) (i : ι) :
    finsuppRight R S M N ι t i = lTensor M (Finsupp.lapply i) t := by
  induction t with
  | zero => simp
  | tmul m f => simp [finsuppRight_apply_tmul_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
/--
lemma `finsuppRight_tmul_single` / 引理 `finsuppRight_tmul_single`

English:
lemma finsuppRight_tmul_single
  given: (i : ι) (m : M) (n : N)
  proof: by
  ext; simp +contextual [Finsupp.single_apply, apply_ite]

@[simp]

中文:
引理 finsuppRight_tmul_single
  条件: (i : ι) (m : M) (n : N)
  证明: by
  ext; simp +contextual [Finsupp.single_apply, apply_ite]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, apply_ite, contextual, single_apply
-/
lemma finsuppRight_tmul_single (i : ι) (m : M) (n : N) :
    finsuppRight R S M N ι (m otimesₜ[R] Finsupp.single i n) = Finsupp.single i (m otimesₜ[R] n) := by
  ext; simp +contextual [Finsupp.single_apply, apply_ite]

@[simp]
/--
lemma `finsuppRight_symm_apply_single` / 引理 `finsuppRight_symm_apply_single`

English:
lemma finsuppRight_symm_apply_single
  given: (i : ι) (m : M) (n : N)
  proof: by
  simp [LinearEquiv.symm_apply_eq]

中文:
引理 finsuppRight_symm_apply_single
  条件: (i : ι) (m : M) (n : N)
  证明: by
  simp [LinearEquiv.symm_apply_eq]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
lemma finsuppRight_symm_apply_single (i : ι) (m : M) (n : N) :
    (finsuppRight R S M N ι).symm (Finsupp.single i (m otimesₜ[R] n)) =
      m otimesₜ[R] Finsupp.single i n := by
  simp [LinearEquiv.symm_apply_eq]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `finsuppLeft_smul'` / 引理 `finsuppLeft_smul'`

English:
lemma finsuppLeft_smul'
  given: (s : S) (t : (ι ->₀ M) otimes[R] N)
  proof: by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppLeft' := finsuppLeft

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]

中文:
引理 finsuppLeft_smul'
  条件: (s : S) (t : (ι ->₀ M) otimes[R] N)
  证明: by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppLeft' := finsuppLeft

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
-/
lemma finsuppLeft_smul' (s : S) (t : (ι ->₀ M) otimes[R] N) :
    finsuppLeft R S M N ι (s • t) = s • finsuppLeft R S M N ι t := by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppLeft' := finsuppLeft

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
/--
lemma `finsuppLeft'_apply` / 引理 `finsuppLeft'_apply`

English:
lemma finsuppLeft'_apply
  given: (x : (ι ->₀ M) otimes[R] N)
  proof: rfl

中文:
引理 finsuppLeft'_apply
  条件: (x : (ι ->₀ M) otimes[R] N)
  证明: rfl
-/
lemma finsuppLeft'_apply (x : (ι ->₀ M) otimes[R] N) :
    finsuppLeft R S M N ι x = finsuppLeft R S M N ι x := rfl

variable (R M N ι) in
/--
Definition of `finsuppScalarLeft` / `finsuppScalarLeft` 的定义

English:
definition finsuppScalarLeft
  signature: :
  body: finsuppLeft R R R N ι ≪≫ₗ (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))

@[simp]

中文:
定义 finsuppScalarLeft
  签名: :
  定义体: finsuppLeft R R R N ι ≪≫ₗ (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearEquiv, TensorProduct, TensorProduct.lid, finsuppLeft, linearEquiv, mapRange
-/
noncomputable def finsuppScalarLeft :
    (ι ->₀ R) otimes[R] N ≃ₗ[R] ι ->₀ N :=
  finsuppLeft R R R N ι ≪≫ₗ (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))

@[simp]
/--
lemma `finsuppScalarLeft_apply_tmul_apply` / 引理 `finsuppScalarLeft_apply_tmul_apply`

English:
lemma finsuppScalarLeft_apply_tmul_apply
  given: (p : ι ->₀ R) (n : N) (i : ι)
  proof: by
  simp [finsuppScalarLeft]

中文:
引理 finsuppScalarLeft_apply_tmul_apply
  条件: (p : ι ->₀ R) (n : N) (i : ι)
  证明: by
  simp [finsuppScalarLeft]

Depends on / 依赖: finsuppScalarLeft
-/
lemma finsuppScalarLeft_apply_tmul_apply (p : ι ->₀ R) (n : N) (i : ι) :
    finsuppScalarLeft R N ι (p otimesₜ[R] n) i = p i • n := by
  simp [finsuppScalarLeft]

/--
lemma `finsuppScalarLeft_apply_tmul` / 引理 `finsuppScalarLeft_apply_tmul`

English:
lemma finsuppScalarLeft_apply_tmul
  given: (p : ι ->₀ R) (n : N)
  proof: by
  ext i
  rw [finsuppScalarLeft_apply_tmul_apply]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

中文:
引理 finsuppScalarLeft_apply_tmul
  条件: (p : ι ->₀ R) (n : N)
  证明: by
  ext i
  rw [finsuppScalarLeft_apply_tmul_apply]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

Depends on / 依赖: Finsupp, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, Finsupp.sum_apply, Finsupp.sum_eq_single, finsuppScalarLeft_apply_tmul_apply, single_eq_of_ne, single_eq_same, sum_apply, sum_eq_single
-/
lemma finsuppScalarLeft_apply_tmul (p : ι ->₀ R) (n : N) :
    finsuppScalarLeft R N ι (p otimesₜ[R] n) = p.sum fun i m => Finsupp.single i (m • n) := by
  ext i
  rw [finsuppScalarLeft_apply_tmul_apply]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

/--
lemma `finsuppScalarLeft_apply` / 引理 `finsuppScalarLeft_apply`

English:
lemma finsuppScalarLeft_apply
  given: (pn : (ι ->₀ R) otimes[R] N) (i : ι)
  proof: by
  simp [finsuppScalarLeft, finsuppLeft_apply]

@[simp]

中文:
引理 finsuppScalarLeft_apply
  条件: (pn : (ι ->₀ R) otimes[R] N) (i : ι)
  证明: by
  simp [finsuppScalarLeft, finsuppLeft_apply]

@[simp]

Depends on / 依赖: _eq_lintegral_enorm, eLpNorm, finsuppLeft_apply, finsuppScalarLeft
-/
lemma finsuppScalarLeft_apply (pn : (ι ->₀ R) otimes[R] N) (i : ι) :
    finsuppScalarLeft R N ι pn i = TensorProduct.lid R N ((Finsupp.lapply i).rTensor N pn) := by
  simp [finsuppScalarLeft, finsuppLeft_apply]

@[simp]
/--
lemma `finsuppScalarLeft_symm_apply_single` / 引理 `finsuppScalarLeft_symm_apply_single`

English:
lemma finsuppScalarLeft_symm_apply_single
  given: (i : ι) (n : N)
  proof: by
  simp [finsuppScalarLeft, finsuppLeft_symm_apply_single]

中文:
引理 finsuppScalarLeft_symm_apply_single
  条件: (i : ι) (n : N)
  证明: by
  simp [finsuppScalarLeft, finsuppLeft_symm_apply_single]

Depends on / 依赖: _eq_lintegral_enorm, eLpNorm, finsuppLeft_symm_apply_single, finsuppScalarLeft
-/
lemma finsuppScalarLeft_symm_apply_single (i : ι) (n : N) :
    (finsuppScalarLeft R N ι).symm (Finsupp.single i n) =
      (Finsupp.single i 1) otimesₜ[R] n := by
  simp [finsuppScalarLeft, finsuppLeft_symm_apply_single]

variable (R S M N ι) in
/--
Definition of `finsuppScalarRight` / `finsuppScalarRight` 的定义

English:
definition finsuppScalarRight
  signature: :
  body: finsuppRight R S M R ι ≪≫ₗ Finsupp.mapRange.linearEquiv (AlgebraTensorModule.rid R S M)

@[simp]

中文:
定义 finsuppScalarRight
  签名: :
  定义体: finsuppRight R S M R ι ≪≫ₗ Finsupp.mapRange.linearEquiv (AlgebraTensorModule.rid R S M)

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.rid, Finsupp, Finsupp.mapRange.linearEquiv, finsuppRight, linearEquiv, mapRange
-/
noncomputable def finsuppScalarRight :
    M otimes[R] (ι ->₀ R) ≃ₗ[S] ι ->₀ M :=
  finsuppRight R S M R ι ≪≫ₗ Finsupp.mapRange.linearEquiv (AlgebraTensorModule.rid R S M)

@[simp]
/--
lemma `finsuppScalarRight_apply_tmul_apply` / 引理 `finsuppScalarRight_apply_tmul_apply`

English:
lemma finsuppScalarRight_apply_tmul_apply
  given: (m : M) (p : ι ->₀ R) (i : ι)
  proof: by
  simp [finsuppScalarRight]

中文:
引理 finsuppScalarRight_apply_tmul_apply
  条件: (m : M) (p : ι ->₀ R) (i : ι)
  证明: by
  simp [finsuppScalarRight]

Depends on / 依赖: finsuppScalarRight
-/
lemma finsuppScalarRight_apply_tmul_apply (m : M) (p : ι ->₀ R) (i : ι) :
    finsuppScalarRight R S M ι (m otimesₜ[R] p) i = p i • m := by
  simp [finsuppScalarRight]

/--
lemma `finsuppScalarRight_apply_tmul` / 引理 `finsuppScalarRight_apply_tmul`

English:
lemma finsuppScalarRight_apply_tmul
  given: (m : M) (p : ι ->₀ R)
  proof: by
  ext i
  rw [finsuppScalarRight_apply_tmul_apply]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

中文:
引理 finsuppScalarRight_apply_tmul
  条件: (m : M) (p : ι ->₀ R)
  证明: by
  ext i
  rw [finsuppScalarRight_apply_tmul_apply]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

Depends on / 依赖: ENNReal, ENNReal.rpow_mul, Finsupp, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, Finsupp.sum_apply, Finsupp.sum_eq_single, eLpNorm, enorm_eq_self, finsuppScalarRight_apply_tmul_apply, hq_pos, hq_pos.ne.symm, mul_assoc, mul_comm, mul_one, one_div, one_div_mul_one_div, rpow_mul, simp_rw, single_eq_of_ne
-/
lemma finsuppScalarRight_apply_tmul (m : M) (p : ι ->₀ R) :
    finsuppScalarRight R S M ι (m otimesₜ[R] p) = p.sum fun i n => Finsupp.single i (n • m) := by
  ext i
  rw [finsuppScalarRight_apply_tmul_apply]; rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne') (by simp)]; rw [Finsupp.single_eq_same]

/--
lemma `finsuppScalarRight_apply` / 引理 `finsuppScalarRight_apply`

English:
lemma finsuppScalarRight_apply
  given: (t : M otimes[R] (ι ->₀ R)) (i : ι)
  proof: by
  simp [finsuppScalarRight, finsuppRight_apply]

@[simp]

中文:
引理 finsuppScalarRight_apply
  条件: (t : M otimes[R] (ι ->₀ R)) (i : ι)
  证明: by
  simp [finsuppScalarRight, finsuppRight_apply]

@[simp]

Depends on / 依赖: finsuppRight_apply, finsuppScalarRight
-/
lemma finsuppScalarRight_apply (t : M otimes[R] (ι ->₀ R)) (i : ι) :
    finsuppScalarRight R S M ι t i =
      AlgebraTensorModule.rid R S M ((Finsupp.lapply i).lTensor M t) := by
  simp [finsuppScalarRight, finsuppRight_apply]

@[simp]
/--
lemma `finsuppScalarRight_symm_apply_single` / 引理 `finsuppScalarRight_symm_apply_single`

English:
lemma finsuppScalarRight_symm_apply_single
  given: (i : ι) (m : M)
  proof: by
  simp [finsuppScalarRight, finsuppRight_symm_apply_single]

中文:
引理 finsuppScalarRight_symm_apply_single
  条件: (i : ι) (m : M)
  证明: by
  simp [finsuppScalarRight, finsuppRight_symm_apply_single]

Depends on / 依赖: ENNReal, ENNReal.ofReal_rpow_of_nonneg, ENNReal.rpow_mul, Real.norm_eq_abs, Real.rpow_nonneg, abs_eq_self, abs_eq_self.mpr, eLpNorm, finsuppRight_symm_apply_single, finsuppScalarRight, hq_pos, hq_pos.le, hq_pos.ne.symm, mul_assoc, mul_comm, mul_one, norm_eq_abs, norm_nonneg, ofReal_norm, ofReal_rpow_of_nonneg
-/
lemma finsuppScalarRight_symm_apply_single (i : ι) (m : M) :
    (finsuppScalarRight R S M ι).symm (Finsupp.single i m) =
      m otimesₜ[R] (Finsupp.single i 1) := by
  simp [finsuppScalarRight, finsuppRight_symm_apply_single]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finsuppScalarRight_smul` / 定理 `finsuppScalarRight_smul`

English:
theorem finsuppScalarRight_smul
  given: (s : S) (t)
  proof: by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppScalarRight' := finsuppScalarRight

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]

中文:
定理 finsuppScalarRight_smul
  条件: (s : S) (t)
  证明: by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppScalarRight' := finsuppScalarRight

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
-/
theorem finsuppScalarRight_smul (s : S) (t) :
    finsuppScalarRight R S M ι (s • t) = s • finsuppScalarRight R S M ι t := by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppScalarRight' := finsuppScalarRight

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
/--
theorem `coe_finsuppScalarRight'` / 定理 `coe_finsuppScalarRight'`

English:
theorem coe_finsuppScalarRight'
  proof: rfl

中文:
定理 coe_finsuppScalarRight'
  证明: rfl
-/
theorem coe_finsuppScalarRight' :
    ⇑(finsuppScalarRight R S M ι) = finsuppScalarRight R S M ι :=
  rfl

end TensorProduct

end TensorProduct

variable (R S M N ι κ : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [Semiring S] [Algebra R S]

/--
theorem `Finsupp.linearCombination_one_tmul` / 定理 `Finsupp.linearCombination_one_tmul`

English:
theorem Finsupp.linearCombination_one_tmul
  given: [DecidableEq ι] {v : ι -> M}
  proof: by
  ext; simp [smul_tmul']

中文:
定理 有限支撑.linearCombination_one_tmul
  条件: [DecidableEq ι] {v : ι -> M}
  证明: by
  ext; simp [smul_tmul']

Depends on / 依赖: smul_tmul
-/
theorem Finsupp.linearCombination_one_tmul [DecidableEq ι] {v : ι -> M} :
    (linearCombination S ((1 : S) otimesₜ[R] v ·)).restrictScalars R =
      (linearCombination R v).lTensor S ∘ₗ (finsuppScalarRight R R S ι).symm := by
  ext; simp [smul_tmul']

variable [Module S M] [IsScalarTower R S M]

open scoped Classical in
/--
Definition of `finsuppTensorFinsupp` / `finsuppTensorFinsupp` 的定义

English:
definition finsuppTensorFinsupp
  signature: : (ι ->₀ M) otimes[R] (κ ->₀ N) ≃ₗ[S] ι × κ ->₀ M otimes[R] N
  body: TensorProduct.AlgebraTensorModule.congr
    (finsuppLEquivDirectSum S M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R S (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum S (M otimes[R] N) (ι × κ)).symm)

@[simp]

中文:
定义 finsuppTensorFinsupp
  签名: : (ι ->₀ M) otimes[R] (κ ->₀ N) ≃ₗ[S] ι × κ ->₀ M otimes[R] N
  定义体: TensorProduct.AlgebraTensorModule.congr
    (finsuppLEquivDirectSum S M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R S (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum S (M otimes[R] N) (ι × κ)).symm)

@[simp]

Depends on / 依赖: AlgebraTensorModule, TensorProduct, TensorProduct.AlgebraTensorModule.congr, TensorProduct.directSum, directSum, finsuppLEquivDirectSum, otimes
-/
def finsuppTensorFinsupp : (ι ->₀ M) otimes[R] (κ ->₀ N) ≃ₗ[S] ι × κ ->₀ M otimes[R] N :=
  TensorProduct.AlgebraTensorModule.congr
    (finsuppLEquivDirectSum S M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R S (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum S (M otimes[R] N) (ι × κ)).symm)

@[simp]
/--
theorem `finsuppTensorFinsupp_single` / 定理 `finsuppTensorFinsupp_single`

English:
theorem finsuppTensorFinsupp_single
  given: (i : ι) (m : M) (k : κ) (n : N)
  proof: by
  simp [finsuppTensorFinsupp]

@[simp]

中文:
定理 finsuppTensorFinsupp_single
  条件: (i : ι) (m : M) (k : κ) (n : N)
  证明: by
  simp [finsuppTensorFinsupp]

@[simp]

Depends on / 依赖: finsuppTensorFinsupp
-/
theorem finsuppTensorFinsupp_single (i : ι) (m : M) (k : κ) (n : N) :
    finsuppTensorFinsupp R S M N ι κ (Finsupp.single i m otimesₜ Finsupp.single k n) =
      Finsupp.single (i, k) (m otimesₜ n) := by
  simp [finsuppTensorFinsupp]

@[simp]
/--
theorem `finsuppTensorFinsupp_apply` / 定理 `finsuppTensorFinsupp_apply`

English:
theorem finsuppTensorFinsupp_apply
  given: (f : ι ->₀ M) (g : κ ->₀ N) (i : ι) (k : κ)
  proof: by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp [add_tmul, hf₁, hf₂]
  | single i' m =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ hg₁ hg₂ => simp [tmul_add, hg₁, hg₂]
    | single k' n =>
      classical
      simp_rw [finsuppTensorFinsupp_single, Finsupp.single_apply, Prod.mk_inj, ite_and]
      split_ifs <;> simp

@[simp]

中文:
定理 finsuppTensorFinsupp_apply
  条件: (f : ι ->₀ M) (g : κ ->₀ N) (i : ι) (k : κ)
  证明: by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp [add_tmul, hf₁, hf₂]
  | single i' m =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ hg₁ hg₂ => simp [tmul_add, hg₁, hg₂]
    | single k' n =>
      classical
      simp_rw [finsuppTensorFinsupp_single, Finsupp.single_apply, Prod.mk_inj, ite_and]
      split_ifs <;> simp

@[simp]

Depends on / 依赖: Finsupp, Finsupp.induction_linear, Finsupp.single_apply, Prod.mk_inj, add_tmul, classical, finsuppTensorFinsupp_single, induction_linear, ite_and, mk_inj, simp_rw, single, single_apply, split_ifs, tmul_add
-/
theorem finsuppTensorFinsupp_apply (f : ι ->₀ M) (g : κ ->₀ N) (i : ι) (k : κ) :
    finsuppTensorFinsupp R S M N ι κ (f otimesₜ g) (i, k) = f i otimesₜ g k := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp [add_tmul, hf₁, hf₂]
  | single i' m =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ hg₁ hg₂ => simp [tmul_add, hg₁, hg₂]
    | single k' n =>
      classical
      simp_rw [finsuppTensorFinsupp_single, Finsupp.single_apply, Prod.mk_inj, ite_and]
      split_ifs <;> simp

@[simp]
/--
theorem `finsuppTensorFinsupp_symm_single` / 定理 `finsuppTensorFinsupp_symm_single`

English:
theorem finsuppTensorFinsupp_symm_single
  given: (i : ι × κ) (m : M) (n : N)
  proof: Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _ _).symm

中文:
定理 finsuppTensorFinsupp_symm_single
  条件: (i : ι × κ) (m : M) (n : N)
  证明: Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _ _).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, Prod.casesOn, casesOn, finsuppTensorFinsupp_single, symm_apply_eq
-/
theorem finsuppTensorFinsupp_symm_single (i : ι × κ) (m : M) (n : N) :
    (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single i (m otimesₜ n)) =
      Finsupp.single i.1 m otimesₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _ _).symm

/--
Definition of `finsuppTensorFinsuppLid` / `finsuppTensorFinsuppLid` 的定义

English:
definition finsuppTensorFinsuppLid
  signature: : (ι ->₀ R) otimes[R] (κ ->₀ N) ≃ₗ[R] ι × κ ->₀ N
  body: finsuppTensorFinsupp R R R N ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R N)

@[simp]

中文:
定义 finsuppTensorFinsuppLid
  签名: : (ι ->₀ R) otimes[R] (κ ->₀ N) ≃ₗ[R] ι × κ ->₀ N
  定义体: finsuppTensorFinsupp R R R N ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R N)

@[simp]

Depends on / 依赖: Equiv.refl, Finsupp, Finsupp.lcongr, TensorProduct, TensorProduct.lid, finsuppTensorFinsupp, lcongr
-/
def finsuppTensorFinsuppLid : (ι ->₀ R) otimes[R] (κ ->₀ N) ≃ₗ[R] ι × κ ->₀ N :=
  finsuppTensorFinsupp R R R N ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R N)

@[simp]
/--
theorem `finsuppTensorFinsuppLid_apply_apply` / 定理 `finsuppTensorFinsuppLid_apply_apply`

English:
theorem finsuppTensorFinsuppLid_apply_apply
  given: (f : ι ->₀ R) (g : κ ->₀ N) (a : ι) (b : κ)
  proof: by
  simp [finsuppTensorFinsuppLid]

@[simp]

中文:
定理 finsuppTensorFinsuppLid_apply_apply
  条件: (f : ι ->₀ R) (g : κ ->₀ N) (a : ι) (b : κ)
  证明: by
  simp [finsuppTensorFinsuppLid]

@[simp]

Depends on / 依赖: finsuppTensorFinsuppLid, h.mono, hg.of_le, le_abs_self, le_trans, of_le
-/
theorem finsuppTensorFinsuppLid_apply_apply (f : ι ->₀ R) (g : κ ->₀ N) (a : ι) (b : κ) :
    finsuppTensorFinsuppLid R N ι κ (f otimesₜ[R] g) (a, b) = f a • g b := by
  simp [finsuppTensorFinsuppLid]

@[simp]
/--
theorem `finsuppTensorFinsuppLid_single_tmul_single` / 定理 `finsuppTensorFinsuppLid_single_tmul_single`

English:
theorem finsuppTensorFinsuppLid_single_tmul_single
  given: (a : ι) (b : κ) (r : R) (n : N)
  proof: by
  simp [finsuppTensorFinsuppLid]

@[simp]

中文:
定理 finsuppTensorFinsuppLid_single_tmul_single
  条件: (a : ι) (b : κ) (r : R) (n : N)
  证明: by
  simp [finsuppTensorFinsuppLid]

@[simp]

Depends on / 依赖: finsuppTensorFinsuppLid
-/
theorem finsuppTensorFinsuppLid_single_tmul_single (a : ι) (b : κ) (r : R) (n : N) :
    finsuppTensorFinsuppLid R N ι κ (Finsupp.single a r otimesₜ[R] Finsupp.single b n) =
      Finsupp.single (a, b) (r • n) := by
  simp [finsuppTensorFinsuppLid]

@[simp]
/--
theorem `finsuppTensorFinsuppLid_symm_single_smul` / 定理 `finsuppTensorFinsuppLid_symm_single_smul`

English:
theorem finsuppTensorFinsuppLid_symm_single_smul
  given: (i : ι × κ) (r : R) (n : N)
  proof: Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppLid_single_tmul_single ..).symm

中文:
定理 finsuppTensorFinsuppLid_symm_single_smul
  条件: (i : ι × κ) (r : R) (n : N)
  证明: Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppLid_single_tmul_single ..).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, Prod.casesOn, casesOn, finsuppTensorFinsuppLid_single_tmul_single, symm_apply_eq
-/
theorem finsuppTensorFinsuppLid_symm_single_smul (i : ι × κ) (r : R) (n : N) :
    (finsuppTensorFinsuppLid R N ι κ).symm (Finsupp.single i (r • n)) =
      Finsupp.single i.1 r otimesₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppLid_single_tmul_single ..).symm

/--
Definition of `finsuppTensorFinsuppRid` / `finsuppTensorFinsuppRid` 的定义

English:
definition finsuppTensorFinsuppRid
  signature: : (ι ->₀ M) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ M
  body: finsuppTensorFinsupp R R M R ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.rid R M)

@[simp]

中文:
定义 finsuppTensorFinsuppRid
  签名: : (ι ->₀ M) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ M
  定义体: finsuppTensorFinsupp R R M R ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.rid R M)

@[simp]

Depends on / 依赖: Equiv.refl, Finsupp, Finsupp.lcongr, TensorProduct, TensorProduct.rid, finsuppTensorFinsupp, lcongr
-/
def finsuppTensorFinsuppRid : (ι ->₀ M) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ M :=
  finsuppTensorFinsupp R R M R ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.rid R M)

@[simp]
/--
theorem `finsuppTensorFinsuppRid_apply_apply` / 定理 `finsuppTensorFinsuppRid_apply_apply`

English:
theorem finsuppTensorFinsuppRid_apply_apply
  given: (f : ι ->₀ M) (g : κ ->₀ R) (a : ι) (b : κ)
  proof: by
  simp [finsuppTensorFinsuppRid]

@[simp]

中文:
定理 finsuppTensorFinsuppRid_apply_apply
  条件: (f : ι ->₀ M) (g : κ ->₀ R) (a : ι) (b : κ)
  证明: by
  simp [finsuppTensorFinsuppRid]

@[simp]

Depends on / 依赖: finsuppTensorFinsuppRid
-/
theorem finsuppTensorFinsuppRid_apply_apply (f : ι ->₀ M) (g : κ ->₀ R) (a : ι) (b : κ) :
    finsuppTensorFinsuppRid R M ι κ (f otimesₜ[R] g) (a, b) = g b • f a := by
  simp [finsuppTensorFinsuppRid]

@[simp]
/--
theorem `finsuppTensorFinsuppRid_single_tmul_single` / 定理 `finsuppTensorFinsuppRid_single_tmul_single`

English:
theorem finsuppTensorFinsuppRid_single_tmul_single
  given: (a : ι) (b : κ) (m : M) (r : R)
  proof: by
  simp [finsuppTensorFinsuppRid]

@[simp]

中文:
定理 finsuppTensorFinsuppRid_single_tmul_single
  条件: (a : ι) (b : κ) (m : M) (r : R)
  证明: by
  simp [finsuppTensorFinsuppRid]

@[simp]

Depends on / 依赖: finsuppTensorFinsuppRid
-/
theorem finsuppTensorFinsuppRid_single_tmul_single (a : ι) (b : κ) (m : M) (r : R) :
    finsuppTensorFinsuppRid R M ι κ (Finsupp.single a m otimesₜ[R] Finsupp.single b r) =
      Finsupp.single (a, b) (r • m) := by
  simp [finsuppTensorFinsuppRid]

@[simp]
/--
theorem `finsuppTensorFinsuppRid_symm_single_smul` / 定理 `finsuppTensorFinsuppRid_symm_single_smul`

English:
theorem finsuppTensorFinsuppRid_symm_single_smul
  given: (i : ι × κ) (m : M) (r : R)
  proof: Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppRid_single_tmul_single ..).symm

中文:
定理 finsuppTensorFinsuppRid_symm_single_smul
  条件: (i : ι × κ) (m : M) (r : R)
  证明: Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppRid_single_tmul_single ..).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, Prod.casesOn, casesOn, finsuppTensorFinsuppRid_single_tmul_single, symm_apply_eq
-/
theorem finsuppTensorFinsuppRid_symm_single_smul (i : ι × κ) (m : M) (r : R) :
    (finsuppTensorFinsuppRid R M ι κ).symm (Finsupp.single i (r • m)) =
      Finsupp.single i.1 m otimesₜ Finsupp.single i.2 r :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppRid_single_tmul_single ..).symm

/--
Definition of `finsuppTensorFinsupp'` / `finsuppTensorFinsupp'` 的定义

English:
definition finsuppTensorFinsupp'
  signature: : (ι ->₀ R) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ R
  body: finsuppTensorFinsuppLid R R ι κ

@[simp]

中文:
定义 finsuppTensorFinsupp'
  签名: : (ι ->₀ R) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ R
  定义体: finsuppTensorFinsuppLid R R ι κ

@[simp]

Depends on / 依赖: finsuppTensorFinsuppLid
-/
def finsuppTensorFinsupp' : (ι ->₀ R) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ R :=
  finsuppTensorFinsuppLid R R ι κ

@[simp]
/--
theorem `finsuppTensorFinsupp'_apply_apply` / 定理 `finsuppTensorFinsupp'_apply_apply`

English:
theorem finsuppTensorFinsupp'_apply_apply
  given: (f : ι ->₀ R) (g : κ ->₀ R) (a : ι) (b : κ)
  proof: finsuppTensorFinsuppLid_apply_apply R R ι κ f g a b

@[simp]

中文:
定理 finsuppTensorFinsupp'_apply_apply
  条件: (f : ι ->₀ R) (g : κ ->₀ R) (a : ι) (b : κ)
  证明: finsuppTensorFinsuppLid_apply_apply R R ι κ f g a b

@[simp]
-/
theorem finsuppTensorFinsupp'_apply_apply (f : ι ->₀ R) (g : κ ->₀ R) (a : ι) (b : κ) :
    finsuppTensorFinsupp' R ι κ (f otimesₜ[R] g) (a, b) = f a * g b :=
  finsuppTensorFinsuppLid_apply_apply R R ι κ f g a b

@[simp]
/--
theorem `finsuppTensorFinsupp'_single_tmul_single` / 定理 `finsuppTensorFinsupp'_single_tmul_single`

English:
theorem finsuppTensorFinsupp'_single_tmul_single
  given: (a : ι) (b : κ) (r₁ r₂ : R)
  proof: finsuppTensorFinsuppLid_single_tmul_single R R ι κ a b r₁ r₂

中文:
定理 finsuppTensorFinsupp'_single_tmul_single
  条件: (a : ι) (b : κ) (r₁ r₂ : R)
  证明: finsuppTensorFinsuppLid_single_tmul_single R R ι κ a b r₁ r₂
-/
theorem finsuppTensorFinsupp'_single_tmul_single (a : ι) (b : κ) (r₁ r₂ : R) :
    finsuppTensorFinsupp' R ι κ (Finsupp.single a r₁ otimesₜ[R] Finsupp.single b r₂) =
      Finsupp.single (a, b) (r₁ * r₂) :=
  finsuppTensorFinsuppLid_single_tmul_single R R ι κ a b r₁ r₂

/--
theorem `finsuppTensorFinsupp'_symm_single_mul` / 定理 `finsuppTensorFinsupp'_symm_single_mul`

English:
theorem finsuppTensorFinsupp'_symm_single_mul
  given: (i : ι × κ) (r₁ r₂ : R)
  proof: finsuppTensorFinsuppLid_symm_single_smul R R ι κ i r₁ r₂

中文:
定理 finsuppTensorFinsupp'_symm_single_mul
  条件: (i : ι × κ) (r₁ r₂ : R)
  证明: finsuppTensorFinsuppLid_symm_single_smul R R ι κ i r₁ r₂

Depends on / 依赖: eLpNorm, simp_rw
-/
theorem finsuppTensorFinsupp'_symm_single_mul (i : ι × κ) (r₁ r₂ : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i (r₁ * r₂)) =
      Finsupp.single i.1 r₁ otimesₜ Finsupp.single i.2 r₂ :=
  finsuppTensorFinsuppLid_symm_single_smul R R ι κ i r₁ r₂

/--
theorem `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul` / 定理 `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul`

English:
theorem finsuppTensorFinsupp'_symm_single_eq_single_one_tmul
  given: (i : ι × κ) (r : R)
  proof: by
  nth_rw 1 [← one_mul r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _

中文:
定理 finsuppTensorFinsupp'_symm_single_eq_single_one_tmul
  条件: (i : ι × κ) (r : R)
  证明: by
  nth_rw 1 [← one_mul r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _
-/
theorem finsuppTensorFinsupp'_symm_single_eq_single_one_tmul (i : ι × κ) (r : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i r) =
      Finsupp.single i.1 1 otimesₜ Finsupp.single i.2 r := by
  nth_rw 1 [← one_mul r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _

/--
theorem `finsuppTensorFinsupp'_symm_single_eq_tmul_single_one` / 定理 `finsuppTensorFinsupp'_symm_single_eq_tmul_single_one`

English:
theorem finsuppTensorFinsupp'_symm_single_eq_tmul_single_one
  given: (i : ι × κ) (r : R)
  proof: by
  nth_rw 1 [← mul_one r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _

中文:
定理 finsuppTensorFinsupp'_symm_single_eq_tmul_single_one
  条件: (i : ι × κ) (r : R)
  证明: by
  nth_rw 1 [← mul_one r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _
-/
theorem finsuppTensorFinsupp'_symm_single_eq_tmul_single_one (i : ι × κ) (r : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i r) =
      Finsupp.single i.1 r otimesₜ Finsupp.single i.2 1 := by
  nth_rw 1 [← mul_one r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _

/--
theorem `finsuppTensorFinsuppLid_self` / 定理 `finsuppTensorFinsuppLid_self`

English:
theorem finsuppTensorFinsuppLid_self
  proof: rfl

中文:
定理 finsuppTensorFinsuppLid_self
  证明: rfl
-/
theorem finsuppTensorFinsuppLid_self :
    finsuppTensorFinsuppLid R R ι κ = finsuppTensorFinsupp' R ι κ := rfl

/--
theorem `finsuppTensorFinsuppRid_self` / 定理 `finsuppTensorFinsuppRid_self`

English:
theorem finsuppTensorFinsuppRid_self
  proof: by
  rw [finsuppTensorFinsupp']; rw [finsuppTensorFinsuppLid]; rw [finsuppTensorFinsuppRid]; rw [TensorProduct.lid_eq_rid]

中文:
定理 finsuppTensorFinsuppRid_self
  证明: by
  rw [finsuppTensorFinsupp']; rw [finsuppTensorFinsuppLid]; rw [finsuppTensorFinsuppRid]; rw [TensorProduct.lid_eq_rid]

Depends on / 依赖: TensorProduct, TensorProduct.lid_eq_rid, finsuppTensorFinsupp, finsuppTensorFinsuppLid, finsuppTensorFinsuppRid, lid_eq_rid
-/
theorem finsuppTensorFinsuppRid_self :
    finsuppTensorFinsuppRid R R ι κ = finsuppTensorFinsupp' R ι κ := by
  rw [finsuppTensorFinsupp']; rw [finsuppTensorFinsuppLid]; rw [finsuppTensorFinsuppRid]; rw [TensorProduct.lid_eq_rid]

end
