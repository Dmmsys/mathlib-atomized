/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.SpanRank

/-!

# Cayley-Hamilton theorem for f.g. modules.

Given a fixed finite spanning set `b : ι → M` of an `R`-module `M`, we say that a matrix `M`
represents an endomorphism `f : M →ₗ[R] M` if the matrix as an endomorphism of `ι → R` commutes
with `f` via the projection `(ι → R) →ₗ[R] M` given by `b`.

We show that every endomorphism has a matrix representation, and if `f.range ≤ I • ⊤` for some
ideal `I`, we may furthermore obtain a matrix representation whose entries fall in `I`.

This is used to conclude the Cayley-Hamilton theorem for f.g. modules over arbitrary rings.
-/

@[expose] public section


variable {ι : Type*} [Fintype ι]
variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)
variable (b : ι -> M)

open Polynomial Matrix

/--
Definition of `PiToModule.fromMatrix` / `PiToModule.fromMatrix` 的定义

English:
definition PiToModule.fromMatrix
  signature: [DecidableEq ι]
  body: (LinearMap.llcomp R _ _ _ (Fintype.linearCombination R b)).comp algEquivMatrix'.symm.toLinearMap

中文:
定义 PiToModule.fromMatrix
  签名: [DecidableEq ι]
  定义体: (LinearMap.llcomp R _ _ _ (Fintype.linearCombination R b)).comp algEquivMatrix'.symm.toLinearMap

Depends on / 依赖: Fintype, Fintype.linearCombination, LinearMap, LinearMap.llcomp, algEquivMatrix, linearCombination, llcomp, symm.toLinearMap, toLinearMap
-/
def PiToModule.fromMatrix [DecidableEq ι] : Matrix ι ι R ->ₗ[R] (ι -> R) ->ₗ[R] M :=
  (LinearMap.llcomp R _ _ _ (Fintype.linearCombination R b)).comp algEquivMatrix'.symm.toLinearMap

/--
theorem `PiToModule.fromMatrix_apply` / 定理 `PiToModule.fromMatrix_apply`

English:
theorem PiToModule.fromMatrix_apply
  given: [DecidableEq ι] (A : Matrix ι ι R) (w : ι -> R)
  proof: rfl

中文:
定理 PiToModule.fromMatrix_apply
  条件: [DecidableEq ι] (A : 矩阵 ι ι R) (w : ι -> R)
  证明: rfl
-/
theorem PiToModule.fromMatrix_apply [DecidableEq ι] (A : Matrix ι ι R) (w : ι -> R) :
    PiToModule.fromMatrix R b A w = Fintype.linearCombination R b (A *ᵥ w) :=
  rfl

/--
theorem `PiToModule.fromMatrix_apply_single_one` / 定理 `PiToModule.fromMatrix_apply_single_one`

English:
theorem PiToModule.fromMatrix_apply_single_one
  given: [DecidableEq ι] (A : Matrix ι ι R) (j : ι)
  proof: by
  rw [PiToModule.fromMatrix_apply]; rw [Fintype.linearCombination_apply]; rw [Matrix.mulVec_single]
  simp_rw [MulOpposite.op_one, one_smul, col_apply]

中文:
定理 PiToModule.fromMatrix_apply_single_one
  条件: [DecidableEq ι] (A : 矩阵 ι ι R) (j : ι)
  证明: by
  rw [PiToModule.fromMatrix_apply]; rw [Fintype.linearCombination_apply]; rw [Matrix.mulVec_single]
  simp_rw [MulOpposite.op_one, one_smul, col_apply]

Depends on / 依赖: Fintype, Fintype.linearCombination_apply, Matrix, Matrix.mulVec_single, MulOpposite, MulOpposite.op_one, PiToModule, PiToModule.fromMatrix_apply, col_apply, fromMatrix_apply, linearCombination_apply, mulVec_single, one_smul, op_one, simp_rw
-/
theorem PiToModule.fromMatrix_apply_single_one [DecidableEq ι] (A : Matrix ι ι R) (j : ι) :
    PiToModule.fromMatrix R b A (Pi.single j 1) = ∑ i : ι, A i j • b i := by
  rw [PiToModule.fromMatrix_apply]; rw [Fintype.linearCombination_apply]; rw [Matrix.mulVec_single]
  simp_rw [MulOpposite.op_one, one_smul, col_apply]

/--
Definition of `PiToModule.fromEnd` / `PiToModule.fromEnd` 的定义

English:
definition PiToModule.fromEnd
  signature: : Module.End R M ->ₗ[R] (ι -> R) ->ₗ[R] M
  body: LinearMap.lcomp _ _ (Fintype.linearCombination R b)

中文:
定义 PiToModule.fromEnd
  签名: : 模.End R M ->ₗ[R] (ι -> R) ->ₗ[R] M
  定义体: LinearMap.lcomp _ _ (Fintype.linearCombination R b)

Depends on / 依赖: Fintype, Fintype.linearCombination, LinearMap, LinearMap.lcomp, linearCombination
-/
def PiToModule.fromEnd : Module.End R M ->ₗ[R] (ι -> R) ->ₗ[R] M :=
  LinearMap.lcomp _ _ (Fintype.linearCombination R b)

/--
theorem `PiToModule.fromEnd_apply` / 定理 `PiToModule.fromEnd_apply`

English:
theorem PiToModule.fromEnd_apply
  given: (f : Module.End R M) (w : ι -> R)
  proof: rfl

中文:
定理 PiToModule.fromEnd_apply
  条件: (f : 模.End R M) (w : ι -> R)
  证明: rfl
-/
theorem PiToModule.fromEnd_apply (f : Module.End R M) (w : ι -> R) :
    PiToModule.fromEnd R b f w = f (Fintype.linearCombination R b w) :=
  rfl

/--
theorem `PiToModule.fromEnd_apply_single_one` / 定理 `PiToModule.fromEnd_apply_single_one`

English:
theorem PiToModule.fromEnd_apply_single_one
  given: [DecidableEq ι] (f : Module.End R M) (i : ι)
  proof: by
  rw [PiToModule.fromEnd_apply]; rw [Fintype.linearCombination_apply_single]; rw [one_smul]

中文:
定理 PiToModule.fromEnd_apply_single_one
  条件: [DecidableEq ι] (f : 模.End R M) (i : ι)
  证明: by
  rw [PiToModule.fromEnd_apply]; rw [Fintype.linearCombination_apply_single]; rw [one_smul]

Depends on / 依赖: Fintype, Fintype.linearCombination_apply_single, PiToModule, PiToModule.fromEnd_apply, fromEnd_apply, linearCombination_apply_single, one_smul
-/
theorem PiToModule.fromEnd_apply_single_one [DecidableEq ι] (f : Module.End R M) (i : ι) :
    PiToModule.fromEnd R b f (Pi.single i 1) = f (b i) := by
  rw [PiToModule.fromEnd_apply]; rw [Fintype.linearCombination_apply_single]; rw [one_smul]

/--
theorem `PiToModule.fromEnd_injective` / 定理 `PiToModule.fromEnd_injective`

English:
theorem PiToModule.fromEnd_injective
  given: (hb : Submodule.span R (Set.range b) = ⊤)
  proof: by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m in LinearMap.range (Fintype.linearCombination R b) := by
    rw [(Fintype.range_linearCombination R b).trans hb]
    exact Submodule.mem_top
  exact (LinearMap.congr_fun e m :)

中文:
定理 PiToModule.fromEnd_injective
  条件: (hb : 子模.span R (集合.range b) = ⊤)
  证明: by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m in LinearMap.range (Fintype.linearCombination R b) := by
    rw [(Fintype.range_linearCombination R b).trans hb]
    exact Submodule.mem_top
  exact (LinearMap.congr_fun e m :)

Depends on / 依赖: Fintype, Fintype.linearCombination, Fintype.range_linearCombination, LinearMap, LinearMap.congr_fun, LinearMap.range, Submodule, Submodule.mem_top, congr_fun, linearCombination, mem_top, range_linearCombination
-/
theorem PiToModule.fromEnd_injective (hb : Submodule.span R (Set.range b) = ⊤) :
    Function.Injective (PiToModule.fromEnd R b) := by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m in LinearMap.range (Fintype.linearCombination R b) := by
    rw [(Fintype.range_linearCombination R b).trans hb]
    exact Submodule.mem_top
  exact (LinearMap.congr_fun e m :)

section

variable {R} [DecidableEq ι]

/--
Definition of `Matrix.Represents` / `Matrix.Represents` 的定义

English:
definition Matrix.Represents
  signature: (A : Matrix ι ι R) (f : Module.End R M)
  body: PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f

中文:
定义 矩阵.Represents
  签名: (A : 矩阵 ι ι R) (f : 模.End R M)
  定义体: PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f

Depends on / 依赖: PiToModule, PiToModule.fromEnd, PiToModule.fromMatrix, fromEnd, fromMatrix
-/
def Matrix.Represents (A : Matrix ι ι R) (f : Module.End R M) : Prop :=
  PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f

variable {b}

/--
theorem `Matrix.Represents.congr_fun` / 定理 `Matrix.Represents.congr_fun`

English:
theorem Matrix.Represents.congr_fun
  statement: {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
  proof: LinearMap.congr_fun h x

中文:
定理 矩阵.Represents.congr_fun
  结论: {A : 矩阵 ι ι R} {f : 模.End R M} (h : A.Represents b f)
  证明: LinearMap.congr_fun h x

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
theorem Matrix.Represents.congr_fun {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (x) : Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCombination R b x) :=
  LinearMap.congr_fun h x

/--
theorem `Matrix.represents_iff` / 定理 `Matrix.represents_iff`

English:
theorem Matrix.represents_iff
  given: {A : Matrix ι ι R} {f : Module.End R M}
  proof: ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩

中文:
定理 矩阵.represents_iff
  条件: {A : 矩阵 ι ι R} {f : 模.End R M}
  证明: ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩

Depends on / 依赖: LinearMap, LinearMap.ext, congr_fun, e.congr_fun
-/
theorem Matrix.represents_iff {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔
      forall x, Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCombination R b x) :=
  ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩

/--
theorem `Matrix.represents_iff'` / 定理 `Matrix.represents_iff'`

English:
theorem Matrix.represents_iff'
  given: {A : Matrix ι ι R} {f : Module.End R M}
  proof: by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.fromEnd_apply_single_one,
      PiToM

中文:
定理 矩阵.represents_iff'
  条件: {A : 矩阵 ι ι R} {f : 模.End R M}
  证明: by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.fromEnd_apply_single_one,
      PiToM

Depends on / 依赖: LinearMap, LinearMap.coe_single, LinearMap.comp_apply, LinearMap.congr_fun, Pi.single, PiToModule, PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one, coe_single, comp_apply, congr_fun, fromEnd_apply_single_one, fromMatrix_apply_single_one, simp_rw, single
-/
theorem Matrix.represents_iff' {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔ forall j, ∑ i : ι, A i j • b i = f (b j) := by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.fromEnd_apply_single_one,
      PiToModule.fromMatrix_apply_single_one]
    apply h

/--
theorem `Matrix.Represents.mul` / 定理 `Matrix.Represents.mul`

English:
theorem Matrix.Represents.mul
  statement: {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
  proof: by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply]; rw [AlgEquiv.toLinearMap_apply]; rw [map_mul]
  ext
  dsimp [PiToModule.fromEnd]
  rw [← h'.congr_fun]; rw [← h.congr_fun]
  rfl

中文:
定理 矩阵.Represents.mul
  结论: {A A' : 矩阵 ι ι R} {f f' : 模.End R M} (h : A.Represents b f)
  证明: by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply]; rw [AlgEquiv.toLinearMap_apply]; rw [map_mul]
  ext
  dsimp [PiToModule.fromEnd]
  rw [← h'.congr_fun]; rw [← h.congr_fun]
  rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.toLinearMap_apply, LinearMap, LinearMap.comp_apply, Matrix, Matrix.Represents, PiToModule, PiToModule.fromEnd, PiToModule.fromMatrix, Represents, comp_apply, congr_fun, fromEnd, fromMatrix, h.congr_fun, map_mul, toLinearMap_apply
-/
theorem Matrix.Represents.mul {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A * A').Represents b (f * f') := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply]; rw [AlgEquiv.toLinearMap_apply]; rw [map_mul]
  ext
  dsimp [PiToModule.fromEnd]
  rw [← h'.congr_fun]; rw [← h.congr_fun]
  rfl

/--
theorem `Matrix.Represents.one` / 定理 `Matrix.Represents.one`

English:
theorem Matrix.Represents.one
  statement: (1 : Matrix ι ι R).Represents b 1
  proof: by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply]; rw [AlgEquiv.toLinearMap_apply]; rw [map_one]
  ext
  rfl

中文:
定理 矩阵.Represents.one
  结论: (1 : 矩阵 ι ι R).Represents b 1
  证明: by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply]; rw [AlgEquiv.toLinearMap_apply]; rw [map_one]
  ext
  rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.toLinearMap_apply, LinearMap, LinearMap.comp_apply, Matrix, Matrix.Represents, PiToModule, PiToModule.fromMatrix, Represents, comp_apply, fromMatrix, map_one, toLinearMap_apply
-/
theorem Matrix.Represents.one : (1 : Matrix ι ι R).Represents b 1 := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply]; rw [AlgEquiv.toLinearMap_apply]; rw [map_one]
  ext
  rfl

/--
theorem `Matrix.Represents.add` / 定理 `Matrix.Represents.add`

English:
theorem Matrix.Represents.add
  statement: {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
  proof: by
  delta Matrix.Represents at h h' ⊢; rw [map_add, map_add, h, h']

中文:
定理 矩阵.Represents.add
  结论: {A A' : 矩阵 ι ι R} {f f' : 模.End R M} (h : A.Represents b f)
  证明: by
  delta Matrix.Represents at h h' ⊢; rw [map_add, map_add, h, h']

Depends on / 依赖: Matrix, Matrix.Represents, Represents, map_add
-/
theorem Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A + A').Represents b (f + f') := by
  delta Matrix.Represents at h h' ⊢; rw [map_add, map_add, h, h']

/--
theorem `Matrix.Represents.zero` / 定理 `Matrix.Represents.zero`

English:
theorem Matrix.Represents.zero
  statement: (0 : Matrix ι ι R).Represents b 0
  proof: by
  delta Matrix.Represents
  rw [map_zero]; rw [map_zero]

中文:
定理 矩阵.Represents.zero
  结论: (0 : 矩阵 ι ι R).Represents b 0
  证明: by
  delta Matrix.Represents
  rw [map_zero]; rw [map_zero]

Depends on / 依赖: Matrix, Matrix.Represents, Represents, map_zero
-/
theorem Matrix.Represents.zero : (0 : Matrix ι ι R).Represents b 0 := by
  delta Matrix.Represents
  rw [map_zero]; rw [map_zero]

/--
theorem `Matrix.Represents.smul` / 定理 `Matrix.Represents.smul`

English:
theorem Matrix.Represents.smul
  statement: {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
  proof: by
  delta Matrix.Represents at h ⊢
  rw [map_smul]; rw [map_smul]; rw [h]

中文:
定理 矩阵.Represents.smul
  结论: {A : 矩阵 ι ι R} {f : 模.End R M} (h : A.Represents b f)
  证明: by
  delta Matrix.Represents at h ⊢
  rw [map_smul]; rw [map_smul]; rw [h]

Depends on / 依赖: Matrix, Matrix.Represents, Represents, map_smul
-/
theorem Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (r : R) : (r • A).Represents b (r • f) := by
  delta Matrix.Represents at h ⊢
  rw [map_smul]; rw [map_smul]; rw [h]

/--
theorem `Matrix.Represents.algebraMap` / 定理 `Matrix.Represents.algebraMap`

English:
theorem Matrix.Represents.algebraMap
  given: (r : R)
  proof: by
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.Represents.one.smul r

中文:
定理 矩阵.Represents.algebraMap
  条件: (r : R)
  证明: by
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.Represents.one.smul r

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Matrix, Matrix.Represents.one.smul, Represents, algebraMap_eq_smul_one
-/
theorem Matrix.Represents.algebraMap (r : R) :
    (algebraMap _ (Matrix ι ι R) r).Represents b (algebraMap _ (Module.End R M) r) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.Represents.one.smul r

/--
theorem `Matrix.Represents.eq` / 定理 `Matrix.Represents.eq`

English:
theorem Matrix.Represents.eq
  statement: (hb : Submodule.span R (Set.range b) = ⊤)
  proof: PiToModule.fromEnd_injective R b hb (h.symm.trans h')

中文:
定理 矩阵.Represents.eq
  结论: (hb : 子模.span R (集合.range b) = ⊤)
  证明: PiToModule.fromEnd_injective R b hb (h.symm.trans h')

Depends on / 依赖: PiToModule, PiToModule.fromEnd_injective, fromEnd_injective, h.symm.trans
-/
theorem Matrix.Represents.eq (hb : Submodule.span R (Set.range b) = ⊤)
    {A : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : A.Represents b f') : f = f' :=
  PiToModule.fromEnd_injective R b hb (h.symm.trans h')

variable (b R)

/--
Definition of `Matrix.isRepresentation` / `Matrix.isRepresentation` 的定义

English:
definition Matrix.isRepresentation
  signature: : Subalgebra R (Matrix ι ι R) where
  body: { A | exists f : Module.End R M, A.Represents b f }
  mul_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ * f₂, e₁.mul e₂⟩
  one_mem' := ⟨1, Matrix.Represents.one⟩
  add_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ + f₂, e₁.add e₂⟩
  zero_mem' := ⟨0, Matrix.Represents.zero⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, .a

中文:
定义 矩阵.isRepresentation
  签名: : 子代数 R (矩阵 ι ι R) where
  定义体: { A | exists f : Module.End R M, A.Represents b f }
  mul_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ * f₂, e₁.mul e₂⟩
  one_mem' := ⟨1, Matrix.Represents.one⟩
  add_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ + f₂, e₁.add e₂⟩
  zero_mem' := ⟨0, Matrix.Represents.zero⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, .a

Depends on / 依赖: A.Represents, Module, Module.End, Represents
-/
def Matrix.isRepresentation : Subalgebra R (Matrix ι ι R) where
  carrier := { A | exists f : Module.End R M, A.Represents b f }
  mul_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ * f₂, e₁.mul e₂⟩
  one_mem' := ⟨1, Matrix.Represents.one⟩
  add_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ + f₂, e₁.add e₂⟩
  zero_mem' := ⟨0, Matrix.Represents.zero⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, .algebraMap _⟩

variable (hb : Submodule.span R (Set.range b) = ⊤)
include hb

/--
Definition of `Matrix.isRepresentation.toEnd` / `Matrix.isRepresentation.toEnd` 的定义

English:
definition Matrix.isRepresentation.toEnd
  signature: :
  body: A.2.choose
  map_one' := (1 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.one
  map_mul' A₁ A₂ := (A₁ * A₂).2.choose_spec.eq hb (A₁.2.choose_spec.mul A₂.2.choose_spec)
  map_zero' := (0 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.zero
  map_add' A₁ A₂ 

中文:
定义 矩阵.isRepresentation.toEnd
  签名: :
  定义体: A.2.choose
  map_one' := (1 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.one
  map_mul' A₁ A₂ := (A₁ * A₂).2.choose_spec.eq hb (A₁.2.choose_spec.mul A₂.2.choose_spec)
  map_zero' := (0 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.zero
  map_add' A₁ A₂ 
-/
noncomputable def Matrix.isRepresentation.toEnd :
    Matrix.isRepresentation R b ->ₐ[R] Module.End R M where
  toFun A := A.2.choose
  map_one' := (1 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.one
  map_mul' A₁ A₂ := (A₁ * A₂).2.choose_spec.eq hb (A₁.2.choose_spec.mul A₂.2.choose_spec)
  map_zero' := (0 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.zero
  map_add' A₁ A₂ := (A₁ + A₂).2.choose_spec.eq hb (A₁.2.choose_spec.add A₂.2.choose_spec)
  commutes' r :=
    (algebraMap _ (Matrix.isRepresentation R b) r).2.choose_spec.eq hb (.algebraMap r)

/--
theorem `Matrix.isRepresentation.toEnd_represents` / 定理 `Matrix.isRepresentation.toEnd_represents`

English:
theorem Matrix.isRepresentation.toEnd_represents
  given: (A : Matrix.isRepresentation R b)
  proof: A.2.choose_spec

中文:
定理 矩阵.isRepresentation.toEnd_represents
  条件: (A : 矩阵.isRepresentation R b)
  证明: A.2.choose_spec

Depends on / 依赖: choose_spec
-/
theorem Matrix.isRepresentation.toEnd_represents (A : Matrix.isRepresentation R b) :
    (A : Matrix ι ι R).Represents b (Matrix.isRepresentation.toEnd R b hb A) :=
  A.2.choose_spec

/--
theorem `Matrix.isRepresentation.eq_toEnd_of_represents` / 定理 `Matrix.isRepresentation.eq_toEnd_of_represents`

English:
theorem Matrix.isRepresentation.eq_toEnd_of_represents
  statement: (A : Matrix.isRepresentation R b)
  proof: A.2.choose_spec.eq hb h

中文:
定理 矩阵.isRepresentation.eq_toEnd_of_represents
  结论: (A : 矩阵.isRepresentation R b)
  证明: A.2.choose_spec.eq hb h

Depends on / 依赖: choose_spec, choose_spec.eq
-/
theorem Matrix.isRepresentation.eq_toEnd_of_represents (A : Matrix.isRepresentation R b)
    {f : Module.End R M} (h : (A : Matrix ι ι R).Represents b f) :
    Matrix.isRepresentation.toEnd R b hb A = f :=
  A.2.choose_spec.eq hb h

/--
theorem `Matrix.isRepresentation.toEnd_exists_mem_ideal` / 定理 `Matrix.isRepresentation.toEnd_exists_mem_ideal`

English:
theorem Matrix.isRepresentation.toEnd_exists_mem_ideal
  statement: (f : Module.End R M) (I : Ideal R)
  proof: by
  have : forall x, f x in LinearMap.range (Ideal.finsuppTotal ι M I b) := by
    rw [Ideal.range_finsuppTotal]; rw [hb]
    exact fun x => hI (LinearMap.mem_range_self f x)
  choose bM' hbM' using this
  let A : Matrix ι ι R := fun i j => bM' (b j) i
  have : A.Represents b f := by
    rw [Matrix

中文:
定理 矩阵.isRepresentation.toEnd_存在_mem_ideal
  结论: (f : 模.End R M) (I : 理想 R)
  证明: by
  have : forall x, f x in LinearMap.range (Ideal.finsuppTotal ι M I b) := by
    rw [Ideal.range_finsuppTotal]; rw [hb]
    exact fun x => hI (LinearMap.mem_range_self f x)
  choose bM' hbM' using this
  let A : Matrix ι ι R := fun i j => bM' (b j) i
  have : A.Represents b f := by
    rw [Matrix

Depends on / 依赖: A.Represents, Ideal.finsuppTotal, Ideal.finsuppTotal_apply_eq_of_fintype, Ideal.range_finsuppTotal, LinearMap, LinearMap.mem_range_self, LinearMap.range, Matrix, Matrix.isRepresentation.eq_toEnd_of_represents, Matrix.represents_iff, Represents, eq_toEnd_of_represents, finsuppTotal, finsuppTotal_apply_eq_of_fintype, isRepresentation, mem_range_self, range_finsuppTotal, represents_iff, specialize
-/
theorem Matrix.isRepresentation.toEnd_exists_mem_ideal (f : Module.End R M) (I : Ideal R)
    (hI : LinearMap.range f <= I • ⊤) :
    exists M, Matrix.isRepresentation.toEnd R b hb M = f ∧ forall i j, M.1 i j in I := by
  have : forall x, f x in LinearMap.range (Ideal.finsuppTotal ι M I b) := by
    rw [Ideal.range_finsuppTotal]; rw [hb]
    exact fun x => hI (LinearMap.mem_range_self f x)
  choose bM' hbM' using this
  let A : Matrix ι ι R := fun i j => bM' (b j) i
  have : A.Represents b f := by
    rw [Matrix.represents_iff']
    dsimp [A]
    intro j
    specialize hbM' (b j)
    rwa [Ideal.finsuppTotal_apply_eq_of_fintype] at hbM'
  exact
    ⟨⟨A, f, this⟩, Matrix.isRepresentation.eq_toEnd_of_represents R b hb ⟨A, f, this⟩ this,
      fun i j => (bM' (b j) i).prop⟩

/--
theorem `Matrix.isRepresentation.toEnd_surjective` / 定理 `Matrix.isRepresentation.toEnd_surjective`

English:
theorem Matrix.isRepresentation.toEnd_surjective
  proof: by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R b hb f ⊤ (by simp)
  exact ⟨M, e⟩

中文:
定理 矩阵.isRepresentation.toEnd_surjective
  证明: by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R b hb f ⊤ (by simp)
  exact ⟨M, e⟩

Depends on / 依赖: Matrix, Matrix.isRepresentation.toEnd_exists_mem_ideal, isRepresentation, toEnd_exists_mem_ideal
-/
theorem Matrix.isRepresentation.toEnd_surjective :
    Function.Surjective (Matrix.isRepresentation.toEnd R b hb) := by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R b hb f ⊤ (by simp)
  exact ⟨M, e⟩

end

/--
theorem `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero` / 定理 `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero`

English:
theorem LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
  proof: by
  classical
    cases subsingleton_or_nontrivial R
    · exact ⟨0, by simp [nontriviality]⟩
    obtain ⟨s, hs_card, hs_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank (R := R) (M := M) Module.Finite.fg_top
    have : Submodule.span R (Set.range ((↑) : s -> M)) = ⊤ := by simp [h

中文:
定理 线性映射.存在_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
  证明: by
  classical
    cases subsingleton_or_nontrivial R
    · exact ⟨0, by simp [nontriviality]⟩
    obtain ⟨s, hs_card, hs_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank (R := R) (M := M) Module.Finite.fg_top
    have : Submodule.span R (Set.range ((↑) : s -> M)) = ⊤ := by simp [h

Depends on / 依赖: Finite, Matrix, Matrix.isRepresentation.toEnd_exists_mem_ideal, Module, Module.Finite.fg_top, Set.range, Submodule, Submodule.FG.exists_span_finset_card_eq_spanFinrank, Submodule.span, charpoly, charpoly_monic, classical, coeff_charpoly_mem_ideal_pow, exists_span_finset_card_eq_spanFinrank, fg_top, hs_card, hs_span, isRepresentation, nontriviality, subsingleton_or_nontrivial
-/
theorem LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
    [Module.Finite R M] (f : Module.End R M) (I : Ideal R) (hI : LinearMap.range f <= I • ⊤) :
    exists p : R[X], p.Monic ∧ p.natDegree = (⊤ : Submodule R M).spanFinrank ∧
                (forall k, p.coeff k in I ^ (p.natDegree - k)) ∧ Polynomial.aeval f p = 0 := by
  classical
    cases subsingleton_or_nontrivial R
    · exact ⟨0, by simp [nontriviality]⟩
    obtain ⟨s, hs_card, hs_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank (R := R) (M := M) Module.Finite.fg_top
    have : Submodule.span R (Set.range ((↑) : s -> M)) = ⊤ := by simp [hs_span]
    obtain ⟨A, rfl, h⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R ((↑) : s -> M) this f I hI
    refine ⟨A.1.charpoly, A.1.charpoly_monic, by simp [hs_card],
            by simpa using coeff_charpoly_mem_ideal_pow h, ?_⟩
    rw [Polynomial.aeval_algHom_apply]; rw [← map_zero (Matrix.isRepresentation.toEnd R ((↑) : s -> M) this)]
    congr 1
    ext1
    rw [Polynomial.aeval_subalgebra_coe]; rw [Matrix.aeval_self_charpoly]; rw [Subalgebra.coe_zero]

@[deprecated
"strengthened conclusion to
`LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero`"
(since := "2026-04-10")] alias
LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul :=
  LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero

/--
theorem `LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero` / 定理 `LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero`

English:
theorem LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero
  proof: (LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R f ⊤ (by simp)).imp
    fun _ h => h.imp_right (And.imp_right And.right)

中文:
定理 线性映射.存在_monic_and_natDegree_eq_and_aeval_eq_zero
  证明: (LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R f ⊤ (by simp)).imp
    fun _ h => h.imp_right (And.imp_right And.right)

Depends on / 依赖: And.imp_right, And.right, LinearMap, LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero, exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero, h.imp_right, imp_right
-/
theorem LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero
    [Module.Finite R M] (f : Module.End R M) :
    exists p : R[X], p.Monic ∧ p.natDegree = (⊤ : Submodule R M).spanFinrank ∧
                Polynomial.aeval f p = 0 :=
  (LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R f ⊤ (by simp)).imp
    fun _ h => h.imp_right (And.imp_right And.right)

/--
theorem `LinearMap.exists_monic_and_aeval_eq_zero` / 定理 `LinearMap.exists_monic_and_aeval_eq_zero`

English:
theorem LinearMap.exists_monic_and_aeval_eq_zero
  given: [Module.Finite R M] (f : Module.End R M)
  proof: (LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero R f).imp
    fun _ h => h.imp_right And.right

中文:
定理 线性映射.存在_monic_and_aeval_eq_zero
  条件: [模.有限 R M] (f : 模.End R M)
  证明: (LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero R f).imp
    fun _ h => h.imp_right And.right

Depends on / 依赖: And.right, LinearMap, LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero, exists_monic_and_natDegree_eq_and_aeval_eq_zero, h.imp_right, imp_right
-/
theorem LinearMap.exists_monic_and_aeval_eq_zero [Module.Finite R M] (f : Module.End R M) :
    exists p : R[X], p.Monic ∧ Polynomial.aeval f p = 0 :=
  (LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero R f).imp
    fun _ h => h.imp_right And.right
