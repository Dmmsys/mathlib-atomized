/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Geck's construction of a Lie algebra associated to a root system

This file contains an implementation of Geck's construction of a semisimple Lie algebra from a
reduced crystallographic root system. It follows [Geck](Geck2017) quite closely.

## Main definitions:
* `RootPairing.GeckConstruction.lieAlgebra`: the Geck construction of the Lie algebra associated to
  a root system with distinguished base.
* `RootPairing.GeckConstruction.cartanSubalgebra`: a distinguished subalgebra corresponding to a
  Cartan subalgebra of the Geck construction.
* `RootPairing.GeckConstruction.cartanSubalgebra_le_lieAlgebra`: the distinguished subalgebra is
  contained in the Geck construction.

## Alternative approaches

There are at least three ways to construct a Lie algebra from a root system:
1. As a quotient of a free Lie algebra, using the Serre relations
2. Directly defining the Lie bracket on $H ⊕ K^∣Φ|$
3. The Geck construction

We comment on these as follows:
1. This construction takes just a matrix as input. It yields a semisimple Lie algebra iff the
   matrix is a Cartan matrix but it is quite a lot of work to prove this. On the other hand, it also
   allows construction of Kac-Moody Lie algebras. It has been implemented as `Matrix.ToLieAlgebra`
   but as of May 2025, almost nothing has been proved about it in Mathlib.
2. This construction takes a root system with base as input, together with sufficient additional
   data to determine a collection of extraspecial pairs of roots. The additional data for the
   extraspecial pairs is required to pin down certain signs when defining the Lie bracket. (These
   signs can be interpreted as a set-theoretic splitting of Tits's extension of the Weyl group by
   an elementary 2-group of order $2^l$ where $l$ is the rank.)
3. This construction takes a root system with base as input and is implemented here.

There seems to be no known construction of a Lie algebra from a root system without first choosing
a base: https://mathoverflow.net/questions/495434/

-/

@[expose] public section

noncomputable section

open Function Set Submodule
open scoped Matrix

attribute [local simp] Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}

/--
Definition of `h` / `h` 的定义

English:
definition h
  signature: (i : b.support)
  body: open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn Int · i))

中文:
定义 h
  签名: (i : b.support)
  定义体: open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn Int · i))

Depends on / 依赖: Classical, P.pairingIn, diagonal, fromBlocks, pairingIn, scoped
-/
def h (i : b.support) :
    Matrix (b.support oplus ι) (b.support oplus ι) R :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn Int · i))

/--
lemma `h_def` / 引理 `h_def`

English:
lemma h_def
  given: [DecidableEq ι] (i : b.support)
  proof: by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

中文:
引理 h_def
  条件: [DecidableEq ι] (i : b.support)
  证明: by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

Depends on / 依赖: Matrix, Matrix.diagonal_apply, diagonal_apply
-/
lemma h_def [DecidableEq ι] (i : b.support) :
    h i = .fromBlocks 0 0 0 (.diagonal (P.pairingIn Int · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

/--
lemma `h_eq_diagonal` / 引理 `h_eq_diagonal`

English:
lemma h_eq_diagonal
  given: [DecidableEq ι] (i : b.support)
  proof: by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

中文:
引理 h_eq_diagonal
  条件: [DecidableEq ι] (i : b.support)
  证明: by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

Depends on / 依赖: Matrix, Matrix.diagonal_apply, diagonal_apply
-/
lemma h_eq_diagonal [DecidableEq ι] (i : b.support) :
    h i = .diagonal (Sum.elim 0 (P.pairingIn Int · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

variable (b) in
/--
lemma `linearIndependent_h` / 引理 `linearIndependent_h`

English:
lemma linearIndependent_h
  given: [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem]
  proof: by
  classical
  have : Matrix.diagLinearMap (b.support oplus ι) R R ∘ h =
      Sum.elimZeroLeft ∘ fun i : b.support => algebraMap Int R ∘ (P.pairingIn Int · i) := by
    ext; rw [comp_apply, h_def]; aesop
  apply LinearIndependent.of_comp (Matrix.diagLinearMap _ _ _)
  rw [this]; rw [LinearMap.linearIndependent_iff_of_injOn _ Sum.elim_injective'.injOn]; rw [linearIndependent_algebraMap_comp_iff]
  suffices LinearIndependent Int (fun i j : b.support => P.pairingIn Int j i) from
    this.of_linearIndependent_subset b.support
  apply b.cartanMatrix.transpose.linearIndependent_rows_of_det_ne_zero
  rw [Matrix.det_transpose]; rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

中文:
引理 linearIndependent_h
  条件: [有限 ι] [特征零 R] [是整环 R] [P.是RootSystem]
  证明: by
  classical
  have : Matrix.diagLinearMap (b.support oplus ι) R R ∘ h =
      Sum.elimZeroLeft ∘ fun i : b.support => algebraMap Int R ∘ (P.pairingIn Int · i) := by
    ext; rw [comp_apply, h_def]; aesop
  apply LinearIndependent.of_comp (Matrix.diagLinearMap _ _ _)
  rw [this]; rw [LinearMap.linearIndependent_iff_of_injOn _ Sum.elim_injective'.injOn]; rw [linearIndependent_algebraMap_comp_iff]
  suffices LinearIndependent Int (fun i j : b.support => P.pairingIn Int j i) from
    this.of_linearIndependent_subset b.support
  apply b.cartanMatrix.transpose.linearIndependent_rows_of_det_ne_zero
  rw [Matrix.det_transpose]; rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

Depends on / 依赖: LinearIndependent, LinearIndependent.of_comp, LinearMap, LinearMap.linearIndependent_iff_of_injOn, Matrix, Matrix.diagLinearMap, P.pairingIn, Sum.elimZeroLeft, Sum.elim_injective, algebraMap, b.support, classical, comp_apply, diagLinearMap, elimZeroLeft, elim_injective, h_def, linearIndependent_algebraMap_comp_iff, linearIndependent_iff_of_injOn, of_comp
-/
lemma linearIndependent_h [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem] :
    LinearIndependent R (h (b := b)) := by
  classical
  have : Matrix.diagLinearMap (b.support oplus ι) R R ∘ h =
      Sum.elimZeroLeft ∘ fun i : b.support => algebraMap Int R ∘ (P.pairingIn Int · i) := by
    ext; rw [comp_apply, h_def]; aesop
  apply LinearIndependent.of_comp (Matrix.diagLinearMap _ _ _)
  rw [this]; rw [LinearMap.linearIndependent_iff_of_injOn _ Sum.elim_injective'.injOn]; rw [linearIndependent_algebraMap_comp_iff]
  suffices LinearIndependent Int (fun i j : b.support => P.pairingIn Int j i) from
    this.of_linearIndependent_subset b.support
  apply b.cartanMatrix.transpose.linearIndependent_rows_of_det_ne_zero
  rw [Matrix.det_transpose]; rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

/--
lemma `span_range_h_le_range_diagonal` / 引理 `span_range_h_le_range_diagonal`

English:
lemma span_range_h_le_range_diagonal
  given: [DecidableEq ι]
  proof: by
  rw [span_le]
  rintro - ⟨i, rfl⟩
  rw [h_eq_diagonal]
  exact LinearMap.mem_range_self _ _

中文:
引理 span_range_h_le_range_diagonal
  条件: [DecidableEq ι]
  证明: by
  rw [span_le]
  rintro - ⟨i, rfl⟩
  rw [h_eq_diagonal]
  exact LinearMap.mem_range_self _ _

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, h_eq_diagonal, mem_range_self, span_le
-/
lemma span_range_h_le_range_diagonal [DecidableEq ι] :
    span R (range h) <= LinearMap.range (Matrix.diagonalLinearMap (b.support oplus ι) R R) := by
  rw [span_le]
  rintro - ⟨i, rfl⟩
  rw [h_eq_diagonal]
  exact LinearMap.mem_range_self _ _

open Matrix in
/--
lemma `diagonal_elim_mem_span_h_iff` / 引理 `diagonal_elim_mem_span_h_iff`

English:
lemma diagonal_elim_mem_span_h_iff
  given: [DecidableEq ι] {d : ι -> R}
  proof: by
  let g : Matrix ι ι R ->ₗ[R] Matrix (b.support oplus ι) (b.support oplus ι) R :=
    { toFun := .fromBlocks 0 0 0
      map_add' x y := by ext (i | i) (j | j) <;> simp
      map_smul' t x := by ext (i | i) (j | j) <;> simp }
have h₀ : Injective (g ∘ diagonalLinearMap ι R R) := fun _ _ hd => funext by simpa [g] using hd
  have h₁ {d : ι -> R} : diagonal (Sum.elim 0 d) = g (diagonalLinearMap ι R R d) := by
    ext (i | i) (j | j) <;> simp [g]
  have h₂ : range h = g '' (diagonalLinearMap ι R R ''
    (range <| fun (i : b.support) j => (P.pairingIn Int j i : R))) := by ext; simp [g, h_def]
  simp_rw [h₁, h₂, span_image, ← map_comp, ← comp_apply (f := g), mem_map, LinearMap.coe_comp,
    h₀.eq_iff, exists_eq_right]

中文:
引理 diagonal_elim_mem_span_h_iff
  条件: [DecidableEq ι] {d : ι -> R}
  证明: by
  let g : Matrix ι ι R ->ₗ[R] Matrix (b.support oplus ι) (b.support oplus ι) R :=
    { toFun := .fromBlocks 0 0 0
      map_add' x y := by ext (i | i) (j | j) <;> simp
      map_smul' t x := by ext (i | i) (j | j) <;> simp }
have h₀ : Injective (g ∘ diagonalLinearMap ι R R) := fun _ _ hd => funext by simpa [g] using hd
  have h₁ {d : ι -> R} : diagonal (Sum.elim 0 d) = g (diagonalLinearMap ι R R d) := by
    ext (i | i) (j | j) <;> simp [g]
  have h₂ : range h = g '' (diagonalLinearMap ι R R ''
    (range <| fun (i : b.support) j => (P.pairingIn Int j i : R))) := by ext; simp [g, h_def]
  simp_rw [h₁, h₂, span_image, ← map_comp, ← comp_apply (f := g), mem_map, LinearMap.coe_comp,
    h₀.eq_iff, exists_eq_right]
-/
@[simp] lemma diagonal_elim_mem_span_h_iff [DecidableEq ι] {d : ι -> R} :
    diagonal (Sum.elim 0 d) in span R (range <| h (b := b)) ↔
      d in span R (range <| fun (i : b.support) j => (P.pairingIn Int j i : R)) := by
  let g : Matrix ι ι R ->ₗ[R] Matrix (b.support oplus ι) (b.support oplus ι) R :=
    { toFun := .fromBlocks 0 0 0
      map_add' x y := by ext (i | i) (j | j) <;> simp
      map_smul' t x := by ext (i | i) (j | j) <;> simp }
have h₀ : Injective (g ∘ diagonalLinearMap ι R R) := fun _ _ hd => funext by simpa [g] using hd
  have h₁ {d : ι -> R} : diagonal (Sum.elim 0 d) = g (diagonalLinearMap ι R R d) := by
    ext (i | i) (j | j) <;> simp [g]
  have h₂ : range h = g '' (diagonalLinearMap ι R R ''
    (range <| fun (i : b.support) j => (P.pairingIn Int j i : R))) := by ext; simp [g, h_def]
  simp_rw [h₁, h₂, span_image, ← map_comp, ← comp_apply (f := g), mem_map, LinearMap.coe_comp,
    h₀.eq_iff, exists_eq_right]

/--
lemma `apply_sum_inl_eq_zero_of_mem_span_h` / 引理 `apply_sum_inl_eq_zero_of_mem_span_h`

English:
lemma apply_sum_inl_eq_zero_of_mem_span_h
  proof: by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; cases j <;> simp [h]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

中文:
引理 apply_sum_inl_eq_zero_of_mem_span_h
  证明: by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; cases j <;> simp [h]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

Depends on / 依赖: span_induction
-/
lemma apply_sum_inl_eq_zero_of_mem_span_h
    (i : b.support) (j : b.support oplus ι) {x : Matrix (b.support oplus ι) (b.support oplus ι) R}
    (hx : x in span R (range h)) :
    x j (Sum.inl i) = 0 := by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; cases j <;> simp [h]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

/--
lemma `lie_h_h` / 引理 `lie_h_h`

English:
lemma lie_h_h
  given: [Fintype ι] (i j : b.support)
  proof: by
  classical
  simpa only [h_eq_diagonal, ← commute_iff_lie_eq] using Matrix.commute_diagonal _ _

中文:
引理 lie_h_h
  条件: [有限类型 ι] (i j : b.support)
  证明: by
  classical
  simpa only [h_eq_diagonal, ← commute_iff_lie_eq] using Matrix.commute_diagonal _ _

Depends on / 依赖: Matrix, Matrix.commute_diagonal, classical, commute_diagonal, commute_iff_lie_eq, h_eq_diagonal
-/
lemma lie_h_h [Fintype ι] (i j : b.support) :
    ⁅h i, h j⁆ = 0 := by
  classical
  simpa only [h_eq_diagonal, ← commute_iff_lie_eq] using Matrix.commute_diagonal _ _

variable [Finite ι] [IsDomain R] [CharZero R]

/--
Definition of `e` / `e` 的定义

English:
definition e
  signature: (i : b.support)
  body: open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j => if i' = i ∧ j = -i then 1 else 0)
    (.of fun i' j => if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j => if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

中文:
定义 e
  签名: (i : b.support)
  定义体: open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j => if i' = i ∧ j = -i then 1 else 0)
    (.of fun i' j => if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j => if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

Depends on / 依赖: Classical, P.chainBotCoeff, P.indexNeg, P.root, b.cartanMatrix, cartanMatrix, chainBotCoeff, fromBlocks, indexNeg, scoped
-/
def e (i : b.support) :
    Matrix (b.support oplus ι) (b.support oplus ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j => if i' = i ∧ j = -i then 1 else 0)
    (.of fun i' j => if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j => if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: (i : b.support)
  body: open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j => if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j => if i' = -i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j => if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

中文:
定义 f
  签名: (i : b.support)
  定义体: open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j => if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j => if i' = -i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j => if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

Depends on / 依赖: Classical, P.chainTopCoeff, P.indexNeg, P.root, b.cartanMatrix, cartanMatrix, chainTopCoeff, fromBlocks, indexNeg, scoped
-/
def f (i : b.support) :
    Matrix (b.support oplus ι) (b.support oplus ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j => if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j => if i' = -i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j => if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

variable (b)

/--
Definition of `ω` / `ω` 的定义

English:
definition ω
  signature: :
  body: open scoped Classical in
  letI := P.indexNeg
.fromBlocks 1 0 0 .of fun i j => if i = -j then 1 else 0

中文:
定义 ω
  签名: :
  定义体: open scoped Classical in
  letI := P.indexNeg
.fromBlocks 1 0 0 .of fun i j => if i = -j then 1 else 0

Depends on / 依赖: Classical, P.indexNeg, fromBlocks, indexNeg, scoped
-/
def ω :
    Matrix (b.support oplus ι) (b.support oplus ι) R :=
  open scoped Classical in
  letI := P.indexNeg
.fromBlocks 1 0 0 .of fun i j => if i = -j then 1 else 0

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `lieAlgebra` / `lieAlgebra` 的定义

English:
definition lieAlgebra
  signature: [Fintype ι] [DecidableEq ι]
  body: LieSubalgebra.lieSpan R _ (range h union range e union range f)

中文:
定义 lieAlgebra
  签名: [有限类型 ι] [DecidableEq ι]
  定义体: LieSubalgebra.lieSpan R _ (range h union range e union range f)

Depends on / 依赖: LieSubalgebra, LieSubalgebra.lieSpan, lieSpan
-/
def lieAlgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support oplus ι) (b.support oplus ι) R) :=
  LieSubalgebra.lieSpan R _ (range h union range e union range f)

/--
Definition of `cartanSubalgebra` / `cartanSubalgebra` 的定义

English:
definition cartanSubalgebra
  signature: [Fintype ι] [DecidableEq ι]
  body: Submodule.span R (range h)
  lie_mem' {x y} hx hy := by
    have aux : (forall u in range (h (b := b)), forall v in range (h (b := b)), ⁅u, v⁆ = 0) := by
      rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact lie_h_h i j
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule,
      ← LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := R) aux] at hx hy ⊢
    exact LieSubalgebra.lie_mem _ hx hy

中文:
定义 cartanSubalgebra
  签名: [有限类型 ι] [DecidableEq ι]
  定义体: Submodule.span R (range h)
  lie_mem' {x y} hx hy := by
    have aux : (forall u in range (h (b := b)), forall v in range (h (b := b)), ⁅u, v⁆ = 0) := by
      rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact lie_h_h i j
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule,
      ← LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := R) aux] at hx hy ⊢
    exact LieSubalgebra.lie_mem _ hx hy

Depends on / 依赖: Submodule, Submodule.span
-/
def cartanSubalgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support oplus ι) (b.support oplus ι) R) where
  __ := Submodule.span R (range h)
  lie_mem' {x y} hx hy := by
    have aux : (forall u in range (h (b := b)), forall v in range (h (b := b)), ⁅u, v⁆ = 0) := by
      rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact lie_h_h i j
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule,
      ← LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := R) aux] at hx hy ⊢
    exact LieSubalgebra.lie_mem _ hx hy

/--
Definition of `cartanSubalgebra'` / `cartanSubalgebra'` 的定义

English:
definition cartanSubalgebra'
  signature: [Fintype ι] [DecidableEq ι]
  body: (cartanSubalgebra b).comap (lieAlgebra b).incl

omit [Finite ι] [IsDomain R] [CharZero R] in

中文:
定义 cartanSubalgebra'
  签名: [有限类型 ι] [DecidableEq ι]
  定义体: (cartanSubalgebra b).comap (lieAlgebra b).incl

omit [Finite ι] [IsDomain R] [CharZero R] in

Depends on / 依赖: cartanSubalgebra, lieAlgebra
-/
def cartanSubalgebra' [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (lieAlgebra b) :=
  (cartanSubalgebra b).comap (lieAlgebra b).incl

omit [Finite ι] [IsDomain R] [CharZero R] in
/--
lemma `cartanSubalgebra_eq_lieSpan` / 引理 `cartanSubalgebra_eq_lieSpan`

English:
lemma cartanSubalgebra_eq_lieSpan
  given: [Fintype ι] [DecidableEq ι]
  proof: by
  refine le_antisymm LieSubalgebra.submodule_span_le_lieSpan ?_
  rw [LieSubalgebra.lieSpan_le]; rw [cartanSubalgebra]
  exact Submodule.subset_span

中文:
引理 cartanSubalgebra_eq_lieSpan
  条件: [有限类型 ι] [DecidableEq ι]
  证明: by
  refine le_antisymm LieSubalgebra.submodule_span_le_lieSpan ?_
  rw [LieSubalgebra.lieSpan_le]; rw [cartanSubalgebra]
  exact Submodule.subset_span

Depends on / 依赖: LieSubalgebra, LieSubalgebra.lieSpan_le, LieSubalgebra.submodule_span_le_lieSpan, Submodule, Submodule.subset_span, cartanSubalgebra, le_antisymm, lieSpan_le, submodule_span_le_lieSpan, subset_span
-/
lemma cartanSubalgebra_eq_lieSpan [Fintype ι] [DecidableEq ι] :
    cartanSubalgebra b = LieSubalgebra.lieSpan R _ (range h) := by
  refine le_antisymm LieSubalgebra.submodule_span_le_lieSpan ?_
  rw [LieSubalgebra.lieSpan_le]; rw [cartanSubalgebra]
  exact Submodule.subset_span

variable {b}

omit [Finite ι] [IsDomain R] [CharZero R] in
/--
lemma `h_mem_cartanSubalgebra` / 引理 `h_mem_cartanSubalgebra`

English:
lemma h_mem_cartanSubalgebra
  given: [Fintype ι] [DecidableEq ι] (i : b.support)
  proof: Submodule.subset_span mem_range_self i

中文:
引理 h_mem_cartanSubalgebra
  条件: [有限类型 ι] [DecidableEq ι] (i : b.support)
  证明: Submodule.subset_span mem_range_self i
-/
@[simp] lemma h_mem_cartanSubalgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    h i in cartanSubalgebra b :=
Submodule.subset_span mem_range_self i

/--
lemma `h_mem_cartanSubalgebra'` / 引理 `h_mem_cartanSubalgebra'`

English:
lemma h_mem_cartanSubalgebra'
  given: [Fintype ι] [DecidableEq ι] (i : b.support) (hi)
  proof: by
  simp [cartanSubalgebra']

中文:
引理 h_mem_cartanSubalgebra'
  条件: [有限类型 ι] [DecidableEq ι] (i : b.support) (hi)
  证明: by
  simp [cartanSubalgebra']

Depends on / 依赖: TopologicalSpace, isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
-/
@[simp] lemma h_mem_cartanSubalgebra' [Fintype ι] [DecidableEq ι] (i : b.support) (hi) :
    ⟨h i, hi⟩ in cartanSubalgebra' b := by
  simp [cartanSubalgebra']

/--
lemma `h_mem_lieAlgebra` / 引理 `h_mem_lieAlgebra`

English:
lemma h_mem_lieAlgebra
  given: [Fintype ι] [DecidableEq ι] (i : b.support)
  proof: LieSubalgebra.subset_lieSpan by simp

中文:
引理 h_mem_lieAlgebra
  条件: [有限类型 ι] [DecidableEq ι] (i : b.support)
  证明: LieSubalgebra.subset_lieSpan by simp

Depends on / 依赖: LieSubalgebra, LieSubalgebra.subset_lieSpan, subset_lieSpan
-/
lemma h_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    h i in lieAlgebra b :=
LieSubalgebra.subset_lieSpan by simp

/--
lemma `e_mem_lieAlgebra` / 引理 `e_mem_lieAlgebra`

English:
lemma e_mem_lieAlgebra
  given: [Fintype ι] [DecidableEq ι] (i : b.support)
  proof: LieSubalgebra.subset_lieSpan by simp

中文:
引理 e_mem_lieAlgebra
  条件: [有限类型 ι] [DecidableEq ι] (i : b.support)
  证明: LieSubalgebra.subset_lieSpan by simp

Depends on / 依赖: LieSubalgebra, LieSubalgebra.subset_lieSpan, subset_lieSpan
-/
lemma e_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    e i in lieAlgebra b :=
LieSubalgebra.subset_lieSpan by simp

/--
lemma `f_mem_lieAlgebra` / 引理 `f_mem_lieAlgebra`

English:
lemma f_mem_lieAlgebra
  given: [Fintype ι] [DecidableEq ι] (i : b.support)
  proof: LieSubalgebra.subset_lieSpan by simp

中文:
引理 f_mem_lieAlgebra
  条件: [有限类型 ι] [DecidableEq ι] (i : b.support)
  证明: LieSubalgebra.subset_lieSpan by simp

Depends on / 依赖: LieSubalgebra, LieSubalgebra.subset_lieSpan, subset_lieSpan
-/
lemma f_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    f i in lieAlgebra b :=
LieSubalgebra.subset_lieSpan by simp

/--
Definition of `h'` / `h'` 的定义

English:
definition h'
  signature: [Fintype ι] [DecidableEq ι] (i : b.support)
  body: ⟨⟨h i, h_mem_lieAlgebra i⟩, h_mem_cartanSubalgebra' i (h_mem_lieAlgebra i)⟩

中文:
定义 h'
  签名: [有限类型 ι] [DecidableEq ι] (i : b.support)
  定义体: ⟨⟨h i, h_mem_lieAlgebra i⟩, h_mem_cartanSubalgebra' i (h_mem_lieAlgebra i)⟩

Depends on / 依赖: h_mem_cartanSubalgebra, h_mem_lieAlgebra
-/
def h' [Fintype ι] [DecidableEq ι] (i : b.support) : cartanSubalgebra' b :=
  ⟨⟨h i, h_mem_lieAlgebra i⟩, h_mem_cartanSubalgebra' i (h_mem_lieAlgebra i)⟩

variable (b) in
@[simp]
/--
lemma `span_range_h'_eq_top` / 引理 `span_range_h'_eq_top`

English:
lemma span_range_h'_eq_top
  given: [Fintype ι] [DecidableEq ι]
  proof: by
  rw [eq_top_iff]
  rintro ⟨⟨x, -⟩, hx : x in span R (range h)⟩ -
  let g : cartanSubalgebra' b ->ₗ[R] Matrix (b.support oplus ι) (b.support oplus ι) R :=
    (lieAlgebra b).subtype ∘ₗ (cartanSubalgebra' b).subtype
  suffices x in (span R (range h')).map g by
    rwa [← SetLike.mem_coe, ← (injective_subtype _).mem_set_image,
        ← (injective_subtype _).mem_set_image, ← image_comp]
  rwa [map_span, ← range_comp]

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in

中文:
引理 span_range_h'_eq_top
  条件: [有限类型 ι] [DecidableEq ι]
  证明: by
  rw [eq_top_iff]
  rintro ⟨⟨x, -⟩, hx : x in span R (range h)⟩ -
  let g : cartanSubalgebra' b ->ₗ[R] Matrix (b.support oplus ι) (b.support oplus ι) R :=
    (lieAlgebra b).subtype ∘ₗ (cartanSubalgebra' b).subtype
  suffices x in (span R (range h')).map g by
    rwa [← SetLike.mem_coe, ← (injective_subtype _).mem_set_image,
        ← (injective_subtype _).mem_set_image, ← image_comp]
  rwa [map_span, ← range_comp]

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in

Depends on / 依赖: Matrix, SetLike, SetLike.mem_coe, b.support, cartanSubalgebra, eq_top_iff, image_comp, injective_subtype, lieAlgebra, map_span, mem_coe, mem_set_image, range_comp, subtype, support
-/
lemma span_range_h'_eq_top [Fintype ι] [DecidableEq ι] :
    span R (range h') = (⊤ : Submodule R (cartanSubalgebra' b)) := by
  rw [eq_top_iff]
  rintro ⟨⟨x, -⟩, hx : x in span R (range h)⟩ -
  let g : cartanSubalgebra' b ->ₗ[R] Matrix (b.support oplus ι) (b.support oplus ι) R :=
    (lieAlgebra b).subtype ∘ₗ (cartanSubalgebra' b).subtype
  suffices x in (span R (range h')).map g by
    rwa [← SetLike.mem_coe, ← (injective_subtype _).mem_set_image,
        ← (injective_subtype _).mem_set_image, ← image_comp]
  rwa [map_span, ← range_comp]

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
/--
lemma `ω_mul_ω` / 引理 `ω_mul_ω`

English:
lemma ω_mul_ω
  given: [DecidableEq ι] [Fintype ι]
  proof: by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

omit [Finite ι] [IsDomain R] in

中文:
引理 ω_mul_ω
  条件: [DecidableEq ι] [有限类型 ι]
  证明: by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

omit [Finite ι] [IsDomain R] in
-/
@[simp] lemma ω_mul_ω [DecidableEq ι] [Fintype ι] :
    ω b * ω b = 1 := by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

omit [Finite ι] [IsDomain R] in
/--
lemma `ω_mul_h` / 引理 `ω_mul_h`

English:
lemma ω_mul_h
  given: [Fintype ι] (i : b.support)
  proof: by
  classical
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop

中文:
引理 ω_mul_h
  条件: [有限类型 ι] (i : b.support)
  证明: by
  classical
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop

Depends on / 依赖: Fintype, Fintype.sum_sum_type, Matrix, Matrix.fromBlocks_apply, Matrix.mul_apply, classical, mul_apply, sum_sum_type
-/
lemma ω_mul_h [Fintype ι] (i : b.support) :
    ω b * h i = -h i * ω b := by
  classical
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop

/--
lemma `ω_mul_e` / 引理 `ω_mul_e`

English:
lemma ω_mul_e
  given: [Fintype ι] (i : b.support)
  proof: by
  let := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by simp_all)]
    simp [← ite_and, and_comm, -indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]

中文:
引理 ω_mul_e
  条件: [有限类型 ι] (i : b.support)
  证明: by
  let := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by simp_all)]
    simp [← ite_and, and_comm, -indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_eq_single_of_mem, Finset.sum_ite_eq, Fintype, Fintype.sum_sum_type, Matrix, Matrix.fromBlocks_apply, Matrix.mul_apply, Matrix.of_apply, P.indexNeg, and_comm, classical, indexNeg, indexNeg_neg, ite_and, mem_univ, mul_apply, mul_ite, mul_zero
-/
lemma ω_mul_e [Fintype ι] (i : b.support) :
    ω b * e i = f i * ω b := by
  let := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by simp_all)]
    simp [← ite_and, and_comm, -indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]

/--
lemma `ω_mul_f` / 引理 `ω_mul_f`

English:
lemma ω_mul_f
  given: [Fintype ι] (i : b.support)
  proof: by
  classical
  have := congr_arg (· * ω b) (congr_arg (ω b * ·) (ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm

中文:
引理 ω_mul_f
  条件: [有限类型 ι] (i : b.support)
  证明: by
  classical
  have := congr_arg (· * ω b) (congr_arg (ω b * ·) (ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm

Depends on / 依赖: classical, congr_arg, mul_assoc, this.symm
-/
lemma ω_mul_f [Fintype ι] (i : b.support) :
    ω b * f i = e i * ω b := by
  classical
  have := congr_arg (· * ω b) (congr_arg (ω b * ·) (ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm

/--
lemma `lie_e_f_mul_ω` / 引理 `lie_e_f_mul_ω`

English:
lemma lie_e_f_mul_ω
  given: [Fintype ι] (i j : b.support)
  proof: by
  calc ⁅e i, f j⁆ * ω b = e i * f j * ω b - f j * e i * ω b := by rw [Ring.lie_def, sub_mul]
                      _ = e i * (f j * ω b) - f j * (e i * ω b) := by rw [mul_assoc, mul_assoc]
                      _ = e i * (ω b * e j) - f j * (ω b * f i) := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = (e i * ω b) * e j - (f j * ω b) * f i := by rw [← mul_assoc, ← mul_assoc]
                      _ = (ω b * f i) * e j - (ω b * e j) * f i := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = ω b * (f i * e j) - ω b * (e j * f i) := by rw [mul_assoc, mul_assoc]
                      _ = -ω b * ⁅e j, f i⁆ := ?_
  rw [Ring.lie_def]; rw [mul_sub]; rw [neg_mul]; rw [neg_mul]; rw [sub_neg_eq_add]
  abel

中文:
引理 lie_e_f_mul_ω
  条件: [有限类型 ι] (i j : b.support)
  证明: by
  calc ⁅e i, f j⁆ * ω b = e i * f j * ω b - f j * e i * ω b := by rw [Ring.lie_def, sub_mul]
                      _ = e i * (f j * ω b) - f j * (e i * ω b) := by rw [mul_assoc, mul_assoc]
                      _ = e i * (ω b * e j) - f j * (ω b * f i) := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = (e i * ω b) * e j - (f j * ω b) * f i := by rw [← mul_assoc, ← mul_assoc]
                      _ = (ω b * f i) * e j - (ω b * e j) * f i := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = ω b * (f i * e j) - ω b * (e j * f i) := by rw [mul_assoc, mul_assoc]
                      _ = -ω b * ⁅e j, f i⁆ := ?_
  rw [Ring.lie_def]; rw [mul_sub]; rw [neg_mul]; rw [neg_mul]; rw [sub_neg_eq_add]
  abel

Depends on / 依赖: Ring.lie_def, lie_def, mul_assoc, sub_mul
-/
lemma lie_e_f_mul_ω [Fintype ι] (i j : b.support) :
    ⁅e i, f j⁆ * ω b = -ω b * ⁅e j, f i⁆ := by
  calc ⁅e i, f j⁆ * ω b = e i * f j * ω b - f j * e i * ω b := by rw [Ring.lie_def, sub_mul]
                      _ = e i * (f j * ω b) - f j * (e i * ω b) := by rw [mul_assoc, mul_assoc]
                      _ = e i * (ω b * e j) - f j * (ω b * f i) := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = (e i * ω b) * e j - (f j * ω b) * f i := by rw [← mul_assoc, ← mul_assoc]
                      _ = (ω b * f i) * e j - (ω b * e j) * f i := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = ω b * (f i * e j) - ω b * (e j * f i) := by rw [mul_assoc, mul_assoc]
                      _ = -ω b * ⁅e j, f i⁆ := ?_
  rw [Ring.lie_def]; rw [mul_sub]; rw [neg_mul]; rw [neg_mul]; rw [sub_neg_eq_add]
  abel

variable [DecidableEq ι]

/--
Definition of `u` / `u` 的定义

English:
abbreviation u
  signature: (i : b.support)
  body: Pi.single (Sum.inl i) 1

中文:
缩写 u
  签名: (i : b.support)
  定义体: Pi.single (Sum.inl i) 1

Depends on / 依赖: Pi.single, Sum.inl, single
-/
abbrev u (i : b.support) : b.support oplus ι -> R := Pi.single (Sum.inl i) 1

variable (b) in
/--
Definition of `v` / `v` 的定义

English:
abbreviation v
  signature: (i : ι)
  body: Pi.single (Sum.inr i) 1

中文:
缩写 v
  签名: (i : ι)
  定义体: Pi.single (Sum.inr i) 1

Depends on / 依赖: Pi.single, Sum.inr, single
-/
abbrev v (i : ι) : b.support oplus ι -> R := Pi.single (Sum.inr i) 1

variable (b) in
omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
/--
lemma `apply_inr_eq_zero_of_mem_span_range_u` / 引理 `apply_inr_eq_zero_of_mem_span_range_u`

English:
lemma apply_inr_eq_zero_of_mem_span_range_u
  statement: (j : ι) {x : b.support oplus ι -> R}
  proof: by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; simp [u]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

中文:
引理 apply_inr_eq_zero_of_mem_span_range_u
  结论: (j : ι) {x : b.support oplus ι -> R}
  证明: by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; simp [u]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

Depends on / 依赖: span_induction
-/
lemma apply_inr_eq_zero_of_mem_span_range_u (j : ι) {x : b.support oplus ι -> R}
    (hx : x in span R (range u)) : x (Sum.inr j) = 0 := by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; simp [u]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

/--
lemma `lie_e_lie_f_apply` / 引理 `lie_e_lie_f_apply`

English:
lemma lie_e_lie_f_apply
  given: [Fintype ι] (i j : b.support)
  proof: by
  ext (k | k)
  · simp [e, f, Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [e, f, Matrix.mulVec, dotProduct, P.ne_zero]

中文:
引理 lie_e_lie_f_apply
  条件: [有限类型 ι] (i j : b.support)
  证明: by
  ext (k | k)
  · simp [e, f, Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [e, f, Matrix.mulVec, dotProduct, P.ne_zero]

Depends on / 依赖: Matrix, Matrix.mulVec, P.ne_zero, Pi.single_apply, dotProduct, mulVec, ne_zero, single_apply
-/
lemma lie_e_lie_f_apply [Fintype ι] (i j : b.support) :
    ⁅e i, ⁅f i, u j⁆⁆ = |b.cartanMatrix i j| • u i := by
  ext (k | k)
  · simp [e, f, Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [e, f, Matrix.mulVec, dotProduct, P.ne_zero]

variable [Fintype ι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLieAbelian (cartanSubalgebra b)
  body: by
  rw [cartanSubalgebra_eq_lieSpan]; rw [LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact lie_h_h i j

中文:
实例 :
  签名: IsLieAbelian (cartanSubalgebra b)
  定义体: by
  rw [cartanSubalgebra_eq_lieSpan]; rw [LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact lie_h_h i j

Depends on / 依赖: LieSubalgebra, LieSubalgebra.isLieAbelian_lieSpan_iff, cartanSubalgebra_eq_lieSpan, isLieAbelian_lieSpan_iff, lie_h_h
-/
instance : IsLieAbelian (cartanSubalgebra b) := by
  rw [cartanSubalgebra_eq_lieSpan]; rw [LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact lie_h_h i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLieAbelian (cartanSubalgebra' b)
  body: by
  refine ⟨fun ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ => ?_⟩
  let x' : cartanSubalgebra b := ⟨x, hx'⟩
  let y' : cartanSubalgebra b := ⟨y, hy'⟩
  suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
  simp [trivial_lie_zero]

中文:
实例 :
  签名: IsLieAbelian (cartanSubalgebra' b)
  定义体: by
  refine ⟨fun ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ => ?_⟩
  let x' : cartanSubalgebra b := ⟨x, hx'⟩
  let y' : cartanSubalgebra b := ⟨y, hy'⟩
  suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
  simp [trivial_lie_zero]

Depends on / 依赖: Subtype, Subtype.ext_iff, cartanSubalgebra, ext_iff, trivial_lie_zero
-/
instance : IsLieAbelian (cartanSubalgebra' b) := by
  refine ⟨fun ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ => ?_⟩
  let x' : cartanSubalgebra b := ⟨x, hx'⟩
  let y' : cartanSubalgebra b := ⟨y, hy'⟩
  suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
  simp [trivial_lie_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule.IsTriangularizable R (cartanSubalgebra' b) (b.support oplus ι -> R)
  body: by
  refine ⟨fun ⟨⟨x, hx'⟩, hx⟩ => ?_⟩
  obtain ⟨d, rfl⟩ : exists d : b.support oplus ι -> R, Matrix.diagonal d = x :=
span_range_h_le_range_diagonal by simpa using! hx
  simp

中文:
实例 :
  签名: Lie模.是Triangularizable R (cartanSubalgebra' b) (b.support oplus ι -> R)
  定义体: by
  refine ⟨fun ⟨⟨x, hx'⟩, hx⟩ => ?_⟩
  obtain ⟨d, rfl⟩ : exists d : b.support oplus ι -> R, Matrix.diagonal d = x :=
span_range_h_le_range_diagonal by simpa using! hx
  simp

Depends on / 依赖: Matrix, Matrix.diagonal, b.support, diagonal, span_range_h_le_range_diagonal, support
-/
instance : LieModule.IsTriangularizable R (cartanSubalgebra' b) (b.support oplus ι -> R) := by
  refine ⟨fun ⟨⟨x, hx'⟩, hx⟩ => ?_⟩
  obtain ⟨d, rfl⟩ : exists d : b.support oplus ι -> R, Matrix.diagonal d = x :=
span_range_h_le_range_diagonal by simpa using! hx
  simp

/--
lemma `cartanSubalgebra_le_lieAlgebra` / 引理 `cartanSubalgebra_le_lieAlgebra`

English:
lemma cartanSubalgebra_le_lieAlgebra
  proof: by
  rw [cartanSubalgebra]; rw [lieAlgebra]; rw [← LieSubalgebra.toSubmodule_le_toSubmodule]; rw [Submodule.span_le]
  rintro - ⟨i, rfl⟩
exact LieSubalgebra.subset_lieSpan Or.inl Or.inl mem_range_self i

中文:
引理 cartanSubalgebra_le_lieAlgebra
  证明: by
  rw [cartanSubalgebra]; rw [lieAlgebra]; rw [← LieSubalgebra.toSubmodule_le_toSubmodule]; rw [Submodule.span_le]
  rintro - ⟨i, rfl⟩
exact LieSubalgebra.subset_lieSpan Or.inl Or.inl mem_range_self i

Depends on / 依赖: LieSubalgebra, LieSubalgebra.subset_lieSpan, LieSubalgebra.toSubmodule_le_toSubmodule, Or.inl, Submodule, Submodule.span_le, cartanSubalgebra, lieAlgebra, mem_range_self, span_le, subset_lieSpan, toSubmodule_le_toSubmodule
-/
lemma cartanSubalgebra_le_lieAlgebra :
    cartanSubalgebra b <= lieAlgebra b := by
  rw [cartanSubalgebra]; rw [lieAlgebra]; rw [← LieSubalgebra.toSubmodule_le_toSubmodule]; rw [Submodule.span_le]
  rintro - ⟨i, rfl⟩
exact LieSubalgebra.subset_lieSpan Or.inl Or.inl mem_range_self i

/--
lemma `e_lie_u` / 引理 `e_lie_u`

English:
lemma e_lie_u
  given: (i j : b.support)
  proof: by
  ext (k | k) <;> simp [e, Pi.single_apply]

中文:
引理 e_lie_u
  条件: (i j : b.support)
  证明: by
  ext (k | k) <;> simp [e, Pi.single_apply]

Depends on / 依赖: Pi.single_apply, single_apply
-/
lemma e_lie_u (i j : b.support) :
    ⁅e i, u j⁆ = |b.cartanMatrix i j| • v b i := by
  ext (k | k) <;> simp [e, Pi.single_apply]

/--
lemma `e_lie_v_ne` / 引理 `e_lie_v_ne`

English:
lemma e_lie_v_ne
  given: {i j : ι} {k : b.support} (h : P.root j = P.root k + P.root i)
  proof: by
  let := P.indexNeg
  ext (l | l)
· replace h : i != -k := by rintro rfl; exact P.ne_zero j by simpa using h
    simp [e, h, -indexNeg_neg]
  · simp [e, ← h, Pi.single_apply]

中文:
引理 e_lie_v_ne
  条件: {i j : ι} {k : b.support} (h : P.root j = P.root k + P.root i)
  证明: by
  let := P.indexNeg
  ext (l | l)
· replace h : i != -k := by rintro rfl; exact P.ne_zero j by simpa using h
    simp [e, h, -indexNeg_neg]
  · simp [e, ← h, Pi.single_apply]

Depends on / 依赖: P.indexNeg, P.ne_zero, Pi.single_apply, indexNeg, indexNeg_neg, ne_zero, replace, single_apply
-/
lemma e_lie_v_ne {i j : ι} {k : b.support} (h : P.root j = P.root k + P.root i) :
    ⁅e k, v b i⁆ = (P.chainBotCoeff k i + 1 : R) • v b j := by
  let := P.indexNeg
  ext (l | l)
· replace h : i != -k := by rintro rfl; exact P.ne_zero j by simpa using h
    simp [e, h, -indexNeg_neg]
  · simp [e, ← h, Pi.single_apply]

/--
lemma `f_lie_v_same` / 引理 `f_lie_v_same`

English:
lemma f_lie_v_same
  given: (i : b.support)
  proof: by
  ext (j | j)
  · simp [f, Pi.single_apply]
  · simp [f, P.ne_zero j]

中文:
引理 f_lie_v_same
  条件: (i : b.support)
  证明: by
  ext (j | j)
  · simp [f, Pi.single_apply]
  · simp [f, P.ne_zero j]

Depends on / 依赖: P.ne_zero, Pi.single_apply, ne_zero, single_apply
-/
lemma f_lie_v_same (i : b.support) :
    ⁅f i, v b i⁆ = u i := by
  ext (j | j)
  · simp [f, Pi.single_apply]
  · simp [f, P.ne_zero j]

/--
lemma `f_lie_v_ne` / 引理 `f_lie_v_ne`

English:
lemma f_lie_v_ne
  given: {i j : ι} {k : b.support} (h : P.root i = P.root j + P.root k)
  proof: by
  ext (l | l)
· replace h : i != k := by rintro rfl; exact P.ne_zero j by simpa using h
    simp [f, h]
  · simp [f, h, Pi.single_apply]

中文:
引理 f_lie_v_ne
  条件: {i j : ι} {k : b.support} (h : P.root i = P.root j + P.root k)
  证明: by
  ext (l | l)
· replace h : i != k := by rintro rfl; exact P.ne_zero j by simpa using h
    simp [f, h]
  · simp [f, h, Pi.single_apply]

Depends on / 依赖: P.ne_zero, Pi.single_apply, ne_zero, replace, single_apply
-/
lemma f_lie_v_ne {i j : ι} {k : b.support} (h : P.root i = P.root j + P.root k) :
    ⁅f k, v b i⁆ = (P.chainTopCoeff k i + 1 : R) • v b j := by
  ext (l | l)
· replace h : i != k := by rintro rfl; exact P.ne_zero j by simpa using h
    simp [f, h]
  · simp [f, h, Pi.single_apply]

section ωConj

variable (b) in
/--
Definition of `ωConj` / `ωConj` 的定义

English:
definition ωConj
  signature: :
  body: ω b * x * ω b
  invFun x := ω b * x * ω b
  map_add' x y := by noncomm_ring
  map_smul' t x := by simp
  map_lie' {x y} := by
    simp only [Ring.lie_def]
    nth_rw 1 [← mul_one x]
    nth_rw 2 [← one_mul x]
    simp only [← ω_mul_ω (b := b)]
    noncomm_ring
  left_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
  right_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]

中文:
定义 ωConj
  签名: :
  定义体: ω b * x * ω b
  invFun x := ω b * x * ω b
  map_add' x y := by noncomm_ring
  map_smul' t x := by simp
  map_lie' {x y} := by
    simp only [Ring.lie_def]
    nth_rw 1 [← mul_one x]
    nth_rw 2 [← one_mul x]
    simp only [← ω_mul_ω (b := b)]
    noncomm_ring
  left_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
  right_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
-/
@[simps] def ωConj :
    Matrix (b.support oplus ι) (b.support oplus ι) R ≃ₗ⁅R⁆ Matrix (b.support oplus ι) (b.support oplus ι) R where
  toFun x := ω b * x * ω b
  invFun x := ω b * x * ω b
  map_add' x y := by noncomm_ring
  map_smul' t x := by simp
  map_lie' {x y} := by
    simp only [Ring.lie_def]
    nth_rw 1 [← mul_one x]
    nth_rw 2 [← one_mul x]
    simp only [← ω_mul_ω (b := b)]
    noncomm_ring
  left_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
  right_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]

/--
lemma `ωConj_mem_of_mem` / 引理 `ωConj_mem_of_mem`

English:
lemma ωConj_mem_of_mem
  proof: by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩) : (exists j, h j = u) ∨ (exists j, e j = u) ∨ (exists j, f j = u) := by
      simpa only [mem_union, mem_range, or_assoc] using hu
    · rw [← neg_mem_iff]
exact LieSubalgebra.subset_lieSpan by simp [ω_mul_h, mul_assoc]
· exact LieSubalgebra.subset_lieSpan by simp [ω_mul_e, mul_assoc]
· exact LieSubalgebra.subset_lieSpan by simp [ω_mul_f, mul_assoc]
  | zero => simp
  | add u v _ _ hu hv => simpa [mul_add, add_mul] using add_mem hu hv
  | smul t u _ hu => simpa using SMulMemClass.smul_mem _ hu
  | lie u v _ _ hu hv =>
    rw [LieEquiv.map_lie]
    exact (lieAlgebra b).lie_mem hu hv

中文:
引理 ωConj_mem_of_mem
  证明: by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩) : (exists j, h j = u) ∨ (exists j, e j = u) ∨ (exists j, f j = u) := by
      simpa only [mem_union, mem_range, or_assoc] using hu
    · rw [← neg_mem_iff]
exact LieSubalgebra.subset_lieSpan by simp [ω_mul_h, mul_assoc]
· exact LieSubalgebra.subset_lieSpan by simp [ω_mul_e, mul_assoc]
· exact LieSubalgebra.subset_lieSpan by simp [ω_mul_f, mul_assoc]
  | zero => simp
  | add u v _ _ hu hv => simpa [mul_add, add_mul] using add_mem hu hv
  | smul t u _ hu => simpa using SMulMemClass.smul_mem _ hu
  | lie u v _ _ hu hv =>
    rw [LieEquiv.map_lie]
    exact (lieAlgebra b).lie_mem hu hv

Depends on / 依赖: LieSubalgebra, LieSubalgebra.lieSpan_induction, LieSubalgebra.subset_lieSpan, lieSpan_induction, mem_range, mem_union, mul_assoc, neg_mem_iff, or_assoc, subset_lieSpan
-/
lemma ωConj_mem_of_mem
    {x : Matrix (b.support oplus ι) (b.support oplus ι) R} (hx : x in lieAlgebra b) :
    ωConj b x in lieAlgebra b := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩) : (exists j, h j = u) ∨ (exists j, e j = u) ∨ (exists j, f j = u) := by
      simpa only [mem_union, mem_range, or_assoc] using hu
    · rw [← neg_mem_iff]
exact LieSubalgebra.subset_lieSpan by simp [ω_mul_h, mul_assoc]
· exact LieSubalgebra.subset_lieSpan by simp [ω_mul_e, mul_assoc]
· exact LieSubalgebra.subset_lieSpan by simp [ω_mul_f, mul_assoc]
  | zero => simp
  | add u v _ _ hu hv => simpa [mul_add, add_mul] using add_mem hu hv
  | smul t u _ hu => simpa using SMulMemClass.smul_mem _ hu
  | lie u v _ _ hu hv =>
    rw [LieEquiv.map_lie]
    exact (lieAlgebra b).lie_mem hu hv

variable (N : LieSubmodule R (lieAlgebra b) (b.support oplus ι -> R))

/--
Definition of `ωConjLieSubmodule` / `ωConjLieSubmodule` 的定义

English:
definition ωConjLieSubmodule
  signature: :
  body: N.toSubmodule.comap (ω b).toLin'
  lie_mem A {x} hx := by
    let A' : lieAlgebra b := ⟨ωConj b _, ωConj_mem_of_mem A.property⟩
    suffices ⁅A', ω b *ᵥ x⁆ in N by simpa [A', mul_assoc] using this
    exact LieSubmodule.lie_mem _ hx

中文:
定义 ωConjLieSubmodule
  签名: :
  定义体: N.toSubmodule.comap (ω b).toLin'
  lie_mem A {x} hx := by
    let A' : lieAlgebra b := ⟨ωConj b _, ωConj_mem_of_mem A.property⟩
    suffices ⁅A', ω b *ᵥ x⁆ in N by simpa [A', mul_assoc] using this
    exact LieSubmodule.lie_mem _ hx

Depends on / 依赖: N.toSubmodule.comap, toSubmodule
-/
def ωConjLieSubmodule :
    LieSubmodule R (lieAlgebra b) (b.support oplus ι -> R) where
  __ := N.toSubmodule.comap (ω b).toLin'
  lie_mem A {x} hx := by
    let A' : lieAlgebra b := ⟨ωConj b _, ωConj_mem_of_mem A.property⟩
    suffices ⁅A', ω b *ᵥ x⁆ in N by simpa [A', mul_assoc] using this
    exact LieSubmodule.lie_mem _ hx

/--
lemma `mem_ωConjLieSubmodule_iff` / 引理 `mem_ωConjLieSubmodule_iff`

English:
lemma mem_ωConjLieSubmodule_iff
  given: {x : b.support oplus ι -> R}
  proof: Iff.rfl

中文:
引理 mem_ωConjLieSubmodule_iff
  条件: {x : b.support oplus ι -> R}
  证明: Iff.rfl
-/
@[simp] lemma mem_ωConjLieSubmodule_iff {x : b.support oplus ι -> R} :
    x in ωConjLieSubmodule N ↔ (ω b) *ᵥ x in N :=
  Iff.rfl

/--
lemma `ωConjLieSubmodule_eq_top_iff` / 引理 `ωConjLieSubmodule_eq_top_iff`

English:
lemma ωConjLieSubmodule_eq_top_iff
  statement: ωConjLieSubmodule N = ⊤ ↔ N = ⊤
  proof: by
  rw [← LieSubmodule.toSubmodule_eq_top]
  let e : Submodule R (b.support oplus ι -> R) ≃o Submodule R (b.support oplus ι -> R) :=
    Submodule.orderIsoMapComapOfBijective (ω b).toLin' (Involutive.bijective fun x => by simp)
  change e.symm N = ⊤ ↔ _
  simp

中文:
引理 ωConjLieSubmodule_eq_top_iff
  结论: ωConjLieSubmodule N = ⊤ ↔ N = ⊤
  证明: by
  rw [← LieSubmodule.toSubmodule_eq_top]
  let e : Submodule R (b.support oplus ι -> R) ≃o Submodule R (b.support oplus ι -> R) :=
    Submodule.orderIsoMapComapOfBijective (ω b).toLin' (Involutive.bijective fun x => by simp)
  change e.symm N = ⊤ ↔ _
  simp
-/
@[simp] lemma ωConjLieSubmodule_eq_top_iff : ωConjLieSubmodule N = ⊤ ↔ N = ⊤ := by
  rw [← LieSubmodule.toSubmodule_eq_top]
  let e : Submodule R (b.support oplus ι -> R) ≃o Submodule R (b.support oplus ι -> R) :=
    Submodule.orderIsoMapComapOfBijective (ω b).toLin' (Involutive.bijective fun x => by simp)
  change e.symm N = ⊤ ↔ _
  simp

end ωConj

end RootPairing.GeckConstruction
