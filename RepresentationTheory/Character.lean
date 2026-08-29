/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

A key result is the orthogonality of characters for irreducible representations of finite group
over an algebraically closed field whose characteristic doesn't divide the order of the group. It
is the theorem `char_orthonormal`

## Implementation notes

Irreducible representations are implemented categorically, using the `CategoryTheory.Simple` class
defined in `Mathlib/CategoryTheory/Simple.lean`

## TODO
* Once we have the monoidal closed structure on `FDRep k G` and a better API for the rigid
  structure, `char_dual` and `char_linHom` should probably be stated
  in terms of `Vᘁ` and `ihom V W`.
-/

@[expose] public section


noncomputable section

universe u v

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation Module

variable {k : Type u} [Field k]

namespace Representation

section Monoid

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

/--
Definition of `character` / `character` 的定义

English:
definition character
  signature: (g : G)
  body: LinearMap.trace k V (ρ g)

omit [FiniteDimensional k V] in

中文:
定义 character
  签名: (g : G)
  定义体: LinearMap.trace k V (ρ g)

omit [FiniteDimensional k V] in

Depends on / 依赖: LinearMap, LinearMap.trace
-/
def character (g : G) :=
  LinearMap.trace k V (ρ g)

omit [FiniteDimensional k V] in
/--
theorem `char_mul_comm` / 定理 `char_mul_comm`

English:
theorem char_mul_comm
  given: (g : G) (h : G)
  proof: by simp only [trace_mul_comm, character, map_mul]

@[simp]

中文:
定理 char_mul_comm
  条件: (g : G) (h : G)
  证明: by simp only [trace_mul_comm, character, map_mul]

@[simp]

Depends on / 依赖: character, map_mul, trace_mul_comm
-/
theorem char_mul_comm (g : G) (h : G) :
    ρ.character (h * g) = ρ.character (g * h) := by simp only [trace_mul_comm, character, map_mul]

@[simp]
/--
theorem `char_one` / 定理 `char_one`

English:
theorem char_one
  given: (ρ : Representation k G V)
  statement: ρ.character 1 = Module.finrank k V
  proof: by
  simp only [character, map_one, trace_one]

中文:
定理 char_one
  条件: (ρ : Representation k G V)
  结论: ρ.character 1 = Module.finrank k V
  证明: by
  simp only [character, map_one, trace_one]

Depends on / 依赖: character, map_one, trace_one
-/
theorem char_one (ρ : Representation k G V) : ρ.character 1 = Module.finrank k V := by
  simp only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp]
/--
theorem `char_tensor` / 定理 `char_tensor`

English:
theorem char_tensor
  statement: (tprod ρ σ).character = ρ.character * σ.character
  proof: by
  ext g; convert! trace_tensorProduct' (ρ g) (σ g)

omit [FiniteDimensional k V] [FiniteDimensional k W] in

中文:
定理 char_tensor
  结论: (tprod ρ σ).character = ρ.character * σ.character
  证明: by
  ext g; convert! trace_tensorProduct' (ρ g) (σ g)

omit [FiniteDimensional k V] [FiniteDimensional k W] in

Depends on / 依赖: convert, trace_tensorProduct
-/
theorem char_tensor : (tprod ρ σ).character = ρ.character * σ.character := by
  ext g; convert! trace_tensorProduct' (ρ g) (σ g)

omit [FiniteDimensional k V] [FiniteDimensional k W] in
variable {ρ σ} in
/--
theorem `char_iso` / 定理 `char_iso`

English:
theorem char_iso
  given: (φ : Equiv ρ σ)
  statement: ρ.character = σ.character
  proof: by
  ext g
  simp [character, ← φ.conj_apply_self]

中文:
定理 char_iso
  条件: (φ : Equiv ρ σ)
  结论: ρ.character = σ.character
  证明: by
  ext g
  simp [character, ← φ.conj_apply_self]

Depends on / 依赖: character, conj_apply_self
-/
theorem char_iso (φ : Equiv ρ σ) : ρ.character = σ.character := by
  ext g
  simp [character, ← φ.conj_apply_self]

end Monoid

section Group

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

omit [FiniteDimensional k V] in
/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
/--
theorem `char_conj` / 定理 `char_conj`

English:
theorem char_conj
  given: (g : G) (h : G)
  statement: ρ.character (h * g * h⁻¹) = ρ.character g
  proof: by
  rw [char_mul_comm]; rw [inv_mul_cancel_left]

@[simp]

中文:
定理 char_conj
  条件: (g : G) (h : G)
  结论: ρ.character (h * g * h⁻¹) = ρ.character g
  证明: by
  rw [char_mul_comm]; rw [inv_mul_cancel_left]

@[simp]

Depends on / 依赖: char_mul_comm, inv_mul_cancel_left
-/
theorem char_conj (g : G) (h : G) : ρ.character (h * g * h⁻¹) = ρ.character g := by
  rw [char_mul_comm]; rw [inv_mul_cancel_left]

@[simp]
/--
theorem `char_dual` / 定理 `char_dual`

English:
theorem char_dual
  given: (g : G)
  statement: ρ.dual.character g = ρ.character g⁻¹
  proof: trace_transpose' (ρ g⁻¹)

@[simp]

中文:
定理 char_dual
  条件: (g : G)
  结论: ρ.dual.character g = ρ.character g⁻¹
  证明: trace_transpose' (ρ g⁻¹)

@[simp]

Depends on / 依赖: trace_transpose
-/
theorem char_dual (g : G) : ρ.dual.character g = ρ.character g⁻¹ :=
  trace_transpose' (ρ g⁻¹)

@[simp]
/--
theorem `char_linHom` / 定理 `char_linHom`

English:
theorem char_linHom
  given: (g : G)
  proof: by
  rw [← char_iso (Equiv.dualTensorHom ρ σ)]; rw [char_tensor]; rw [Pi.mul_apply]; rw [char_dual]

中文:
定理 char_linHom
  条件: (g : G)
  证明: by
  rw [← char_iso (Equiv.dualTensorHom ρ σ)]; rw [char_tensor]; rw [Pi.mul_apply]; rw [char_dual]

Depends on / 依赖: Equiv.dualTensorHom, Pi.mul_apply, char_dual, char_iso, char_tensor, dualTensorHom, mul_apply
-/
theorem char_linHom (g : G) :
    (linHom ρ σ).character g = ρ.character g⁻¹ * σ.character g := by
  rw [← char_iso (Equiv.dualTensorHom ρ σ)]; rw [char_tensor]; rw [Pi.mul_apply]; rw [char_dual]

variable [Fintype G] [Invertible (Nat.card G : k)]

/--
theorem `card_inv_mul_sum_char_eq_finrank` / 定理 `card_inv_mul_sum_char_eq_finrank`

English:
theorem card_inv_mul_sum_char_eq_finrank
  proof: by
  have : Invertible (Fintype.card G : k) := by rw [Fintype.card_eq_nat_card]; assumption
  rw [← (isProj_averageMap ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

中文:
定理 card_inv_mul_sum_char_eq_finrank
  证明: by
  have : Invertible (Fintype.card G : k) := by rw [Fintype.card_eq_nat_card]; assumption
  rw [← (isProj_averageMap ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_eq_nat_card, GroupAlgebra, GroupAlgebra.average, Invertible, _root_, _root_.map_sum, average, card_eq_nat_card, character, isProj_averageMap, map_sum
-/
theorem card_inv_mul_sum_char_eq_finrank :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g = finrank k (invariants ρ) := by
  have : Invertible (Fintype.card G : k) := by rw [Fintype.card_eq_nat_card]; assumption
  rw [← (isProj_averageMap ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

/--
theorem `card_inv_mul_sum_char_mul_char_eq_finrank` / 定理 `card_inv_mul_sum_char_mul_char_eq_finrank`

English:
theorem card_inv_mul_sum_char_mul_char_eq_finrank
  proof: by
  simp_rw [mul_comm, ← char_linHom, card_inv_mul_sum_char_eq_finrank,
    (invariantsEquivIntertwiningMap ρ σ).finrank_eq]

中文:
定理 card_inv_mul_sum_char_mul_char_eq_finrank
  证明: by
  simp_rw [mul_comm, ← char_linHom, card_inv_mul_sum_char_eq_finrank,
    (invariantsEquivIntertwiningMap ρ σ).finrank_eq]

Depends on / 依赖: card_inv_mul_sum_char_eq_finrank, char_linHom, finrank_eq, invariantsEquivIntertwiningMap, mul_comm, simp_rw
-/
theorem card_inv_mul_sum_char_mul_char_eq_finrank :
    (Nat.card G : k)⁻¹ * ∑ g : G, σ.character g * ρ.character g⁻¹ =
      finrank k (IntertwiningMap ρ σ) := by
  simp_rw [mul_comm, ← char_linHom, card_inv_mul_sum_char_eq_finrank,
    (invariantsEquivIntertwiningMap ρ σ).finrank_eq]

end Group

section Orthogonality

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

variable [Fintype G] [Invertible (Nat.card G : k)] [IsAlgClosed k]

open scoped Classical in
/--
theorem `char_orthonormal` / 定理 `char_orthonormal`

English:
theorem char_orthonormal
  given: [IsIrreducible ρ] [IsIrreducible σ]
  proof: by
  cases isEmpty_or_nonempty (Equiv σ ρ)
  · rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simpa [finrank_eq_zero_of_subsingleton]
  · obtain φ : σ.Equiv ρ := Classical.choice inferInstance
    rw [char_iso φ]; rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simp

中文:
定理 char_orthonormal
  条件: [IsIrreducible ρ] [IsIrreducible σ]
  证明: by
  cases isEmpty_or_nonempty (Equiv σ ρ)
  · rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simpa [finrank_eq_zero_of_subsingleton]
  · obtain φ : σ.Equiv ρ := Classical.choice inferInstance
    rw [char_iso φ]; rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simp

Depends on / 依赖: Classical, Classical.choice, card_inv_mul_sum_char_mul_char_eq_finrank, char_iso, choice, finrank_eq_zero_of_subsingleton, isEmpty_or_nonempty
-/
theorem char_orthonormal [IsIrreducible ρ] [IsIrreducible σ] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      if Nonempty (Equiv σ ρ) then ↑1 else ↑0 := by
  cases isEmpty_or_nonempty (Equiv σ ρ)
  · rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simpa [finrank_eq_zero_of_subsingleton]
  · obtain φ : σ.Equiv ρ := Classical.choice inferInstance
    rw [char_iso φ]; rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simp

end Orthogonality

end Representation

namespace FDRep

section Monoid

variable {G : Type v} [Monoid G]

/--
Definition of `character` / `character` 的定义

English:
definition character
  signature: (V : FDRep k G) (g : G)
  body: LinearMap.trace k V (V.ρ g)

中文:
定义 character
  签名: (V : FDRep k G) (g : G)
  定义体: LinearMap.trace k V (V.ρ g)

Depends on / 依赖: LinearMap, LinearMap.trace
-/
def character (V : FDRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)

/--
theorem `char_mul_comm` / 定理 `char_mul_comm`

English:
theorem char_mul_comm
  given: (V : FDRep k G) (g : G) (h : G)
  proof: by simp only [trace_mul_comm, character, map_mul]

@[simp]

中文:
定理 char_mul_comm
  条件: (V : FDRep k G) (g : G) (h : G)
  证明: by simp only [trace_mul_comm, character, map_mul]

@[simp]

Depends on / 依赖: character, map_mul, trace_mul_comm
-/
theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) :
    V.character (h * g) = V.character (g * h) := by simp only [trace_mul_comm, character, map_mul]

@[simp]
/--
theorem `char_one` / 定理 `char_one`

English:
theorem char_one
  given: (V : FDRep k G)
  statement: V.character 1 = Module.finrank k V
  proof: by
  simp only [character, map_one, trace_one]

中文:
定理 char_one
  条件: (V : FDRep k G)
  结论: V.character 1 = Module.finrank k V
  证明: by
  simp only [character, map_one, trace_one]

Depends on / 依赖: character, map_one, trace_one
-/
theorem char_one (V : FDRep k G) : V.character 1 = Module.finrank k V := by
  simp only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp]
/--
theorem `char_tensor` / 定理 `char_tensor`

English:
theorem char_tensor
  given: (V W : FDRep k G)
  statement: (V otimes W).character = V.character * W.character
  proof: by
  ext g; convert! trace_tensorProduct' (V.ρ g) (W.ρ g)

中文:
定理 char_tensor
  条件: (V W : FDRep k G)
  结论: (V otimes W).character = V.character * W.character
  证明: by
  ext g; convert! trace_tensorProduct' (V.ρ g) (W.ρ g)

Depends on / 依赖: convert, trace_tensorProduct
-/
theorem char_tensor (V W : FDRep k G) : (V otimes W).character = V.character * W.character := by
  ext g; convert! trace_tensorProduct' (V.ρ g) (W.ρ g)

/--
theorem `char_iso` / 定理 `char_iso`

English:
theorem char_iso
  given: {V W : FDRep k G} (i : V ≅ W)
  statement: V.character = W.character
  proof: by
  ext g
  simp only [character, FDRep.Iso.conj_ρ i]
  exact (trace_conj' (V.ρ g) _).symm

中文:
定理 char_iso
  条件: {V W : FDRep k G} (i : V ≅ W)
  结论: V.character = W.character
  证明: by
  ext g
  simp only [character, FDRep.Iso.conj_ρ i]
  exact (trace_conj' (V.ρ g) _).symm

Depends on / 依赖: FDRep.Iso.conj_, character, trace_conj
-/
theorem char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character := by
  ext g
  simp only [character, FDRep.Iso.conj_ρ i]
  exact (trace_conj' (V.ρ g) _).symm

end Monoid

section Group

variable {G : Type v} [Group G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
/--
theorem `char_conj` / 定理 `char_conj`

English:
theorem char_conj
  given: (V : FDRep k G) (g : G) (h : G)
  statement: V.character (h * g * h⁻¹) = V.character g
  proof: by
  rw [char_mul_comm]; rw [inv_mul_cancel_left]

@[simp]

中文:
定理 char_conj
  条件: (V : FDRep k G) (g : G) (h : G)
  结论: V.character (h * g * h⁻¹) = V.character g
  证明: by
  rw [char_mul_comm]; rw [inv_mul_cancel_left]

@[simp]

Depends on / 依赖: char_mul_comm, inv_mul_cancel_left
-/
theorem char_conj (V : FDRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm]; rw [inv_mul_cancel_left]

@[simp]
/--
theorem `char_dual` / 定理 `char_dual`

English:
theorem char_dual
  given: (V : FDRep k G) (g : G)
  statement: (of (dual V.ρ)).character g = V.character g⁻¹
  proof: trace_transpose' (V.ρ g⁻¹)

@[simp]

中文:
定理 char_dual
  条件: (V : FDRep k G) (g : G)
  结论: (of (dual V.ρ)).character g = V.character g⁻¹
  证明: trace_transpose' (V.ρ g⁻¹)

@[simp]

Depends on / 依赖: trace_transpose
-/
theorem char_dual (V : FDRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)

@[simp]
/--
theorem `char_linHom` / 定理 `char_linHom`

English:
theorem char_linHom
  given: (V W : FDRep k G) (g : G)
  proof: by
  rw [← char_iso (dualTensorIsoLinHom _ _)]; rw [char_tensor]; rw [Pi.mul_apply]; rw [char_dual]

中文:
定理 char_linHom
  条件: (V W : FDRep k G) (g : G)
  证明: by
  rw [← char_iso (dualTensorIsoLinHom _ _)]; rw [char_tensor]; rw [Pi.mul_apply]; rw [char_dual]

Depends on / 依赖: Pi.mul_apply, char_dual, char_iso, char_tensor, dualTensorIsoLinHom, mul_apply
-/
theorem char_linHom (V W : FDRep k G) (g : G) :
    (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g := by
  rw [← char_iso (dualTensorIsoLinHom _ _)]; rw [char_tensor]; rw [Pi.mul_apply]; rw [char_dual]

variable [Fintype G] [Invertible (Nat.card G : k)]

/--
theorem `average_char_eq_finrank_invariants` / 定理 `average_char_eq_finrank_invariants`

English:
theorem average_char_eq_finrank_invariants
  given: (V : FDRep k G)
  proof: by
  have : Invertible (Fintype.card G : k) := by
    rwa [Fintype.card_eq_nat_card]
  rw [← (isProj_averageMap V.ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

中文:
定理 average_char_eq_finrank_invariants
  条件: (V : FDRep k G)
  证明: by
  have : Invertible (Fintype.card G : k) := by
    rwa [Fintype.card_eq_nat_card]
  rw [← (isProj_averageMap V.ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_eq_nat_card, GroupAlgebra, GroupAlgebra.average, Invertible, _root_, _root_.map_sum, average, card_eq_nat_card, character, isProj_averageMap, map_sum
-/
theorem average_char_eq_finrank_invariants (V : FDRep k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  have : Invertible (Fintype.card G : k) := by
    rwa [Fintype.card_eq_nat_card]
  rw [← (isProj_averageMap V.ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

/--
theorem `scalar_product_char_eq_finrank_equivariant` / 定理 `scalar_product_char_eq_finrank_equivariant`

English:
theorem scalar_product_char_eq_finrank_equivariant
  given: (V W : FDRep k G)
  proof: by
  conv_lhs => congr; rfl; congr; rfl; intro _; rw [mul_comm, ← FDRep.char_linHom]
  -- The scalar product is the character of `Hom(V, W).`
  rw [FDRep.average_char_eq_finrank_invariants]; rw [← LinearEquiv.finrank_eq
    (Representation.linHom.invariantsEquivFDRepHom V W)]; rw [of_ρ']
  -- The av

中文:
定理 scalar_product_char_eq_finrank_equivariant
  条件: (V W : FDRep k G)
  证明: by
  conv_lhs => congr; rfl; congr; rfl; intro _; rw [mul_comm, ← FDRep.char_linHom]
  -- The scalar product is the character of `Hom(V, W).`
  rw [FDRep.average_char_eq_finrank_invariants]; rw [← LinearEquiv.finrank_eq
    (Representation.linHom.invariantsEquivFDRepHom V W)]; rw [of_ρ']
  -- The av

Depends on / 依赖: FDRep.char_linHom, char_linHom, conv_lhs, mul_comm
-/
theorem scalar_product_char_eq_finrank_equivariant (V W : FDRep k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, W.character g * V.character g⁻¹ =
    Module.finrank k (V ⟶ W) := by
  conv_lhs => congr; rfl; congr; rfl; intro _; rw [mul_comm, ← FDRep.char_linHom]
  -- The scalar product is the character of `Hom(V, W).`
  rw [FDRep.average_char_eq_finrank_invariants]; rw [← LinearEquiv.finrank_eq
    (Representation.linHom.invariantsEquivFDRepHom V W)]; rw [of_ρ']
  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants, and the space of invariants of `Hom(V, W)` is the subspace of
  -- `G`-equivariant linear maps, `Hom_G(V, W)`.

end Group

section Orthogonality

variable {G : Type v} [Group G] [IsAlgClosed k]

variable [Fintype G] [Invertible (Nat.card G : k)]

open scoped Classical in
/--
theorem `char_orthonormal` / 定理 `char_orthonormal`

English:
theorem char_orthonormal
  given: (V W : FDRep k G) [Simple V] [Simple W]
  proof: by
  rw [scalar_product_char_eq_finrank_equivariant]
  -- The scalar product of the characters is equal to the dimension of the space of
  -- equivariant maps `W ⟶ V`.
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` if

中文:
定理 char_orthonormal
  条件: (V W : FDRep k G) [Simple V] [Simple W]
  证明: by
  rw [scalar_product_char_eq_finrank_equivariant]
  -- The scalar product of the characters is equal to the dimension of the space of
  -- equivariant maps `W ⟶ V`.
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` if

Depends on / 依赖: scalar_product_char_eq_finrank_equivariant
-/
theorem char_orthonormal (V W : FDRep k G) [Simple V] [Simple W] :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  rw [scalar_product_char_eq_finrank_equivariant]
  -- The scalar product of the characters is equal to the dimension of the space of
  -- equivariant maps `W ⟶ V`.
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` if `V ≅ W` and `0` otherwise.

end Orthogonality

end FDRep
