/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Module
public import Mathlib.Data.Fintype.Quotient

/-!
# `DFinsupp` on `Sigma` types

## Main definitions

* `DFinsupp.sigmaCurry`: turn a `DFinsupp` indexed by a `Sigma` type into a `DFinsupp` with two
  parameters.
* `DFinsupp.sigmaUncurry`: turn a `DFinsupp` with two parameters into a `DFinsupp` indexed by a
  `Sigma` type. Inverse of `DFinsupp.sigmaCurry`.
* `DFinsupp.sigmaCurryEquiv`: `DFinsupp.sigmaCurry` and `DFinsupp.sigmaUncurry` bundled into a
  bijection.

-/

@[expose] public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}

namespace DFinsupp

section Equiv

open Finset

variable {κ : Type*}

section SigmaCurry

variable {α : ι -> Type*} {δ : forall i, α i -> Type v}

variable [DecidableEq ι]

/--
Definition of `sigmaCurry` / `sigmaCurry` 的定义

English:
definition sigmaCurry
  signature: [forall i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2)
  body: fun i =>
  { toFun := fun j => f ⟨i, j⟩,
    support' := f.support'.map (fun ⟨m, hm⟩ =>
      ⟨m.filterMap (fun ⟨i', j'⟩ => if h : i' = i then some <| h.rec j' else none),
        fun j => (hm ⟨i, j⟩).imp_left (fun h => (m.mem_filterMap _).mpr ⟨⟨i, j⟩, h, dif_pos rfl⟩)⟩) }
  support' := f.support'.m

中文:
定义 sigmaCurry
  签名: [对任意 i j, 零 (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2)
  定义体: fun i =>
  { toFun := fun j => f ⟨i, j⟩,
    support' := f.support'.map (fun ⟨m, hm⟩ =>
      ⟨m.filterMap (fun ⟨i', j'⟩ => if h : i' = i then some <| h.rec j' else none),
        fun j => (hm ⟨i, j⟩).imp_left (fun h => (m.mem_filterMap _).mpr ⟨⟨i, j⟩, h, dif_pos rfl⟩)⟩) }
  support' := f.support'.m
-/
def sigmaCurry [forall i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    Π₀ (i) (j), δ i j where
  toFun := fun i =>
  { toFun := fun j => f ⟨i, j⟩,
    support' := f.support'.map (fun ⟨m, hm⟩ =>
      ⟨m.filterMap (fun ⟨i', j'⟩ => if h : i' = i then some <| h.rec j' else none),
        fun j => (hm ⟨i, j⟩).imp_left (fun h => (m.mem_filterMap _).mpr ⟨⟨i, j⟩, h, dif_pos rfl⟩)⟩) }
  support' := f.support'.map (fun ⟨m, hm⟩ =>
    ⟨m.map Sigma.fst, fun i => Decidable.or_iff_not_imp_left.mpr (fun h => DFinsupp.ext
      (fun j => (hm ⟨i, j⟩).resolve_left (fun H => (Multiset.mem_map.not.mp h) ⟨⟨i, j⟩, H, rfl⟩)))⟩)

@[simp]
/--
theorem `sigmaCurry_apply` / 定理 `sigmaCurry_apply`

English:
theorem sigmaCurry_apply
  given: [forall i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i)
  proof: rfl

@[simp]

中文:
定理 sigmaCurry_apply
  条件: [对任意 i j, 零 (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i)
  证明: rfl

@[simp]
-/
theorem sigmaCurry_apply [forall i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  rfl

@[simp]
/--
theorem `sigmaCurry_zero` / 定理 `sigmaCurry_zero`

English:
theorem sigmaCurry_zero
  given: [forall i j, Zero (δ i j)]
  proof: rfl

@[simp]

中文:
定理 sigmaCurry_zero
  条件: [对任意 i j, 零 (δ i j)]
  证明: rfl

@[simp]
-/
theorem sigmaCurry_zero [forall i j, Zero (δ i j)] :
    sigmaCurry (0 : Π₀ (i : Σ _, _), δ i.1 i.2) = 0 :=
  rfl

@[simp]
/--
theorem `sigmaCurry_add` / 定理 `sigmaCurry_add`

English:
theorem sigmaCurry_add
  given: [forall i j, AddZeroClass (δ i j)] (f g : Π₀ (i : Σ _, _), δ i.1 i.2)
  proof: by
  ext (i j)
  rfl

@[simp]

中文:
定理 sigmaCurry_add
  条件: [对任意 i j, 加法零类 (δ i j)] (f g : Π₀ (i : Σ _, _), δ i.1 i.2)
  证明: by
  ext (i j)
  rfl

@[simp]
-/
theorem sigmaCurry_add [forall i j, AddZeroClass (δ i j)] (f g : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (f + g) = (sigmaCurry f + sigmaCurry g : Π₀ (i) (j), δ i j) := by
  ext (i j)
  rfl

@[simp]
/--
theorem `sigmaCurry_smul` / 定理 `sigmaCurry_smul`

English:
theorem sigmaCurry_smul
  statement: [Monoid γ] [forall i j, AddMonoid (δ i j)] [forall i j, DistribMulAction γ (δ i j)]
  proof: by
  ext (i j)
  rfl

@[simp]

中文:
定理 sigmaCurry_smul
  结论: [幺半群 γ] [对任意 i j, 加法幺半群 (δ i j)] [对任意 i j, 分配乘法作用 γ (δ i j)]
  证明: by
  ext (i j)
  rfl

@[simp]
-/
theorem sigmaCurry_smul [Monoid γ] [forall i j, AddMonoid (δ i j)] [forall i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (r • f) = (r • sigmaCurry f : Π₀ (i) (j), δ i j) := by
  ext (i j)
  rfl

@[simp]
/--
theorem `sigmaCurry_single` / 定理 `sigmaCurry_single`

English:
theorem sigmaCurry_single
  statement: [forall i, DecidableEq (α i)] [forall i j, Zero (δ i j)]
  proof: by
  obtain ⟨i, j⟩ := ij
  ext i' j'
  dsimp only
  rw [sigmaCurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
  · simp [hi]

中文:
定理 sigmaCurry_single
  结论: [对任意 i, DecidableEq (α i)] [对任意 i j, 零 (δ i j)]
  证明: by
  obtain ⟨i, j⟩ := ij
  ext i' j'
  dsimp only
  rw [sigmaCurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
  · simp [hi]

Depends on / 依赖: eq_or_ne, sigmaCurry_apply, single_eq_of_ne, single_eq_same
-/
theorem sigmaCurry_single [forall i, DecidableEq (α i)] [forall i j, Zero (δ i j)]
    (ij : Σ i, α i) (x : δ ij.1 ij.2) :
    sigmaCurry (single ij x) = single ij.1 (single ij.2 x : Π₀ j, δ ij.1 j) := by
  obtain ⟨i, j⟩ := ij
  ext i' j'
  dsimp only
  rw [sigmaCurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
  · simp [hi]

/--
Definition of `sigmaUncurry` / `sigmaUncurry` 的定义

English:
definition sigmaUncurry
  signature: [forall i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j)
  body: f i.1 i.2
  support' :=
    f.support'.bind fun s =>
      (Trunc.finChoice (fun i : ↥s.val.toFinset => (f i).support')).map fun fs =>
        ⟨s.val.toFinset.attach.val.bind fun i => (fs i).val.map (Sigma.mk i.val), by
          rintro ⟨i, a⟩
          cases s.prop i with
          | inl hi =>
    

中文:
定义 sigmaUncurry
  签名: [对任意 i j, 零 (δ i j)] (f : Π₀ (i) (j), δ i j)
  定义体: f i.1 i.2
  support' :=
    f.support'.bind fun s =>
      (Trunc.finChoice (fun i : ↥s.val.toFinset => (f i).support')).map fun fs =>
        ⟨s.val.toFinset.attach.val.bind fun i => (fs i).val.map (Sigma.mk i.val), by
          rintro ⟨i, a⟩
          cases s.prop i with
          | inl hi =>
    
-/
def sigmaUncurry [forall i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) : Π₀ i : Σ _, _, δ i.1 i.2 where
  toFun i := f i.1 i.2
  support' :=
    f.support'.bind fun s =>
      (Trunc.finChoice (fun i : ↥s.val.toFinset => (f i).support')).map fun fs =>
        ⟨s.val.toFinset.attach.val.bind fun i => (fs i).val.map (Sigma.mk i.val), by
          rintro ⟨i, a⟩
          cases s.prop i with
          | inl hi =>
            cases (fs ⟨i, Multiset.mem_toFinset.mpr hi⟩).prop a with
            | inl ha =>
              left; rw [Multiset.mem_bind]
              use ⟨i, Multiset.mem_toFinset.mpr hi⟩
              constructor
              case right => simp [ha]
              case left => apply Multiset.mem_attach
            | inr ha => right; simp [toFun_eq_coe (f i) ▸ ha]
          | inr hi => right; simp [toFun_eq_coe f ▸ hi]⟩

@[simp]
/--
theorem `sigmaUncurry_apply` / 定理 `sigmaUncurry_apply`

English:
theorem sigmaUncurry_apply
  statement: [forall i j, Zero (δ i j)]
  proof: rfl

@[simp]

中文:
定理 sigmaUncurry_apply
  结论: [对任意 i j, 零 (δ i j)]
  证明: rfl

@[simp]
-/
theorem sigmaUncurry_apply [forall i j, Zero (δ i j)]
    (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  rfl

@[simp]
/--
theorem `sigmaUncurry_zero` / 定理 `sigmaUncurry_zero`

English:
theorem sigmaUncurry_zero
  given: [forall i j, Zero (δ i j)]
  proof: rfl

@[simp]

中文:
定理 sigmaUncurry_zero
  条件: [对任意 i j, 零 (δ i j)]
  证明: rfl

@[simp]
-/
theorem sigmaUncurry_zero [forall i j, Zero (δ i j)] :
    sigmaUncurry (0 : Π₀ (i) (j), δ i j) = 0 :=
  rfl

@[simp]
/--
theorem `sigmaUncurry_add` / 定理 `sigmaUncurry_add`

English:
theorem sigmaUncurry_add
  given: [forall i j, AddZeroClass (δ i j)] (f g : Π₀ (i) (j), δ i j)
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 sigmaUncurry_add
  条件: [对任意 i j, 加法零类 (δ i j)] (f g : Π₀ (i) (j), δ i j)
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem sigmaUncurry_add [forall i j, AddZeroClass (δ i j)] (f g : Π₀ (i) (j), δ i j) :
    sigmaUncurry (f + g) = sigmaUncurry f + sigmaUncurry g :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `sigmaUncurry_smul` / 定理 `sigmaUncurry_smul`

English:
theorem sigmaUncurry_smul
  statement: [Monoid γ] [forall i j, AddMonoid (δ i j)]
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 sigmaUncurry_smul
  结论: [幺半群 γ] [对任意 i j, 加法幺半群 (δ i j)]
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem sigmaUncurry_smul [Monoid γ] [forall i j, AddMonoid (δ i j)]
    [forall i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • f) = r • sigmaUncurry f :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `sigmaUncurry_single` / 定理 `sigmaUncurry_single`

English:
theorem sigmaUncurry_single
  statement: [forall i j, Zero (δ i j)] [forall i, DecidableEq (α i)]
  proof: by
  ext ⟨i', j'⟩
  dsimp only
  rw [sigmaUncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
  · simp [hi]

中文:
定理 sigmaUncurry_single
  结论: [对任意 i j, 零 (δ i j)] [对任意 i, DecidableEq (α i)]
  证明: by
  ext ⟨i', j'⟩
  dsimp only
  rw [sigmaUncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
  · simp [hi]

Depends on / 依赖: eq_or_ne, sigmaUncurry_apply, single_eq_of_ne, single_eq_same
-/
theorem sigmaUncurry_single [forall i j, Zero (δ i j)] [forall i, DecidableEq (α i)]
    (i) (j : α i) (x : δ i j) :
    sigmaUncurry (single i (single j x : Π₀ j : α i, δ i j)) = single ⟨i, j⟩ (by exact x) := by
  ext ⟨i', j'⟩
  dsimp only
  rw [sigmaUncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
  · simp [hi]

/--
Definition of `sigmaCurryEquiv` / `sigmaCurryEquiv` 的定义

English:
definition sigmaCurryEquiv
  signature: [forall i j, Zero (δ i j)]
  body: sigmaCurry
  invFun := sigmaUncurry
  left_inv f := by
    ext ⟨i, j⟩
    rw [sigmaUncurry_apply]; rw [sigmaCurry_apply]
  right_inv f := by
    ext i j
    rw [sigmaCurry_apply]; rw [sigmaUncurry_apply]

中文:
定义 sigmaCurryEquiv
  签名: [对任意 i j, 零 (δ i j)]
  定义体: sigmaCurry
  invFun := sigmaUncurry
  left_inv f := by
    ext ⟨i, j⟩
    rw [sigmaUncurry_apply]; rw [sigmaCurry_apply]
  right_inv f := by
    ext i j
    rw [sigmaCurry_apply]; rw [sigmaUncurry_apply]

Depends on / 依赖: sigmaCurry
-/
def sigmaCurryEquiv [forall i j, Zero (δ i j)] : (Π₀ i : Σ _, _, δ i.1 i.2) ≃ Π₀ (i) (j), δ i j where
  toFun := sigmaCurry
  invFun := sigmaUncurry
  left_inv f := by
    ext ⟨i, j⟩
    rw [sigmaUncurry_apply]; rw [sigmaCurry_apply]
  right_inv f := by
    ext i j
    rw [sigmaCurry_apply]; rw [sigmaUncurry_apply]

end SigmaCurry

end Equiv

end DFinsupp
