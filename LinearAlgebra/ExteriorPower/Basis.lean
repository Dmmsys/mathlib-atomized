/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Constructs a basis for exterior powers
-/

@[expose] public section

variable {R K M E : Type*} {n : Nat}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/--
Instance `instFinite` / 实例 `instFinite`

English:
instance instFinite
  signature: [Module.Finite R M]
  body: by
  rw [Module.Finite.iff_fg]; rw [ExteriorAlgebra.exteriorPower]; rw [LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

中文:
实例 instFinite
  签名: [模.有限 R M]
  定义体: by
  rw [Module.Finite.iff_fg]; rw [ExteriorAlgebra.exteriorPower]; rw [LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

Depends on / 依赖: ExteriorAlgebra, ExteriorAlgebra.exteriorPower, Finite, LinearMap, LinearMap.range_eq_map, Module, Module.Finite.fg_top, Module.Finite.iff_fg, Submodule, Submodule.FG.map, Submodule.FG.pow, exteriorPower, fg_top, iff_fg, range_eq_map
-/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  rw [Module.Finite.iff_fg]; rw [ExteriorAlgebra.exteriorPower]; rw [LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

open Module Set Set.powersetCard

variable (R n)

/--
Definition of `ιMultiDual` / `ιMultiDual` 的定义

English:
definition ιMultiDual
  signature: {I : Type*} [LinearOrder I] (b : Basis I R M)
  body: pairingDual R M n (ιMulti_family R n b.coord s)

@[simp]

中文:
定义 ιMultiDual
  签名: {I : 类型} [线性序 I] (b : 基 I R M)
  定义体: pairingDual R M n (ιMulti_family R n b.coord s)

@[simp]

Depends on / 依赖: b.coord, pairingDual
-/
noncomputable def ιMultiDual {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) : Module.Dual R (⋀[R]^n M) :=
  pairingDual R M n (ιMulti_family R n b.coord s)

@[simp]
/--
lemma `ιMultiDual_apply_ιMulti` / 引理 `ιMultiDual_apply_ιMulti`

English:
lemma ιMultiDual_apply_ιMulti
  statement: {I : Type*} [LinearOrder I] (b : Basis I R M)
  proof: by
  simp [ιMultiDual, ιMulti_family, pairingDual_ιMulti_ιMulti]

中文:
引理 ιMultiDual_apply_ιMulti
  结论: {I : 类型} [线性序 I] (b : 基 I R M)
  证明: by
  simp [ιMultiDual, ιMulti_family, pairingDual_ιMulti_ιMulti]
-/
lemma ιMultiDual_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) (v : Fin n -> M) :
    ιMultiDual R n b s (ιMulti R n v) =
    (Matrix.of fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j) (v i)).det := by
  simp [ιMultiDual, ιMulti_family, pairingDual_ιMulti_ιMulti]

/--
lemma `ιMultiDual_apply_diag` / 引理 `ιMultiDual_apply_diag`

English:
lemma ιMultiDual_apply_diag
  statement: {I : Type*} [LinearOrder I] (b : Basis I R M)
  proof: by
  rw [ιMulti_family]; rw [ιMultiDual_apply_ιMulti]
  suffices Matrix.of (fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j)
    (b (powersetCard.ofFinEmbEquiv.symm s i))) = 1 by
    simp_rw [Function.comp_apply, this, Matrix.det_one]
  ext
  simp [Matrix.one_apply, Finsupp.single_apply]

中文:
引理 ιMultiDual_apply_diag
  结论: {I : 类型} [线性序 I] (b : 基 I R M)
  证明: by
  rw [ιMulti_family]; rw [ιMultiDual_apply_ιMulti]
  suffices Matrix.of (fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j)
    (b (powersetCard.ofFinEmbEquiv.symm s i))) = 1 by
    simp_rw [Function.comp_apply, this, Matrix.det_one]
  ext
  simp [Matrix.one_apply, Finsupp.single_apply]

Depends on / 依赖: Finsupp, Finsupp.single_apply, Function, Function.comp_apply, Matrix, Matrix.det_one, Matrix.of, Matrix.one_apply, b.coord, comp_apply, det_one, ofFinEmbEquiv, one_apply, powersetCard, powersetCard.ofFinEmbEquiv.symm, simp_rw, single_apply
-/
lemma ιMultiDual_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) :
    ιMultiDual R n b s (ιMulti_family R n b s) = 1 := by
  rw [ιMulti_family]; rw [ιMultiDual_apply_ιMulti]
  suffices Matrix.of (fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j)
    (b (powersetCard.ofFinEmbEquiv.symm s i))) = 1 by
    simp_rw [Function.comp_apply, this, Matrix.det_one]
  ext
  simp [Matrix.one_apply, Finsupp.single_apply]

/--
lemma `ιMultiDual_apply_nondiag` / 引理 `ιMultiDual_apply_nondiag`

English:
lemma ιMultiDual_apply_nondiag
  statement: {I : Type*} [LinearOrder I] (b : Basis I R M)
  proof: by
  rw [ιMulti_family]; rw [ιMultiDual_apply_ιMulti]
  obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).mp hst
  obtain ⟨k, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  apply Matrix.det_eq_zero_of_column_eq_zero k
  simp_rw [Matrix.of_apply, Basis.coord_apply, Function.comp_ap

中文:
引理 ιMultiDual_apply_nondiag
  结论: {I : 类型} [线性序 I] (b : 基 I R M)
  证明: by
  rw [ιMulti_family]; rw [ιMultiDual_apply_ιMulti]
  obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).mp hst
  obtain ⟨k, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  apply Matrix.det_eq_zero_of_column_eq_zero k
  simp_rw [Matrix.of_apply, Basis.coord_apply, Function.comp_ap

Depends on / 依赖: Basis.coord_apply, Basis.repr_self, Finset, Finset.orderEmbOfFin_mem, Finsupp, Finsupp.single_eq_of_ne, Function, Function.comp_apply, Matrix, Matrix.det_eq_zero_of_column_eq_zero, Matrix.of_apply, comp_apply, coord_apply, det_eq_zero_of_column_eq_zero, exists_mem_notMem_iff_ne, mem_coe_iff, mem_range_ofFinEmbEquiv_symm_iff_mem, ofFinEmbEquiv_symm_apply, of_apply, orderEmbOfFin_mem
-/
lemma ιMultiDual_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s t : powersetCard I n) (hst : s != t) :
    ιMultiDual R n b s (ιMulti_family R n b t) = 0 := by
  rw [ιMulti_family]; rw [ιMultiDual_apply_ιMulti]
  obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).mp hst
  obtain ⟨k, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  apply Matrix.det_eq_zero_of_column_eq_zero k
  simp_rw [Matrix.of_apply, Basis.coord_apply, Function.comp_apply, Basis.repr_self]
  intro j
  apply Finsupp.single_eq_of_ne
  by_contra! h
  apply hit
  rw [h]; rw [powersetCard.ofFinEmbEquiv_symm_apply]; rw [← powersetCard.mem_coe_iff]
  exact Finset.orderEmbOfFin_mem t.val t.prop j

/--
lemma `ιMulti_family_linearIndependent_ofBasis` / 引理 `ιMulti_family_linearIndependent_ofBasis`

English:
lemma ιMulti_family_linearIndependent_ofBasis
  given: {I : Type*} [LinearOrder I] (b : Basis I R M)
  proof: LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun s => ιMultiDual R n b s)
    (fun _ _ h => ιMultiDual_apply_nondiag R n b _ _ h)
    (fun _ => ιMultiDual_apply_diag _ _ _ _)

中文:
引理 ιMulti_family_linearIndependent_ofBasis
  条件: {I : 类型} [线性序 I] (b : 基 I R M)
  证明: LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun s => ιMultiDual R n b s)
    (fun _ _ h => ιMultiDual_apply_nondiag R n b _ _ h)
    (fun _ => ιMultiDual_apply_diag _ _ _ _)

Depends on / 依赖: LinearIndependent, LinearIndependent.of_pairwise_dual_eq_zero_one, of_pairwise_dual_eq_zero_one
-/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun s => ιMultiDual R n b s)
    (fun _ _ h => ιMultiDual_apply_nondiag R n b _ _ h)
    (fun _ => ιMultiDual_apply_diag _ _ _ _)

variable {R} in
/--
Definition of `_root_.Module.Basis.exteriorPower` / `_root_.Module.Basis.exteriorPower` 的定义

English:
definition _root_.Module.Basis.exteriorPower
  signature: {I : Type*} [LinearOrder I] (b : Basis I R M)
  body: Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]

中文:
定义 _root_.模.基.exteriorPower
  签名: {I : 类型} [线性序 I] (b : 基 I R M)
  定义体: Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]

Depends on / 依赖: Basis.mk, b.span_eq, eq_top_iff, eq_top_iff.mp, span_eq
-/
noncomputable def _root_.Module.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis (powersetCard I n) R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]
/--
lemma `coe_basis` / 引理 `coe_basis`

English:
lemma coe_basis
  given: {I : Type*} [LinearOrder I] (b : Basis I R M)
  proof: Basis.coe_mk _ _

中文:
引理 coe_basis
  条件: {I : 类型} [线性序 I] (b : 基 I R M)
  证明: Basis.coe_mk _ _

Depends on / 依赖: Basis.coe_mk, coe_mk
-/
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (b.exteriorPower n) = ιMulti_family R n b :=
  Basis.coe_mk _ _

/--
lemma `basis_apply` / 引理 `basis_apply`

English:
lemma basis_apply
  given: {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n)
  proof: by
  rw [coe_basis]

中文:
引理 basis_apply
  条件: {I : 类型} [线性序 I] (b : 基 I R M) (s : powersetCard I n)
  证明: by
  rw [coe_basis]

Depends on / 依赖: coe_basis
-/
lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    b.exteriorPower n s = ιMulti_family R n b s := by
  rw [coe_basis]

/--
lemma `basis_coord` / 引理 `basis_coord`

English:
lemma basis_coord
  given: {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n)
  proof: by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases! hst : s = t
  · rw [hst, ιMultiDual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMultiDual_apply_nondiag R n b s t hst, ← basis_apply,

中文:
引理 basis_coord
  条件: {I : 类型} [线性序 I] (b : 基 I R M) (s : powersetCard I n)
  证明: by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases! hst : s = t
  · rw [hst, ιMultiDual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMultiDual_apply_nondiag R n b s t hst, ← basis_apply,

Depends on / 依赖: Basis.coord_apply, Basis.repr_self, Basis.span_eq, Finsupp, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, LinearMap, LinearMap.ext_on, basis_apply, coord_apply, ext_on, repr_self, single_eq_of_ne, single_eq_same, span_eq
-/
lemma basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.coord (b.exteriorPower n) s = ιMultiDual R n b s := by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases! hst : s = t
  · rw [hst, ιMultiDual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMultiDual_apply_nondiag R n b s t hst, ← basis_apply, Basis.repr_self,
      Finsupp.single_eq_of_ne hst]

/--
lemma `basis_repr_apply` / 引理 `basis_repr_apply`

English:
lemma basis_repr_apply
  statement: {I : Type*} [LinearOrder I] (b : Basis I R M) (x : ⋀[R]^n M)
  proof: by
  simpa [← Basis.coord_apply] using LinearMap.congr_fun (basis_coord R n b s) x

@[simp]

中文:
引理 basis_repr_apply
  结论: {I : 类型} [线性序 I] (b : 基 I R M) (x : ⋀[R]^n M)
  证明: by
  simpa [← Basis.coord_apply] using LinearMap.congr_fun (basis_coord R n b s) x

@[simp]

Depends on / 依赖: Basis.coord_apply, LinearMap, LinearMap.congr_fun, basis_coord, congr_fun, coord_apply
-/
lemma basis_repr_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (x : ⋀[R]^n M)
    (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) x s = ιMultiDual R n b s x := by
  simpa [← Basis.coord_apply] using LinearMap.congr_fun (basis_coord R n b s) x

@[simp]
/--
lemma `basis_repr_self` / 引理 `basis_repr_self`

English:
lemma basis_repr_self
  given: {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n)
  proof: by
  simpa [basis_repr_apply] using ιMultiDual_apply_diag R n b s

@[simp]

中文:
引理 basis_repr_self
  条件: {I : 类型} [线性序 I] (b : 基 I R M) (s : powersetCard I n)
  证明: by
  simpa [basis_repr_apply] using ιMultiDual_apply_diag R n b s

@[simp]

Depends on / 依赖: basis_repr_apply
-/
lemma basis_repr_self {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) s = 1 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_diag R n b s

@[simp]
/--
lemma `basis_repr_ne` / 引理 `basis_repr_ne`

English:
lemma basis_repr_ne
  statement: {I : Type*} [LinearOrder I] (b : Basis I R M)
  proof: by
  simpa [basis_repr_apply] using ιMultiDual_apply_nondiag R n b t s hst.symm

中文:
引理 basis_repr_ne
  结论: {I : 类型} [线性序 I] (b : 基 I R M)
  证明: by
  simpa [basis_repr_apply] using ιMultiDual_apply_nondiag R n b t s hst.symm

Depends on / 依赖: basis_repr_apply, hst.symm
-/
lemma basis_repr_ne {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : powersetCard I n} (hst : s != t) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) t = 0 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_nondiag R n b t s hst.symm

/--
lemma `basis_repr` / 引理 `basis_repr`

English:
lemma basis_repr
  given: {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n)
  proof: by
  ext t
  by_cases hst : s = t <;> simp [hst]

中文:
引理 basis_repr
  条件: {I : 类型} [线性序 I] (b : 基 I R M) (s : powersetCard I n)
  证明: by
  ext t
  by_cases hst : s = t <;> simp [hst]
-/
lemma basis_repr {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) = Finsupp.single s 1 := by
  ext t
  by_cases hst : s = t <;> simp [hst]

/-! ### Freeness and dimension of `⋀[R]^n M`. -/

/--
Instance `instFree` / 实例 `instFree`

English:
instance instFree
  signature: [Module.Free R M]
  body: by
  classical
  have ⟨I, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis (b.exteriorPower n)

中文:
实例 instFree
  签名: [模.自由 R M]
  定义体: by
  classical
  have ⟨I, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis (b.exteriorPower n)

Depends on / 依赖: LinearOrder, Module, Module.Free.exists_basis, Module.Free.of_basis, WellOrderingRel, b.exteriorPower, classical, exists_basis, exteriorPower, linearOrderOfSTO, of_basis
-/
instance instFree [Module.Free R M] : Module.Free R (⋀[R]^n M) := by
  classical
  have ⟨I, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis (b.exteriorPower n)

variable [Nontrivial R]

/--
lemma `finrank_eq` / 引理 `finrank_eq`

English:
lemma finrank_eq
  given: [Module.Free R M] [Module.Finite R M]
  proof: by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let B := (Module.Free.chooseBasis R M).exteriorPower n
  rw [Module.finrank_eq_card_basis (Module.Free.chooseBasis R M)]; rw [Module.finrank_eq_card_basis B]; rw [Fintype.card_eq_nat_card]; rw

中文:
引理 finrank_eq
  条件: [模.自由 R M] [模.有限 R M]
  证明: by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let B := (Module.Free.chooseBasis R M).exteriorPower n
  rw [Module.finrank_eq_card_basis (Module.Free.chooseBasis R M)]; rw [Module.finrank_eq_card_basis B]; rw [Fintype.card_eq_nat_card]; rw

Depends on / 依赖: ChooseBasisIndex, Fintype, Fintype.card_eq_nat_card, LinearOrder, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Module.finrank_eq_card_basis, WellOrderingRel, card_eq_nat_card, chooseBasis, classical, exteriorPower, finrank_eq_card_basis, linearOrderOfSTO, powersetCard, powersetCard.card
-/
lemma finrank_eq [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) = Nat.choose (Module.finrank R M) n := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let B := (Module.Free.chooseBasis R M).exteriorPower n
  rw [Module.finrank_eq_card_basis (Module.Free.chooseBasis R M)]; rw [Module.finrank_eq_card_basis B]; rw [Fintype.card_eq_nat_card]; rw [powersetCard.card]; rw [Fintype.card_eq_nat_card]

/-! Results that only hold over a field. -/

/--
lemma `ιMulti_family_linearIndependent_field` / 引理 `ιMulti_family_linearIndependent_field`

English:
lemma ιMulti_family_linearIndependent_field
  statement: {I : Type*} [LinearOrder I] {v : I -> E}
  proof: by
  let W := Submodule.span K (Set.range v)
  suffices exists b : Basis I K W, v = W.subtype ∘ b by
    obtain ⟨b, hb⟩ := this
    rw [hb]; rw [← map_comp_ιMulti_family]
    exact LinearIndependent.map' (coe_basis K n b ▸ (b.exteriorPower n).linearIndependent)
      _ (LinearMap.ker_eq_bot.mpr (map

中文:
引理 ιMulti_family_linearIndependent_field
  结论: {I : 类型} [线性序 I] {v : I -> E}
  证明: by
  let W := Submodule.span K (Set.range v)
  suffices exists b : Basis I K W, v = W.subtype ∘ b by
    obtain ⟨b, hb⟩ := this
    rw [hb]; rw [← map_comp_ιMulti_family]
    exact LinearIndependent.map' (coe_basis K n b ▸ (b.exteriorPower n).linearIndependent)
      _ (LinearMap.ker_eq_bot.mpr (map

Depends on / 依赖: Basis.span_apply, Function, Function.comp_apply, LinearIndependent, LinearIndependent.map, LinearMap, LinearMap.ker_eq_bot.mpr, Module, Module.Basis.span, Set.range, Submodule, Submodule.coe_subtype, Submodule.span, Submodule.subtype_injective, W.subtype, b.exteriorPower, coe_basis, coe_subtype, comp_apply, exteriorPower
-/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I -> E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  let W := Submodule.span K (Set.range v)
  suffices exists b : Basis I K W, v = W.subtype ∘ b by
    obtain ⟨b, hb⟩ := this
    rw [hb]; rw [← map_comp_ιMulti_family]
    exact LinearIndependent.map' (coe_basis K n b ▸ (b.exteriorPower n).linearIndependent)
      _ (LinearMap.ker_eq_bot.mpr (map_injective_field (Submodule.subtype_injective _)))
  use Module.Basis.span hv
  ext i
  rw [Submodule.coe_subtype]; rw [Function.comp_apply]; rw [Basis.span_apply]

end exteriorPower
