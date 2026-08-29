/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Quotient.Pi

/-! # Quotient of submodules of full rank in free finite modules over PIDs

## Main results

* `Submodule.quotientEquivPiSpan`: `M ⧸ N`, if `M` is free finite module over a PID `R` and `N`
  is a submodule of full rank, can be written as a product of quotients of `R` by principal ideals.

-/

@[expose] public section

open Module
open scoped DirectSum

namespace Submodule

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsDomain R] [IsPrincipalIdealRing R] [Finite ι]

/--
Definition of `quotientEquivPiSpan` / `quotientEquivPiSpan` 的定义

English:
definition quotientEquivPiSpan
  signature: (N : Submodule R M) (b : Basis ι R M)
  body: by
  haveI := Fintype.ofFinite ι
  -- Choose `e : M ≃ₗ N` and a basis `b'` for `M` that turns the map
  -- `f := ((Submodule.subtype N).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopB

中文:
定义 quotientEquivPiSpan
  签名: (N : 子模 R M) (b : 基 ι R M)
  定义体: by
  haveI := Fintype.ofFinite ι
  -- Choose `e : M ≃ₗ N` and a basis `b'` for `M` that turns the map
  -- `f := ((Submodule.subtype N).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopB

Depends on / 依赖: Fintype, Fintype.ofFinite, ofFinite
-/
noncomputable def quotientEquivPiSpan (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    (M ⧸ N) ≃ₗ[R] Π i, R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R) := by
  haveI := Fintype.ofFinite ι
  -- Choose `e : M ≃ₗ N` and a basis `b'` for `M` that turns the map
  -- `f := ((Submodule.subtype N).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  have mem_I_iff : forall x, x in N ↔ forall i, a i ∣ b'.repr x i := by
    intro x
    simp_rw [ab.mem_submodule_iff', ab, ab_eq]
    have : forall (c : ι -> R) (i), b'.repr (∑ j : ι, c j • a j • b' j) i = a i * c i := by
      intro c i
      simp only [← mul_smul, b'.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, this c i⟩
    · rintro ha
      choose c hc using ha
      exact ⟨c, b'.ext_elem fun i => Eq.trans (hc i) (this c i).symm⟩
  -- Now we map everything through the linear equiv `M ≃ₗ (ι → R)`,
  -- which maps `N` to `N' := Π i, a i ℤ`.
  let N' : Submodule R (ι -> R) := Submodule.pi Set.univ fun i => span R ({a i} : Set R)
  have : Submodule.map (b'.equivFun : M ->ₗ[R] ι -> R) N = N' := by
    ext x
    simp only [N', Submodule.mem_map, Submodule.mem_pi, mem_span_singleton, Set.mem_univ,
      mem_I_iff, smul_eq_mul, forall_true_left, LinearEquiv.coe_coe,
      Basis.equivFun_apply, mul_comm _ (a _), eq_comm (b := (x _))]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact hy i
    · rintro hdvd
      refine ⟨∑ i, x i • b' i, fun i => ?_, ?_⟩ <;> rw [b'.repr_sum_self]
      · exact hdvd i
  refine (Submodule.Quotient.equiv N N' b'.equivFun this).trans (re₂₃ := inferInstance)
    (re₃₂ := inferInstance) ?_
  classical
  exact Submodule.quotientPi (show _ -> Submodule R R from fun i => span R ({a i} : Set R))

/--
Definition of `quotientEquivPiZMod` / `quotientEquivPiZMod` 的定义

English:
definition quotientEquivPiZMod
  signature: (N : Submodule Int M) (b : Basis ι Int M)
  body: let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiSpan b h
  let e' : (forall i : ι, Int ⧸ Ideal.span ({a i} : Set Int)) ≃+ forall i : ι, ZMod (a i).natAbs :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
  (↑(e : (M ⧸ N) ≃ₗ[Int] _) : M ⧸ N ≃+ _).trans e'

中文:
定义 quotientEquivPiZMod
  签名: (N : 子模 整数 M) (b : 基 ι 整数 M)
  定义体: let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiSpan b h
  let e' : (forall i : ι, Int ⧸ Ideal.span ({a i} : Set Int)) ≃+ forall i : ι, ZMod (a i).natAbs :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
  (↑(e : (M ⧸ N) ≃ₗ[Int] _) : M ⧸ N ≃+ _).trans e'

Depends on / 依赖: AddEquiv, AddEquiv.piCongrRight, Ideal.span, Int.quotientSpanEquivZMod, N.quotientEquivPiSpan, natAbs, piCongrRight, quotientEquivPiSpan, quotientSpanEquivZMod, smithNormalFormCoeffs
-/
noncomputable def quotientEquivPiZMod (N : Submodule Int M) (b : Basis ι Int M)
    (h : Module.finrank Int N = Module.finrank Int M) :
    M ⧸ N ≃+ Π i, ZMod (smithNormalFormCoeffs b h i).natAbs :=
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiSpan b h
  let e' : (forall i : ι, Int ⧸ Ideal.span ({a i} : Set Int)) ≃+ forall i : ι, ZMod (a i).natAbs :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
  (↑(e : (M ⧸ N) ≃ₗ[Int] _) : M ⧸ N ≃+ _).trans e'

/--
theorem `finiteQuotientOfFreeOfRankEq` / 定理 `finiteQuotientOfFreeOfRankEq`

English:
theorem finiteQuotientOfFreeOfRankEq
  statement: [Module.Free Int M] [Module.Finite Int M]
  proof: by
  let b := Module.Free.chooseBasis Int M
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiZMod b h
  have : forall i, NeZero (a i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr (smithNormalFormCoeffs_ne_zero b h i)⟩
  exact Finite.of_equiv (Π i, ZMod (a i).natAbs) e.symm

中文:
定理 finiteQuotientOfFreeOfRankEq
  结论: [模.自由 整数 M] [模.有限 整数 M]
  证明: by
  let b := Module.Free.chooseBasis Int M
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiZMod b h
  have : forall i, NeZero (a i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr (smithNormalFormCoeffs_ne_zero b h i)⟩
  exact Finite.of_equiv (Π i, ZMod (a i).natAbs) e.symm

Depends on / 依赖: Finite, Finite.of_equiv, Int.natAbs_ne_zero.mpr, Module, Module.Free.chooseBasis, N.quotientEquivPiZMod, NeZero, chooseBasis, e.symm, natAbs, natAbs_ne_zero, of_equiv, quotientEquivPiZMod, smithNormalFormCoeffs, smithNormalFormCoeffs_ne_zero
-/
theorem finiteQuotientOfFreeOfRankEq [Module.Free Int M] [Module.Finite Int M]
    (N : Submodule Int M) (h : Module.finrank Int N = Module.finrank Int M) : Finite (M ⧸ N) := by
  let b := Module.Free.chooseBasis Int M
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiZMod b h
  have : forall i, NeZero (a i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr (smithNormalFormCoeffs_ne_zero b h i)⟩
  exact Finite.of_equiv (Π i, ZMod (a i).natAbs) e.symm

/--
theorem `finiteQuotient_iff` / 定理 `finiteQuotient_iff`

English:
theorem finiteQuotient_iff
  given: [Module.Free Int M] [Module.Finite Int M] (N : Submodule Int M)
  proof: by
refine ⟨fun h => le_antisymm (finrank_le N)
    ((LinearMap.lsmul Int M (Nat.card (M ⧸ N))).codRestrict N
      fun x => ?_).finrank_le_finrank_of_injective ?_, fun h => finiteQuotientOfFreeOfRankEq N h⟩
  · simpa using! AddSubgroup.nsmul_index_mem N.toAddSubgroup x
  · refine (LinearMap.lsmul_in

中文:
定理 finiteQuotient_iff
  条件: [模.自由 整数 M] [模.有限 整数 M] (N : 子模 整数 M)
  证明: by
refine ⟨fun h => le_antisymm (finrank_le N)
    ((LinearMap.lsmul Int M (Nat.card (M ⧸ N))).codRestrict N
      fun x => ?_).finrank_le_finrank_of_injective ?_, fun h => finiteQuotientOfFreeOfRankEq N h⟩
  · simpa using! AddSubgroup.nsmul_index_mem N.toAddSubgroup x
  · refine (LinearMap.lsmul_in

Depends on / 依赖: AddSubgroup, AddSubgroup.nsmul_index_mem, Int.ofNat_ne_zero.mpr, LinearMap, LinearMap.lsmul, LinearMap.lsmul_injective, N.toAddSubgroup, Nat.card, Nat.card_ne_zero.mpr, Set.nonempty_iff_univ_nonempty.mpr, Set.univ_nonempty, card_ne_zero, codRestrict, finiteQuotientOfFreeOfRankEq, finrank_le, finrank_le_finrank_of_injective, le_antisymm, lsmul_injective, nonempty_iff_univ_nonempty, nsmul_index_mem
-/
theorem finiteQuotient_iff [Module.Free Int M] [Module.Finite Int M] (N : Submodule Int M) :
    Finite (M ⧸ N) ↔ Module.finrank Int N = Module.finrank Int M := by
refine ⟨fun h => le_antisymm (finrank_le N)
    ((LinearMap.lsmul Int M (Nat.card (M ⧸ N))).codRestrict N
      fun x => ?_).finrank_le_finrank_of_injective ?_, fun h => finiteQuotientOfFreeOfRankEq N h⟩
  · simpa using! AddSubgroup.nsmul_index_mem N.toAddSubgroup x
  · refine (LinearMap.lsmul_injective ?_).codRestrict _
exact Int.ofNat_ne_zero.mpr Nat.card_ne_zero.mpr
      ⟨Set.nonempty_iff_univ_nonempty.mpr Set.univ_nonempty, h⟩

variable (F : Type*) [CommRing F] [Algebra F R] [Module F M] [IsScalarTower F R M]
  (b : Basis ι R M) {N : Submodule R M}

/--
Definition of `quotientEquivDirectSum` / `quotientEquivDirectSum` 的定义

English:
definition quotientEquivDirectSum
  signature: (h : Module.finrank R N = Module.finrank R M)
  body: by
  haveI := Fintype.ofFinite ι
  exact ((N.quotientEquivPiSpan b _).restrictScalars F).trans
    (DirectSum.linearEquivFunOnFintype _ _ _).symm

中文:
定义 quotientEquivDirectSum
  签名: (h : 模.finrank R N = 模.finrank R M)
  定义体: by
  haveI := Fintype.ofFinite ι
  exact ((N.quotientEquivPiSpan b _).restrictScalars F).trans
    (DirectSum.linearEquivFunOnFintype _ _ _).symm

Depends on / 依赖: DirectSum, DirectSum.linearEquivFunOnFintype, Fintype, Fintype.ofFinite, N.quotientEquivPiSpan, linearEquivFunOnFintype, ofFinite, quotientEquivPiSpan, restrictScalars
-/
noncomputable def quotientEquivDirectSum (h : Module.finrank R N = Module.finrank R M) :
    (M ⧸ N) ≃ₗ[F] ⨁ i, R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R) := by
  haveI := Fintype.ofFinite ι
  exact ((N.quotientEquivPiSpan b _).restrictScalars F).trans
    (DirectSum.linearEquivFunOnFintype _ _ _).symm

/--
theorem `finrank_quotient_eq_sum` / 定理 `finrank_quotient_eq_sum`

English:
theorem finrank_quotient_eq_sum
  statement: {ι} [Fintype ι] (b : Basis ι R M) [Nontrivial F]
  proof: by
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b h]; rw [Module.finrank_directSum]

中文:
定理 finrank_quotient_eq_sum
  结论: {ι} [有限类型 ι] (b : 基 ι R M) [非平凡 F]
  证明: by
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b h]; rw [Module.finrank_directSum]

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_eq, Module, Module.finrank_directSum, finrank_directSum, finrank_eq, quotientEquivDirectSum
-/
theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R M) [Nontrivial F]
    (h : Module.finrank R N = Module.finrank R M)
    [forall i, Module.Free F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R))]
    [forall i, Module.Finite F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R))] :
    Module.finrank F (M ⧸ N) =
      ∑ i, Module.finrank F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R)) := by
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b h]; rw [Module.finrank_directSum]

end Submodule
