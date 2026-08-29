/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Algebra.Lie.Weights.Basic

/-!

# The Lie algebra `sl₂` and its representations

The Lie algebra `sl₂` is the unique simple Lie algebra of minimal rank, 1, and as such occupies a
distinguished position in the general theory. This file provides some basic definitions and results
about `sl₂`.

## Main definitions:
* `IsSl2Triple`: a structure representing a triple of elements in a Lie algebra which satisfy the
  standard relations for `sl₂`.
* `IsSl2Triple.HasPrimitiveVectorWith`: a structure representing a primitive vector in a
  representation of a Lie algebra relative to a distinguished `sl₂` triple.
* `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`: the eigenvalue of a primitive vector must be a
  natural number if the representation is finite-dimensional.

-/

@[expose] public section

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieModule Module Set

variable {L} in
/--
Definition of `IsSl2Triple` / `IsSl2Triple` 的定义

English:
structure IsSl2Triple
  parameters: (h e f : L)
  axioms and operations (4):
    - h_ne_zero : h != 0
    - lie_e_f : ⁅e, f⁆ = h
    - lie_h_e_nsmul : ⁅h, e⁆ = 2 • e
    - lie_h_f_nsmul : ⁅h, f⁆ = -(2 • f)

中文:
结构 IsSl2Triple
  参数: (h e f : L)
  公理与运算 (4 个):
    - h_ne_zero : h != 0
    - lie_e_f : ⁅e, f⁆ = h
    - lie_h_e_nsmul : ⁅h, e⁆ = 2 • e
    - lie_h_f_nsmul : ⁅h, f⁆ = -(2 • f)
-/
structure IsSl2Triple (h e f : L) : Prop where
  h_ne_zero : h != 0
  lie_e_f : ⁅e, f⁆ = h
  lie_h_e_nsmul : ⁅h, e⁆ = 2 • e
  lie_h_f_nsmul : ⁅h, f⁆ = -(2 • f)

namespace IsSl2Triple

variable {L M}
variable {h e f : L}

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (ht : IsSl2Triple h e f)
  statement: IsSl2Triple (-h) f e where
  proof: by simpa using ht.h_ne_zero
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, ht.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, ht.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, ht.lie_h_e_nsmul]

中文:
引理 symm
  条件: (ht : IsSl2Triple h e f)
  结论: IsSl2Triple (-h) f e where
  证明: by simpa using ht.h_ne_zero
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, ht.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, ht.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, ht.lie_h_e_nsmul]

Depends on / 依赖: IsScalarTower, IsScalarTower.compatibleSMul, compatibleSMul, h_ne_zero, ht.h_ne_zero, ht.lie_e_f, ht.lie_h_e_nsmul, ht.lie_h_f_nsmul, lie_e_f, lie_h_e_nsmul, lie_h_f_nsmul, lie_skew, neg_eq_iff_eq_neg, neg_inj, neg_lie
-/
lemma symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e where
  h_ne_zero := by simpa using ht.h_ne_zero
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, ht.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, ht.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, ht.lie_h_e_nsmul]

/--
lemma `symm_iff` / 引理 `symm_iff`

English:
lemma symm_iff
  statement: IsSl2Triple (-h) f e ↔ IsSl2Triple h e f
  proof: ⟨fun t => neg_neg h ▸ t.symm, symm⟩

中文:
引理 symm_iff
  结论: IsSl2Triple (-h) f e ↔ IsSl2Triple h e f
  证明: ⟨fun t => neg_neg h ▸ t.symm, symm⟩
-/
@[simp] lemma symm_iff : IsSl2Triple (-h) f e ↔ IsSl2Triple h e f :=
  ⟨fun t => neg_neg h ▸ t.symm, symm⟩

/--
lemma `lie_h_e_smul` / 引理 `lie_h_e_smul`

English:
lemma lie_h_e_smul
  given: (t : IsSl2Triple h e f)
  statement: ⁅h, e⁆ = (2 : R) • e
  proof: by
  simp [t.lie_h_e_nsmul, two_smul]

中文:
引理 lie_h_e_smul
  条件: (t : IsSl2Triple h e f)
  结论: ⁅h, e⁆ = (2 : R) • e
  证明: by
  simp [t.lie_h_e_nsmul, two_smul]

Depends on / 依赖: lie_h_e_nsmul, t.lie_h_e_nsmul, two_smul
-/
lemma lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ = (2 : R) • e := by
  simp [t.lie_h_e_nsmul, two_smul]

/--
lemma `lie_lie_smul_f` / 引理 `lie_lie_smul_f`

English:
lemma lie_lie_smul_f
  given: (t : IsSl2Triple h e f)
  statement: ⁅h, f⁆ = -((2 : R) • f)
  proof: by
  simp [t.lie_h_f_nsmul, two_smul]

中文:
引理 lie_lie_smul_f
  条件: (t : IsSl2Triple h e f)
  结论: ⁅h, f⁆ = -((2 : R) • f)
  证明: by
  simp [t.lie_h_f_nsmul, two_smul]

Depends on / 依赖: lie_h_f_nsmul, t.lie_h_f_nsmul, two_smul
-/
lemma lie_lie_smul_f (t : IsSl2Triple h e f) : ⁅h, f⁆ = -((2 : R) • f) := by
  simp [t.lie_h_f_nsmul, two_smul]

/--
lemma `e_ne_zero` / 引理 `e_ne_zero`

English:
lemma e_ne_zero
  given: (t : IsSl2Triple h e f)
  statement: e != 0
  proof: by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm

中文:
引理 e_ne_zero
  条件: (t : IsSl2Triple h e f)
  结论: e != 0
  证明: by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm

Depends on / 依赖: contrapose, h_ne_zero, lie_e_f, t.h_ne_zero, t.lie_e_f.symm
-/
lemma e_ne_zero (t : IsSl2Triple h e f) : e != 0 := by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm

/--
lemma `f_ne_zero` / 引理 `f_ne_zero`

English:
lemma f_ne_zero
  given: (t : IsSl2Triple h e f)
  statement: f != 0
  proof: by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm

中文:
引理 f_ne_zero
  条件: (t : IsSl2Triple h e f)
  结论: f != 0
  证明: by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm

Depends on / 依赖: contrapose, h_ne_zero, lie_e_f, t.h_ne_zero, t.lie_e_f.symm
-/
lemma f_ne_zero (t : IsSl2Triple h e f) : f != 0 := by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm

variable {R}

/--
Definition of `HasPrimitiveVectorWith` / `HasPrimitiveVectorWith` 的定义

English:
structure HasPrimitiveVectorWith
  parameters: (t : IsSl2Triple h e f) (m : M) (μ : R)
  axioms and operations (3):
    - ne_zero : m != 0
    - lie_h : ⁅h, m⁆ = μ • m
    - lie_e : ⁅e, m⁆ = 0

中文:
结构 HasPrimitiveVectorWith
  参数: (t : IsSl2Triple h e f) (m : M) (μ : R)
  公理与运算 (3 个):
    - ne_zero : m != 0
    - lie_h : ⁅h, m⁆ = μ • m
    - lie_e : ⁅e, m⁆ = 0
-/
structure HasPrimitiveVectorWith (t : IsSl2Triple h e f) (m : M) (μ : R) : Prop where
  ne_zero : m != 0
  lie_h : ⁅h, m⁆ = μ • m
  lie_e : ⁅e, m⁆ = 0

/--
lemma `HasPrimitiveVectorWith.mk'` / 引理 `HasPrimitiveVectorWith.mk'`

English:
lemma HasPrimitiveVectorWith.mk'
  statement: [IsAddTorsionFree M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R)
  proof: hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie]; rw [← t.lie_h_e_nsmul]; rw [lie_lie]; rw [hm']; rw [lie_smul]; rw [he]; rw [lie_smul]; rw [hm']; rw [smul_smul]; rw [smul_smul]; rw [mul_comm ρ μ]; rw [sub_self]

中文:
引理 HasPrimitiveVectorWith.mk'
  结论: [IsAddTorsionFree M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R)
  证明: hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie]; rw [← t.lie_h_e_nsmul]; rw [lie_lie]; rw [hm']; rw [lie_smul]; rw [he]; rw [lie_smul]; rw [hm']; rw [smul_smul]; rw [smul_smul]; rw [mul_comm ρ μ]; rw [sub_self]
-/
lemma HasPrimitiveVectorWith.mk' [IsAddTorsionFree M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R)
    (hm : m != 0) (hm' : ⁅h, m⁆ = μ • m) (he : ⁅e, m⁆ = ρ • m) :
    HasPrimitiveVectorWith t m μ where
  ne_zero := hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie]; rw [← t.lie_h_e_nsmul]; rw [lie_lie]; rw [hm']; rw [lie_smul]; rw [he]; rw [lie_smul]; rw [hm']; rw [smul_smul]; rw [smul_smul]; rw [mul_comm ρ μ]; rw [sub_self]

variable (R) in
open Submodule in
/--
Definition of `toLieSubalgebra` / `toLieSubalgebra` 的定义

English:
definition toLieSubalgebra
  signature: (t : IsSl2Triple h e f)
  body: span R {e, f, h}
  lie_mem' {x y} hx hy := by
    simp only [carrier_eq_coe, SetLike.mem_coe] at hx hy ⊢
    induction hx using span_induction with
    | zero => simp
    | add u v hu hv hu' hv' => simpa only [add_lie] using add_mem hu' hv'
    | smul t u hu hu' => simpa only [smul_lie] using smul_m

中文:
定义 toLieSubalgebra
  签名: (t : IsSl2Triple h e f)
  定义体: span R {e, f, h}
  lie_mem' {x y} hx hy := by
    simp only [carrier_eq_coe, SetLike.mem_coe] at hx hy ⊢
    induction hx using span_induction with
    | zero => simp
    | add u v hu hv hu' hv' => simpa only [add_lie] using add_mem hu' hv'
    | smul t u hu hu' => simpa only [smul_lie] using smul_m
-/
def toLieSubalgebra (t : IsSl2Triple h e f) :
    LieSubalgebra R L where
  __ := span R {e, f, h}
  lie_mem' {x y} hx hy := by
    simp only [carrier_eq_coe, SetLike.mem_coe] at hx hy ⊢
    induction hx using span_induction with
    | zero => simp
    | add u v hu hv hu' hv' => simpa only [add_lie] using add_mem hu' hv'
    | smul t u hu hu' => simpa only [smul_lie] using smul_mem _ t hu'
    | mem u hu =>
      induction hy using span_induction with
      | zero => simp
      | add u v hu hv hu' hv' => simpa only [lie_add] using add_mem hu' hv'
      | smul t u hv hv' => simpa only [lie_smul] using smul_mem _ t hv'
      | mem v hv =>
        push _ in _ at hu hv
        rcases hu with rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl <;> (try simp only [lie_self, zero_mem])
        · rw [t.lie_e_f]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_e_nsmul, neg_mem_iff]
apply nsmul_mem subset_span _
          simp
        · rw [← lie_skew, t.lie_e_f, neg_mem_iff]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_f_nsmul, neg_neg]
apply nsmul_mem subset_span _
          simp
        · rw [t.lie_h_e_nsmul]
apply nsmul_mem subset_span _
          simp
        · rw [t.lie_h_f_nsmul, neg_mem_iff]
apply nsmul_mem subset_span _
          simp

/--
lemma `mem_toLieSubalgebra_iff` / 引理 `mem_toLieSubalgebra_iff`

English:
lemma mem_toLieSubalgebra_iff
  given: {x : L} {t : IsSl2Triple h e f}
  proof: by
  simp_rw [t.lie_e_f, toLieSubalgebra, ← LieSubalgebra.mem_toSubmodule, Submodule.mem_span_triple,
    eq_comm]

中文:
引理 mem_toLieSubalgebra_iff
  条件: {x : L} {t : IsSl2Triple h e f}
  证明: by
  simp_rw [t.lie_e_f, toLieSubalgebra, ← LieSubalgebra.mem_toSubmodule, Submodule.mem_span_triple,
    eq_comm]

Depends on / 依赖: LieSubalgebra, LieSubalgebra.mem_toSubmodule, Submodule, Submodule.mem_span_triple, eq_comm, lie_e_f, mem_span_triple, mem_toSubmodule, simp_rw, t.lie_e_f, toLieSubalgebra
-/
lemma mem_toLieSubalgebra_iff {x : L} {t : IsSl2Triple h e f} :
    x in t.toLieSubalgebra R ↔ exists c₁ c₂ c₃ : R, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp_rw [t.lie_e_f, toLieSubalgebra, ← LieSubalgebra.mem_toSubmodule, Submodule.mem_span_triple,
    eq_comm]

namespace HasPrimitiveVectorWith

variable {m : M} {μ : R} {t : IsSl2Triple h e f}
local notation "ψ " n => ((toEnd R L M f) ^ n) m

-- Although this is true by definition, we include this lemma (and the assumption) to mirror the API
-- for `lie_h_pow_toEnd_f` and `lie_e_pow_succ_toEnd_f`.
set_option linter.unusedVariables false in
@[nolint unusedArguments]
/--
lemma `lie_f_pow_toEnd_f` / 引理 `lie_f_pow_toEnd_f`

English:
lemma lie_f_pow_toEnd_f
  given: (P : HasPrimitiveVectorWith t m μ) (n : Nat)
  proof: by
  simp [pow_succ']

中文:
引理 lie_f_pow_toEnd_f
  条件: (P : HasPrimitiveVectorWith t m μ) (n : 自然数)
  证明: by
  simp [pow_succ']

Depends on / 依赖: pow_succ
-/
lemma lie_f_pow_toEnd_f (P : HasPrimitiveVectorWith t m μ) (n : Nat) :
    ⁅f, ψ n⁆ = ψ (n + 1) := by
  simp [pow_succ']

variable (P : HasPrimitiveVectorWith t m μ)
include P

/--
lemma `lie_h_pow_toEnd_f` / 引理 `lie_h_pow_toEnd_f`

English:
lemma lie_h_pow_toEnd_f
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simpa using P.lie_h
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; rw [toEnd_apply_apply]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [leibniz_lie h]; rw [t.lie_lie_smul_f R]; rw [← neg_smul]; rw [ih]; rw [lie_smul]; rw [smul_lie]; rw [← add_smul]
   

中文:
引理 lie_h_pow_toEnd_f
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simpa using P.lie_h
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; rw [toEnd_apply_apply]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [leibniz_lie h]; rw [t.lie_lie_smul_f R]; rw [← neg_smul]; rw [ih]; rw [lie_smul]; rw [smul_lie]; rw [← add_smul]
   

Depends on / 依赖: Module, Module.End.mul_apply, Nat.cast_add, Nat.cast_one, P.lie_h, add_smul, cast_add, cast_one, leibniz_lie, lie_h, lie_lie_smul_f, lie_smul, mul_apply, neg_smul, pow_succ, smul_lie, t.lie_lie_smul_f, toEnd_apply_apply
-/
lemma lie_h_pow_toEnd_f (n : Nat) :
    ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n := by
  induction n with
  | zero => simpa using P.lie_h
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; rw [toEnd_apply_apply]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [leibniz_lie h]; rw [t.lie_lie_smul_f R]; rw [← neg_smul]; rw [ih]; rw [lie_smul]; rw [smul_lie]; rw [← add_smul]
    congr
    ring

/--
lemma `lie_e_pow_succ_toEnd_f` / 引理 `lie_e_pow_succ_toEnd_f`

English:
lemma lie_e_pow_succ_toEnd_f
  given: (n : Nat)
  proof: by
  induction n with
  | zero =>
      simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        pow_zero, Module.End.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
        add_zero]
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; r

中文:
引理 lie_e_pow_succ_toEnd_f
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero =>
      simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        pow_zero, Module.End.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
        add_zero]
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; r

Depends on / 依赖: Module, Module.End.mul_apply, Module.End.one_apply, Nat.cast_add, Nat.cast_one, Nat.cast_zero, P.lie_e, P.lie_h, add_smul, add_zero, cast_add, cast_one, cast_zero, leibniz_lie, lie_e, lie_e_f, lie_f_pow_toEnd_f, lie_h, lie_h_pow_toEnd_f, lie_smul
-/
lemma lie_e_pow_succ_toEnd_f (n : Nat) :
    ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n := by
  induction n with
  | zero =>
      simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        pow_zero, Module.End.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
        add_zero]
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; rw [toEnd_apply_apply]; rw [leibniz_lie e]; rw [t.lie_e_f]; rw [lie_h_pow_toEnd_f P]; rw [ih]; rw [lie_smul]; rw [lie_f_pow_toEnd_f P]; rw [← add_smul]; rw [Nat.cast_add]; rw [Nat.cast_one]
    congr
    ring

/--
lemma `exists_nat` / 引理 `exists_nat`

English:
lemma exists_nat
  given: [IsNoetherian R M] [IsTorsionFree R M] [IsDomain R] [CharZero R]
  proof: by
  suffices exists n : Nat, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists P.ne_zero this
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEnd_f P n
    rw [hn₂]; rw [lie_zero]; rw [eq_comm]; rw [smul_eq_zero_iff_left hn₁]; rw [mul_eq_zero]; rw [sub_eq_zero] 

中文:
引理 exists_nat
  条件: [IsNoetherian R M] [IsTorsionFree R M] [IsDomain R] [CharZero R]
  证明: by
  suffices exists n : Nat, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists P.ne_zero this
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEnd_f P n
    rw [hn₂]; rw [lie_zero]; rw [eq_comm]; rw [smul_eq_zero_iff_left hn₁]; rw [mul_eq_zero]; rw [sub_eq_zero] 

Depends on / 依赖: Infinite, Nat.cast_add_one_ne_zero, Nat.exists_not_and_succ_of_not_zero_of_exists, P.ne_zero, cast_add_one_ne_zero, contra, eq_comm, exists_not_and_succ_of_not_zero_of_exists, infer_instance, infinite_range_iff, lie_e_pow_succ_toEnd_f, lie_zero, mul_eq_zero, ne_zero, resolve_left, smul_eq_zero_iff_left, sub_eq_zero, this.resolve_left
-/
lemma exists_nat [IsNoetherian R M] [IsTorsionFree R M] [IsDomain R] [CharZero R] :
    exists n : Nat, μ = n := by
  suffices exists n : Nat, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists P.ne_zero this
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEnd_f P n
    rw [hn₂]; rw [lie_zero]; rw [eq_comm]; rw [smul_eq_zero_iff_left hn₁]; rw [mul_eq_zero]; rw [sub_eq_zero] at this
exact this.resolve_left Nat.cast_add_one_ne_zero n
  have hs : (range <| fun (n : Nat) => μ - 2 * n).Infinite := by
    rw [infinite_range_iff (fun n m => by simp)]; infer_instance
  by_contra! contra
  exact hs ((toEnd R L M h).eigenvectors_linearIndependent
    {μ - 2 * n | n : Nat}
    (fun ⟨s, hs⟩ => ψ Classical.choose hs)
    (fun ⟨r, hr⟩ => by simp [lie_h_pow_toEnd_f P, Classical.choose_spec hr, contra,
      Module.End.hasEigenvector_iff])).finite

/--
lemma `pow_toEnd_f_ne_zero_of_eq_nat` / 引理 `pow_toEnd_f_ne_zero_of_eq_nat`

English:
lemma pow_toEnd_f_ne_zero_of_eq_nat
  statement: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  proof: by
  intro H
  induction i
  · exact P.ne_zero (by simpa using H)
  · next i IH =>
    have : ((i + 1) * (n - i) : Int) • (toEnd R L M f ^ i) m = 0 := by
      have := congr_arg (⁅e, ·⁆) H
      simpa [← Int.cast_smul_eq_zsmul R, P.lie_e_pow_succ_toEnd_f, hn] using this
    rw [← Int.cast_smul_eq_zs

中文:
引理 pow_toEnd_f_ne_zero_of_eq_nat
  结论: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  证明: by
  intro H
  induction i
  · exact P.ne_zero (by simpa using H)
  · next i IH =>
    have : ((i + 1) * (n - i) : Int) • (toEnd R L M f ^ i) m = 0 := by
      have := congr_arg (⁅e, ·⁆) H
      simpa [← Int.cast_smul_eq_zsmul R, P.lie_e_pow_succ_toEnd_f, hn] using this
    rw [← Int.cast_smul_eq_zs

Depends on / 依赖: Int.cast_eq_zero, Int.cast_smul_eq_zsmul, Nat.cast_add, Nat.cast_eq_zero, Nat.cast_inj, Nat.cast_one, P.lie_e_pow_succ_toEnd_f, P.ne_zero, add_eq_zero, and_false, cast_add, cast_eq_zero, cast_inj, cast_one, cast_smul_eq_zsmul, congr_arg, lie_e_pow_succ_toEnd_f, mul_eq_zero, ne_zero, one_ne_zero
-/
lemma pow_toEnd_f_ne_zero_of_eq_nat [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {n : Nat} (hn : μ = n) {i} (hi : i <= n) : (ψ i) != 0 := by
  intro H
  induction i
  · exact P.ne_zero (by simpa using H)
  · next i IH =>
    have : ((i + 1) * (n - i) : Int) • (toEnd R L M f ^ i) m = 0 := by
      have := congr_arg (⁅e, ·⁆) H
      simpa [← Int.cast_smul_eq_zsmul R, P.lie_e_pow_succ_toEnd_f, hn] using this
    rw [← Int.cast_smul_eq_zsmul R]; rw [smul_eq_zero]; rw [Int.cast_eq_zero]; rw [mul_eq_zero]; rw [sub_eq_zero]; rw [Nat.cast_inj]; rw [← @Nat.cast_one Int]; rw [← Nat.cast_add]; rw [Nat.cast_eq_zero] at this
    simp only [add_eq_zero, one_ne_zero, and_false, false_or] at this
    exact (hi.trans_eq (this.resolve_right (IH (i.le_succ.trans hi)))).not_gt i.lt_succ_self

/--
lemma `pow_toEnd_f_eq_zero_of_eq_nat` / 引理 `pow_toEnd_f_eq_zero_of_eq_nat`

English:
lemma pow_toEnd_f_eq_zero_of_eq_nat
  statement: [IsDomain R] [CharZero R] [IsNoetherian R M] [IsTorsionFree R M]
  proof: by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := this.exists_nat
  have : (n : Int) < m + 2 * (

中文:
引理 pow_toEnd_f_eq_zero_of_eq_nat
  结论: [IsDomain R] [CharZero R] [IsNoetherian R M] [IsTorsionFree R M]
  证明: by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := this.exists_nat
  have : (n : Int) < m + 2 * (

Depends on / 依赖: HasPrimitiveVectorWith, Int.cast_injective, P.lie_e_pow_succ_toEnd_f, P.lie_h_pow_toEnd_f, cast_injective, exists_nat, lie_e, lie_e_pow_succ_toEnd_f, lie_h, lie_h_pow_toEnd_f, ne_zero, sub_eq_iff_eq_add, t.HasPrimitiveVectorWith, this.exists_nat, this.ne
-/
lemma pow_toEnd_f_eq_zero_of_eq_nat [IsDomain R] [CharZero R] [IsNoetherian R M] [IsTorsionFree R M]
    {n : Nat} (hn : μ = n) : (ψ (n + 1)) = 0 := by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := this.exists_nat
  have : (n : Int) < m + 2 * (n + 1) := by lia
  exact this.ne (Int.cast_injective (α := R) <| by simpa [sub_eq_iff_eq_add] using hm)

end HasPrimitiveVectorWith

variable {m : M} {μ : R}
local notation "φ " n => ((toEnd R L M e) ^ n) m

/--
lemma `lie_e_pow_toEnd_e` / 引理 `lie_e_pow_toEnd_e`

English:
lemma lie_e_pow_toEnd_e
  given: (n : Nat)
  proof: by
  simp [pow_succ']

中文:
引理 lie_e_pow_toEnd_e
  条件: (n : 自然数)
  证明: by
  simp [pow_succ']

Depends on / 依赖: pow_succ
-/
lemma lie_e_pow_toEnd_e (n : Nat) :
    ⁅e, φ n⁆ = φ (n + 1) := by
  simp [pow_succ']

/--
lemma `lie_h_pow_toEnd_e` / 引理 `lie_h_pow_toEnd_e`

English:
lemma lie_h_pow_toEnd_e
  statement: (t : IsSl2Triple h e f)
  proof: by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; rw [toEnd_apply_apply]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [leibniz_lie h]; rw [IsSl2Triple.lie_h_e_smul R t]; rw [smul_lie]; rw [ih]; rw [lie_smul]; rw [← add_smul]
    congr 1
   

中文:
引理 lie_h_pow_toEnd_e
  结论: (t : IsSl2Triple h e f)
  证明: by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; rw [toEnd_apply_apply]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [leibniz_lie h]; rw [IsSl2Triple.lie_h_e_smul R t]; rw [smul_lie]; rw [ih]; rw [lie_smul]; rw [← add_smul]
    congr 1
   

Depends on / 依赖: IsSl2Triple, IsSl2Triple.lie_h_e_smul, Module, Module.End.mul_apply, Nat.cast_add, Nat.cast_one, add_smul, cast_add, cast_one, leibniz_lie, lie_h_e_smul, lie_smul, mul_apply, pow_succ, smul_lie, toEnd_apply_apply
-/
lemma lie_h_pow_toEnd_e (t : IsSl2Triple h e f)
    (hm : ⁅h, m⁆ = μ • m) (n : Nat) :
    ⁅h, φ n⁆ = (μ + 2 * n) • φ n := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ']; rw [Module.End.mul_apply]; rw [toEnd_apply_apply]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [leibniz_lie h]; rw [IsSl2Triple.lie_h_e_smul R t]; rw [smul_lie]; rw [ih]; rw [lie_smul]; rw [← add_smul]
    congr 1
    ring

section CharZero

variable [IsDomain R] [CharZero R]
  [Nontrivial M] [IsTorsionFree R M] [Module.Finite R M] [IsTriangularizable R L M]
  (t : IsSl2Triple h e f)

/--
lemma `exists_hasPrimitiveVectorWith` / 引理 `exists_hasPrimitiveVectorWith`

English:
lemma exists_hasPrimitiveVectorWith
  proof: by
  obtain ⟨μ₀, hμ₀⟩ := IsTriangularizable.exists_hasEigenvalue R L M h
  obtain ⟨m₀, hm₀⟩ := hμ₀.exists_hasEigenvector
  let evals (n : Nat) : R := μ₀ + 2 * (n : R)
  let e_vecs (n : Nat) : M := ((toEnd R L M e) ^ n) m₀
  have h_exists_zero : exists k, e_vecs k = 0 := by
    by_contra! contra
    

中文:
引理 exists_hasPrimitiveVectorWith
  证明: by
  obtain ⟨μ₀, hμ₀⟩ := IsTriangularizable.exists_hasEigenvalue R L M h
  obtain ⟨m₀, hm₀⟩ := hμ₀.exists_hasEigenvector
  let evals (n : Nat) : R := μ₀ + 2 * (n : R)
  let e_vecs (n : Nat) : M := ((toEnd R L M e) ^ n) m₀
  have h_exists_zero : exists k, e_vecs k = 0 := by
    by_contra! contra
    

Depends on / 依赖: Function, Function.Injective, HasEigenvector, Injective, IsTriangularizable, IsTriangularizable.exists_hasEigenvalue, Nat.cast_inj, add_right_inj, cast_inj, contra, e_vecs, exists_hasEigenvalue, exists_hasEigenvector, h_exists_zero, h_inj, mul_eq_mul_left_iff, property, property.choo
-/
lemma exists_hasPrimitiveVectorWith :
    exists (μ : R) (m : M), m != 0 ∧ HasPrimitiveVectorWith t m μ := by
  obtain ⟨μ₀, hμ₀⟩ := IsTriangularizable.exists_hasEigenvalue R L M h
  obtain ⟨m₀, hm₀⟩ := hμ₀.exists_hasEigenvector
  let evals (n : Nat) : R := μ₀ + 2 * (n : R)
  let e_vecs (n : Nat) : M := ((toEnd R L M e) ^ n) m₀
  have h_exists_zero : exists k, e_vecs k = 0 := by
    by_contra! contra
    have h_inj : Function.Injective evals := fun a b hab => by
      simpa [evals, add_right_inj, mul_eq_mul_left_iff, Nat.cast_inj] using hab
    have aux (μ : range evals) : (toEnd R L M h).HasEigenvector μ (e_vecs μ.property.choose) := by
      set n := μ.property.choose
      refine ⟨?_, contra n⟩
      rw [Module.End.mem_eigenspace_iff]; rw [toEnd_apply_apply]; rw [← μ.property.choose_spec]
      exact t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n
    have _i := ((toEnd R L M h).eigenvectors_linearIndependent (range evals) _ aux).finite
    exact (Set.infinite_range_of_injective h_inj) (Set.toFinite _)
  obtain ⟨n, hn_ne, hn_zero⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hm₀.2 h_exists_zero
  exact ⟨evals n, e_vecs n, hn_ne,
    { ne_zero := hn_ne
      lie_h := t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n
      lie_e := by rwa [lie_e_pow_toEnd_e n] }⟩

end CharZero

end IsSl2Triple
