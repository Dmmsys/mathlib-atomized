/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Morenikeji Neri
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Principal ideal rings, principal ideal domains, and Bézout rings

A principal ideal ring (PIR) is a ring in which all left ideals are principal. A
principal ideal domain (PID) is an integral domain which is a principal ideal ring.

The definition of `IsPrincipalIdealRing` can be found in `Mathlib/RingTheory/Ideal/Span.lean`.

## Main definitions

Note that for principal ideal domains, one should use
`[IsDomain R] [IsPrincipalIdealRing R]`. There is no explicit definition of a PID.
Theorems about PID's are in the `PrincipalIdealRing` namespace.

- `IsBezout`: the predicate saying that every finitely generated left ideal is principal.
- `generator`: a generator of a principal ideal (or more generally submodule)
- `to_uniqueFactorizationMonoid`: a PID is a unique factorization domain

## Main results

- `Ideal.IsPrime.to_maximal_ideal`: a non-zero prime ideal in a PID is maximal.
- `EuclideanDomain.to_principal_ideal_domain` : a Euclidean domain is a PID.
- `IsBezout.nonemptyGCDMonoid`: Every Bézout domain is a GCD domain.

-/

@[expose] public section


universe u v

variable {R : Type u} {M : Type v}

open Set Function

open Submodule

section

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
Instance `bot_isPrincipal` / 实例 `bot_isPrincipal`

English:
instance bot_isPrincipal
  signature: : (⊥ : Submodule R M).IsPrincipal
  body: ⟨⟨0, by simp⟩⟩

中文:
实例 bot_isPrincipal
  签名: : (⊥ : Submodule R M).IsPrincipal
  定义体: ⟨⟨0, by simp⟩⟩
-/
instance bot_isPrincipal : (⊥ : Submodule R M).IsPrincipal :=
  ⟨⟨0, by simp⟩⟩

/--
Instance `top_isPrincipal` / 实例 `top_isPrincipal`

English:
instance top_isPrincipal
  signature: : (⊤ : Submodule R R).IsPrincipal
  body: ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩

中文:
实例 top_isPrincipal
  签名: : (⊤ : Submodule R R).IsPrincipal
  定义体: ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩

Depends on / 依赖: Ideal.span_singleton_one.symm, span_singleton_one
-/
instance top_isPrincipal : (⊤ : Submodule R R).IsPrincipal :=
  ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩

variable (R)

/--
Definition of `IsBezout` / `IsBezout` 的定义

English:
class IsBezout
  parameters: : Prop where
  axioms and operations (1):
    - isPrincipal_of_FG : forall I : Ideal R, I.FG -> I.IsPrincipal

中文:
类 IsBezout
  参数: : 命题 where
  公理与运算 (1 个):
    - isPrincipal_of_FG : 对任意 I : Ideal R, I.FG -> I.IsPrincipal
-/
class IsBezout : Prop where
  /-- Any finitely generated ideal is principal. -/
  isPrincipal_of_FG : forall I : Ideal R, I.FG -> I.IsPrincipal

instance (priority := 100) IsBezout.of_isPrincipalIdealRing [IsPrincipalIdealRing R] : IsBezout R :=
  ⟨fun I _ => IsPrincipalIdealRing.principal I⟩

instance (priority := 100) DivisionSemiring.isPrincipalIdealRing (K : Type u) [DivisionSemiring K] :
    IsPrincipalIdealRing K where
  principal S := by
    rcases Ideal.eq_bot_or_top S with (rfl | rfl)
    · apply bot_isPrincipal
    · apply top_isPrincipal

end

namespace Submodule.IsPrincipal

variable [AddCommMonoid M]

section Semiring

variable [Semiring R] [Module R M]

@[simp]
/--
theorem `_root_.Ideal.span_singleton_generator` / 定理 `_root_.Ideal.span_singleton_generator`

English:
theorem _root_.Ideal.span_singleton_generator
  given: (I : Ideal R) [I.IsPrincipal]
  proof: Eq.symm (Classical.choose_spec (principal I))

@[simp]

中文:
定理 _root_.Ideal.span_singleton_generator
  条件: (I : Ideal R) [I.IsPrincipal]
  证明: Eq.symm (Classical.choose_spec (principal I))

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, Eq.symm, choose_spec, principal
-/
theorem _root_.Ideal.span_singleton_generator (I : Ideal R) [I.IsPrincipal] :
    Ideal.span ({generator I} : Set R) = I :=
  Eq.symm (Classical.choose_spec (principal I))

@[simp]
/--
theorem `generator_mem` / 定理 `generator_mem`

English:
theorem generator_mem
  given: (S : Submodule R M) [S.IsPrincipal]
  statement: generator S in S
  proof: by
  have : generator S in span R {generator S} := subset_span (mem_singleton _)
  convert! this
.symm exact span_singleton_generator S

中文:
定理 generator_mem
  条件: (S : Submodule R M) [S.IsPrincipal]
  结论: generator S in S
  证明: by
  have : generator S in span R {generator S} := subset_span (mem_singleton _)
  convert! this
.symm exact span_singleton_generator S

Depends on / 依赖: convert, generator, mem_singleton, span_singleton_generator, subset_span
-/
theorem generator_mem (S : Submodule R M) [S.IsPrincipal] : generator S in S := by
  have : generator S in span R {generator S} := subset_span (mem_singleton _)
  convert! this
.symm exact span_singleton_generator S

/--
theorem `mem_iff_eq_smul_generator` / 定理 `mem_iff_eq_smul_generator`

English:
theorem mem_iff_eq_smul_generator
  given: (S : Submodule R M) [S.IsPrincipal] {x : M}
  proof: by
  simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]

中文:
定理 mem_iff_eq_smul_generator
  条件: (S : Submodule R M) [S.IsPrincipal] {x : M}
  证明: by
  simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]

Depends on / 依赖: eq_comm, mem_span_singleton, simp_rw, span_singleton_generator
-/
theorem mem_iff_eq_smul_generator (S : Submodule R M) [S.IsPrincipal] {x : M} :
    x in S ↔ exists s : R, x = s • generator S := by
  simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]

/--
theorem `eq_bot_iff_generator_eq_zero` / 定理 `eq_bot_iff_generator_eq_zero`

English:
theorem eq_bot_iff_generator_eq_zero
  given: (S : Submodule R M) [S.IsPrincipal]
  proof: by rw [← @span_singleton_eq_bot R M, span_singleton_generator]

@[simp]

中文:
定理 eq_bot_iff_generator_eq_zero
  条件: (S : Submodule R M) [S.IsPrincipal]
  证明: by rw [← @span_singleton_eq_bot R M, span_singleton_generator]

@[simp]

Depends on / 依赖: span_singleton_eq_bot, span_singleton_generator
-/
theorem eq_bot_iff_generator_eq_zero (S : Submodule R M) [S.IsPrincipal] :
    S = ⊥ ↔ generator S = 0 := by rw [← @span_singleton_eq_bot R M, span_singleton_generator]

@[simp]
/--
theorem `generator_bot` / 定理 `generator_bot`

English:
theorem generator_bot
  statement: generator (⊥ : Submodule R M) = 0
  proof: (eq_bot_iff_generator_eq_zero ⊥).mp rfl

中文:
定理 generator_bot
  结论: generator (⊥ : Submodule R M) = 0
  证明: (eq_bot_iff_generator_eq_zero ⊥).mp rfl

Depends on / 依赖: eq_bot_iff_generator_eq_zero
-/
theorem generator_bot : generator (⊥ : Submodule R M) = 0 :=
  (eq_bot_iff_generator_eq_zero ⊥).mp rfl

/--
lemma `fg` / 引理 `fg`

English:
lemma fg
  given: {S : Submodule R M} (h : S.IsPrincipal)
  statement: S.FG
  proof: ⟨{h.generator}, by simp only [Finset.coe_singleton, span_singleton_generator]⟩

中文:
引理 fg
  条件: {S : Submodule R M} (h : S.IsPrincipal)
  结论: S.FG
  证明: ⟨{h.generator}, by simp only [Finset.coe_singleton, span_singleton_generator]⟩
-/
protected lemma fg {S : Submodule R M} (h : S.IsPrincipal) : S.FG :=
  ⟨{h.generator}, by simp only [Finset.coe_singleton, span_singleton_generator]⟩

-- See note [lower instance priority]
instance (priority := 100) _root_.PrincipalIdealRing.isNoetherianRing [IsPrincipalIdealRing R] :
    IsNoetherianRing R where
  noetherian S := (IsPrincipalIdealRing.principal S).fg

-- See note [lower instance priority]
instance (priority := 100) _root_.IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
    [IsNoetherianRing R] [IsBezout R] : IsPrincipalIdealRing R where
  principal S := IsBezout.isPrincipal_of_FG S (IsNoetherian.noetherian S)

end Semiring

section CommSemiring

variable [CommSemiring R] [Module R M]

/--
theorem `associated_generator_span_self` / 定理 `associated_generator_span_self`

English:
theorem associated_generator_span_self
  given: [IsDomain R] (r : R)
  proof: by
  rw [← Ideal.span_singleton_eq_span_singleton]
  exact Ideal.span_singleton_generator _

中文:
定理 associated_generator_span_self
  条件: [IsDomain R] (r : R)
  证明: by
  rw [← Ideal.span_singleton_eq_span_singleton]
  exact Ideal.span_singleton_generator _

Depends on / 依赖: Ideal.span_singleton_eq_span_singleton, Ideal.span_singleton_generator, span_singleton_eq_span_singleton, span_singleton_generator
-/
theorem associated_generator_span_self [IsDomain R] (r : R) :
    Associated (generator <| Ideal.span {r}) r := by
  rw [← Ideal.span_singleton_eq_span_singleton]
  exact Ideal.span_singleton_generator _

/--
theorem `mem_iff_generator_dvd` / 定理 `mem_iff_generator_dvd`

English:
theorem mem_iff_generator_dvd
  given: (S : Ideal R) [S.IsPrincipal] {x : R}
  statement: x in S ↔ generator S ∣ x
  proof: (mem_iff_eq_smul_generator S).trans (exists_congr fun a => by simp only [mul_comm, smul_eq_mul])

中文:
定理 mem_iff_generator_dvd
  条件: (S : Ideal R) [S.IsPrincipal] {x : R}
  结论: x in S ↔ generator S ∣ x
  证明: (mem_iff_eq_smul_generator S).trans (exists_congr fun a => by simp only [mul_comm, smul_eq_mul])

Depends on / 依赖: exists_congr, mem_iff_eq_smul_generator, mul_comm, smul_eq_mul
-/
theorem mem_iff_generator_dvd (S : Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x :=
  (mem_iff_eq_smul_generator S).trans (exists_congr fun a => by simp only [mul_comm, smul_eq_mul])

/--
theorem `prime_generator_of_isPrime` / 定理 `prime_generator_of_isPrime`

English:
theorem prime_generator_of_isPrime
  statement: (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime]
  proof: ⟨fun h => ne_bot ((eq_bot_iff_generator_eq_zero S).2 h), fun h =>
    is_prime.ne_top (S.eq_top_of_isUnit_mem (generator_mem S) h), fun _ _ => by
    simpa only [← mem_iff_generator_dvd S] using is_prime.2⟩

中文:
定理 prime_generator_of_isPrime
  结论: (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime]
  证明: ⟨fun h => ne_bot ((eq_bot_iff_generator_eq_zero S).2 h), fun h =>
    is_prime.ne_top (S.eq_top_of_isUnit_mem (generator_mem S) h), fun _ _ => by
    simpa only [← mem_iff_generator_dvd S] using is_prime.2⟩

Depends on / 依赖: S.eq_top_of_isUnit_mem, eq_bot_iff_generator_eq_zero, eq_top_of_isUnit_mem, generator_mem, is_prime, is_prime.ne_top, mem_iff_generator_dvd, ne_bot, ne_top
-/
theorem prime_generator_of_isPrime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime]
    (ne_bot : S != ⊥) : Prime (generator S) :=
  ⟨fun h => ne_bot ((eq_bot_iff_generator_eq_zero S).2 h), fun h =>
    is_prime.ne_top (S.eq_top_of_isUnit_mem (generator_mem S) h), fun _ _ => by
    simpa only [← mem_iff_generator_dvd S] using is_prime.2⟩

-- Note that the converse may not hold if `ϕ` is not injective.
/--
theorem `generator_map_dvd_of_mem` / 定理 `generator_map_dvd_of_mem`

English:
theorem generator_map_dvd_of_mem
  statement: {N : Submodule R M} (ϕ : M ->ₗ[R] R) [(N.map ϕ).IsPrincipal] {x : M}
  proof: by
  rw [← mem_iff_generator_dvd]; rw [Submodule.mem_map]
  exact ⟨x, hx, rfl⟩

中文:
定理 generator_map_dvd_of_mem
  结论: {N : Submodule R M} (ϕ : M ->ₗ[R] R) [(N.map ϕ).IsPrincipal] {x : M}
  证明: by
  rw [← mem_iff_generator_dvd]; rw [Submodule.mem_map]
  exact ⟨x, hx, rfl⟩

Depends on / 依赖: Submodule, Submodule.mem_map, mem_iff_generator_dvd, mem_map
-/
theorem generator_map_dvd_of_mem {N : Submodule R M} (ϕ : M ->ₗ[R] R) [(N.map ϕ).IsPrincipal] {x : M}
    (hx : x in N) : generator (N.map ϕ) ∣ ϕ x := by
  rw [← mem_iff_generator_dvd]; rw [Submodule.mem_map]
  exact ⟨x, hx, rfl⟩

-- Note that the converse may not hold if `ϕ` is not injective.
/--
theorem `generator_submoduleImage_dvd_of_mem` / 定理 `generator_submoduleImage_dvd_of_mem`

English:
theorem generator_submoduleImage_dvd_of_mem
  statement: {N O : Submodule R M} (hNO : N <= O) (ϕ : O ->ₗ[R] R)
  proof: by
  rw [← mem_iff_generator_dvd]; rw [LinearMap.mem_submoduleImage_of_le hNO]
  exact ⟨x, hx, rfl⟩

中文:
定理 generator_submoduleImage_dvd_of_mem
  结论: {N O : Submodule R M} (hNO : N <= O) (ϕ : O ->ₗ[R] R)
  证明: by
  rw [← mem_iff_generator_dvd]; rw [LinearMap.mem_submoduleImage_of_le hNO]
  exact ⟨x, hx, rfl⟩

Depends on / 依赖: LinearMap, LinearMap.mem_submoduleImage_of_le, mem_iff_generator_dvd, mem_submoduleImage_of_le
-/
theorem generator_submoduleImage_dvd_of_mem {N O : Submodule R M} (hNO : N <= O) (ϕ : O ->ₗ[R] R)
    [(ϕ.submoduleImage N).IsPrincipal] {x : M} (hx : x in N) :
    generator (ϕ.submoduleImage N) ∣ ϕ ⟨x, hNO hx⟩ := by
  rw [← mem_iff_generator_dvd]; rw [LinearMap.mem_submoduleImage_of_le hNO]
  exact ⟨x, hx, rfl⟩

/--
theorem `dvd_generator_span_iff` / 定理 `dvd_generator_span_iff`

English:
theorem dvd_generator_span_iff
  given: {r : R} {s : Set R} [(Ideal.span s).IsPrincipal]
  proof: h.trans (mem_iff_generator_dvd _).mp (Ideal.subset_span hx)
  mpr h := have : (span R s).IsPrincipal := ‹_›
    span_induction h (dvd_zero _) (fun _ _ _ _ => dvd_add) (fun _ _ _ => (·.mul_left _))
      (generator_mem _)

中文:
定理 dvd_generator_span_iff
  条件: {r : R} {s : Set R} [(Ideal.span s).IsPrincipal]
  证明: h.trans (mem_iff_generator_dvd _).mp (Ideal.subset_span hx)
  mpr h := have : (span R s).IsPrincipal := ‹_›
    span_induction h (dvd_zero _) (fun _ _ _ _ => dvd_add) (fun _ _ _ => (·.mul_left _))
      (generator_mem _)

Depends on / 依赖: Ideal.subset_span, h.trans, mem_iff_generator_dvd, subset_span
-/
theorem dvd_generator_span_iff {r : R} {s : Set R} [(Ideal.span s).IsPrincipal] :
    r ∣ generator (Ideal.span s) ↔ forall x in s, r ∣ x where
mp h x hx := h.trans (mem_iff_generator_dvd _).mp (Ideal.subset_span hx)
  mpr h := have : (span R s).IsPrincipal := ‹_›
    span_induction h (dvd_zero _) (fun _ _ _ _ => dvd_add) (fun _ _ _ => (·.mul_left _))
      (generator_mem _)

end CommSemiring

end Submodule.IsPrincipal

namespace IsBezout

section

variable [Ring R]

/--
Instance `span_pair_isPrincipal` / 实例 `span_pair_isPrincipal`

English:
instance span_pair_isPrincipal
  signature: [IsBezout R] (x y : R)
  body: by
  classical exact isPrincipal_of_FG (Ideal.span {x, y}) ⟨{x, y}, by simp⟩

中文:
实例 span_pair_isPrincipal
  签名: [IsBezout R] (x y : R)
  定义体: by
  classical exact isPrincipal_of_FG (Ideal.span {x, y}) ⟨{x, y}, by simp⟩

Depends on / 依赖: Ideal.span, classical, isPrincipal_of_FG
-/
instance span_pair_isPrincipal [IsBezout R] (x y : R) : (Ideal.span {x, y}).IsPrincipal := by
  classical exact isPrincipal_of_FG (Ideal.span {x, y}) ⟨{x, y}, by simp⟩

variable (x y : R) [(Ideal.span {x, y}).IsPrincipal]

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: : R
  body: Submodule.IsPrincipal.generator (Ideal.span {x, y})

中文:
定义 gcd
  签名: : R
  定义体: Submodule.IsPrincipal.generator (Ideal.span {x, y})

Depends on / 依赖: Ideal.span, IsPrincipal, Submodule, Submodule.IsPrincipal.generator, generator
-/
noncomputable def gcd : R := Submodule.IsPrincipal.generator (Ideal.span {x, y})

/--
theorem `span_gcd` / 定理 `span_gcd`

English:
theorem span_gcd
  statement: Ideal.span {gcd x y} = Ideal.span {x, y}
  proof: Ideal.span_singleton_generator _

中文:
定理 span_gcd
  结论: Ideal.span {gcd x y} = Ideal.span {x, y}
  证明: Ideal.span_singleton_generator _

Depends on / 依赖: Ideal.span_singleton_generator, span_singleton_generator
-/
theorem span_gcd : Ideal.span {gcd x y} = Ideal.span {x, y} :=
  Ideal.span_singleton_generator _

end

variable [CommRing R] (x y z : R) [(Ideal.span {x, y}).IsPrincipal]

/--
theorem `gcd_dvd_left` / 定理 `gcd_dvd_left`

English:
theorem gcd_dvd_left
  statement: gcd x y ∣ x
  proof: (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

中文:
定理 gcd_dvd_left
  结论: gcd x y ∣ x
  证明: (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

Depends on / 依赖: Ideal.subset_span, IsPrincipal, Submodule, Submodule.IsPrincipal.mem_iff_generator_dvd, mem_iff_generator_dvd, subset_span
-/
theorem gcd_dvd_left : gcd x y ∣ x :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

/--
theorem `gcd_dvd_right` / 定理 `gcd_dvd_right`

English:
theorem gcd_dvd_right
  statement: gcd x y ∣ y
  proof: (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

中文:
定理 gcd_dvd_right
  结论: gcd x y ∣ y
  证明: (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

Depends on / 依赖: Ideal.subset_span, IsPrincipal, Submodule, Submodule.IsPrincipal.mem_iff_generator_dvd, mem_iff_generator_dvd, subset_span
-/
theorem gcd_dvd_right : gcd x y ∣ y :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

variable {x y z} in
/--
theorem `dvd_gcd` / 定理 `dvd_gcd`

English:
theorem dvd_gcd
  given: (hx : z ∣ x) (hy : z ∣ y)
  statement: z ∣ gcd x y
  proof: by
  rw [← Ideal.span_singleton_le_span_singleton] at hx hy ⊢
  rw [span_gcd]; rw [Ideal.span_insert]; rw [sup_le_iff]
  exact ⟨hx, hy⟩

中文:
定理 dvd_gcd
  条件: (hx : z ∣ x) (hy : z ∣ y)
  结论: z ∣ gcd x y
  证明: by
  rw [← Ideal.span_singleton_le_span_singleton] at hx hy ⊢
  rw [span_gcd]; rw [Ideal.span_insert]; rw [sup_le_iff]
  exact ⟨hx, hy⟩

Depends on / 依赖: Ideal.span_insert, Ideal.span_singleton_le_span_singleton, span_gcd, span_insert, span_singleton_le_span_singleton, sup_le_iff
-/
theorem dvd_gcd (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y := by
  rw [← Ideal.span_singleton_le_span_singleton] at hx hy ⊢
  rw [span_gcd]; rw [Ideal.span_insert]; rw [sup_le_iff]
  exact ⟨hx, hy⟩

/--
theorem `gcd_eq_sum` / 定理 `gcd_eq_sum`

English:
theorem gcd_eq_sum
  statement: exists a b : R, a * x + b * y = gcd x y
  proof: Ideal.mem_span_pair.mp (by rw [← span_gcd]; apply Ideal.subset_span; simp)

中文:
定理 gcd_eq_sum
  结论: 存在 a b : R, a * x + b * y = gcd x y
  证明: Ideal.mem_span_pair.mp (by rw [← span_gcd]; apply Ideal.subset_span; simp)

Depends on / 依赖: Ideal.mem_span_pair.mp, Ideal.subset_span, mem_span_pair, span_gcd, subset_span
-/
theorem gcd_eq_sum : exists a b : R, a * x + b * y = gcd x y :=
  Ideal.mem_span_pair.mp (by rw [← span_gcd]; apply Ideal.subset_span; simp)

variable {x y}

/--
theorem `_root_.IsRelPrime.isCoprime` / 定理 `_root_.IsRelPrime.isCoprime`

English:
theorem _root_.IsRelPrime.isCoprime
  given: (h : IsRelPrime x y)
  statement: IsCoprime x y
  proof: by
  rw [← Ideal.isCoprime_span_singleton_iff]; rw [Ideal.isCoprime_iff_sup_eq]; rw [← Ideal.span_union]; rw [Set.singleton_union]; rw [← span_gcd]; rw [Ideal.span_singleton_eq_top]
  exact h (gcd_dvd_left x y) (gcd_dvd_right x y)

中文:
定理 _root_.IsRelPrime.isCoprime
  条件: (h : IsRelPrime x y)
  结论: IsCoprime x y
  证明: by
  rw [← Ideal.isCoprime_span_singleton_iff]; rw [Ideal.isCoprime_iff_sup_eq]; rw [← Ideal.span_union]; rw [Set.singleton_union]; rw [← span_gcd]; rw [Ideal.span_singleton_eq_top]
  exact h (gcd_dvd_left x y) (gcd_dvd_right x y)

Depends on / 依赖: Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff, Ideal.span_singleton_eq_top, Ideal.span_union, Set.singleton_union, gcd_dvd_left, gcd_dvd_right, isCoprime_iff_sup_eq, isCoprime_span_singleton_iff, singleton_union, span_gcd, span_singleton_eq_top, span_union
-/
theorem _root_.IsRelPrime.isCoprime (h : IsRelPrime x y) : IsCoprime x y := by
  rw [← Ideal.isCoprime_span_singleton_iff]; rw [Ideal.isCoprime_iff_sup_eq]; rw [← Ideal.span_union]; rw [Set.singleton_union]; rw [← span_gcd]; rw [Ideal.span_singleton_eq_top]
  exact h (gcd_dvd_left x y) (gcd_dvd_right x y)

/--
theorem `_root_.isRelPrime_iff_isCoprime` / 定理 `_root_.isRelPrime_iff_isCoprime`

English:
theorem _root_.isRelPrime_iff_isCoprime
  statement: IsRelPrime x y ↔ IsCoprime x y
  proof: ⟨IsRelPrime.isCoprime, IsCoprime.isRelPrime⟩

中文:
定理 _root_.isRelPrime_iff_isCoprime
  结论: IsRelPrime x y ↔ IsCoprime x y
  证明: ⟨IsRelPrime.isCoprime, IsCoprime.isRelPrime⟩

Depends on / 依赖: IsCoprime, IsCoprime.isRelPrime, IsRelPrime, IsRelPrime.isCoprime, isCoprime, isRelPrime
-/
theorem _root_.isRelPrime_iff_isCoprime : IsRelPrime x y ↔ IsCoprime x y :=
  ⟨IsRelPrime.isCoprime, IsCoprime.isRelPrime⟩

variable (R)

/-- Any Bézout domain is a GCD domain. This is not an instance since `GCDMonoid` contains data,
and this might not be how we would like to construct it. -/
@[instance_reducible]
/--
Definition of `toGCDDomain` / `toGCDDomain` 的定义

English:
definition toGCDDomain
  signature: [IsBezout R] [IsCancelMulZero R] [DecidableEq R]
  body: gcdMonoidOfGCD (gcd · ·) (gcd_dvd_left · ·) (gcd_dvd_right · ·) dvd_gcd

中文:
定义 toGCDDomain
  签名: [IsBezout R] [IsCancelMulZero R] [DecidableEq R]
  定义体: gcdMonoidOfGCD (gcd · ·) (gcd_dvd_left · ·) (gcd_dvd_right · ·) dvd_gcd

Depends on / 依赖: dvd_gcd, gcdMonoidOfGCD, gcd_dvd_left, gcd_dvd_right
-/
noncomputable def toGCDDomain [IsBezout R] [IsCancelMulZero R] [DecidableEq R] : GCDMonoid R :=
  gcdMonoidOfGCD (gcd · ·) (gcd_dvd_left · ·) (gcd_dvd_right · ·) dvd_gcd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsBezout
  signature: R] [IsCancelMulZero R] : IsGCDMonoid R
  body: by
  classical exact ⟨toGCDDomain R⟩

中文:
实例 [IsBezout
  签名: R] [IsCancelMulZero R] : IsGCDMonoid R
  定义体: by
  classical exact ⟨toGCDDomain R⟩

Depends on / 依赖: classical, toGCDDomain
-/
instance [IsBezout R] [IsCancelMulZero R] : IsGCDMonoid R := by
  classical exact ⟨toGCDDomain R⟩

/--
theorem `associated_gcd_gcd` / 定理 `associated_gcd_gcd`

English:
theorem associated_gcd_gcd
  given: [GCDMonoid R]
  statement: Associated (IsBezout.gcd x y) (GCDMonoid.gcd x y)
  proof: gcd_greatest_associated (gcd_dvd_left _ _) (gcd_dvd_right _ _) (fun _ => dvd_gcd)

中文:
定理 associated_gcd_gcd
  条件: [GCDMonoid R]
  结论: Associated (IsBezout.gcd x y) (GCDMonoid.gcd x y)
  证明: gcd_greatest_associated (gcd_dvd_left _ _) (gcd_dvd_right _ _) (fun _ => dvd_gcd)

Depends on / 依赖: dvd_gcd, gcd_dvd_left, gcd_dvd_right, gcd_greatest_associated
-/
theorem associated_gcd_gcd [GCDMonoid R] : Associated (IsBezout.gcd x y) (GCDMonoid.gcd x y) :=
  gcd_greatest_associated (gcd_dvd_left _ _) (gcd_dvd_right _ _) (fun _ => dvd_gcd)

end IsBezout

/--
lemma `Finset.gcd_eq_sum_mul` / 引理 `Finset.gcd_eq_sum_mul`

English:
lemma Finset.gcd_eq_sum_mul
  statement: {α : Type*} [CommRing R] [IsBezout R] [NormalizedGCDMonoid R]
  proof: by classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨x, y, hxy⟩ := IsBezout.gcd_eq_sum (f a) (s.gcd f)
    obtain ⟨u, hu⟩ := IsBezout.associated_gcd_gcd R (x := f a) (y := s.gcd f)
    rw [← hxy]; rw [add_mul]; rw [mul_comm x]; rw [mul_comm y] 

中文:
引理 Finset.gcd_eq_sum_mul
  结论: {α : 类型} [CommRing R] [IsBezout R] [NormalizedGCDMonoid R]
  证明: by classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨x, y, hxy⟩ := IsBezout.gcd_eq_sum (f a) (s.gcd f)
    obtain ⟨u, hu⟩ := IsBezout.associated_gcd_gcd R (x := f a) (y := s.gcd f)
    rw [← hxy]; rw [add_mul]; rw [mul_comm x]; rw [mul_comm y] 

Depends on / 依赖: Finset, Finset.induction, Function, Function.update, Function.update_self, IsBezout, IsBezout.associated_gcd_gcd, IsBezout.gcd_eq_sum, add_mul, add_right_inj, associated_gcd_gcd, classical, gcd_eq_sum, gcd_insert, insert, mul_assoc, mul_comm, s.gcd, sum_co, sum_insert
-/
lemma Finset.gcd_eq_sum_mul {α : Type*} [CommRing R] [IsBezout R] [NormalizedGCDMonoid R]
    (s : Finset α) (f : α -> R) :
    exists g : α -> R, s.gcd f = ∑ a in s, f a * g a := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨x, y, hxy⟩ := IsBezout.gcd_eq_sum (f a) (s.gcd f)
    obtain ⟨u, hu⟩ := IsBezout.associated_gcd_gcd R (x := f a) (y := s.gcd f)
    rw [← hxy]; rw [add_mul]; rw [mul_comm x]; rw [mul_comm y] at hu
    obtain ⟨g, hg⟩ := ih
    refine ⟨Function.update (g · * (y * u)) a (x * u), ?_⟩
    rw [gcd_insert]; rw [sum_insert ha]; rw [← hu]; rw [hg]
    simp only [Function.update_self, add_right_inj, sum_mul, mul_assoc]
exact sum_congr rfl fun b hb => congrArg (f b * ·)
      (Function.update_of_ne (show b != a by grind) (x * u) (g · * (y * u))).symm

namespace IsPrime

open Submodule.IsPrincipal Ideal

-- TODO -- for a non-ID one could perhaps prove that if p < q are prime then q maximal;
-- 0 isn't prime in a non-ID PIR but the Krull dimension is still <= 1.
-- The below result follows from this, but we could also use the below result to
-- prove this (quotient out by p).
/--
theorem `to_maximal_ideal` / 定理 `to_maximal_ideal`

English:
theorem to_maximal_ideal
  statement: [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {S : Ideal R}
  proof: isMaximal_iff.2
    ⟨(ne_top_iff_one S).1 hpi.1, by
      intro T x hST hxS hxT
      obtain ⟨z, hz⟩ := (mem_iff_generator_dvd _).1 (hST <| generator_mem S)
      cases hpi.mem_or_mem (show generator T * z in S from hz ▸ generator_mem S) with
      | inl h =>
        have hTS : T <= S := by
        

中文:
定理 to_maximal_ideal
  结论: [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {S : Ideal R}
  证明: isMaximal_iff.2
    ⟨(ne_top_iff_one S).1 hpi.1, by
      intro T x hST hxS hxT
      obtain ⟨z, hz⟩ := (mem_iff_generator_dvd _).1 (hST <| generator_mem S)
      cases hpi.mem_or_mem (show generator T * z in S from hz ▸ generator_mem S) with
      | inl h =>
        have hTS : T <= S := by
        

Depends on / 依赖: Ideal.span_le, T.span_singleton_generator, eq_bot_iff_generator_eq_zero, generator, generator_mem, hpi.mem_or_mem, isMaximal_iff, mem_iff_generator_dvd, mem_or_mem, mul_one, ne_top_iff_one, singleton_subset_iff, span_le, span_singleton_generator
-/
theorem to_maximal_ideal [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {S : Ideal R}
    [hpi : IsPrime S] (hS : S != ⊥) : IsMaximal S :=
  isMaximal_iff.2
    ⟨(ne_top_iff_one S).1 hpi.1, by
      intro T x hST hxS hxT
      obtain ⟨z, hz⟩ := (mem_iff_generator_dvd _).1 (hST <| generator_mem S)
      cases hpi.mem_or_mem (show generator T * z in S from hz ▸ generator_mem S) with
      | inl h =>
        have hTS : T <= S := by
          rwa [← T.span_singleton_generator, Ideal.span_le, singleton_subset_iff]
        exact (hxS <| hTS hxT).elim
      | inr h =>
        obtain ⟨y, hy⟩ := (mem_iff_generator_dvd _).1 h
        have : generator S != 0 := mt (eq_bot_iff_generator_eq_zero _).2 hS
        rw [← mul_one (generator S)]; rw [hy]; rw [mul_left_comm]; rw [mul_right_inj' this] at hz
        exact hz.symm ▸ T.mul_mem_right _ (generator_mem T)⟩

end IsPrime

section

open EuclideanDomain

variable [EuclideanDomain R]

/--
theorem `mod_mem_iff` / 定理 `mod_mem_iff`

English:
theorem mod_mem_iff
  given: {S : Ideal R} {x y : R} (hy : y in S)
  statement: x % y in S ↔ x in S
  proof: ⟨fun hxy => div_add_mod x y ▸ S.add_mem (S.mul_mem_right _ hy) hxy, fun hx =>
    (mod_eq_sub_mul_div x y).symm ▸ S.sub_mem hx (S.mul_mem_right _ hy)⟩

中文:
定理 mod_mem_iff
  条件: {S : Ideal R} {x y : R} (hy : y in S)
  结论: x % y in S ↔ x in S
  证明: ⟨fun hxy => div_add_mod x y ▸ S.add_mem (S.mul_mem_right _ hy) hxy, fun hx =>
    (mod_eq_sub_mul_div x y).symm ▸ S.sub_mem hx (S.mul_mem_right _ hy)⟩

Depends on / 依赖: S.add_mem, S.mul_mem_right, S.sub_mem, add_mem, div_add_mod, mod_eq_sub_mul_div, mul_mem_right, sub_mem
-/
theorem mod_mem_iff {S : Ideal R} {x y : R} (hy : y in S) : x % y in S ↔ x in S :=
  ⟨fun hxy => div_add_mod x y ▸ S.add_mem (S.mul_mem_right _ hy) hxy, fun hx =>
    (mod_eq_sub_mul_div x y).symm ▸ S.sub_mem hx (S.mul_mem_right _ hy)⟩

-- see Note [lower instance priority]
instance (priority := 100) EuclideanDomain.to_principal_ideal_domain : IsPrincipalIdealRing R where
  principal S := by classical exact
    ⟨if h : { x : R | x in S ∧ x != 0 }.Nonempty then
        have wf : WellFounded (EuclideanDomain.r : R -> R -> Prop) := EuclideanDomain.r_wellFounded
        have hmin : WellFounded.min wf { x : R | x in S ∧ x != 0 } h in S ∧
            WellFounded.min wf { x : R | x in S ∧ x != 0 } h != 0 :=
          WellFounded.min_mem wf { x : R | x in S ∧ x != 0 } h
        ⟨WellFounded.min wf { x : R | x in S ∧ x != 0 } h,
          Submodule.ext fun x => ⟨fun hx =>
            div_add_mod x (WellFounded.min wf { x : R | x in S ∧ x != 0 } h) ▸
              (Ideal.mem_span_singleton.2 <| dvd_add (dvd_mul_right _ _) <| by
                have : x % WellFounded.min wf { x : R | x in S ∧ x != 0 } h ∉
                    { x : R | x in S ∧ x != 0 } :=
                  fun h₁ => WellFounded.not_lt_min wf _ h₁ (mod_lt x hmin.2)
                have : x % WellFounded.min wf { x : R | x in S ∧ x != 0 } h = 0 := by
                  simp only [not_and_or, Set.mem_ofPred_eq, not_ne_iff] at this
exact this.neg_resolve_left (mod_mem_iff hmin.1).2 hx
                simp [*]),
              fun hx =>
                let ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
                hy.symm ▸ S.mul_mem_right _ hmin.1⟩⟩
      else ⟨0, Submodule.ext fun a => by
            rw [← @Submodule.bot_coe R R _ _ _]; rw [span_eq]; rw [Submodule.mem_bot]
            exact ⟨fun haS => by_contra fun ha0 => h ⟨a, ⟨haS, ha0⟩⟩,
              fun h₁ => h₁.symm ▸ S.zero_mem⟩⟩⟩

end

/--
theorem `IsField.isPrincipalIdealRing` / 定理 `IsField.isPrincipalIdealRing`

English:
theorem IsField.isPrincipalIdealRing
  given: {R : Type*} [Ring R] (h : IsField R)
  proof: @EuclideanDomain.to_principal_ideal_domain R (@Field.toEuclideanDomain R h.toField)

中文:
定理 IsField.isPrincipalIdealRing
  条件: {R : 类型} [Ring R] (h : IsField R)
  证明: @EuclideanDomain.to_principal_ideal_domain R (@Field.toEuclideanDomain R h.toField)

Depends on / 依赖: EuclideanDomain, EuclideanDomain.to_principal_ideal_domain, Field.toEuclideanDomain, h.toField, toEuclideanDomain, toField, to_principal_ideal_domain
-/
theorem IsField.isPrincipalIdealRing {R : Type*} [Ring R] (h : IsField R) :
    IsPrincipalIdealRing R :=
  @EuclideanDomain.to_principal_ideal_domain R (@Field.toEuclideanDomain R h.toField)

namespace PrincipalIdealRing

open IsPrincipalIdealRing

/--
theorem `isMaximal_of_irreducible` / 定理 `isMaximal_of_irreducible`

English:
theorem isMaximal_of_irreducible
  statement: [CommSemiring R] [IsPrincipalIdealRing R] {p : R}
  proof: ⟨⟨mt Ideal.span_singleton_eq_top.1 hp.1, fun I hI => by
      rcases principal I with ⟨a, rfl⟩
      rw [Ideal.submodule_span_eq]; rw [Ideal.span_singleton_eq_top]
      rcases Ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩
      refine (of_irreducible_mul hp).resolve_right (mt

中文:
定理 isMaximal_of_irreducible
  结论: [CommSemiring R] [IsPrincipalIdealRing R] {p : R}
  证明: ⟨⟨mt Ideal.span_singleton_eq_top.1 hp.1, fun I hI => by
      rcases principal I with ⟨a, rfl⟩
      rw [Ideal.submodule_span_eq]; rw [Ideal.span_singleton_eq_top]
      rcases Ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩
      refine (of_irreducible_mul hp).resolve_right (mt

Depends on / 依赖: Ideal.span_singleton_eq_top, Ideal.span_singleton_le_span_singleton, Ideal.submodule_span_eq, IsUnit, IsUnit.mul_right_dvd, le_of_lt, mul_right_dvd, not_le_of_gt, of_irreducible_mul, principal, resolve_right, span_singleton_eq_top, span_singleton_le_span_singleton, submodule_span_eq
-/
theorem isMaximal_of_irreducible [CommSemiring R] [IsPrincipalIdealRing R] {p : R}
    (hp : Irreducible p) : Ideal.IsMaximal (span R ({p} : Set R)) :=
  ⟨⟨mt Ideal.span_singleton_eq_top.1 hp.1, fun I hI => by
      rcases principal I with ⟨a, rfl⟩
      rw [Ideal.submodule_span_eq]; rw [Ideal.span_singleton_eq_top]
      rcases Ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩
      refine (of_irreducible_mul hp).resolve_right (mt (fun hb => ?_) (not_le_of_gt hI))
      rw [Ideal.submodule_span_eq]; rw [Ideal.submodule_span_eq]; rw [Ideal.span_singleton_le_span_singleton]; rw [IsUnit.mul_right_dvd hb]⟩⟩

/--
theorem `_root_.Ideal.irreducible_iff_isMaximal_span_singleton` / 定理 `_root_.Ideal.irreducible_iff_isMaximal_span_singleton`

English:
theorem _root_.Ideal.irreducible_iff_isMaximal_span_singleton
  proof: ⟨isMaximal_of_irreducible, Ideal.irreducible_of_isMaximal_span_singleton hp⟩

中文:
定理 _root_.Ideal.irreducible_iff_isMaximal_span_singleton
  证明: ⟨isMaximal_of_irreducible, Ideal.irreducible_of_isMaximal_span_singleton hp⟩

Depends on / 依赖: Ideal.irreducible_of_isMaximal_span_singleton, irreducible_of_isMaximal_span_singleton, isMaximal_of_irreducible
-/
theorem _root_.Ideal.irreducible_iff_isMaximal_span_singleton
    [CommSemiring R] [IsPrincipalIdealRing R] [IsDomain R] {p : R} (hp : p != 0) :
    Irreducible p ↔ Ideal.IsMaximal (span R ({p} : Set R)) :=
  ⟨isMaximal_of_irreducible, Ideal.irreducible_of_isMaximal_span_singleton hp⟩

variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

section

open scoped Classical in
/--
Definition of `factors` / `factors` 的定义

English:
definition factors
  signature: (a : R)
  body: if h : a = 0 then ∅ else Classical.choose (WfDvdMonoid.exists_factors a h)

中文:
定义 factors
  签名: (a : R)
  定义体: if h : a = 0 then ∅ else Classical.choose (WfDvdMonoid.exists_factors a h)

Depends on / 依赖: Classical, Classical.choose, WfDvdMonoid, WfDvdMonoid.exists_factors, exists_factors
-/
noncomputable def factors (a : R) : Multiset R :=
  if h : a = 0 then ∅ else Classical.choose (WfDvdMonoid.exists_factors a h)

/--
theorem `factors_spec` / 定理 `factors_spec`

English:
theorem factors_spec
  given: (a : R) (h : a != 0)
  proof: by
  unfold factors; rw [dif_neg h]
  exact Classical.choose_spec (WfDvdMonoid.exists_factors a h)

中文:
定理 factors_spec
  条件: (a : R) (h : a != 0)
  证明: by
  unfold factors; rw [dif_neg h]
  exact Classical.choose_spec (WfDvdMonoid.exists_factors a h)

Depends on / 依赖: Classical, Classical.choose_spec, WfDvdMonoid, WfDvdMonoid.exists_factors, choose_spec, dif_neg, exists_factors, factors
-/
theorem factors_spec (a : R) (h : a != 0) :
    (forall b in factors a, Irreducible b) ∧ Associated (factors a).prod a := by
  unfold factors; rw [dif_neg h]
  exact Classical.choose_spec (WfDvdMonoid.exists_factors a h)

/--
theorem `ne_zero_of_mem_factors` / 定理 `ne_zero_of_mem_factors`

English:
theorem ne_zero_of_mem_factors
  statement: {R : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  proof: Irreducible.ne_zero ((factors_spec a ha).1 b hb)

中文:
定理 ne_zero_of_mem_factors
  结论: {R : 类型v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  证明: Irreducible.ne_zero ((factors_spec a ha).1 b hb)

Depends on / 依赖: Irreducible, Irreducible.ne_zero, factors_spec, ne_zero
-/
theorem ne_zero_of_mem_factors {R : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {a b : R} (ha : a != 0) (hb : b in factors a) : b != 0 :=
  Irreducible.ne_zero ((factors_spec a ha).1 b hb)

/--
theorem `mem_submonoid_of_factors_subset_of_units_subset` / 定理 `mem_submonoid_of_factors_subset_of_units_subset`

English:
theorem mem_submonoid_of_factors_subset_of_units_subset
  statement: (s : Submonoid R) {a : R} (ha : a != 0)
  proof: by
  rcases (factors_spec a ha).2 with ⟨c, hc⟩
  rw [← hc]
  exact mul_mem (multiset_prod_mem _ hfac) (hunit _)

中文:
定理 mem_submonoid_of_factors_subset_of_units_subset
  结论: (s : Submonoid R) {a : R} (ha : a != 0)
  证明: by
  rcases (factors_spec a ha).2 with ⟨c, hc⟩
  rw [← hc]
  exact mul_mem (multiset_prod_mem _ hfac) (hunit _)

Depends on / 依赖: factors_spec, mul_mem, multiset_prod_mem
-/
theorem mem_submonoid_of_factors_subset_of_units_subset (s : Submonoid R) {a : R} (ha : a != 0)
    (hfac : forall b in factors a, b in s) (hunit : forall c : Rˣ, (c : R) in s) : a in s := by
  rcases (factors_spec a ha).2 with ⟨c, hc⟩
  rw [← hc]
  exact mul_mem (multiset_prod_mem _ hfac) (hunit _)

/--
theorem `ringHom_mem_submonoid_of_factors_subset_of_units_subset` / 定理 `ringHom_mem_submonoid_of_factors_subset_of_units_subset`

English:
theorem ringHom_mem_submonoid_of_factors_subset_of_units_subset
  statement: {R S : Type*} [CommRing R]
  proof: mem_submonoid_of_factors_subset_of_units_subset (s.comap f.toMonoidHom) ha h hf

中文:
定理 ringHom_mem_submonoid_of_factors_subset_of_units_subset
  结论: {R S : 类型} [CommRing R]
  证明: mem_submonoid_of_factors_subset_of_units_subset (s.comap f.toMonoidHom) ha h hf

Depends on / 依赖: f.toMonoidHom, mem_submonoid_of_factors_subset_of_units_subset, s.comap, toMonoidHom
-/
theorem ringHom_mem_submonoid_of_factors_subset_of_units_subset {R S : Type*} [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] [NonAssocSemiring S] (f : R ->+* S) (s : Submonoid S)
    (a : R) (ha : a != 0) (h : forall b in factors a, f b in s) (hf : forall c : Rˣ, f c in s) : f a in s :=
  mem_submonoid_of_factors_subset_of_units_subset (s.comap f.toMonoidHom) ha h hf

-- see Note [lower instance priority]
/-- A principal ideal domain has unique factorization -/
instance (priority := 100) to_uniqueFactorizationMonoid : UniqueFactorizationMonoid R :=
  { (IsNoetherianRing.wfDvdMonoid : WfDvdMonoid R) with
    irreducible_iff_prime := irreducible_iff_prime }

end

end PrincipalIdealRing

section Surjective

open Submodule

variable {S N F : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Semiring S]
variable [Module R M] [Module R N] [FunLike F R S] [RingHomClass F R S]

/--
theorem `Submodule.IsPrincipal.map` / 定理 `Submodule.IsPrincipal.map`

English:
theorem Submodule.IsPrincipal.map
  statement: (f : M ->ₗ[R] N) {S : Submodule R M}
  proof: ⟨⟨f (IsPrincipal.generator S), by
      rw [← Set.image_singleton]; rw [← map_span]; rw [span_singleton_generator]⟩⟩

中文:
定理 Submodule.IsPrincipal.map
  结论: (f : M ->ₗ[R] N) {S : Submodule R M}
  证明: ⟨⟨f (IsPrincipal.generator S), by
      rw [← Set.image_singleton]; rw [← map_span]; rw [span_singleton_generator]⟩⟩

Depends on / 依赖: IsPrincipal, IsPrincipal.generator, Set.image_singleton, generator, image_singleton, map_span, span_singleton_generator
-/
theorem Submodule.IsPrincipal.map (f : M ->ₗ[R] N) {S : Submodule R M}
    (hI : IsPrincipal S) : IsPrincipal (map f S) :=
  ⟨⟨f (IsPrincipal.generator S), by
      rw [← Set.image_singleton]; rw [← map_span]; rw [span_singleton_generator]⟩⟩

/--
theorem `Submodule.IsPrincipal.of_comap` / 定理 `Submodule.IsPrincipal.of_comap`

English:
theorem Submodule.IsPrincipal.of_comap
  statement: (f : M ->ₗ[R] N) (hf : Function.Surjective f)
  proof: by
  rw [← Submodule.map_comap_eq_of_surjective hf S]
  exact hI.map f

中文:
定理 Submodule.IsPrincipal.of_comap
  结论: (f : M ->ₗ[R] N) (hf : Function.Surjective f)
  证明: by
  rw [← Submodule.map_comap_eq_of_surjective hf S]
  exact hI.map f

Depends on / 依赖: Submodule, Submodule.map_comap_eq_of_surjective, hI.map, map_comap_eq_of_surjective
-/
theorem Submodule.IsPrincipal.of_comap (f : M ->ₗ[R] N) (hf : Function.Surjective f)
    (S : Submodule R N) [hI : IsPrincipal (S.comap f)] : IsPrincipal S := by
  rw [← Submodule.map_comap_eq_of_surjective hf S]
  exact hI.map f

/--
theorem `Submodule.IsPrincipal.map_ringHom` / 定理 `Submodule.IsPrincipal.map_ringHom`

English:
theorem Submodule.IsPrincipal.map_ringHom
  statement: (f : F) {I : Ideal R}
  proof: ⟨⟨f (IsPrincipal.generator I), by
      rw [Ideal.submodule_span_eq]; rw [← Set.image_singleton]; rw [← Ideal.map_span]; rw [Ideal.span_singleton_generator]⟩⟩

中文:
定理 Submodule.IsPrincipal.map_ringHom
  结论: (f : F) {I : Ideal R}
  证明: ⟨⟨f (IsPrincipal.generator I), by
      rw [Ideal.submodule_span_eq]; rw [← Set.image_singleton]; rw [← Ideal.map_span]; rw [Ideal.span_singleton_generator]⟩⟩

Depends on / 依赖: Ideal.map_span, Ideal.span_singleton_generator, Ideal.submodule_span_eq, IsPrincipal, IsPrincipal.generator, Set.image_singleton, generator, image_singleton, map_span, span_singleton_generator, submodule_span_eq
-/
theorem Submodule.IsPrincipal.map_ringHom (f : F) {I : Ideal R}
    (hI : IsPrincipal I) : IsPrincipal (Ideal.map f I) :=
  ⟨⟨f (IsPrincipal.generator I), by
      rw [Ideal.submodule_span_eq]; rw [← Set.image_singleton]; rw [← Ideal.map_span]; rw [Ideal.span_singleton_generator]⟩⟩

/--
theorem `Ideal.IsPrincipal.of_comap` / 定理 `Ideal.IsPrincipal.of_comap`

English:
theorem Ideal.IsPrincipal.of_comap
  statement: (f : F) (hf : Function.Surjective f) (I : Ideal S)
  proof: by
  rw [← map_comap_of_surjective f hf I]
  exact hI.map_ringHom f

中文:
定理 Ideal.IsPrincipal.of_comap
  结论: (f : F) (hf : Function.Surjective f) (I : Ideal S)
  证明: by
  rw [← map_comap_of_surjective f hf I]
  exact hI.map_ringHom f

Depends on / 依赖: hI.map_ringHom, map_comap_of_surjective, map_ringHom
-/
theorem Ideal.IsPrincipal.of_comap (f : F) (hf : Function.Surjective f) (I : Ideal S)
    [hI : IsPrincipal (I.comap f)] : IsPrincipal I := by
  rw [← map_comap_of_surjective f hf I]
  exact hI.map_ringHom f

/--
theorem `IsPrincipalIdealRing.of_surjective` / 定理 `IsPrincipalIdealRing.of_surjective`

English:
theorem IsPrincipalIdealRing.of_surjective
  statement: [IsPrincipalIdealRing R] (f : F)
  proof: ⟨fun I => Ideal.IsPrincipal.of_comap f hf I⟩

中文:
定理 IsPrincipalIdealRing.of_surjective
  结论: [IsPrincipalIdealRing R] (f : F)
  证明: ⟨fun I => Ideal.IsPrincipal.of_comap f hf I⟩

Depends on / 依赖: Ideal.IsPrincipal.of_comap, IsPrincipal, of_comap
-/
theorem IsPrincipalIdealRing.of_surjective [IsPrincipalIdealRing R] (f : F)
    (hf : Function.Surjective f) : IsPrincipalIdealRing S :=
  ⟨fun I => Ideal.IsPrincipal.of_comap f hf I⟩

/--
theorem `isPrincipalIdealRing_prod_iff` / 定理 `isPrincipalIdealRing_prod_iff`

English:
theorem isPrincipalIdealRing_prod_iff
  proof: ⟨h.of_surjective (RingHom.fst R S) Prod.fst_surjective,
    h.of_surjective (RingHom.snd R S) Prod.snd_surjective⟩
  mpr := fun ⟨_, _⟩ => inferInstance

中文:
定理 isPrincipalIdealRing_prod_iff
  证明: ⟨h.of_surjective (RingHom.fst R S) Prod.fst_surjective,
    h.of_surjective (RingHom.snd R S) Prod.snd_surjective⟩
  mpr := fun ⟨_, _⟩ => inferInstance

Depends on / 依赖: Prod.fst_surjective, RingHom, RingHom.fst, fst_surjective, h.of_surjective, of_surjective
-/
theorem isPrincipalIdealRing_prod_iff :
    IsPrincipalIdealRing (R × S) ↔ IsPrincipalIdealRing R ∧ IsPrincipalIdealRing S where
  mp h := ⟨h.of_surjective (RingHom.fst R S) Prod.fst_surjective,
    h.of_surjective (RingHom.snd R S) Prod.snd_surjective⟩
  mpr := fun ⟨_, _⟩ => inferInstance

/--
theorem `isPrincipalIdealRing_pi_iff` / 定理 `isPrincipalIdealRing_pi_iff`

English:
theorem isPrincipalIdealRing_pi_iff
  given: {ι} [Finite ι] {R : ι -> Type*} [forall i, Semiring (R i)]
  proof: h.of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)
  mpr _ := inferInstance

中文:
定理 isPrincipalIdealRing_pi_iff
  条件: {ι} [Finite ι] {R : ι -> 类型} [对任意 i, Semiring (R i)]
  证明: h.of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)
  mpr _ := inferInstance

Depends on / 依赖: Function, Function.surjective_eval, Pi.evalRingHom, evalRingHom, h.of_surjective, of_surjective, surjective_eval
-/
theorem isPrincipalIdealRing_pi_iff {ι} [Finite ι] {R : ι -> Type*} [forall i, Semiring (R i)] :
    IsPrincipalIdealRing (Π i, R i) ↔ forall i, IsPrincipalIdealRing (R i) where
  mp h i := h.of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)
  mpr _ := inferInstance

end Surjective

section

open Ideal

variable [CommRing R]

section Bezout
variable [IsBezout R]

/--
theorem `isCoprime_of_dvd` / 定理 `isCoprime_of_dvd`

English:
theorem isCoprime_of_dvd
  statement: (x y : R) (nonzero : ¬(x = 0 ∧ y = 0))
  proof: (isRelPrime_of_no_nonunits_factors nonzero H).isCoprime

中文:
定理 isCoprime_of_dvd
  结论: (x y : R) (nonzero : ¬(x = 0 ∧ y = 0))
  证明: (isRelPrime_of_no_nonunits_factors nonzero H).isCoprime

Depends on / 依赖: isCoprime, isRelPrime_of_no_nonunits_factors, nonzero
-/
theorem isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0))
    (H : forall z in nonunits R, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y :=
  (isRelPrime_of_no_nonunits_factors nonzero H).isCoprime

/--
theorem `dvd_or_isCoprime` / 定理 `dvd_or_isCoprime`

English:
theorem dvd_or_isCoprime
  given: (x y : R) (h : Irreducible x)
  statement: x ∣ y ∨ IsCoprime x y
  proof: h.dvd_or_isRelPrime.imp_right IsRelPrime.isCoprime

中文:
定理 dvd_or_isCoprime
  条件: (x y : R) (h : Irreducible x)
  结论: x ∣ y ∨ IsCoprime x y
  证明: h.dvd_or_isRelPrime.imp_right IsRelPrime.isCoprime

Depends on / 依赖: IsRelPrime, IsRelPrime.isCoprime, dvd_or_isRelPrime, h.dvd_or_isRelPrime.imp_right, imp_right, isCoprime
-/
theorem dvd_or_isCoprime (x y : R) (h : Irreducible x) : x ∣ y ∨ IsCoprime x y :=
  h.dvd_or_isRelPrime.imp_right IsRelPrime.isCoprime

/--
theorem `Irreducible.coprime_iff_not_dvd` / 定理 `Irreducible.coprime_iff_not_dvd`

English:
theorem Irreducible.coprime_iff_not_dvd
  given: {p n : R} (hp : Irreducible p)
  proof: by rw [← isRelPrime_iff_isCoprime, hp.isRelPrime_iff_not_dvd]

中文:
定理 Irreducible.coprime_iff_not_dvd
  条件: {p n : R} (hp : Irreducible p)
  证明: by rw [← isRelPrime_iff_isCoprime, hp.isRelPrime_iff_not_dvd]

Depends on / 依赖: hp.isRelPrime_iff_not_dvd, isRelPrime_iff_isCoprime, isRelPrime_iff_not_dvd
-/
theorem Irreducible.coprime_iff_not_dvd {p n : R} (hp : Irreducible p) :
    IsCoprime p n ↔ ¬p ∣ n := by rw [← isRelPrime_iff_isCoprime, hp.isRelPrime_iff_not_dvd]

/--
theorem `Irreducible.dvd_iff_not_isCoprime` / 定理 `Irreducible.dvd_iff_not_isCoprime`

English:
theorem Irreducible.dvd_iff_not_isCoprime
  given: {p n : R} (hp : Irreducible p)
  statement: p ∣ n ↔ ¬IsCoprime p n
  proof: iff_not_comm.2 hp.coprime_iff_not_dvd

中文:
定理 Irreducible.dvd_iff_not_isCoprime
  条件: {p n : R} (hp : Irreducible p)
  结论: p ∣ n ↔ ¬IsCoprime p n
  证明: iff_not_comm.2 hp.coprime_iff_not_dvd

Depends on / 依赖: coprime_iff_not_dvd, hp.coprime_iff_not_dvd, iff_not_comm
-/
theorem Irreducible.dvd_iff_not_isCoprime {p n : R} (hp : Irreducible p) : p ∣ n ↔ ¬IsCoprime p n :=
  iff_not_comm.2 hp.coprime_iff_not_dvd

/--
theorem `Irreducible.coprime_pow_of_not_dvd` / 定理 `Irreducible.coprime_pow_of_not_dvd`

English:
theorem Irreducible.coprime_pow_of_not_dvd
  given: {p a : R} (m : Nat) (hp : Irreducible p) (h : ¬p ∣ a)
  proof: (hp.coprime_iff_not_dvd.2 h).symm.pow_right

中文:
定理 Irreducible.coprime_pow_of_not_dvd
  条件: {p a : R} (m : 自然数) (hp : Irreducible p) (h : ¬p ∣ a)
  证明: (hp.coprime_iff_not_dvd.2 h).symm.pow_right

Depends on / 依赖: coprime_iff_not_dvd, hp.coprime_iff_not_dvd, pow_right, symm.pow_right
-/
theorem Irreducible.coprime_pow_of_not_dvd {p a : R} (m : Nat) (hp : Irreducible p) (h : ¬p ∣ a) :
    IsCoprime a (p ^ m) :=
  (hp.coprime_iff_not_dvd.2 h).symm.pow_right

/--
theorem `Irreducible.isCoprime_or_dvd` / 定理 `Irreducible.isCoprime_or_dvd`

English:
theorem Irreducible.isCoprime_or_dvd
  given: {p : R} (hp : Irreducible p) (i : R)
  statement: IsCoprime p i ∨ p ∣ i
  proof: (_root_.em _).imp_right hp.dvd_iff_not_isCoprime.2

中文:
定理 Irreducible.isCoprime_or_dvd
  条件: {p : R} (hp : Irreducible p) (i : R)
  结论: IsCoprime p i ∨ p ∣ i
  证明: (_root_.em _).imp_right hp.dvd_iff_not_isCoprime.2

Depends on / 依赖: _root_, _root_.em, dvd_iff_not_isCoprime, hp.dvd_iff_not_isCoprime, imp_right
-/
theorem Irreducible.isCoprime_or_dvd {p : R} (hp : Irreducible p) (i : R) : IsCoprime p i ∨ p ∣ i :=
  (_root_.em _).imp_right hp.dvd_iff_not_isCoprime.2

variable [IsDomain R]

section GCD
variable [GCDMonoid R]

/--
theorem `IsBezout.span_gcd_eq_span_gcd` / 定理 `IsBezout.span_gcd_eq_span_gcd`

English:
theorem IsBezout.span_gcd_eq_span_gcd
  given: (x y : R)
  proof: by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    (IsBezout.dvd_gcd (GCDMonoid.gcd_dvd_left _ _) <| GCDMonoid.gcd_dvd_right _ _)
    (GCDMonoid.dvd_gcd (IsBezout.gcd_dvd_left _ _) <| IsBezout.gcd_dvd_right _ _)

中文:
定理 IsBezout.span_gcd_eq_span_gcd
  条件: (x y : R)
  证明: by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    (IsBezout.dvd_gcd (GCDMonoid.gcd_dvd_left _ _) <| GCDMonoid.gcd_dvd_right _ _)
    (GCDMonoid.dvd_gcd (IsBezout.gcd_dvd_left _ _) <| IsBezout.gcd_dvd_right _ _)

Depends on / 依赖: GCDMonoid, GCDMonoid.dvd_gcd, GCDMonoid.gcd_dvd_left, GCDMonoid.gcd_dvd_right, Ideal.span_singleton_eq_span_singleton, IsBezout, IsBezout.dvd_gcd, IsBezout.gcd_dvd_left, IsBezout.gcd_dvd_right, associated_of_dvd_dvd, dvd_gcd, gcd_dvd_left, gcd_dvd_right, span_singleton_eq_span_singleton
-/
theorem IsBezout.span_gcd_eq_span_gcd (x y : R) :
    span {GCDMonoid.gcd x y} = span {IsBezout.gcd x y} := by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    (IsBezout.dvd_gcd (GCDMonoid.gcd_dvd_left _ _) <| GCDMonoid.gcd_dvd_right _ _)
    (GCDMonoid.dvd_gcd (IsBezout.gcd_dvd_left _ _) <| IsBezout.gcd_dvd_right _ _)

/--
theorem `span_gcd` / 定理 `span_gcd`

English:
theorem span_gcd
  given: (x y : R)
  statement: span {gcd x y} = span {x, y}
  proof: by
  rw [← IsBezout.span_gcd]; rw [IsBezout.span_gcd_eq_span_gcd]

中文:
定理 span_gcd
  条件: (x y : R)
  结论: span {gcd x y} = span {x, y}
  证明: by
  rw [← IsBezout.span_gcd]; rw [IsBezout.span_gcd_eq_span_gcd]

Depends on / 依赖: IsBezout, IsBezout.span_gcd, IsBezout.span_gcd_eq_span_gcd, span_gcd, span_gcd_eq_span_gcd
-/
theorem span_gcd (x y : R) : span {gcd x y} = span {x, y} := by
  rw [← IsBezout.span_gcd]; rw [IsBezout.span_gcd_eq_span_gcd]

/--
theorem `gcd_dvd_iff_exists` / 定理 `gcd_dvd_iff_exists`

English:
theorem gcd_dvd_iff_exists
  given: (a b : R) {z}
  statement: gcd a b ∣ z ↔ exists x y, z = a * x + b * y
  proof: by
  simp_rw [mul_comm a, mul_comm b, @eq_comm _ z, ← Ideal.mem_span_pair, ← span_gcd,
    Ideal.mem_span_singleton]

中文:
定理 gcd_dvd_iff_exists
  条件: (a b : R) {z}
  结论: gcd a b ∣ z ↔ 存在 x y, z = a * x + b * y
  证明: by
  simp_rw [mul_comm a, mul_comm b, @eq_comm _ z, ← Ideal.mem_span_pair, ← span_gcd,
    Ideal.mem_span_singleton]

Depends on / 依赖: Ideal.mem_span_pair, Ideal.mem_span_singleton, eq_comm, mem_span_pair, mem_span_singleton, mul_comm, simp_rw, span_gcd
-/
theorem gcd_dvd_iff_exists (a b : R) {z} : gcd a b ∣ z ↔ exists x y, z = a * x + b * y := by
  simp_rw [mul_comm a, mul_comm b, @eq_comm _ z, ← Ideal.mem_span_pair, ← span_gcd,
    Ideal.mem_span_singleton]

/--
theorem `exists_gcd_eq_mul_add_mul` / 定理 `exists_gcd_eq_mul_add_mul`

English:
theorem exists_gcd_eq_mul_add_mul
  given: (a b : R)
  statement: exists x y, gcd a b = a * x + b * y
  proof: by
  rw [← gcd_dvd_iff_exists]

中文:
定理 exists_gcd_eq_mul_add_mul
  条件: (a b : R)
  结论: 存在 x y, gcd a b = a * x + b * y
  证明: by
  rw [← gcd_dvd_iff_exists]

Depends on / 依赖: gcd_dvd_iff_exists
-/
theorem exists_gcd_eq_mul_add_mul (a b : R) : exists x y, gcd a b = a * x + b * y := by
  rw [← gcd_dvd_iff_exists]

/--
theorem `gcd_isUnit_iff` / 定理 `gcd_isUnit_iff`

English:
theorem gcd_isUnit_iff
  given: (x y : R)
  statement: IsUnit (gcd x y) ↔ IsCoprime x y
  proof: by
  rw [IsCoprime]; rw [← Ideal.mem_span_pair]; rw [← span_gcd]; rw [← span_singleton_eq_top]; rw [eq_top_iff_one]

中文:
定理 gcd_isUnit_iff
  条件: (x y : R)
  结论: IsUnit (gcd x y) ↔ IsCoprime x y
  证明: by
  rw [IsCoprime]; rw [← Ideal.mem_span_pair]; rw [← span_gcd]; rw [← span_singleton_eq_top]; rw [eq_top_iff_one]

Depends on / 依赖: Ideal.mem_span_pair, IsCoprime, eq_top_iff_one, mem_span_pair, span_gcd, span_singleton_eq_top
-/
theorem gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime x y := by
  rw [IsCoprime]; rw [← Ideal.mem_span_pair]; rw [← span_gcd]; rw [← span_singleton_eq_top]; rw [eq_top_iff_one]

end GCD

/--
theorem `Prime.coprime_iff_not_dvd` / 定理 `Prime.coprime_iff_not_dvd`

English:
theorem Prime.coprime_iff_not_dvd
  given: {p n : R} (hp : Prime p)
  statement: IsCoprime p n ↔ ¬p ∣ n
  proof: hp.irreducible.coprime_iff_not_dvd

中文:
定理 Prime.coprime_iff_not_dvd
  条件: {p n : R} (hp : Prime p)
  结论: IsCoprime p n ↔ ¬p ∣ n
  证明: hp.irreducible.coprime_iff_not_dvd
-/
theorem Prime.coprime_iff_not_dvd {p n : R} (hp : Prime p) : IsCoprime p n ↔ ¬p ∣ n :=
  hp.irreducible.coprime_iff_not_dvd

/--
theorem `exists_associated_pow_of_mul_eq_pow'` / 定理 `exists_associated_pow_of_mul_eq_pow'`

English:
theorem exists_associated_pow_of_mul_eq_pow'
  statement: {a b c : R} (hab : IsCoprime a b) {k : Nat}
  proof: by
  classical
  let := IsBezout.toGCDDomain R
  exact exists_associated_pow_of_mul_eq_pow ((gcd_isUnit_iff _ _).mpr hab) h

中文:
定理 exists_associated_pow_of_mul_eq_pow'
  结论: {a b c : R} (hab : IsCoprime a b) {k : 自然数}
  证明: by
  classical
  let := IsBezout.toGCDDomain R
  exact exists_associated_pow_of_mul_eq_pow ((gcd_isUnit_iff _ _).mpr hab) h

Depends on / 依赖: IsBezout, IsBezout.toGCDDomain, classical, exists_associated_pow_of_mul_eq_pow, gcd_isUnit_iff, toGCDDomain
-/
theorem exists_associated_pow_of_mul_eq_pow' {a b c : R} (hab : IsCoprime a b) {k : Nat}
    (h : a * b = c ^ k) : exists d : R, Associated (d ^ k) a := by
  classical
  let := IsBezout.toGCDDomain R
  exact exists_associated_pow_of_mul_eq_pow ((gcd_isUnit_iff _ _).mpr hab) h

/--
theorem `exists_associated_pow_of_associated_pow_mul` / 定理 `exists_associated_pow_of_associated_pow_mul`

English:
theorem exists_associated_pow_of_associated_pow_mul
  statement: {a b c : R} (hab : IsCoprime a b) {k : Nat}
  proof: by
  obtain ⟨u, hu⟩ := h.symm
  exact exists_associated_pow_of_mul_eq_pow'
((isCoprime_mul_unit_right_right u.isUnit a b).mpr hab) mul_assoc a _ _ ▸ hu

中文:
定理 exists_associated_pow_of_associated_pow_mul
  结论: {a b c : R} (hab : IsCoprime a b) {k : 自然数}
  证明: by
  obtain ⟨u, hu⟩ := h.symm
  exact exists_associated_pow_of_mul_eq_pow'
((isCoprime_mul_unit_right_right u.isUnit a b).mpr hab) mul_assoc a _ _ ▸ hu

Depends on / 依赖: exists_associated_pow_of_mul_eq_pow, h.symm, isCoprime_mul_unit_right_right, isUnit, mul_assoc, u.isUnit
-/
theorem exists_associated_pow_of_associated_pow_mul {a b c : R} (hab : IsCoprime a b) {k : Nat}
    (h : Associated (c ^ k) (a * b)) : exists d : R, Associated (d ^ k) a := by
  obtain ⟨u, hu⟩ := h.symm
  exact exists_associated_pow_of_mul_eq_pow'
((isCoprime_mul_unit_right_right u.isUnit a b).mpr hab) mul_assoc a _ _ ▸ hu

end Bezout

variable [IsDomain R] [IsPrincipalIdealRing R]

/--
theorem `isCoprime_of_irreducible_dvd` / 定理 `isCoprime_of_irreducible_dvd`

English:
theorem isCoprime_of_irreducible_dvd
  statement: {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
  proof: (WfDvdMonoid.isRelPrime_of_no_irreducible_factors nonzero H).isCoprime

中文:
定理 isCoprime_of_irreducible_dvd
  结论: {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
  证明: (WfDvdMonoid.isRelPrime_of_no_irreducible_factors nonzero H).isCoprime

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.isRelPrime_of_no_irreducible_factors, isCoprime, isRelPrime_of_no_irreducible_factors, nonzero
-/
theorem isCoprime_of_irreducible_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : forall z : R, Irreducible z -> z ∣ x -> ¬z ∣ y) : IsCoprime x y :=
  (WfDvdMonoid.isRelPrime_of_no_irreducible_factors nonzero H).isCoprime

/--
theorem `isCoprime_of_prime_dvd` / 定理 `isCoprime_of_prime_dvd`

English:
theorem isCoprime_of_prime_dvd
  statement: {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
  proof: isCoprime_of_irreducible_dvd nonzero fun z zi => H z zi.prime

中文:
定理 isCoprime_of_prime_dvd
  结论: {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
  证明: isCoprime_of_irreducible_dvd nonzero fun z zi => H z zi.prime

Depends on / 依赖: isCoprime_of_irreducible_dvd, nonzero, zi.prime
-/
theorem isCoprime_of_prime_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : forall z : R, Prime z -> z ∣ x -> ¬z ∣ y) : IsCoprime x y :=
  isCoprime_of_irreducible_dvd nonzero fun z zi => H z zi.prime

end

section PrincipalOfPrime

namespace Ideal

variable (R) [Semiring R]

/--
Definition of `nonPrincipals` / `nonPrincipals` 的定义

English:
abbreviation nonPrincipals
  body: { I : Ideal R | ¬I.IsPrincipal }

中文:
缩写 nonPrincipals
  定义体: { I : Ideal R | ¬I.IsPrincipal }

Depends on / 依赖: I.IsPrincipal, IsPrincipal
-/
abbrev nonPrincipals := { I : Ideal R | ¬I.IsPrincipal }

variable {R}

/--
theorem `nonPrincipals_eq_empty_iff` / 定理 `nonPrincipals_eq_empty_iff`

English:
theorem nonPrincipals_eq_empty_iff
  statement: nonPrincipals R = ∅ ↔ IsPrincipalIdealRing R
  proof: by
  simp [Set.eq_empty_iff_forall_notMem, isPrincipalIdealRing_iff]

中文:
定理 nonPrincipals_eq_empty_iff
  结论: nonPrincipals R = ∅ ↔ IsPrincipalIdealRing R
  证明: by
  simp [Set.eq_empty_iff_forall_notMem, isPrincipalIdealRing_iff]

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem, isPrincipalIdealRing_iff
-/
theorem nonPrincipals_eq_empty_iff : nonPrincipals R = ∅ ↔ IsPrincipalIdealRing R := by
  simp [Set.eq_empty_iff_forall_notMem, isPrincipalIdealRing_iff]

/--
theorem `nonPrincipals_zorn` / 定理 `nonPrincipals_zorn`

English:
theorem nonPrincipals_zorn
  statement: (hR : ¬IsPrincipalIdealRing R) (c : Set (Ideal R))
  proof: by
  by_cases H : c.Nonempty
  · obtain ⟨K, hKmem⟩ := Set.nonempty_def.1 H
    refine ⟨sSup c, fun ⟨x, hx⟩ => ?_, fun _ => le_sSup⟩
    have hxmem : x in sSup c := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨J, hJc, hxJ⟩ := (Submodule.mem_sSup_of_directed ⟨K, hKmem⟩ hchain.directedOn).

中文:
定理 nonPrincipals_zorn
  结论: (hR : ¬IsPrincipalIdealRing R) (c : Set (Ideal R))
  证明: by
  by_cases H : c.Nonempty
  · obtain ⟨K, hKmem⟩ := Set.nonempty_def.1 H
    refine ⟨sSup c, fun ⟨x, hx⟩ => ?_, fun _ => le_sSup⟩
    have hxmem : x in sSup c := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨J, hJc, hxJ⟩ := (Submodule.mem_sSup_of_directed ⟨K, hKmem⟩ hchain.directedOn).

Depends on / 依赖: Ideal.span_le, Nonempty, Set.nonempty_def, Set.not_nonempty_iff_eq_empty, Submodule, Submodule.mem_sSup_of_directed, Submodule.mem_span_singleton_self, SwapTrue, c.Nonempty, directedOn, g.prop, g.val, hchain, hchain.directedOn, hsSupJ, hx.symm, isPrincipalIdealRing_iff, le_antisymm, le_sSup, mem_sSup_of_directed
-/
theorem nonPrincipals_zorn (hR : ¬IsPrincipalIdealRing R) (c : Set (Ideal R))
    (hs : c subseteq nonPrincipals R) (hchain : IsChain (· <= ·) c) :
    exists I in nonPrincipals R, forall J in c, J <= I := by
  by_cases H : c.Nonempty
  · obtain ⟨K, hKmem⟩ := Set.nonempty_def.1 H
    refine ⟨sSup c, fun ⟨x, hx⟩ => ?_, fun _ => le_sSup⟩
    have hxmem : x in sSup c := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨J, hJc, hxJ⟩ := (Submodule.mem_sSup_of_directed ⟨K, hKmem⟩ hchain.directedOn).1 hxmem
    have hsSupJ : sSup c = J := le_antisymm (by simp [hx, Ideal.span_le, hxJ]) (le_sSup hJc)
    exact hs hJc ⟨hsSupJ ▸ ⟨x, hx⟩⟩
  · simpa [Set.not_nonempty_iff_eq_empty.1 H, isPrincipalIdealRing_iff] using hR

/--
theorem `exists_maximal_not_isPrincipal` / 定理 `exists_maximal_not_isPrincipal`

English:
theorem exists_maximal_not_isPrincipal
  given: (hR : ¬IsPrincipalIdealRing R)
  proof: zorn_le₀ _ (nonPrincipals_zorn hR)

中文:
定理 exists_maximal_not_isPrincipal
  条件: (hR : ¬IsPrincipalIdealRing R)
  证明: zorn_le₀ _ (nonPrincipals_zorn hR)

Depends on / 依赖: nonPrincipals_zorn
-/
theorem exists_maximal_not_isPrincipal (hR : ¬IsPrincipalIdealRing R) :
    exists I : Ideal R, Maximal (¬·.IsPrincipal) I :=
  zorn_le₀ _ (nonPrincipals_zorn hR)

end Ideal

end PrincipalOfPrime

open Ideal in
/--
lemma `span_singleton_inf_span_singleton` / 引理 `span_singleton_inf_span_singleton`

English:
lemma span_singleton_inf_span_singleton
  given: [EuclideanDomain R] [GCDMonoid R] (n m : R)
  proof: by
  rw [Ideal.ext_iff]
  intro x
  rw [Ideal.mem_inf]
  simp only [Ideal.mem_span_singleton]
  exact lcm_dvd_iff.symm

中文:
引理 span_singleton_inf_span_singleton
  条件: [EuclideanDomain R] [GCDMonoid R] (n m : R)
  证明: by
  rw [Ideal.ext_iff]
  intro x
  rw [Ideal.mem_inf]
  simp only [Ideal.mem_span_singleton]
  exact lcm_dvd_iff.symm

Depends on / 依赖: Continuous, Continuous.comp, Continuous.subtype_mk, Ideal.ext_iff, Ideal.mem_inf, Ideal.mem_span_singleton, continuous_subtype_val, continuous_swapTrue, ext_iff, lcm_dvd_iff, lcm_dvd_iff.symm, mem_inf, mem_span_singleton, subtype_mk
-/
lemma span_singleton_inf_span_singleton [EuclideanDomain R] [GCDMonoid R] (n m : R) :
    span {n} ⊓ span {m} = span {lcm n m} := by
  rw [Ideal.ext_iff]
  intro x
  rw [Ideal.mem_inf]
  simp only [Ideal.mem_span_singleton]
  exact lcm_dvd_iff.symm

/--
lemma `Ideal.exists_normalized_span_of_isPrincipal` / 引理 `Ideal.exists_normalized_span_of_isPrincipal`

English:
lemma Ideal.exists_normalized_span_of_isPrincipal
  statement: {R : Type*} [CommSemiring R]
  proof: by
  obtain ⟨x, rfl⟩ := ‹I.IsPrincipal›
  refine ⟨normalize x, normalize_idem x, le_antisymm ?_ ?_⟩ <;>
  simp [Ideal.mem_span_singleton]

中文:
引理 Ideal.exists_normalized_span_of_isPrincipal
  结论: {R : 类型} [CommSemiring R]
  证明: by
  obtain ⟨x, rfl⟩ := ‹I.IsPrincipal›
  refine ⟨normalize x, normalize_idem x, le_antisymm ?_ ?_⟩ <;>
  simp [Ideal.mem_span_singleton]

Depends on / 依赖: I.IsPrincipal, Ideal.mem_span_singleton, IsPrincipal, le_antisymm, mem_span_singleton, normalize, normalize_idem
-/
lemma Ideal.exists_normalized_span_of_isPrincipal {R : Type*} [CommSemiring R]
    [NormalizationMonoid R] (I : Ideal R) [I.IsPrincipal] :
    exists x, normalize x = x ∧ I = Ideal.span {x} := by
  obtain ⟨x, rfl⟩ := ‹I.IsPrincipal›
  refine ⟨normalize x, normalize_idem x, le_antisymm ?_ ?_⟩ <;>
  simp [Ideal.mem_span_singleton]
