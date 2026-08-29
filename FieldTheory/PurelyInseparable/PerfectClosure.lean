/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!

# Basic results about relative perfect closure

This file contains basic results about relative perfect closures.

## Main definitions

- `perfectClosure`: the relative perfect closure of `F` in `E`, it consists of the elements
  `x` of `E` such that there exists a natural number `n` such that `x ^ (ringExpChar F) ^ n`
  is contained in `F`, where `ringExpChar F` is the exponential characteristic of `F`.
  It is also the maximal purely inseparable subextension of `E / F` (`le_perfectClosure_iff`).

## Main results

- `le_perfectClosure_iff`: an intermediate field of `E / F` is contained in the relative perfect
  closure of `F` in `E` if and only if it is purely inseparable over `F`.

- `perfectClosure.perfectRing`, `perfectClosure.perfectField`: if `E` is a perfect field, then the
  (relative) perfect closure `perfectClosure F E` is perfect.

- `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`: if `F` is of exponential
  characteristic `q`, then `F(S) / F` is a purely inseparable extension if and only if for any
  `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

@[expose] public section

open IntermediateField Module

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section perfectClosure

/-- The relative perfect closure of `F` in `E`, consists of the elements `x` of `E` such that there
exists a natural number `n` such that `x ^ (ringExpChar F) ^ n` is contained in `F`, where
`ringExpChar F` is the exponential characteristic of `F`. It is also the maximal purely inseparable
subextension of `E / F` (`le_perfectClosure_iff`). -/
@[stacks 09HH]
/--
Definition of `perfectClosure` / `perfectClosure` 的定义

English:
definition perfectClosure
  signature: : IntermediateField F E where
  body: have := expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
    Subalgebra.perfectClosure F E (ringExpChar F)
  inv_mem' := by
    rintro x ⟨n, hx⟩
    use n; rw [inv_pow]
    apply inv_mem (id hx : _ in (⊥ : IntermediateField F E))

中文:
定义 perfectClosure
  签名: : 中间域 F E where
  定义体: have := expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
    Subalgebra.perfectClosure F E (ringExpChar F)
  inv_mem' := by
    rintro x ⟨n, hx⟩
    use n; rw [inv_pow]
    apply inv_mem (id hx : _ in (⊥ : IntermediateField F E))

Depends on / 依赖: algebraMap, expChar_of_injective_algebraMap, injective, ringExpChar
-/
def perfectClosure : IntermediateField F E where
  __ := have := expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
    Subalgebra.perfectClosure F E (ringExpChar F)
  inv_mem' := by
    rintro x ⟨n, hx⟩
    use n; rw [inv_pow]
    apply inv_mem (id hx : _ in (⊥ : IntermediateField F E))

variable {F E}

/--
theorem `mem_perfectClosure_iff` / 定理 `mem_perfectClosure_iff`

English:
theorem mem_perfectClosure_iff
  given: {x : E}
  proof: Iff.rfl

中文:
定理 mem_perfectClosure_iff
  条件: {x : E}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_perfectClosure_iff {x : E} :
    x in perfectClosure F E ↔ exists n : Nat, x ^ (ringExpChar F) ^ n in (algebraMap F E).range := Iff.rfl

/--
theorem `mem_perfectClosure_iff_pow_mem` / 定理 `mem_perfectClosure_iff_pow_mem`

English:
theorem mem_perfectClosure_iff_pow_mem
  given: (q : Nat) [ExpChar F q] {x : E}
  proof: by
  rw [mem_perfectClosure_iff]; rw [ringExpChar.eq F q]

中文:
定理 mem_perfectClosure_iff_pow_mem
  条件: (q : 自然数) [ExpChar F q] {x : E}
  证明: by
  rw [mem_perfectClosure_iff]; rw [ringExpChar.eq F q]

Depends on / 依赖: mem_perfectClosure_iff, ringExpChar, ringExpChar.eq
-/
theorem mem_perfectClosure_iff_pow_mem (q : Nat) [ExpChar F q] {x : E} :
    x in perfectClosure F E ↔ exists n : Nat, x ^ q ^ n in (algebraMap F E).range := by
  rw [mem_perfectClosure_iff]; rw [ringExpChar.eq F q]

/--
theorem `mem_perfectClosure_iff_natSepDegree_eq_one` / 定理 `mem_perfectClosure_iff_natSepDegree_eq_one`

English:
theorem mem_perfectClosure_iff_natSepDegree_eq_one
  given: {x : E}
  proof: by
  rw [mem_perfectClosure_iff]; rw [minpoly.natSepDegree_eq_one_iff_pow_mem (ringExpChar F)]

中文:
定理 mem_perfectClosure_iff_natSepDegree_eq_one
  条件: {x : E}
  证明: by
  rw [mem_perfectClosure_iff]; rw [minpoly.natSepDegree_eq_one_iff_pow_mem (ringExpChar F)]

Depends on / 依赖: mem_perfectClosure_iff, minpoly, minpoly.natSepDegree_eq_one_iff_pow_mem, natSepDegree_eq_one_iff_pow_mem, ringExpChar
-/
theorem mem_perfectClosure_iff_natSepDegree_eq_one {x : E} :
    x in perfectClosure F E ↔ (minpoly F x).natSepDegree = 1 := by
  rw [mem_perfectClosure_iff]; rw [minpoly.natSepDegree_eq_one_iff_pow_mem (ringExpChar F)]

/--
theorem `isPurelyInseparable_iff_perfectClosure_eq_top` / 定理 `isPurelyInseparable_iff_perfectClosure_eq_top`

English:
theorem isPurelyInseparable_iff_perfectClosure_eq_top
  proof: by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact ⟨fun H => top_unique fun x _ => H x, fun H _ => H.ge trivial⟩

中文:
定理 isPurelyInseparable_iff_perfectClosure_eq_top
  证明: by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact ⟨fun H => top_unique fun x _ => H x, fun H _ => H.ge trivial⟩

Depends on / 依赖: H.ge, isPurelyInseparable_iff_pow_mem, ringExpChar, top_unique
-/
theorem isPurelyInseparable_iff_perfectClosure_eq_top :
    IsPurelyInseparable F E ↔ perfectClosure F E = ⊤ := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact ⟨fun H => top_unique fun x _ => H x, fun H _ => H.ge trivial⟩

variable (F E)

/--
Instance `perfectClosure.isPurelyInseparable` / 实例 `perfectClosure.isPurelyInseparable`

English:
instance perfectClosure.isPurelyInseparable
  signature: : IsPurelyInseparable F (perfectClosure F E)
  body: by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact fun ⟨_, n, y, h⟩ => ⟨n, y, (algebraMap _ E).injective h⟩

中文:
实例 perfectClosure.isPurelyInseparable
  签名: : 是纯不可分 F (perfectClosure F E)
  定义体: by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact fun ⟨_, n, y, h⟩ => ⟨n, y, (algebraMap _ E).injective h⟩

Depends on / 依赖: algebraMap, injective, isPurelyInseparable_iff_pow_mem, ringExpChar
-/
instance perfectClosure.isPurelyInseparable : IsPurelyInseparable F (perfectClosure F E) := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact fun ⟨_, n, y, h⟩ => ⟨n, y, (algebraMap _ E).injective h⟩

/--
Instance `perfectClosure.isAlgebraic` / 实例 `perfectClosure.isAlgebraic`

English:
instance perfectClosure.isAlgebraic
  signature: : Algebra.IsAlgebraic F (perfectClosure F E)
  body: IsPurelyInseparable.isAlgebraic F _

中文:
实例 perfectClosure.isAlgebraic
  签名: : 代数.是代数 F (perfectClosure F E)
  定义体: IsPurelyInseparable.isAlgebraic F _

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.isAlgebraic, isAlgebraic
-/
instance perfectClosure.isAlgebraic : Algebra.IsAlgebraic F (perfectClosure F E) :=
  IsPurelyInseparable.isAlgebraic F _

/--
theorem `perfectClosure.eq_bot_of_isSeparable` / 定理 `perfectClosure.eq_bot_of_isSeparable`

English:
theorem perfectClosure.eq_bot_of_isSeparable
  given: [Algebra.IsSeparable F E]
  statement: perfectClosure F E = ⊥
  proof: haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (perfectClosure F E) E
  eq_bot_of_isPurelyInseparable_of_isSeparable _

中文:
定理 perfectClosure.eq_bot_of_isSeparable
  条件: [代数.是可分 F E]
  结论: perfectClosure F E = ⊥
  证明: haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (perfectClosure F E) E
  eq_bot_of_isPurelyInseparable_of_isSeparable _

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_bot_of_isSeparable, eq_bot_of_isPurelyInseparable_of_isSeparable, isSeparable_tower_bot_of_isSeparable, perfectClosure
-/
theorem perfectClosure.eq_bot_of_isSeparable [Algebra.IsSeparable F E] : perfectClosure F E = ⊥ :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (perfectClosure F E) E
  eq_bot_of_isPurelyInseparable_of_isSeparable _

/--
theorem `le_perfectClosure` / 定理 `le_perfectClosure`

English:
theorem le_perfectClosure
  given: (L : IntermediateField F E) [h : IsPurelyInseparable F L]
  proof: by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)] at h
  intro x hx
  obtain ⟨n, y, hy⟩ := h ⟨x, hx⟩
  exact ⟨n, y, congr_arg (algebraMap L E) hy⟩

中文:
定理 le_perfectClosure
  条件: (L : 中间域 F E) [h : 是纯不可分 F L]
  证明: by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)] at h
  intro x hx
  obtain ⟨n, y, hy⟩ := h ⟨x, hx⟩
  exact ⟨n, y, congr_arg (algebraMap L E) hy⟩

Depends on / 依赖: algebraMap, congr_arg, isPurelyInseparable_iff_pow_mem, ringExpChar
-/
theorem le_perfectClosure (L : IntermediateField F E) [h : IsPurelyInseparable F L] :
    L <= perfectClosure F E := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)] at h
  intro x hx
  obtain ⟨n, y, hy⟩ := h ⟨x, hx⟩
  exact ⟨n, y, congr_arg (algebraMap L E) hy⟩

/--
theorem `le_perfectClosure_iff` / 定理 `le_perfectClosure_iff`

English:
theorem le_perfectClosure_iff
  given: (L : IntermediateField F E)
  proof: by
  refine ⟨fun h => (isPurelyInseparable_iff_pow_mem F (ringExpChar F)).2 fun x => ?_,
    fun _ => le_perfectClosure F E L⟩
  obtain ⟨n, y, hy⟩ := h x.2
  exact ⟨n, y, (algebraMap L E).injective hy⟩

中文:
定理 le_perfectClosure_iff
  条件: (L : 中间域 F E)
  证明: by
  refine ⟨fun h => (isPurelyInseparable_iff_pow_mem F (ringExpChar F)).2 fun x => ?_,
    fun _ => le_perfectClosure F E L⟩
  obtain ⟨n, y, hy⟩ := h x.2
  exact ⟨n, y, (algebraMap L E).injective hy⟩

Depends on / 依赖: algebraMap, injective, isPurelyInseparable_iff_pow_mem, le_perfectClosure, ringExpChar
-/
theorem le_perfectClosure_iff (L : IntermediateField F E) :
    L <= perfectClosure F E ↔ IsPurelyInseparable F L := by
  refine ⟨fun h => (isPurelyInseparable_iff_pow_mem F (ringExpChar F)).2 fun x => ?_,
    fun _ => le_perfectClosure F E L⟩
  obtain ⟨n, y, hy⟩ := h x.2
  exact ⟨n, y, (algebraMap L E).injective hy⟩

/--
theorem `separableClosure_inf_perfectClosure` / 定理 `separableClosure_inf_perfectClosure`

English:
theorem separableClosure_inf_perfectClosure
  statement: separableClosure F E ⊓ perfectClosure F E = ⊥
  proof: haveI := (le_separableClosure_iff F E _).mp (inf_le_left (b := perfectClosure F E))
  haveI := (le_perfectClosure_iff F E _).mp (inf_le_right (a := separableClosure F E))
  eq_bot_of_isPurelyInseparable_of_isSeparable _

中文:
定理 separableClosure_inf_perfectClosure
  结论: separableClosure F E ⊓ perfectClosure F E = ⊥
  证明: haveI := (le_separableClosure_iff F E _).mp (inf_le_left (b := perfectClosure F E))
  haveI := (le_perfectClosure_iff F E _).mp (inf_le_right (a := separableClosure F E))
  eq_bot_of_isPurelyInseparable_of_isSeparable _

Depends on / 依赖: eq_bot_of_isPurelyInseparable_of_isSeparable, inf_le_left, inf_le_right, le_perfectClosure_iff, le_separableClosure_iff, perfectClosure, separableClosure
-/
theorem separableClosure_inf_perfectClosure : separableClosure F E ⊓ perfectClosure F E = ⊥ :=
  haveI := (le_separableClosure_iff F E _).mp (inf_le_left (b := perfectClosure F E))
  haveI := (le_perfectClosure_iff F E _).mp (inf_le_right (a := separableClosure F E))
  eq_bot_of_isPurelyInseparable_of_isSeparable _

section map

variable {F E K}

/--
theorem `map_mem_perfectClosure_iff` / 定理 `map_mem_perfectClosure_iff`

English:
theorem map_mem_perfectClosure_iff
  given: (i : E ->ₐ[F] K) {x : E}
  proof: by
  simp_rw [mem_perfectClosure_iff]
  refine ⟨fun ⟨n, y, h⟩ => ⟨n, y, ?_⟩, fun ⟨n, y, h⟩ => ⟨n, y, ?_⟩⟩
  · apply_fun i using i.injective
    rwa [AlgHom.commutes, map_pow]
  simpa only [AlgHom.commutes, map_pow] using congr_arg i h

中文:
定理 map_mem_perfectClosure_iff
  条件: (i : E ->ₐ[F] K) {x : E}
  证明: by
  simp_rw [mem_perfectClosure_iff]
  refine ⟨fun ⟨n, y, h⟩ => ⟨n, y, ?_⟩, fun ⟨n, y, h⟩ => ⟨n, y, ?_⟩⟩
  · apply_fun i using i.injective
    rwa [AlgHom.commutes, map_pow]
  simpa only [AlgHom.commutes, map_pow] using congr_arg i h

Depends on / 依赖: AlgHom, AlgHom.commutes, apply_fun, commutes, congr_arg, i.injective, injective, map_pow, mem_perfectClosure_iff, simp_rw
-/
theorem map_mem_perfectClosure_iff (i : E ->ₐ[F] K) {x : E} :
    i x in perfectClosure F K ↔ x in perfectClosure F E := by
  simp_rw [mem_perfectClosure_iff]
  refine ⟨fun ⟨n, y, h⟩ => ⟨n, y, ?_⟩, fun ⟨n, y, h⟩ => ⟨n, y, ?_⟩⟩
  · apply_fun i using i.injective
    rwa [AlgHom.commutes, map_pow]
  simpa only [AlgHom.commutes, map_pow] using congr_arg i h

/--
theorem `perfectClosure.comap_eq_of_algHom` / 定理 `perfectClosure.comap_eq_of_algHom`

English:
theorem perfectClosure.comap_eq_of_algHom
  given: (i : E ->ₐ[F] K)
  proof: by
  ext x
  exact map_mem_perfectClosure_iff i

中文:
定理 perfectClosure.comap_eq_of_algHom
  条件: (i : E ->ₐ[F] K)
  证明: by
  ext x
  exact map_mem_perfectClosure_iff i

Depends on / 依赖: map_mem_perfectClosure_iff
-/
theorem perfectClosure.comap_eq_of_algHom (i : E ->ₐ[F] K) :
    (perfectClosure F K).comap i = perfectClosure F E := by
  ext x
  exact map_mem_perfectClosure_iff i

/--
theorem `perfectClosure.map_le_of_algHom` / 定理 `perfectClosure.map_le_of_algHom`

English:
theorem perfectClosure.map_le_of_algHom
  given: (i : E ->ₐ[F] K)
  proof: map_le_iff_le_comap.mpr (perfectClosure.comap_eq_of_algHom i).ge

中文:
定理 perfectClosure.map_le_of_algHom
  条件: (i : E ->ₐ[F] K)
  证明: map_le_iff_le_comap.mpr (perfectClosure.comap_eq_of_algHom i).ge

Depends on / 依赖: comap_eq_of_algHom, map_le_iff_le_comap, map_le_iff_le_comap.mpr, perfectClosure, perfectClosure.comap_eq_of_algHom
-/
theorem perfectClosure.map_le_of_algHom (i : E ->ₐ[F] K) :
    (perfectClosure F E).map i <= perfectClosure F K :=
  map_le_iff_le_comap.mpr (perfectClosure.comap_eq_of_algHom i).ge

/--
theorem `perfectClosure.map_eq_of_algEquiv` / 定理 `perfectClosure.map_eq_of_algEquiv`

English:
theorem perfectClosure.map_eq_of_algEquiv
  given: (i : E ≃ₐ[F] K)
  proof: (map_le_of_algHom i.toAlgHom).antisymm (fun x hx => ⟨i.symm x,
    (map_mem_perfectClosure_iff i.symm.toAlgHom).2 hx, i.right_inv x⟩)

中文:
定理 perfectClosure.map_eq_of_algEquiv
  条件: (i : E ≃ₐ[F] K)
  证明: (map_le_of_algHom i.toAlgHom).antisymm (fun x hx => ⟨i.symm x,
    (map_mem_perfectClosure_iff i.symm.toAlgHom).2 hx, i.right_inv x⟩)

Depends on / 依赖: antisymm, i.right_inv, i.symm, i.symm.toAlgHom, i.toAlgHom, map_le_of_algHom, map_mem_perfectClosure_iff, right_inv, toAlgHom
-/
theorem perfectClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (perfectClosure F E).map i.toAlgHom = perfectClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm (fun x hx => ⟨i.symm x,
    (map_mem_perfectClosure_iff i.symm.toAlgHom).2 hx, i.right_inv x⟩)

/--
Definition of `perfectClosure.algEquivOfAlgEquiv` / `perfectClosure.algEquivOfAlgEquiv` 的定义

English:
definition perfectClosure.algEquivOfAlgEquiv
  signature: (i : E ≃ₐ[F] K)
  body: (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

noncomputable
alias AlgEquiv.perfectClosure := perfectClosure.algEquivOfAlgEquiv

中文:
定义 perfectClosure.algEquivOfAlgEquiv
  签名: (i : E ≃ₐ[F] K)
  定义体: (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

noncomputable
alias AlgEquiv.perfectClosure := perfectClosure.algEquivOfAlgEquiv

Depends on / 依赖: equivOfEq, intermediateFieldMap, map_eq_of_algEquiv
-/
def perfectClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    perfectClosure F E ≃ₐ[F] perfectClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

noncomputable
alias AlgEquiv.perfectClosure := perfectClosure.algEquivOfAlgEquiv

end map

/--
Instance `perfectClosure.perfectRing` / 实例 `perfectClosure.perfectRing`

English:
instance perfectClosure.perfectRing
  signature: (p : Nat) [ExpChar E p]
  body: .ofSurjective _ p fun x => by
  have := RingHom.expChar _ (algebraMap F E).injective p
  obtain ⟨x', hx⟩ := surjective_frobenius E p x.1
  obtain ⟨n, y, hy⟩ := (mem_perfectClosure_iff_pow_mem p).1 x.2
  rw [frobenius_def] at hx
  rw [← hx]; rw [← pow_mul]; rw [← pow_succ'] at hy
  exact ⟨⟨x', (mem_perfectClosure_iff_pow_mem p).2 ⟨n + 1, y, hy⟩⟩, by
    simp_rw [frobenius_def, SubmonoidClass.mk_pow, hx]⟩

中文:
实例 perfectClosure.perfectRing
  签名: (p : 自然数) [ExpChar E p]
  定义体: .ofSurjective _ p fun x => by
  have := RingHom.expChar _ (algebraMap F E).injective p
  obtain ⟨x', hx⟩ := surjective_frobenius E p x.1
  obtain ⟨n, y, hy⟩ := (mem_perfectClosure_iff_pow_mem p).1 x.2
  rw [frobenius_def] at hx
  rw [← hx]; rw [← pow_mul]; rw [← pow_succ'] at hy
  exact ⟨⟨x', (mem_perfectClosure_iff_pow_mem p).2 ⟨n + 1, y, hy⟩⟩, by
    simp_rw [frobenius_def, SubmonoidClass.mk_pow, hx]⟩

Depends on / 依赖: RingHom, RingHom.expChar, SubmonoidClass, SubmonoidClass.mk_pow, algebraMap, expChar, frobenius_def, injective, mem_perfectClosure_iff_pow_mem, mk_pow, ofSurjective, pow_mul, pow_succ, simp_rw, strongRankCondition_of_orzechProperty, surjective_frobenius
-/
instance perfectClosure.perfectRing (p : Nat) [ExpChar E p]
    [PerfectRing E p] : PerfectRing (perfectClosure F E) p := .ofSurjective _ p fun x => by
  have := RingHom.expChar _ (algebraMap F E).injective p
  obtain ⟨x', hx⟩ := surjective_frobenius E p x.1
  obtain ⟨n, y, hy⟩ := (mem_perfectClosure_iff_pow_mem p).1 x.2
  rw [frobenius_def] at hx
  rw [← hx]; rw [← pow_mul]; rw [← pow_succ'] at hy
  exact ⟨⟨x', (mem_perfectClosure_iff_pow_mem p).2 ⟨n + 1, y, hy⟩⟩, by
    simp_rw [frobenius_def, SubmonoidClass.mk_pow, hx]⟩

/--
Instance `perfectClosure.perfectField` / 实例 `perfectClosure.perfectField`

English:
instance perfectClosure.perfectField
  signature: [PerfectField E]
  body: PerfectRing.toPerfectField _ (ringExpChar E)

中文:
实例 perfectClosure.perfectField
  签名: [完美域 E]
  定义体: PerfectRing.toPerfectField _ (ringExpChar E)

Depends on / 依赖: PerfectRing, PerfectRing.toPerfectField, ringExpChar, toPerfectField
-/
instance perfectClosure.perfectField [PerfectField E] : PerfectField (perfectClosure F E) :=
  PerfectRing.toPerfectField _ (ringExpChar E)

end perfectClosure

namespace IntermediateField

/--
theorem `isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one` / 定理 `isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one`

English:
theorem isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one
  given: {x : E}
  proof: by
  rw [← le_perfectClosure_iff]; rw [adjoin_simple_le_iff]; rw [mem_perfectClosure_iff_natSepDegree_eq_one]

中文:
定理 isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one
  条件: {x : E}
  证明: by
  rw [← le_perfectClosure_iff]; rw [adjoin_simple_le_iff]; rw [mem_perfectClosure_iff_natSepDegree_eq_one]

Depends on / 依赖: adjoin_simple_le_iff, le_perfectClosure_iff, mem_perfectClosure_iff_natSepDegree_eq_one
-/
theorem isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ (minpoly F x).natSepDegree = 1 := by
  rw [← le_perfectClosure_iff]; rw [adjoin_simple_le_iff]; rw [mem_perfectClosure_iff_natSepDegree_eq_one]

/--
theorem `isPurelyInseparable_adjoin_simple_iff_pow_mem` / 定理 `isPurelyInseparable_adjoin_simple_iff_pow_mem`

English:
theorem isPurelyInseparable_adjoin_simple_iff_pow_mem
  given: (q : Nat) [hF : ExpChar F q] {x : E}
  proof: by
  rw [← le_perfectClosure_iff]; rw [adjoin_simple_le_iff]; rw [mem_perfectClosure_iff_pow_mem q]

中文:
定理 isPurelyInseparable_adjoin_simple_iff_pow_mem
  条件: (q : 自然数) [hF : ExpChar F q] {x : E}
  证明: by
  rw [← le_perfectClosure_iff]; rw [adjoin_simple_le_iff]; rw [mem_perfectClosure_iff_pow_mem q]

Depends on / 依赖: adjoin_simple_le_iff, le_perfectClosure_iff, mem_perfectClosure_iff_pow_mem
-/
theorem isPurelyInseparable_adjoin_simple_iff_pow_mem (q : Nat) [hF : ExpChar F q] {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ exists n : Nat, x ^ q ^ n in (algebraMap F E).range := by
  rw [← le_perfectClosure_iff]; rw [adjoin_simple_le_iff]; rw [mem_perfectClosure_iff_pow_mem q]

/--
theorem `isPurelyInseparable_adjoin_iff_pow_mem` / 定理 `isPurelyInseparable_adjoin_iff_pow_mem`

English:
theorem isPurelyInseparable_adjoin_iff_pow_mem
  given: (q : Nat) [hF : ExpChar F q] {S : Set E}
  proof: by
  simp_rw [← le_perfectClosure_iff, adjoin_le_iff, ← mem_perfectClosure_iff_pow_mem q,
    Set.subset_def, SetLike.mem_coe]

中文:
定理 isPurelyInseparable_adjoin_iff_pow_mem
  条件: (q : 自然数) [hF : ExpChar F q] {S : 集合 E}
  证明: by
  simp_rw [← le_perfectClosure_iff, adjoin_le_iff, ← mem_perfectClosure_iff_pow_mem q,
    Set.subset_def, SetLike.mem_coe]

Depends on / 依赖: Set.subset_def, SetLike, SetLike.mem_coe, adjoin_le_iff, le_perfectClosure_iff, mem_coe, mem_perfectClosure_iff_pow_mem, simp_rw, subset_def
-/
theorem isPurelyInseparable_adjoin_iff_pow_mem (q : Nat) [hF : ExpChar F q] {S : Set E} :
    IsPurelyInseparable F (adjoin F S) ↔ forall x in S, exists n : Nat, x ^ q ^ n in (algebraMap F E).range := by
  simp_rw [← le_perfectClosure_iff, adjoin_le_iff, ← mem_perfectClosure_iff_pow_mem q,
    Set.subset_def, SetLike.mem_coe]

/--
Instance `isPurelyInseparable_sup` / 实例 `isPurelyInseparable_sup`

English:
instance isPurelyInseparable_sup
  signature: (L1 L2 : IntermediateField F E)
  body: by
  rw [← le_perfectClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

中文:
实例 isPurelyInseparable_sup
  签名: (L1 L2 : 中间域 F E)
  定义体: by
  rw [← le_perfectClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

Depends on / 依赖: le_perfectClosure_iff, sup_le
-/
instance isPurelyInseparable_sup (L1 L2 : IntermediateField F E)
    [h1 : IsPurelyInseparable F L1] [h2 : IsPurelyInseparable F L2] :
    IsPurelyInseparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_perfectClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/--
Instance `isPurelyInseparable_iSup` / 实例 `isPurelyInseparable_iSup`

English:
instance isPurelyInseparable_iSup
  signature: {ι : Sort*} {t : ι -> IntermediateField F E}
  body: by
  simp_rw [← le_perfectClosure_iff] at h ⊢
  exact iSup_le h

中文:
实例 isPurelyInseparable_iSup
  签名: {ι : 类型层*} {t : ι -> 中间域 F E}
  定义体: by
  simp_rw [← le_perfectClosure_iff] at h ⊢
  exact iSup_le h

Depends on / 依赖: iSup_le, le_perfectClosure_iff, simp_rw
-/
instance isPurelyInseparable_iSup {ι : Sort*} {t : ι -> IntermediateField F E}
    [h : forall i, IsPurelyInseparable F (t i)] :
    IsPurelyInseparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_perfectClosure_iff] at h ⊢
  exact iSup_le h

/--
theorem `adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable` / 定理 `adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable`

English:
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable
  statement: (S : Set E)
  proof: by
  set M := adjoin F ((· ^ q ^ n) '' S)
  have := expChar_of_injective_algebraMap (algebraMap F M).injective q
  refine le_antisymm (adjoin_le_iff.2 fun x hx => ?_) (adjoin_le_iff.2 ?_)
  · have : Algebra.IsSeparable M M⟮x⟯ :=
(isSeparable_adjoin_simple_iff_isSeparable M E).2
        ((isSeparable_adjoin_iff_isSeparable F E).1 inferInstance x hx).tower_top M
    have : IsPurelyInseparable M M⟮x⟯ :=
      (isPurelyInseparable_adjoin_simple_iff_pow_mem M E q).2
        ⟨n, ⟨x ^ q ^ n, subset_adjoin F _ ⟨x, hx, rfl⟩⟩, rfl⟩
    have hx' := mem_adjoin_simple_self M x
    rw [M⟮x⟯.eq_bot_of_isPurelyInseparable_of_isSeparable]; rw [mem_bot] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _

中文:
定理 adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable
  结论: (S : 集合 E)
  证明: by
  set M := adjoin F ((· ^ q ^ n) '' S)
  have := expChar_of_injective_algebraMap (algebraMap F M).injective q
  refine le_antisymm (adjoin_le_iff.2 fun x hx => ?_) (adjoin_le_iff.2 ?_)
  · have : Algebra.IsSeparable M M⟮x⟯ :=
(isSeparable_adjoin_simple_iff_isSeparable M E).2
        ((isSeparable_adjoin_iff_isSeparable F E).1 inferInstance x hx).tower_top M
    have : IsPurelyInseparable M M⟮x⟯ :=
      (isPurelyInseparable_adjoin_simple_iff_pow_mem M E q).2
        ⟨n, ⟨x ^ q ^ n, subset_adjoin F _ ⟨x, hx, rfl⟩⟩, rfl⟩
    have hx' := mem_adjoin_simple_self M x
    rw [M⟮x⟯.eq_bot_of_isPurelyInseparable_of_isSeparable]; rw [mem_bot] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _

Depends on / 依赖: Algebra, Algebra.IsSeparable, IsPurelyInseparable, IsSeparable, StrongRankCondition, adjoin, adjoin_le_iff, algebraMap, expChar_of_injective_algebraMap, injective, isPurelyInseparable_adjoin_simple_iff_pow_mem, isSeparable_adjoin_iff_isSeparable, isSeparable_adjoin_simple_iff_isSeparable, le_antisymm, rankCondition_of_strongRankCondition, subset_adjoin, tower_top
-/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E)
    [Algebra.IsSeparable F (adjoin F S)] (q : Nat) [ExpChar F q] (n : Nat) :
    adjoin F S = adjoin F ((· ^ q ^ n) '' S) := by
  set M := adjoin F ((· ^ q ^ n) '' S)
  have := expChar_of_injective_algebraMap (algebraMap F M).injective q
  refine le_antisymm (adjoin_le_iff.2 fun x hx => ?_) (adjoin_le_iff.2 ?_)
  · have : Algebra.IsSeparable M M⟮x⟯ :=
(isSeparable_adjoin_simple_iff_isSeparable M E).2
        ((isSeparable_adjoin_iff_isSeparable F E).1 inferInstance x hx).tower_top M
    have : IsPurelyInseparable M M⟮x⟯ :=
      (isPurelyInseparable_adjoin_simple_iff_pow_mem M E q).2
        ⟨n, ⟨x ^ q ^ n, subset_adjoin F _ ⟨x, hx, rfl⟩⟩, rfl⟩
    have hx' := mem_adjoin_simple_self M x
    rw [M⟮x⟯.eq_bot_of_isPurelyInseparable_of_isSeparable]; rw [mem_bot] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _

/--
theorem `adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable'` / 定理 `adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable'`

English:
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable'
  statement: [Algebra.IsSeparable F E] (S : Set E)
  proof: haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n

中文:
定理 adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable'
  结论: [代数.是可分 F E] (S : 集合 E)
  证明: haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_bot_of_isSeparable, RankCondition, adjoin, adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable, invariantBasisNumber_of_rankCondition, isSeparable_tower_bot_of_isSeparable
-/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : Nat) [ExpChar F q] (n : Nat) : adjoin F S = adjoin F ((· ^ q ^ n) '' S) :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n

-- TODO: prove the converse when `F(S) / F` is finite
/--
theorem `adjoin_eq_adjoin_pow_expChar_of_isSeparable` / 定理 `adjoin_eq_adjoin_pow_expChar_of_isSeparable`

English:
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable
  statement: (S : Set E) [Algebra.IsSeparable F (adjoin F S)]
  proof: pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1

中文:
定理 adjoin_eq_adjoin_pow_expChar_of_isSeparable
  结论: (S : 集合 E) [代数.是可分 F (adjoin F S)]
  证明: pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1

Depends on / 依赖: adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable, pow_one
-/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable (S : Set E) [Algebra.IsSeparable F (adjoin F S)]
    (q : Nat) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1

/--
theorem `adjoin_eq_adjoin_pow_expChar_of_isSeparable'` / 定理 `adjoin_eq_adjoin_pow_expChar_of_isSeparable'`

English:
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable'
  statement: [Algebra.IsSeparable F E] (S : Set E)
  proof: pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1

中文:
定理 adjoin_eq_adjoin_pow_expChar_of_isSeparable'
  结论: [代数.是可分 F E] (S : 集合 E)
  证明: pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1

Depends on / 依赖: adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable, pow_one
-/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : Nat) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1

-- Special cases for simple adjoin

/--
theorem `adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable` / 定理 `adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable`

English:
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable
  statement: {a : E} (ha : IsSeparable F a)
  proof: by
  have := (isSeparable_adjoin_simple_iff_isSeparable F E).mpr ha
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

中文:
定理 adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable
  结论: {a : E} (ha : 是可分 F a)
  证明: by
  have := (isSeparable_adjoin_simple_iff_isSeparable F E).mpr ha
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

Depends on / 依赖: adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable, isSeparable_adjoin_simple_iff_isSeparable
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable {a : E} (ha : IsSeparable F a)
    (q : Nat) [ExpChar F q] (n : Nat) : F⟮a⟯ = F⟮a ^ q ^ n⟯ := by
  have := (isSeparable_adjoin_simple_iff_isSeparable F E).mpr ha
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

/--
theorem `adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable'` / 定理 `adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable'`

English:
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable'
  statement: [Algebra.IsSeparable F E] (a : E)
  proof: by
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

中文:
定理 adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable'
  结论: [代数.是可分 F E] (a : E)
  证明: by
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

Depends on / 依赖: adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (a : E)
    (q : Nat) [ExpChar F q] (n : Nat) : F⟮a⟯ = F⟮a ^ q ^ n⟯ := by
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

/--
theorem `adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable` / 定理 `adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable`

English:
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable
  statement: {a : E} (ha : IsSeparable F a)
  proof: pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E ha q 1

中文:
定理 adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable
  结论: {a : E} (ha : 是可分 F a)
  证明: pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E ha q 1

Depends on / 依赖: IsNoetherianRing, IsNoetherianRing.strongRankCondition, StrongRankCondition, adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable, pow_one, strongRankCondition
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable {a : E} (ha : IsSeparable F a)
    (q : Nat) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯ :=
  pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E ha q 1

/--
theorem `adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable'` / 定理 `adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable'`

English:
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable'
  statement: [Algebra.IsSeparable F E] (a : E)
  proof: pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E a q 1

中文:
定理 adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable'
  结论: [代数.是可分 F E] (a : E)
  证明: pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E a q 1

Depends on / 依赖: CommRing, adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable, invariantBasisNumber_of_nontrivial_of_commRing, pow_one
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (a : E)
    (q : Nat) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯ :=
  pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E a q 1

end IntermediateField

section

variable (q n : Nat) [hF : ExpChar F q] {ι : Type*} {v : ι -> E} {F E}

/--
theorem `Field.span_map_pow_expChar_pow_eq_top_of_isSeparable` / 定理 `Field.span_map_pow_expChar_pow_eq_top_of_isSeparable`

English:
theorem Field.span_map_pow_expChar_pow_eq_top_of_isSeparable
  statement: [Algebra.IsSeparable F E]
  proof: by
  rw [← Algebra.top_toSubmodule]; rw [← top_toSubalgebra]; rw [← adjoin_univ]; rw [adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E _ q n]; rw [adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x]; rw [Set.image_univ]; rw [Algebra.adjoin_eq_span]
  have := (MonoidHom.mrange (powMonoidHom (α := E) (q ^ n))).closure_eq
  simp only [MonoidHom.mrange, powMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Submonoid.coe_copy] at this
  rw [this]
  refine (Submodule.span_mono <| Set.range_comp_subset_range _ _).antisymm (Submodule.span_le.2 ?_)
  rw [Set.range_comp]; rw [← Set.image_univ]
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  apply h ▸ Submodule.image_span_subset_span (LinearMap.iterateFrobenius F E q n) _

中文:
定理 域.span_map_pow_expChar_pow_eq_top_of_isSeparable
  结论: [代数.是可分 F E]
  证明: by
  rw [← Algebra.top_toSubmodule]; rw [← top_toSubalgebra]; rw [← adjoin_univ]; rw [adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E _ q n]; rw [adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x]; rw [Set.image_univ]; rw [Algebra.adjoin_eq_span]
  have := (MonoidHom.mrange (powMonoidHom (α := E) (q ^ n))).closure_eq
  simp only [MonoidHom.mrange, powMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Submonoid.coe_copy] at this
  rw [this]
  refine (Submodule.span_mono <| Set.range_comp_subset_range _ _).antisymm (Submodule.span_le.2 ?_)
  rw [Set.range_comp]; rw [← Set.image_univ]
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  apply h ▸ Submodule.image_span_subset_span (LinearMap.iterateFrobenius F E q n) _

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, Algebra.adjoin_eq_span, Algebra.top_toSubmodule, IsAlgebraic, MonoidHom, MonoidHom.coe_mk, MonoidHom.mrange, OneHom, OneHom.coe_mk, Set.image_univ, Set.r, Submodule, Submodule.span_mono, Submonoid, Submonoid.coe_copy, adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable, adjoin_eq_span, adjoin_toSubalgebra_of_isAlgebraic, adjoin_univ
-/
theorem Field.span_map_pow_expChar_pow_eq_top_of_isSeparable [Algebra.IsSeparable F E]
    (h : Submodule.span F (Set.range v) = ⊤) :
    Submodule.span F (Set.range (v · ^ q ^ n)) = ⊤ := by
  rw [← Algebra.top_toSubmodule]; rw [← top_toSubalgebra]; rw [← adjoin_univ]; rw [adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E _ q n]; rw [adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x]; rw [Set.image_univ]; rw [Algebra.adjoin_eq_span]
  have := (MonoidHom.mrange (powMonoidHom (α := E) (q ^ n))).closure_eq
  simp only [MonoidHom.mrange, powMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Submonoid.coe_copy] at this
  rw [this]
  refine (Submodule.span_mono <| Set.range_comp_subset_range _ _).antisymm (Submodule.span_le.2 ?_)
  rw [Set.range_comp]; rw [← Set.image_univ]
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  apply h ▸ Submodule.image_span_subset_span (LinearMap.iterateFrobenius F E q n) _

/--
theorem `LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable` / 定理 `LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable`

English:
theorem LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable
  proof: by
  have h' := h.linearIndepOn_id
  let ι' := h'.extend (Set.range v).subset_univ
  let b : Basis ι' F E := Basis.extend h'
  let : Fintype ι' := FiniteDimensional.fintypeBasisIndex b
  have H := linearIndependent_of_top_le_span_of_card_eq_finrank
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
    (Module.finrank_eq_card_basis b).symm
  let f (i : ι) : ι' := ⟨v i, h'.subset_extend _ ⟨i, rfl⟩⟩
  convert! H.comp f fun _ _ heq => h.injective (by simpa only [f, Subtype.mk.injEq] using heq)
  simp_rw [Function.comp_apply, b]
  rw [Basis.extend_apply_self]

中文:
定理 LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable
  证明: by
  have h' := h.linearIndepOn_id
  let ι' := h'.extend (Set.range v).subset_univ
  let b : Basis ι' F E := Basis.extend h'
  let : Fintype ι' := FiniteDimensional.fintypeBasisIndex b
  have H := linearIndependent_of_top_le_span_of_card_eq_finrank
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
    (Module.finrank_eq_card_basis b).symm
  let f (i : ι) : ι' := ⟨v i, h'.subset_extend _ ⟨i, rfl⟩⟩
  convert! H.comp f fun _ _ heq => h.injective (by simpa only [f, Subtype.mk.injEq] using heq)
  simp_rw [Function.comp_apply, b]
  rw [Basis.extend_apply_self]
-/
private theorem LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  have h' := h.linearIndepOn_id
  let ι' := h'.extend (Set.range v).subset_univ
  let b : Basis ι' F E := Basis.extend h'
  let : Fintype ι' := FiniteDimensional.fintypeBasisIndex b
  have H := linearIndependent_of_top_le_span_of_card_eq_finrank
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
    (Module.finrank_eq_card_basis b).symm
  let f (i : ι) : ι' := ⟨v i, h'.subset_extend _ ⟨i, rfl⟩⟩
  convert! H.comp f fun _ _ heq => h.injective (by simpa only [f, Subtype.mk.injEq] using heq)
  simp_rw [Function.comp_apply, b]
  rw [Basis.extend_apply_self]

/--
theorem `LinearIndependent.map_pow_expChar_pow_of_isSeparable` / 定理 `LinearIndependent.map_pow_expChar_pow_of_isSeparable`

English:
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable
  statement: [Algebra.IsSeparable F E]
  proof: by
  classical
  rw [linearIndependent_iff_finset_linearIndependent] at h ⊢
  intro s
  let E' := adjoin F (s.image v : Set E)
  have : FiniteDimensional F E' := finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  let v' (i : s) : E' := ⟨v i.1, subset_adjoin F _ (Finset.mem_image.2 ⟨i.1, i.2, rfl⟩)⟩
  have h' : LinearIndependent F v' := (h s).of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_fd_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

中文:
定理 LinearIndependent.map_pow_expChar_pow_of_isSeparable
  结论: [代数.是可分 F E]
  证明: by
  classical
  rw [linearIndependent_iff_finset_linearIndependent] at h ⊢
  intro s
  let E' := adjoin F (s.image v : Set E)
  have : FiniteDimensional F E' := finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  let v' (i : s) : E' := ⟨v i.1, subset_adjoin F _ (Finset.mem_image.2 ⟨i.1, i.2, rfl⟩)⟩
  have h' : LinearIndependent F v' := (h s).of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_fd_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, FiniteDimensional, Finset, Finset.mem_image, IsIntegral, LinearIndependent, LinearMap, LinearMap.ker_eq_bot_of_injective, adjoin, classical, finiteDimensional_adjoin, isIntegral, ker_eq_bot_of_injective, linearIndependent_iff_finset_linearIndependent, map_pow_expChar_pow_of_fd_isSeparable, mem_image, of_comp, s.image, subset_adjoin
-/
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent] at h ⊢
  intro s
  let E' := adjoin F (s.image v : Set E)
  have : FiniteDimensional F E' := finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  let v' (i : s) : E' := ⟨v i.1, subset_adjoin F _ (Finset.mem_image.2 ⟨i.1, i.2, rfl⟩)⟩
  have h' : LinearIndependent F v' := (h s).of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_fd_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/--
theorem `LinearIndependent.map_pow_expChar_pow_of_isSeparable'` / 定理 `LinearIndependent.map_pow_expChar_pow_of_isSeparable'`

English:
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable'
  proof: by
  let E' := adjoin F (Set.range v)
have : Algebra.IsSeparable F E' := (isSeparable_adjoin_iff_isSeparable F _).2 by
    rintro _ ⟨y, rfl⟩; exact hsep y
  let v' (i : ι) : E' := ⟨v i, subset_adjoin F _ ⟨i, rfl⟩⟩
  have h' : LinearIndependent F v' := h.of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

中文:
定理 LinearIndependent.map_pow_expChar_pow_of_isSeparable'
  证明: by
  let E' := adjoin F (Set.range v)
have : Algebra.IsSeparable F E' := (isSeparable_adjoin_iff_isSeparable F _).2 by
    rintro _ ⟨y, rfl⟩; exact hsep y
  let v' (i : ι) : E' := ⟨v i, subset_adjoin F _ ⟨i, rfl⟩⟩
  have h' : LinearIndependent F v' := h.of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

Depends on / 依赖: Algebra, Algebra.IsSeparable, IsSeparable, LinearIndependent, LinearMap, LinearMap.ker_eq_bot_of_injective, Set.range, adjoin, h.of_comp, injective, isSeparable_adjoin_iff_isSeparable, ker_eq_bot_of_injective, map_pow_expChar_pow_of_isSeparable, of_comp, subset_adjoin, toLinearMap, val.injective, val.toLinearMap
-/
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable'
    (hsep : forall i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  let E' := adjoin F (Set.range v)
have : Algebra.IsSeparable F E' := (isSeparable_adjoin_iff_isSeparable F _).2 by
    rintro _ ⟨y, rfl⟩; exact hsep y
  let v' (i : ι) : E' := ⟨v i, subset_adjoin F _ ⟨i, rfl⟩⟩
  have h' : LinearIndependent F v' := h.of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/--
Definition of `Module.Basis.mapPowExpCharPowOfIsSeparable` / `Module.Basis.mapPowExpCharPowOfIsSeparable` 的定义

English:
definition Module.Basis.mapPowExpCharPowOfIsSeparable
  signature: [Algebra.IsSeparable F E] (b : Basis ι F E)
  body: .mk (b.linearIndependent.map_pow_expChar_pow_of_isSeparable q n)
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge

中文:
定义 模.基.mapPowExpCharPowOfIsSeparable
  签名: [代数.是可分 F E] (b : 基 ι F E)
  定义体: .mk (b.linearIndependent.map_pow_expChar_pow_of_isSeparable q n)
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge

Depends on / 依赖: Field.span_map_pow_expChar_pow_eq_top_of_isSeparable, b.linearIndependent.map_pow_expChar_pow_of_isSeparable, b.span_eq, linearIndependent, map_pow_expChar_pow_of_isSeparable, span_eq, span_map_pow_expChar_pow_eq_top_of_isSeparable
-/
def Module.Basis.mapPowExpCharPowOfIsSeparable [Algebra.IsSeparable F E] (b : Basis ι F E) :
    Basis ι F E :=
  .mk (b.linearIndependent.map_pow_expChar_pow_of_isSeparable q n)
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge

/--
theorem `minpoly.iterateFrobenius_of_isSeparable` / 定理 `minpoly.iterateFrobenius_of_isSeparable`

English:
theorem minpoly.iterateFrobenius_of_isSeparable
  statement: [ExpChar E q] (n : Nat) {a : E}
  proof: by
  have hai : IsIntegral F a := hsep.isIntegral
  have hapi : IsIntegral F (iterateFrobenius E q n a) := hai.pow _
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hapi)
    (minpoly.monic hai |>.map _)
    (minpoly.dvd F (a ^ q ^ n) ?haeval)
    ?hdeg
· simpa using! Eq.symm
      (minpoly F a).map_aeval_eq_aeval_map (RingHom.iterateFrobenius_comm _ q n) a
  · rw [(minpoly F a).natDegree_map_eq_of_injective (iterateFrobenius F q n).injective,
      ← IntermediateField.adjoin.finrank hai,
      IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E hsep q n,
      ← IntermediateField.adjoin.finrank hapi, iterateFrobenius_def]

中文:
定理 minpoly.iterateFrobenius_of_isSeparable
  结论: [ExpChar E q] (n : 自然数) {a : E}
  证明: by
  have hai : IsIntegral F a := hsep.isIntegral
  have hapi : IsIntegral F (iterateFrobenius E q n a) := hai.pow _
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hapi)
    (minpoly.monic hai |>.map _)
    (minpoly.dvd F (a ^ q ^ n) ?haeval)
    ?hdeg
· simpa using! Eq.symm
      (minpoly F a).map_aeval_eq_aeval_map (RingHom.iterateFrobenius_comm _ q n) a
  · rw [(minpoly F a).natDegree_map_eq_of_injective (iterateFrobenius F q n).injective,
      ← IntermediateField.adjoin.finrank hai,
      IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E hsep q n,
      ← IntermediateField.adjoin.finrank hapi, iterateFrobenius_def]

Depends on / 依赖: Eq.symm, Intermediat, IntermediateField, IntermediateField.adjoin.finrank, IsIntegral, Polynomial, Polynomial.eq_of_monic_of_dvd_of_natDegree_le, RingHom, RingHom.iterateFrobenius_comm, adjoin, eq_of_monic_of_dvd_of_natDegree_le, finrank, haeval, hai.pow, hsep.isIntegral, injective, isIntegral, iterateFrobenius, iterateFrobenius_comm, map_aeval_eq_aeval_map
-/
theorem minpoly.iterateFrobenius_of_isSeparable [ExpChar E q] (n : Nat) {a : E}
    (hsep : IsSeparable F a) :
    minpoly F (iterateFrobenius E q n a) = (minpoly F a).map (iterateFrobenius F q n) := by
  have hai : IsIntegral F a := hsep.isIntegral
  have hapi : IsIntegral F (iterateFrobenius E q n a) := hai.pow _
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hapi)
    (minpoly.monic hai |>.map _)
    (minpoly.dvd F (a ^ q ^ n) ?haeval)
    ?hdeg
· simpa using! Eq.symm
      (minpoly F a).map_aeval_eq_aeval_map (RingHom.iterateFrobenius_comm _ q n) a
  · rw [(minpoly F a).natDegree_map_eq_of_injective (iterateFrobenius F q n).injective,
      ← IntermediateField.adjoin.finrank hai,
      IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E hsep q n,
      ← IntermediateField.adjoin.finrank hapi, iterateFrobenius_def]

/--
theorem `minpoly.frobenius_of_isSeparable` / 定理 `minpoly.frobenius_of_isSeparable`

English:
theorem minpoly.frobenius_of_isSeparable
  given: [ExpChar E q] {a : E} (hsep : IsSeparable F a)
  proof: by
  simpa using minpoly.iterateFrobenius_of_isSeparable q 1 hsep

中文:
定理 minpoly.frobenius_of_isSeparable
  条件: [ExpChar E q] {a : E} (hsep : 是可分 F a)
  证明: by
  simpa using minpoly.iterateFrobenius_of_isSeparable q 1 hsep

Depends on / 依赖: iterateFrobenius_of_isSeparable, minpoly, minpoly.iterateFrobenius_of_isSeparable
-/
theorem minpoly.frobenius_of_isSeparable [ExpChar E q] {a : E} (hsep : IsSeparable F a) :
    minpoly F (frobenius E q a) = (minpoly F a).map (frobenius F q) := by
  simpa using minpoly.iterateFrobenius_of_isSeparable q 1 hsep

end

/--
theorem `perfectField_of_perfectClosure_eq_bot` / 定理 `perfectField_of_perfectClosure_eq_bot`

English:
theorem perfectField_of_perfectClosure_eq_bot
  given: [h : PerfectField E] (eq : perfectClosure F E = ⊥)
  proof: by
  let p := ringExpChar F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective p
  have := PerfectRing.ofSurjective F p fun x => by
    obtain ⟨y, h⟩ := surjective_frobenius E p (algebraMap F E x)
    have : y in perfectClosure F E := ⟨1, x, by rw [← h, pow_one, frobenius_def, ringExpChar.eq F p]⟩
    obtain ⟨z, rfl⟩ := eq ▸ this
    simp only [Algebra.ofId] at h
    exact ⟨z, (algebraMap F E).injective (by rw [RingHom.map_frobenius]; rw [h])⟩
  exact PerfectRing.toPerfectField F p

中文:
定理 perfectField_of_perfectClosure_eq_bot
  条件: [h : 完美域 E] (eq : perfectClosure F E = ⊥)
  证明: by
  let p := ringExpChar F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective p
  have := PerfectRing.ofSurjective F p fun x => by
    obtain ⟨y, h⟩ := surjective_frobenius E p (algebraMap F E x)
    have : y in perfectClosure F E := ⟨1, x, by rw [← h, pow_one, frobenius_def, ringExpChar.eq F p]⟩
    obtain ⟨z, rfl⟩ := eq ▸ this
    simp only [Algebra.ofId] at h
    exact ⟨z, (algebraMap F E).injective (by rw [RingHom.map_frobenius]; rw [h])⟩
  exact PerfectRing.toPerfectField F p

Depends on / 依赖: Algebra, Algebra.ofId, PerfectRing, PerfectRing.ofSurjective, PerfectRing.toPerfectField, RingHom, RingHom.map_frobenius, algebraMap, expChar_of_injective_algebraMap, frobenius_def, injective, map_frobenius, ofSurjective, perfectClosure, pow_one, ringExpChar, ringExpChar.eq, surjective_frobenius, toPerfectField
-/
theorem perfectField_of_perfectClosure_eq_bot [h : PerfectField E] (eq : perfectClosure F E = ⊥) :
    PerfectField F := by
  let p := ringExpChar F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective p
  have := PerfectRing.ofSurjective F p fun x => by
    obtain ⟨y, h⟩ := surjective_frobenius E p (algebraMap F E x)
    have : y in perfectClosure F E := ⟨1, x, by rw [← h, pow_one, frobenius_def, ringExpChar.eq F p]⟩
    obtain ⟨z, rfl⟩ := eq ▸ this
    simp only [Algebra.ofId] at h
    exact ⟨z, (algebraMap F E).injective (by rw [RingHom.map_frobenius]; rw [h])⟩
  exact PerfectRing.toPerfectField F p

/--
theorem `perfectField_of_isSeparable_of_perfectField_top` / 定理 `perfectField_of_isSeparable_of_perfectField_top`

English:
theorem perfectField_of_isSeparable_of_perfectField_top
  given: [Algebra.IsSeparable F E] [PerfectField E]
  proof: perfectField_of_perfectClosure_eq_bot F E (perfectClosure.eq_bot_of_isSeparable F E)

中文:
定理 perfectField_of_isSeparable_of_perfectField_top
  条件: [代数.是可分 F E] [完美域 E]
  证明: perfectField_of_perfectClosure_eq_bot F E (perfectClosure.eq_bot_of_isSeparable F E)

Depends on / 依赖: eq_bot_of_isSeparable, perfectClosure, perfectClosure.eq_bot_of_isSeparable, perfectField_of_perfectClosure_eq_bot
-/
theorem perfectField_of_isSeparable_of_perfectField_top [Algebra.IsSeparable F E] [PerfectField E] :
    PerfectField F :=
  perfectField_of_perfectClosure_eq_bot F E (perfectClosure.eq_bot_of_isSeparable F E)

/--
theorem `perfectField_iff_isSeparable_algebraicClosure` / 定理 `perfectField_iff_isSeparable_algebraicClosure`

English:
theorem perfectField_iff_isSeparable_algebraicClosure
  given: [IsAlgClosure F E]
  proof: ⟨fun _ => IsSepClosure.separable, fun _ => haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
    perfectField_of_isSeparable_of_perfectField_top F E⟩

中文:
定理 perfectField_iff_isSeparable_algebraicClosure
  条件: [是AlgClosure F E]
  证明: ⟨fun _ => IsSepClosure.separable, fun _ => haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
    perfectField_of_isSeparable_of_perfectField_top F E⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosure, IsAlgClosure.isAlgClosed, IsSepClosure, IsSepClosure.separable, isAlgClosed, perfectField_of_isSeparable_of_perfectField_top, separable
-/
theorem perfectField_iff_isSeparable_algebraicClosure [IsAlgClosure F E] :
    PerfectField F ↔ Algebra.IsSeparable F E :=
  ⟨fun _ => IsSepClosure.separable, fun _ => haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
    perfectField_of_isSeparable_of_perfectField_top F E⟩
