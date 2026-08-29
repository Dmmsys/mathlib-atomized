/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.FieldTheory.IsSepClosed

/-!

# Basic results about purely inseparable extensions

This file contains basic definitions and results about purely inseparable extensions.

## Main definitions

- `IsPurelyInseparable`: typeclass for purely inseparable field extensions: an algebraic extension
  `E / F` is purely inseparable if and only if the minimal polynomial of every element of `E ∖ F`
  is not separable.

## Main results

- `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`,
  `IsPurelyInseparable.bijective_algebraMap_of_isSeparable`,
  `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`:
  if `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective
  (hence bijective). In particular, if an intermediate field of `E / F` is both purely inseparable
  and separable, then it is equal to `F`.

- `isPurelyInseparable_iff_pow_mem`: a field extension `E / F` of exponential characteristic `q` is
  purely inseparable if and only if for every element `x` of `E`, there exists a natural number `n`
  such that `x ^ (q ^ n)` is contained in `F`.

- `IsPurelyInseparable.trans`: if `E / F` and `K / E` are both purely inseparable extensions, then
  `K / F` is also purely inseparable.

- `isPurelyInseparable_iff_natSepDegree_eq_one`: `E / F` is purely inseparable if and only if for
  every element `x` of `E`, its minimal polynomial has separable degree one.

- `isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `X ^ (q ^ n) - y` for some natural number `n` and some
  element `y` of `F`.

- `isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `(X - x) ^ (q ^ n)` for some natural number `n`.

- `isPurelyInseparable_iff_finSepDegree_eq_one`: an extension is purely inseparable
  if and only if it has finite separable degree (`Field.finSepDegree`) one.

- `IsPurelyInseparable.normal`: a purely inseparable extension is normal.

- `separableClosure.isPurelyInseparable`: if `E / F` is algebraic, then `E` is purely inseparable
  over the separable closure of `F` in `E`.

- `separableClosure_le_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` contains
  the separable closure of `F` in `E` if and only if `E` is purely inseparable over it.

- `eq_separableClosure_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` is equal
  to the separable closure of `F` in `E` if and only if it is separable over `F`, and `E`
  is purely inseparable over it.

- `IsPurelyInseparable.injective_comp_algebraMap`: if `E / F` is purely inseparable, then for any
  reduced ring `L`, the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective.
  In particular, a purely inseparable field extension is an epimorphism in the category of fields.

- `IsPurelyInseparable.of_injective_comp_algebraMap`: if `L` is an algebraically closed field
  containing `E`, such that the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is
  injective, then `E / F` is purely inseparable. As a corollary, epimorphisms in the category of
  fields must be purely inseparable extensions.

- `Field.finSepDegree_eq`: if `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to
  `Field.sepDegree F E` as a natural number. This means that the cardinality of `Field.Emb F E`
  and the degree of `(separableClosure F E) / F` are both finite or infinite, and when they are
  finite, they coincide.

- `Field.finSepDegree_mul_finInsepDegree`: the finite separable degree multiply by the finite
  inseparable degree is equal to the (finite) field extension degree.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

@[expose] public section

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

section General

variable (F E : Type*) [CommRing F] [Ring E] [Algebra F E]
variable (K : Type*) [Ring K] [Algebra F K]

/--
Definition of `IsPurelyInseparable` / `IsPurelyInseparable` 的定义

English:
class IsPurelyInseparable
  parameters: : Prop where
  axioms and operations (2):
    - isIntegral : Algebra.IsIntegral F E
    - inseparable'((x : E)) : IsSeparable F x -> x in (algebraMap F E).range

中文:
类 IsPurelyInseparable
  参数: : 命题 where
  公理与运算 (2 个):
    - isIntegral : Algebra.Is整数egral F E
    - inseparable'((x : E)) : IsSeparable F x -> x in (algebraMap F E).range
-/
class IsPurelyInseparable : Prop where
  isIntegral : Algebra.IsIntegral F E
  inseparable' (x : E) : IsSeparable F x -> x in (algebraMap F E).range

attribute [instance] IsPurelyInseparable.isIntegral

variable {E} in
/--
theorem `IsPurelyInseparable.isIntegral'` / 定理 `IsPurelyInseparable.isIntegral'`

English:
theorem IsPurelyInseparable.isIntegral'
  given: [IsPurelyInseparable F E] (x : E)
  statement: IsIntegral F x
  proof: Algebra.IsIntegral.isIntegral _

中文:
定理 IsPurelyInseparable.isIntegral'
  条件: [IsPurelyInseparable F E] (x : E)
  结论: Is整数egral F x
  证明: Algebra.IsIntegral.isIntegral _

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isIntegral
-/
theorem IsPurelyInseparable.isIntegral' [IsPurelyInseparable F E] (x : E) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral _

/--
theorem `IsPurelyInseparable.isAlgebraic` / 定理 `IsPurelyInseparable.isAlgebraic`

English:
theorem IsPurelyInseparable.isAlgebraic
  given: [Nontrivial F] [IsPurelyInseparable F E]
  proof: inferInstance

中文:
定理 IsPurelyInseparable.isAlgebraic
  条件: [Nontrivial F] [IsPurelyInseparable F E]
  证明: inferInstance
-/
theorem IsPurelyInseparable.isAlgebraic [Nontrivial F] [IsPurelyInseparable F E] :
    Algebra.IsAlgebraic F E := inferInstance

variable {E}

/--
theorem `IsPurelyInseparable.inseparable` / 定理 `IsPurelyInseparable.inseparable`

English:
theorem IsPurelyInseparable.inseparable
  given: [IsPurelyInseparable F E]
  proof: IsPurelyInseparable.inseparable'

中文:
定理 IsPurelyInseparable.inseparable
  条件: [IsPurelyInseparable F E]
  证明: IsPurelyInseparable.inseparable'

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.inseparable, inseparable
-/
theorem IsPurelyInseparable.inseparable [IsPurelyInseparable F E] :
    forall x : E, IsSeparable F x -> x in (algebraMap F E).range :=
  IsPurelyInseparable.inseparable'

variable {F}

/--
theorem `isPurelyInseparable_iff` / 定理 `isPurelyInseparable_iff`

English:
theorem isPurelyInseparable_iff
  statement: IsPurelyInseparable F E ↔ forall x : E,
  proof: ⟨fun h x => ⟨h.isIntegral' _ x, h.inseparable' x⟩, fun h => ⟨⟨fun x => (h x).1⟩, fun x => (h x).2⟩⟩

中文:
定理 isPurelyInseparable_iff
  结论: IsPurelyInseparable F E ↔ 对任意 x : E,
  证明: ⟨fun h x => ⟨h.isIntegral' _ x, h.inseparable' x⟩, fun h => ⟨⟨fun x => (h x).1⟩, fun x => (h x).2⟩⟩

Depends on / 依赖: h.inseparable, h.isIntegral, inseparable, isIntegral
-/
theorem isPurelyInseparable_iff : IsPurelyInseparable F E ↔ forall x : E,
    IsIntegral F x ∧ (IsSeparable F x -> x in (algebraMap F E).range) :=
  ⟨fun h x => ⟨h.isIntegral' _ x, h.inseparable' x⟩, fun h => ⟨⟨fun x => (h x).1⟩, fun x => (h x).2⟩⟩

variable {K}

/--
theorem `AlgEquiv.isPurelyInseparable` / 定理 `AlgEquiv.isPurelyInseparable`

English:
theorem AlgEquiv.isPurelyInseparable
  given: (e : K ≃ₐ[F] E) [IsPurelyInseparable F K]
  proof: by
  refine ⟨⟨fun _ => by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral' F _⟩,
    fun x h => ?_⟩
  rw [IsSeparable]; rw [← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h

中文:
定理 AlgEquiv.isPurelyInseparable
  条件: (e : K ≃ₐ[F] E) [IsPurelyInseparable F K]
  证明: by
  refine ⟨⟨fun _ => by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral' F _⟩,
    fun x h => ?_⟩
  rw [IsSeparable]; rw [← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.inseparable, IsPurelyInseparable.isIntegral, IsSeparable, RingHom, RingHom.mem_range, algEquiv_eq, algebraMap_eq_apply, e.symm, inseparable, isIntegral, isIntegral_algEquiv, mem_range, minpoly, minpoly.algEquiv_eq
-/
theorem AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] :
    IsPurelyInseparable F E := by
  refine ⟨⟨fun _ => by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral' F _⟩,
    fun x h => ?_⟩
  rw [IsSeparable]; rw [← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h

/--
theorem `AlgEquiv.isPurelyInseparable_iff` / 定理 `AlgEquiv.isPurelyInseparable_iff`

English:
theorem AlgEquiv.isPurelyInseparable_iff
  given: (e : K ≃ₐ[F] E)
  proof: ⟨fun _ => e.isPurelyInseparable, fun _ => e.symm.isPurelyInseparable⟩

中文:
定理 AlgEquiv.isPurelyInseparable_iff
  条件: (e : K ≃ₐ[F] E)
  证明: ⟨fun _ => e.isPurelyInseparable, fun _ => e.symm.isPurelyInseparable⟩

Depends on / 依赖: e.isPurelyInseparable, e.symm.isPurelyInseparable, isPurelyInseparable
-/
theorem AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) :
    IsPurelyInseparable F K ↔ IsPurelyInseparable F E :=
  ⟨fun _ => e.isPurelyInseparable, fun _ => e.symm.isPurelyInseparable⟩

/--
Instance `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed` / 实例 `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`

English:
instance Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
  body: ⟨inferInstance, fun x h => minpoly.mem_range_of_degree_eq_one F x
    IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral _)) h⟩

中文:
实例 Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
  定义体: ⟨inferInstance, fun x h => minpoly.mem_range_of_degree_eq_one F x
    IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral _)) h⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, IsSepClosed, IsSepClosed.degree_eq_one_of_irreducible, degree_eq_one_of_irreducible, irreducible, isIntegral, mem_range_of_degree_eq_one, minpoly, minpoly.irreducible, minpoly.mem_range_of_degree_eq_one
-/
instance Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    {F : Type u} {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsSepClosed F] : IsPurelyInseparable F E :=
⟨inferInstance, fun x h => minpoly.mem_range_of_degree_eq_one F x
    IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral _)) h⟩

variable (F E K)

/--
theorem `IsPurelyInseparable.surjective_algebraMap_of_isSeparable` / 定理 `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`

English:
theorem IsPurelyInseparable.surjective_algebraMap_of_isSeparable
  proof: fun x => IsPurelyInseparable.inseparable F x (Algebra.IsSeparable.isSeparable F x)

中文:
定理 IsPurelyInseparable.surjective_algebraMap_of_isSeparable
  证明: fun x => IsPurelyInseparable.inseparable F x (Algebra.IsSeparable.isSeparable F x)

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsPurelyInseparable, IsPurelyInseparable.inseparable, IsSeparable, inseparable, isSeparable
-/
theorem IsPurelyInseparable.surjective_algebraMap_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Surjective (algebraMap F E) :=
  fun x => IsPurelyInseparable.inseparable F x (Algebra.IsSeparable.isSeparable F x)

/--
theorem `IsPurelyInseparable.bijective_algebraMap_of_isSeparable` / 定理 `IsPurelyInseparable.bijective_algebraMap_of_isSeparable`

English:
theorem IsPurelyInseparable.bijective_algebraMap_of_isSeparable
  proof: ⟨FaithfulSMul.algebraMap_injective F E, surjective_algebraMap_of_isSeparable F E⟩

中文:
定理 IsPurelyInseparable.bijective_algebraMap_of_isSeparable
  证明: ⟨FaithfulSMul.algebraMap_injective F E, surjective_algebraMap_of_isSeparable F E⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, surjective_algebraMap_of_isSeparable
-/
theorem IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    [Nontrivial E] [IsDomain F] [IsTorsionFree F E]
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Bijective (algebraMap F E) :=
  ⟨FaithfulSMul.algebraMap_injective F E, surjective_algebraMap_of_isSeparable F E⟩

variable {F E} in
/--
theorem `Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable` / 定理 `Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable`

English:
theorem Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable
  statement: (L : Subalgebra F E)
  proof: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (Subalgebra.val _) hy⟩

中文:
定理 Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable
  结论: (L : Subalgebra F E)
  证明: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (Subalgebra.val _) hy⟩

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.surjective_algebraMap_of_isSeparable, Subalgebra, Subalgebra.val, bot_unique, congr_arg, surjective_algebraMap_of_isSeparable
-/
theorem Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable (L : Subalgebra F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (Subalgebra.val _) hy⟩

/--
theorem `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable` / 定理 `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`

English:
theorem IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
  proof: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩

中文:
定理 IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
  证明: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.surjective_algebraMap_of_isSeparable, algebraMap, bot_unique, congr_arg, surjective_algebraMap_of_isSeparable
-/
theorem IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩

/--
theorem `separableClosure.eq_bot_of_isPurelyInseparable` / 定理 `separableClosure.eq_bot_of_isPurelyInseparable`

English:
theorem separableClosure.eq_bot_of_isPurelyInseparable
  proof: bot_unique fun x h => IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

中文:
定理 separableClosure.eq_bot_of_isPurelyInseparable
  证明: bot_unique fun x h => IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.inseparable, bot_unique, inseparable, mem_separableClosure_iff
-/
theorem separableClosure.eq_bot_of_isPurelyInseparable
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h => IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

/--
theorem `separableClosure.eq_bot_iff` / 定理 `separableClosure.eq_bot_iff`

English:
theorem separableClosure.eq_bot_iff
  proof: ⟨fun h => isPurelyInseparable_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, fun hs => by
    simpa only [h] using! mem_separableClosure_iff.2 hs⟩, fun _ => eq_bot_of_isPurelyInseparable F E⟩

中文:
定理 separableClosure.eq_bot_iff
  证明: ⟨fun h => isPurelyInseparable_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, fun hs => by
    simpa only [h] using! mem_separableClosure_iff.2 hs⟩, fun _ => eq_bot_of_isPurelyInseparable F E⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, eq_bot_of_isPurelyInseparable, isIntegral, isPurelyInseparable_iff, mem_separableClosure_iff
-/
theorem separableClosure.eq_bot_iff
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h => isPurelyInseparable_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, fun hs => by
    simpa only [h] using! mem_separableClosure_iff.2 hs⟩, fun _ => eq_bot_of_isPurelyInseparable F E⟩

/--
Instance `isPurelyInseparable_self` / 实例 `isPurelyInseparable_self`

English:
instance isPurelyInseparable_self
  signature: : IsPurelyInseparable F F
  body: ⟨inferInstance, fun x _ => ⟨x, rfl⟩⟩

中文:
实例 isPurelyInseparable_self
  签名: : IsPurelyInseparable F F
  定义体: ⟨inferInstance, fun x _ => ⟨x, rfl⟩⟩
-/
instance isPurelyInseparable_self : IsPurelyInseparable F F :=
  ⟨inferInstance, fun x _ => ⟨x, rfl⟩⟩

section

variable (F : Type u) {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
variable (q : Nat) [ExpChar F q] (x : E)

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, there exists a natural number `n` such that
`x ^ (q ^ n)` is contained in `F`. -/
@[stacks 09HE]
/--
theorem `isPurelyInseparable_iff_pow_mem` / 定理 `isPurelyInseparable_iff_pow_mem`

English:
theorem isPurelyInseparable_iff_pow_mem
  proof: by
  rw [isPurelyInseparable_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := (minpoly.irreducible (h x).1).hasSeparableContraction q
exact ⟨n, (h _).2 h1.of_dvd minpoly.dvd F _ by
      simpa only [expand_aeval, minpoly.aeval] using congr_arg (aeval x) h2⟩
  have hdeg := (m

中文:
定理 isPurelyInseparable_iff_pow_mem
  证明: by
  rw [isPurelyInseparable_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := (minpoly.irreducible (h x).1).hasSeparableContraction q
exact ⟨n, (h _).2 h1.of_dvd minpoly.dvd F _ by
      simpa only [expand_aeval, minpoly.aeval] using congr_arg (aeval x) h2⟩
  have hdeg := (m

Depends on / 依赖: IsIntegral, congr_arg, eq_zero, expand_aeval, h1.of_dvd, hasSeparableContraction, irreducible, isPurelyInseparable_iff, minpoly, minpoly.aeval, minpoly.dvd, minpoly.eq_zero, minpoly.irreducible, minpoly.natSepDegree_eq_one_iff_pow_mem, natSepDegree_eq_one_iff_pow_mem, natSepDegree_zero, of_dvd, zero_ne_one
-/
theorem isPurelyInseparable_iff_pow_mem :
    IsPurelyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E).range := by
  rw [isPurelyInseparable_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := (minpoly.irreducible (h x).1).hasSeparableContraction q
exact ⟨n, (h _).2 h1.of_dvd minpoly.dvd F _ by
      simpa only [expand_aeval, minpoly.aeval] using congr_arg (aeval x) h2⟩
  have hdeg := (minpoly.natSepDegree_eq_one_iff_pow_mem q).2 (h x)
  have halg : IsIntegral F x := by_contra fun h' => by
    simp only [minpoly.eq_zero h', natSepDegree_zero, zero_ne_one] at hdeg
  refine ⟨halg, fun hsep => ?_⟩
  rwa [hsep.natSepDegree_eq_natDegree, minpoly.natDegree_eq_one_iff] at hdeg

/--
theorem `IsPurelyInseparable.pow_mem` / 定理 `IsPurelyInseparable.pow_mem`

English:
theorem IsPurelyInseparable.pow_mem
  given: [IsPurelyInseparable F E]
  proof: (isPurelyInseparable_iff_pow_mem F q).1 ‹_› x

中文:
定理 IsPurelyInseparable.pow_mem
  条件: [IsPurelyInseparable F E]
  证明: (isPurelyInseparable_iff_pow_mem F q).1 ‹_› x

Depends on / 依赖: isPurelyInseparable_iff_pow_mem
-/
theorem IsPurelyInseparable.pow_mem [IsPurelyInseparable F E] :
    exists n : Nat, x ^ q ^ n in (algebraMap F E).range :=
  (isPurelyInseparable_iff_pow_mem F q).1 ‹_› x

end

end General

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section Field

/--
theorem `IsPurelyInseparable.tower_bot` / 定理 `IsPurelyInseparable.tower_bot`

English:
theorem IsPurelyInseparable.tower_bot
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: by
  refine ⟨⟨fun x => (isIntegral' F (algebraMap E K x)).tower_bot_of_field⟩, fun x h => ?_⟩
  rw [IsSeparable]; rw [← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  exact ⟨y, (algebraMap E K).injective (h.symm ▸ (IsScalarTower.algebraMap_apply F E K y

中文:
定理 IsPurelyInseparable.tower_bot
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: by
  refine ⟨⟨fun x => (isIntegral' F (algebraMap E K x)).tower_bot_of_field⟩, fun x h => ?_⟩
  rw [IsSeparable]; rw [← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  exact ⟨y, (algebraMap E K).injective (h.symm ▸ (IsScalarTower.algebraMap_apply F E K y

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, IsSeparable, algebraMap, algebraMap_apply, algebraMap_eq, h.symm, injective, inseparable, isIntegral, minpoly, minpoly.algebraMap_eq, tower_bot_of_field
-/
theorem IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K]
    [IsPurelyInseparable F K] : IsPurelyInseparable F E := by
  refine ⟨⟨fun x => (isIntegral' F (algebraMap E K x)).tower_bot_of_field⟩, fun x h => ?_⟩
  rw [IsSeparable]; rw [← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  exact ⟨y, (algebraMap E K).injective (h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm)⟩

/--
theorem `IsPurelyInseparable.tower_top` / 定理 `IsPurelyInseparable.tower_top`

English:
theorem IsPurelyInseparable.tower_top
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h ⊢
  intro x
  obtain ⟨n, y, h⟩ := h x
  exact ⟨n, (algebraMap F E) y, h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm⟩

中文:
定理 IsPurelyInseparable.tower_top
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h ⊢
  intro x
  obtain ⟨n, y, h⟩ := h x
  exact ⟨n, (algebraMap F E) y, h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm⟩

Depends on / 依赖: ExpChar, ExpChar.exists, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, expChar_of_injective_algebraMap, h.symm, injective, isPurelyInseparable_iff_pow_mem
-/
theorem IsPurelyInseparable.tower_top [Algebra E K] [IsScalarTower F E K]
    [h : IsPurelyInseparable F K] : IsPurelyInseparable E K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h ⊢
  intro x
  obtain ⟨n, y, h⟩ := h x
  exact ⟨n, (algebraMap F E) y, h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm⟩

/-- If `E / F` and `K / E` are both purely inseparable extensions, then `K / F` is also
purely inseparable. -/
@[stacks 02JJ "See also 00GM"]
/--
theorem `IsPurelyInseparable.trans` / 定理 `IsPurelyInseparable.trans`

English:
theorem IsPurelyInseparable.trans
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h1 h2 ⊢
  intro x
  obtain ⟨n, y, h2⟩ := h2 x
  obtain ⟨m, z, h1⟩ := h1 y
  refine ⟨n + m, z, ?_⟩
  rw [IsScalarTower.algebraMap_apply F E K]; r

中文:
定理 IsPurelyInseparable.trans
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h1 h2 ⊢
  intro x
  obtain ⟨n, y, h2⟩ := h2 x
  obtain ⟨m, z, h1⟩ := h1 y
  refine ⟨n + m, z, ?_⟩
  rw [IsScalarTower.algebraMap_apply F E K]; r

Depends on / 依赖: ExpChar, ExpChar.exists, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, expChar_of_injective_algebraMap, injective, isPurelyInseparable_iff_pow_mem, map_pow, pow_add, pow_mul
-/
theorem IsPurelyInseparable.trans [Algebra E K] [IsScalarTower F E K]
    [h1 : IsPurelyInseparable F E] [h2 : IsPurelyInseparable E K] : IsPurelyInseparable F K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h1 h2 ⊢
  intro x
  obtain ⟨n, y, h2⟩ := h2 x
  obtain ⟨m, z, h1⟩ := h1 y
  refine ⟨n + m, z, ?_⟩
  rw [IsScalarTower.algebraMap_apply F E K]; rw [h1]; rw [map_pow]; rw [h2]; rw [← pow_mul]; rw [← pow_add]

namespace IntermediateField

variable (M : IntermediateField F K)

/--
Instance `isPurelyInseparable_tower_bot` / 实例 `isPurelyInseparable_tower_bot`

English:
instance isPurelyInseparable_tower_bot
  signature: [IsPurelyInseparable F K]
  body: IsPurelyInseparable.tower_bot F M K

中文:
实例 isPurelyInseparable_tower_bot
  签名: [IsPurelyInseparable F K]
  定义体: IsPurelyInseparable.tower_bot F M K

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.tower_bot, tower_bot
-/
instance isPurelyInseparable_tower_bot [IsPurelyInseparable F K] : IsPurelyInseparable F M :=
  IsPurelyInseparable.tower_bot F M K

/--
Instance `isPurelyInseparable_tower_top` / 实例 `isPurelyInseparable_tower_top`

English:
instance isPurelyInseparable_tower_top
  signature: [IsPurelyInseparable F K]
  body: IsPurelyInseparable.tower_top F M K

中文:
实例 isPurelyInseparable_tower_top
  签名: [IsPurelyInseparable F K]
  定义体: IsPurelyInseparable.tower_top F M K

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.tower_top, tower_top
-/
instance isPurelyInseparable_tower_top [IsPurelyInseparable F K] : IsPurelyInseparable M K :=
  IsPurelyInseparable.tower_top F M K

end IntermediateField

variable {E}

/--
theorem `isPurelyInseparable_iff_natSepDegree_eq_one` / 定理 `isPurelyInseparable_iff_natSepDegree_eq_one`

English:
theorem isPurelyInseparable_iff_natSepDegree_eq_one
  proof: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [isPurelyInseparable_iff_pow_mem F q, minpoly.natSepDegree_eq_one_iff_pow_mem q]

中文:
定理 isPurelyInseparable_iff_natSepDegree_eq_one
  证明: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [isPurelyInseparable_iff_pow_mem F q, minpoly.natSepDegree_eq_one_iff_pow_mem q]

Depends on / 依赖: ExpChar, ExpChar.exists, isPurelyInseparable_iff_pow_mem, minpoly, minpoly.natSepDegree_eq_one_iff_pow_mem, natSepDegree_eq_one_iff_pow_mem, simp_rw
-/
theorem isPurelyInseparable_iff_natSepDegree_eq_one :
    IsPurelyInseparable F E ↔ forall x : E, (minpoly F x).natSepDegree = 1 := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [isPurelyInseparable_iff_pow_mem F q, minpoly.natSepDegree_eq_one_iff_pow_mem q]

/--
theorem `IsPurelyInseparable.natSepDegree_eq_one` / 定理 `IsPurelyInseparable.natSepDegree_eq_one`

English:
theorem IsPurelyInseparable.natSepDegree_eq_one
  given: [IsPurelyInseparable F E] (x : E)
  proof: (isPurelyInseparable_iff_natSepDegree_eq_one F).1 ‹_› x

中文:
定理 IsPurelyInseparable.natSepDegree_eq_one
  条件: [IsPurelyInseparable F E] (x : E)
  证明: (isPurelyInseparable_iff_natSepDegree_eq_one F).1 ‹_› x

Depends on / 依赖: isPurelyInseparable_iff_natSepDegree_eq_one
-/
theorem IsPurelyInseparable.natSepDegree_eq_one [IsPurelyInseparable F E] (x : E) :
    (minpoly F x).natSepDegree = 1 :=
  (isPurelyInseparable_iff_natSepDegree_eq_one F).1 ‹_› x

/--
theorem `isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C` / 定理 `isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C`

English:
theorem isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C
  given: (q : Nat) [hF : ExpChar F q]
  proof: by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q]

中文:
定理 isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C
  条件: (q : 自然数) [hF : ExpChar F q]
  证明: by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q]

Depends on / 依赖: isPurelyInseparable_iff_natSepDegree_eq_one, minpoly, minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C, natSepDegree_eq_one_iff_eq_X_pow_sub_C, simp_rw
-/
theorem isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C (q : Nat) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔ forall x : E, exists (n : Nat) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q]

/--
theorem `IsPurelyInseparable.minpoly_eq_X_pow_sub_C` / 定理 `IsPurelyInseparable.minpoly_eq_X_pow_sub_C`

English:
theorem IsPurelyInseparable.minpoly_eq_X_pow_sub_C
  statement: (q : Nat) [ExpChar F q] [IsPurelyInseparable F E]
  proof: (isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C F q).1 ‹_› x

中文:
定理 IsPurelyInseparable.minpoly_eq_X_pow_sub_C
  结论: (q : 自然数) [ExpChar F q] [IsPurelyInseparable F E]
  证明: (isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C F q).1 ‹_› x

Depends on / 依赖: isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C
-/
theorem IsPurelyInseparable.minpoly_eq_X_pow_sub_C (q : Nat) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : exists (n : Nat) (y : F), minpoly F x = X ^ q ^ n - C y :=
  (isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C F q).1 ‹_› x

/--
theorem `isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow` / 定理 `isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow`

English:
theorem isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow
  given: (q : Nat) [hF : ExpChar F q]
  proof: by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow q]

中文:
定理 isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow
  条件: (q : 自然数) [hF : ExpChar F q]
  证明: by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow q]

Depends on / 依赖: isPurelyInseparable_iff_natSepDegree_eq_one, minpoly, minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow, natSepDegree_eq_one_iff_eq_X_sub_C_pow, simp_rw
-/
theorem isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow (q : Nat) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔
    forall x : E, exists n : Nat, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow q]

/--
theorem `IsPurelyInseparable.minpoly_eq_X_sub_C_pow` / 定理 `IsPurelyInseparable.minpoly_eq_X_sub_C_pow`

English:
theorem IsPurelyInseparable.minpoly_eq_X_sub_C_pow
  statement: (q : Nat) [ExpChar F q] [IsPurelyInseparable F E]
  proof: (isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow F q).1 ‹_› x

中文:
定理 IsPurelyInseparable.minpoly_eq_X_sub_C_pow
  结论: (q : 自然数) [ExpChar F q] [IsPurelyInseparable F E]
  证明: (isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow F q).1 ‹_› x

Depends on / 依赖: isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow
-/
theorem IsPurelyInseparable.minpoly_eq_X_sub_C_pow (q : Nat) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : exists n : Nat, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n :=
  (isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow F q).1 ‹_› x

variable (E) in
/--
lemma `IsPurelyInseparable.finrank_eq_pow` / 引理 `IsPurelyInseparable.finrank_eq_pow`

English:
lemma IsPurelyInseparable.finrank_eq_pow
  proof: by
  suffices forall (F E : Type v) [Field F] [Field E] [Algebra F E] (q : Nat) [ExpChar F q]
      [IsPurelyInseparable F E] [FiniteDimensional F E], exists n, finrank F E = q ^ n by
    simpa using this (⊥ : IntermediateField F E) E q
  intro F E _ _ _ q _ _ _
  generalize hd : finrank F E = d
  i

中文:
引理 IsPurelyInseparable.finrank_eq_pow
  证明: by
  suffices forall (F E : Type v) [Field F] [Field E] [Algebra F E] (q : Nat) [ExpChar F q]
      [IsPurelyInseparable F E] [FiniteDimensional F E], exists n, finrank F E = q ^ n by
    simpa using this (⊥ : IntermediateField F E) E q
  intro F E _ _ _ q _ _ _
  generalize hd : finrank F E = d
  i

Depends on / 依赖: Algebra, ExpChar, FiniteDimensional, IntermediateField, IntermediateField.finrank_bot, IsPurelyInseparable, Nat.strongRecOn, finrank, finrank_bot, finrank_top, generalize, generalizing, pow_zero, strongRecOn
-/
lemma IsPurelyInseparable.finrank_eq_pow
    (q : Nat) [ExpChar F q] [IsPurelyInseparable F E] [FiniteDimensional F E] :
    exists n, finrank F E = q ^ n := by
  suffices forall (F E : Type v) [Field F] [Field E] [Algebra F E] (q : Nat) [ExpChar F q]
      [IsPurelyInseparable F E] [FiniteDimensional F E], exists n, finrank F E = q ^ n by
    simpa using this (⊥ : IntermediateField F E) E q
  intro F E _ _ _ q _ _ _
  generalize hd : finrank F E = d
  induction d using Nat.strongRecOn generalizing F with
  | ind d IH =>
    by_cases h : (⊥ : IntermediateField F E) = ⊤
    · rw [← finrank_top', ← h, IntermediateField.finrank_bot] at hd
      exact ⟨0, ((pow_zero q).trans hd).symm⟩
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le h :)
    obtain ⟨m, y, e⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x
    have : finrank F F⟮x⟯ = q ^ m := by
      rw [adjoin.finrank (Algebra.IsIntegral.isIntegral x)]; rw [e]; rw [natDegree_sub_C]; rw [natDegree_X_pow]
    obtain ⟨n, hn⟩ := IH _ (by
      rw [← hd]; rw [← finrank_mul_finrank F F⟮x⟯]; rw [Nat.lt_mul_iff_one_lt_left finrank_pos]; rw [this]
      by_contra! H
      refine hx (finrank_adjoin_simple_eq_one_iff.mp (le_antisymm (this ▸ H) ?_))
      exact Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne') (F⟮x⟯) rfl
    exact ⟨m + n, by rw [← hd, ← finrank_mul_finrank F F⟮x⟯, hn, pow_add, this]⟩

variable (E)

variable {F E} in
/--
theorem `isPurelyInseparable_of_finSepDegree_eq_one` / 定理 `isPurelyInseparable_of_finSepDegree_eq_one`

English:
theorem isPurelyInseparable_of_finSepDegree_eq_one
  proof: by
  by_cases H : Algebra.IsAlgebraic F E
  · rw [isPurelyInseparable_iff]
    refine fun x => ⟨Algebra.IsIntegral.isIntegral x, fun hsep => ?_⟩
    have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E
    rw [hdeg]; rw [mul_eq_one]; rw [(finSepDegree_adjoin_simple_eq_finrank_iff F E x
    

中文:
定理 isPurelyInseparable_of_finSepDegree_eq_one
  证明: by
  by_cases H : Algebra.IsAlgebraic F E
  · rw [isPurelyInseparable_iff]
    refine fun x => ⟨Algebra.IsIntegral.isIntegral x, fun hsep => ?_⟩
    have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E
    rw [hdeg]; rw [mul_eq_one]; rw [(finSepDegree_adjoin_simple_eq_finrank_iff F E x
    

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.isAlgebraic, Algebra.IsIntegral.isIntegral, Algebra.transcendental_iff_not_isAlgebraic, IntermediateField, IntermediateField.finrank_eq_one_iff, IsAlgebraic, IsIntegral, finSepD, finSepDegree_adjoin_simple_eq_finrank_iff, finSepDegree_mul_finSepDegree_of_isAlgebraic, finrank_eq_one_iff, isAlgebraic, isIntegral, isPurelyInseparable_iff, mem_adjoin_simple_self, mul_eq_one, transcendental_iff_not_isAlgebraic
-/
theorem isPurelyInseparable_of_finSepDegree_eq_one
    (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E := by
  by_cases H : Algebra.IsAlgebraic F E
  · rw [isPurelyInseparable_iff]
    refine fun x => ⟨Algebra.IsIntegral.isIntegral x, fun hsep => ?_⟩
    have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E
    rw [hdeg]; rw [mul_eq_one]; rw [(finSepDegree_adjoin_simple_eq_finrank_iff F E x
        (Algebra.IsAlgebraic.isAlgebraic x)).2 hsep]; rw [IntermediateField.finrank_eq_one_iff] at this
    simpa only [this.1] using! mem_adjoin_simple_self F x
  · rw [← Algebra.transcendental_iff_not_isAlgebraic] at H
    simp [finSepDegree_eq_zero_of_transcendental F E] at hdeg

namespace IsPurelyInseparable

variable [IsPurelyInseparable F E] (R L : Type*) [CommSemiring R] [Algebra R F] [Algebra R E]

/--
theorem `injective_comp_algebraMap` / 定理 `injective_comp_algebraMap`

English:
theorem injective_comp_algebraMap
  given: [CommRing L] [IsReduced L]
  proof: fun f g heq => by
  ext x
  let q := ringExpChar F
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.pow_mem F q x
  replace heq := congr($heq y)
  simp_rw [RingHom.comp_apply, h, map_pow] at heq
  nontriviality L
  have := expChar_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  exact iterateFr

中文:
定理 injective_comp_algebraMap
  条件: [CommRing L] [IsReduced L]
  证明: fun f g heq => by
  ext x
  let q := ringExpChar F
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.pow_mem F q x
  replace heq := congr($heq y)
  simp_rw [RingHom.comp_apply, h, map_pow] at heq
  nontriviality L
  have := expChar_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  exact iterateFr

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.pow_mem, RingHom, RingHom.comp_apply, algebraMap, comp_apply, expChar_of_injective_ringHom, f.comp, injective, iterateFrobenius_inj, map_pow, nontriviality, pow_mem, replace, ringExpChar, simp_rw
-/
theorem injective_comp_algebraMap [CommRing L] [IsReduced L] :
    Function.Injective fun f : E ->+* L => f.comp (algebraMap F E) := fun f g heq => by
  ext x
  let q := ringExpChar F
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.pow_mem F q x
  replace heq := congr($heq y)
  simp_rw [RingHom.comp_apply, h, map_pow] at heq
  nontriviality L
  have := expChar_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  exact iterateFrobenius_inj L q n heq

/--
theorem `injective_restrictDomain` / 定理 `injective_restrictDomain`

English:
theorem injective_restrictDomain
  given: [CommRing L] [IsReduced L] [Algebra R L] [IsScalarTower R F E]
  proof: fun _ _ eq =>
AlgHom.coe_ringHom_injective injective_comp_algebraMap F E L congr_arg AlgHom.toRingHom eq

中文:
定理 injective_restrictDomain
  条件: [CommRing L] [IsReduced L] [Algebra R L] [IsScalarTower R F E]
  证明: fun _ _ eq =>
AlgHom.coe_ringHom_injective injective_comp_algebraMap F E L congr_arg AlgHom.toRingHom eq
-/
theorem injective_restrictDomain [CommRing L] [IsReduced L] [Algebra R L] [IsScalarTower R F E] :
    Function.Injective (AlgHom.domRestrict (A := R) F (C := E) (D := L)) := fun _ _ eq =>
AlgHom.coe_ringHom_injective injective_comp_algebraMap F E L congr_arg AlgHom.toRingHom eq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: L] [PerfectField L] [Algebra F L] : Nonempty (E ->ₐ[F] L)
  body: nonempty_algHom_of_splits fun x => ⟨IsPurelyInseparable.isIntegral' _ _,
    have ⟨q, _⟩ := ExpChar.exists F
    PerfectField.splits_of_natSepDegree_eq_one (algebraMap F L)
      ((minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mpr <|
        IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x)⟩

中文:
实例 [Field
  签名: L] [PerfectField L] [Algebra F L] : Nonempty (E ->ₐ[F] L)
  定义体: nonempty_algHom_of_splits fun x => ⟨IsPurelyInseparable.isIntegral' _ _,
    have ⟨q, _⟩ := ExpChar.exists F
    PerfectField.splits_of_natSepDegree_eq_one (algebraMap F L)
      ((minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mpr <|
        IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x)⟩

Depends on / 依赖: ExpChar, ExpChar.exists, IsPurelyInseparable, IsPurelyInseparable.isIntegral, IsPurelyInseparable.minpoly_eq_X_pow_sub_C, PerfectField, PerfectField.splits_of_natSepDegree_eq_one, algebraMap, isIntegral, minpoly, minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C, minpoly_eq_X_pow_sub_C, natSepDegree_eq_one_iff_eq_X_pow_sub_C, nonempty_algHom_of_splits, splits_of_natSepDegree_eq_one
-/
instance [Field L] [PerfectField L] [Algebra F L] : Nonempty (E ->ₐ[F] L) :=
  nonempty_algHom_of_splits fun x => ⟨IsPurelyInseparable.isIntegral' _ _,
    have ⟨q, _⟩ := ExpChar.exists F
    PerfectField.splits_of_natSepDegree_eq_one (algebraMap F L)
      ((minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mpr <|
        IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x)⟩

/--
theorem `bijective_comp_algebraMap` / 定理 `bijective_comp_algebraMap`

English:
theorem bijective_comp_algebraMap
  given: [Field L] [PerfectField L]
  proof: ⟨injective_comp_algebraMap F E L, fun g => let _ := g.toAlgebra
    ⟨_, (Classical.arbitrary <| E ->ₐ[F] L).comp_algebraMap⟩⟩

中文:
定理 bijective_comp_algebraMap
  条件: [Field L] [PerfectField L]
  证明: ⟨injective_comp_algebraMap F E L, fun g => let _ := g.toAlgebra
    ⟨_, (Classical.arbitrary <| E ->ₐ[F] L).comp_algebraMap⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, comp_algebraMap, g.toAlgebra, injective_comp_algebraMap, toAlgebra
-/
theorem bijective_comp_algebraMap [Field L] [PerfectField L] :
    Function.Bijective fun f : E ->+* L => f.comp (algebraMap F E) :=
  ⟨injective_comp_algebraMap F E L, fun g => let _ := g.toAlgebra
    ⟨_, (Classical.arbitrary <| E ->ₐ[F] L).comp_algebraMap⟩⟩

/--
theorem `bijective_restrictDomain` / 定理 `bijective_restrictDomain`

English:
theorem bijective_restrictDomain
  given: [Field L] [PerfectField L] [Algebra R L] [IsScalarTower R F E]
  proof: ⟨injective_restrictDomain F E R L, fun g => let _ := g.toAlgebra
    let f := Classical.arbitrary (E ->ₐ[F] L)
    ⟨f.restrictScalars R, AlgHom.coe_ringHom_injective f.comp_algebraMap⟩⟩

中文:
定理 bijective_restrictDomain
  条件: [Field L] [PerfectField L] [Algebra R L] [IsScalarTower R F E]
  证明: ⟨injective_restrictDomain F E R L, fun g => let _ := g.toAlgebra
    let f := Classical.arbitrary (E ->ₐ[F] L)
    ⟨f.restrictScalars R, AlgHom.coe_ringHom_injective f.comp_algebraMap⟩⟩
-/
theorem bijective_restrictDomain [Field L] [PerfectField L] [Algebra R L] [IsScalarTower R F E] :
    Function.Bijective (AlgHom.domRestrict (A := R) F (C := E) (D := L)) :=
  ⟨injective_restrictDomain F E R L, fun g => let _ := g.toAlgebra
    let f := Classical.arbitrary (E ->ₐ[F] L)
    ⟨f.restrictScalars R, AlgHom.coe_ringHom_injective f.comp_algebraMap⟩⟩

end IsPurelyInseparable

/--
Instance `instSubsingletonAlgHomOfIsPurelyInseparable` / 实例 `instSubsingletonAlgHomOfIsPurelyInseparable`

English:
instance instSubsingletonAlgHomOfIsPurelyInseparable
  signature: [IsPurelyInseparable F E] (L : Type w)
  body: AlgHom.coe_ringHom_injective
    IsPurelyInseparable.injective_comp_algebraMap F E L (by simp_rw [AlgHom.comp_algebraMap])

中文:
实例 instSubsingletonAlgHomOfIsPurelyInseparable
  签名: [IsPurelyInseparable F E] (L : Type w)
  定义体: AlgHom.coe_ringHom_injective
    IsPurelyInseparable.injective_comp_algebraMap F E L (by simp_rw [AlgHom.comp_algebraMap])

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, coe_ringHom_injective
-/
instance instSubsingletonAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] : Subsingleton (E ->ₐ[F] L) where
allEq f g := AlgHom.coe_ringHom_injective
    IsPurelyInseparable.injective_comp_algebraMap F E L (by simp_rw [AlgHom.comp_algebraMap])

/--
Instance `instUniqueAlgHomOfIsPurelyInseparable` / 实例 `instUniqueAlgHomOfIsPurelyInseparable`

English:
instance instUniqueAlgHomOfIsPurelyInseparable
  signature: [IsPurelyInseparable F E] (L : Type w)
  body: uniqueOfSubsingleton (IsScalarTower.toAlgHom F E L)

中文:
实例 instUniqueAlgHomOfIsPurelyInseparable
  签名: [IsPurelyInseparable F E] (L : Type w)
  定义体: uniqueOfSubsingleton (IsScalarTower.toAlgHom F E L)

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, toAlgHom, uniqueOfSubsingleton
-/
instance instUniqueAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] [Algebra E L] [IsScalarTower F E L] :
    Unique (E ->ₐ[F] L) := uniqueOfSubsingleton (IsScalarTower.toAlgHom F E L)

/--
Instance `instUniqueEmbOfIsPurelyInseparable` / 实例 `instUniqueEmbOfIsPurelyInseparable`

English:
instance instUniqueEmbOfIsPurelyInseparable
  signature: [IsPurelyInseparable F E]
  body: instUniqueAlgHomOfIsPurelyInseparable F E _

中文:
实例 instUniqueEmbOfIsPurelyInseparable
  签名: [IsPurelyInseparable F E]
  定义体: instUniqueAlgHomOfIsPurelyInseparable F E _

Depends on / 依赖: instUniqueAlgHomOfIsPurelyInseparable
-/
instance instUniqueEmbOfIsPurelyInseparable [IsPurelyInseparable F E] :
    Unique (Emb F E) := instUniqueAlgHomOfIsPurelyInseparable F E _

/--
theorem `IsPurelyInseparable.finSepDegree_eq_one` / 定理 `IsPurelyInseparable.finSepDegree_eq_one`

English:
theorem IsPurelyInseparable.finSepDegree_eq_one
  given: [IsPurelyInseparable F E]
  proof: Nat.card_unique

中文:
定理 IsPurelyInseparable.finSepDegree_eq_one
  条件: [IsPurelyInseparable F E]
  证明: Nat.card_unique

Depends on / 依赖: Nat.card_unique, card_unique
-/
theorem IsPurelyInseparable.finSepDegree_eq_one [IsPurelyInseparable F E] :
    finSepDegree F E = 1 := Nat.card_unique

/--
theorem `IsPurelyInseparable.sepDegree_eq_one` / 定理 `IsPurelyInseparable.sepDegree_eq_one`

English:
theorem IsPurelyInseparable.sepDegree_eq_one
  given: [IsPurelyInseparable F E]
  proof: by
  rw [sepDegree]; rw [separableClosure.eq_bot_of_isPurelyInseparable]; rw [IntermediateField.rank_bot]

中文:
定理 IsPurelyInseparable.sepDegree_eq_one
  条件: [IsPurelyInseparable F E]
  证明: by
  rw [sepDegree]; rw [separableClosure.eq_bot_of_isPurelyInseparable]; rw [IntermediateField.rank_bot]

Depends on / 依赖: IntermediateField, IntermediateField.rank_bot, eq_bot_of_isPurelyInseparable, rank_bot, sepDegree, separableClosure, separableClosure.eq_bot_of_isPurelyInseparable
-/
theorem IsPurelyInseparable.sepDegree_eq_one [IsPurelyInseparable F E] :
    sepDegree F E = 1 := by
  rw [sepDegree]; rw [separableClosure.eq_bot_of_isPurelyInseparable]; rw [IntermediateField.rank_bot]

/--
theorem `IsPurelyInseparable.insepDegree_eq` / 定理 `IsPurelyInseparable.insepDegree_eq`

English:
theorem IsPurelyInseparable.insepDegree_eq
  given: [IsPurelyInseparable F E]
  proof: by
  rw [insepDegree]; rw [separableClosure.eq_bot_of_isPurelyInseparable]; rw [rank_bot']

中文:
定理 IsPurelyInseparable.insepDegree_eq
  条件: [IsPurelyInseparable F E]
  证明: by
  rw [insepDegree]; rw [separableClosure.eq_bot_of_isPurelyInseparable]; rw [rank_bot']

Depends on / 依赖: eq_bot_of_isPurelyInseparable, insepDegree, rank_bot, separableClosure, separableClosure.eq_bot_of_isPurelyInseparable
-/
theorem IsPurelyInseparable.insepDegree_eq [IsPurelyInseparable F E] :
    insepDegree F E = Module.rank F E := by
  rw [insepDegree]; rw [separableClosure.eq_bot_of_isPurelyInseparable]; rw [rank_bot']

/--
theorem `IsPurelyInseparable.finInsepDegree_eq` / 定理 `IsPurelyInseparable.finInsepDegree_eq`

English:
theorem IsPurelyInseparable.finInsepDegree_eq
  given: [IsPurelyInseparable F E]
  proof: congr(Cardinal.toNat $(insepDegree_eq F E))

中文:
定理 IsPurelyInseparable.finInsepDegree_eq
  条件: [IsPurelyInseparable F E]
  证明: congr(Cardinal.toNat $(insepDegree_eq F E))

Depends on / 依赖: Cardinal, Cardinal.toNat, insepDegree_eq
-/
theorem IsPurelyInseparable.finInsepDegree_eq [IsPurelyInseparable F E] :
    finInsepDegree F E = finrank F E := congr(Cardinal.toNat $(insepDegree_eq F E))

/--
theorem `isPurelyInseparable_iff_finSepDegree_eq_one` / 定理 `isPurelyInseparable_iff_finSepDegree_eq_one`

English:
theorem isPurelyInseparable_iff_finSepDegree_eq_one
  proof: ⟨fun _ => IsPurelyInseparable.finSepDegree_eq_one F E,
    fun h => isPurelyInseparable_of_finSepDegree_eq_one h⟩

中文:
定理 isPurelyInseparable_iff_finSepDegree_eq_one
  证明: ⟨fun _ => IsPurelyInseparable.finSepDegree_eq_one F E,
    fun h => isPurelyInseparable_of_finSepDegree_eq_one h⟩

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.finSepDegree_eq_one, finSepDegree_eq_one, isPurelyInseparable_of_finSepDegree_eq_one
-/
theorem isPurelyInseparable_iff_finSepDegree_eq_one :
    IsPurelyInseparable F E ↔ finSepDegree F E = 1 :=
  ⟨fun _ => IsPurelyInseparable.finSepDegree_eq_one F E,
    fun h => isPurelyInseparable_of_finSepDegree_eq_one h⟩

/--
theorem `isPurelyInseparable_iff_subsingleton_emb` / 定理 `isPurelyInseparable_iff_subsingleton_emb`

English:
theorem isPurelyInseparable_iff_subsingleton_emb
  proof: by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one]; rw [Field.finSepDegree]; rw [Nat.card_eq_one_iff_unique]; rw [and_iff_left_iff_imp]
  infer_instance

中文:
定理 isPurelyInseparable_iff_subsingleton_emb
  证明: by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one]; rw [Field.finSepDegree]; rw [Nat.card_eq_one_iff_unique]; rw [and_iff_left_iff_imp]
  infer_instance

Depends on / 依赖: Field.finSepDegree, Nat.card_eq_one_iff_unique, and_iff_left_iff_imp, card_eq_one_iff_unique, finSepDegree, infer_instance, isPurelyInseparable_iff_finSepDegree_eq_one
-/
theorem isPurelyInseparable_iff_subsingleton_emb :
    IsPurelyInseparable F E ↔ Subsingleton (Field.Emb F E) := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one]; rw [Field.finSepDegree]; rw [Nat.card_eq_one_iff_unique]; rw [and_iff_left_iff_imp]
  infer_instance

/--
lemma `isSeparable_iff_finInsepDegree_eq_one` / 引理 `isSeparable_iff_finInsepDegree_eq_one`

English:
lemma isSeparable_iff_finInsepDegree_eq_one
  proof: by
  rw [← separableClosure.eq_top_iff]; rw [← IntermediateField.finrank_eq_one_iff_eq_top]; rw [finInsepDegree]

中文:
引理 isSeparable_iff_finInsepDegree_eq_one
  证明: by
  rw [← separableClosure.eq_top_iff]; rw [← IntermediateField.finrank_eq_one_iff_eq_top]; rw [finInsepDegree]

Depends on / 依赖: IntermediateField, IntermediateField.finrank_eq_one_iff_eq_top, eq_top_iff, finInsepDegree, finrank_eq_one_iff_eq_top, separableClosure, separableClosure.eq_top_iff
-/
lemma isSeparable_iff_finInsepDegree_eq_one :
    Algebra.IsSeparable F K ↔ finInsepDegree F K = 1 := by
  rw [← separableClosure.eq_top_iff]; rw [← IntermediateField.finrank_eq_one_iff_eq_top]; rw [finInsepDegree]

variable {F E} in
/--
theorem `isPurelyInseparable_iff_fd_isPurelyInseparable` / 定理 `isPurelyInseparable_iff_fd_isPurelyInseparable`

English:
theorem isPurelyInseparable_iff_fd_isPurelyInseparable
  given: [Algebra.IsAlgebraic F E]
  proof: by
  refine ⟨fun _ _ _ => IsPurelyInseparable.tower_bot F _ E,
    fun h => isPurelyInseparable_iff.2 fun x => ?_⟩
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  refine ⟨hx, fun _ => ?_⟩
obtain ⟨y, h⟩ := (h _ (adjoin.finiteDimensional hx)).inseparable' _
    show Separable (minpoly 

中文:
定理 isPurelyInseparable_iff_fd_isPurelyInseparable
  条件: [Algebra.IsAlgebraic F E]
  证明: by
  refine ⟨fun _ _ _ => IsPurelyInseparable.tower_bot F _ E,
    fun h => isPurelyInseparable_iff.2 fun x => ?_⟩
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  refine ⟨hx, fun _ => ?_⟩
obtain ⟨y, h⟩ := (h _ (adjoin.finiteDimensional hx)).inseparable' _
    show Separable (minpoly 

Depends on / 依赖: AdjoinSimple, AdjoinSimple.gen, Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, IsPurelyInseparable, IsPurelyInseparable.tower_bot, Separable, adjoin, adjoin.finiteDimensional, algebraMap, congr_arg, finiteDimensional, inseparable, isIntegral, isPurelyInseparable_iff, minpoly, minpoly_eq, tower_bot
-/
theorem isPurelyInseparable_iff_fd_isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable F E ↔
    forall L : IntermediateField F E, FiniteDimensional F L -> IsPurelyInseparable F L := by
  refine ⟨fun _ _ _ => IsPurelyInseparable.tower_bot F _ E,
    fun h => isPurelyInseparable_iff.2 fun x => ?_⟩
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  refine ⟨hx, fun _ => ?_⟩
obtain ⟨y, h⟩ := (h _ (adjoin.finiteDimensional hx)).inseparable' _
    show Separable (minpoly F (AdjoinSimple.gen F x)) by rwa [minpoly_eq]
  exact ⟨y, congr_arg (algebraMap _ E) h⟩

/--
Instance `IsPurelyInseparable.normal` / 实例 `IsPurelyInseparable.normal`

English:
instance IsPurelyInseparable.normal
  signature: [IsPurelyInseparable F E]
  body: isAlgebraic F E
  splits' x := by
    obtain ⟨n, h⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow F (ringExpChar F) x
    rw [h]
    exact Splits.pow (Splits.X_sub_C _) _

中文:
实例 IsPurelyInseparable.normal
  签名: [IsPurelyInseparable F E]
  定义体: isAlgebraic F E
  splits' x := by
    obtain ⟨n, h⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow F (ringExpChar F) x
    rw [h]
    exact Splits.pow (Splits.X_sub_C _) _

Depends on / 依赖: isAlgebraic
-/
instance IsPurelyInseparable.normal [IsPurelyInseparable F E] : Normal F E where
  toIsAlgebraic := isAlgebraic F E
  splits' x := by
    obtain ⟨n, h⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow F (ringExpChar F) x
    rw [h]
    exact Splits.pow (Splits.X_sub_C _) _

/-- If `E / F` is algebraic, then `E` is purely inseparable over the
separable closure of `F` in `E`. -/
@[stacks 030K "$E/E_{sep}$ is purely inseparable."]
/--
Instance `separableClosure.isPurelyInseparable` / 实例 `separableClosure.isPurelyInseparable`

English:
instance separableClosure.isPurelyInseparable
  signature: [Algebra.IsAlgebraic F E]
  body: isPurelyInseparable_iff.2 fun x => by
  set L := separableClosure F E
  refine ⟨(IsAlgebraic.tower_top L (Algebra.IsAlgebraic.isAlgebraic (R := F) x)).isIntegral,
    fun h => ?_⟩
  have := (isSeparable_adjoin_simple_iff_isSeparable L E).2 h
  have : Algebra.IsSeparable F (restrictScalars F L⟮x⟯) :=

中文:
实例 separableClosure.isPurelyInseparable
  签名: [Algebra.IsAlgebraic F E]
  定义体: isPurelyInseparable_iff.2 fun x => by
  set L := separableClosure F E
  refine ⟨(IsAlgebraic.tower_top L (Algebra.IsAlgebraic.isAlgebraic (R := F) x)).isIntegral,
    fun h => ?_⟩
  have := (isSeparable_adjoin_simple_iff_isSeparable L E).2 h
  have : Algebra.IsSeparable F (restrictScalars F L⟮x⟯) :=

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, Algebra.IsSeparable, Algebra.IsSeparable.trans, IsAlgebraic, IsAlgebraic.tower_top, IsSeparable, isAlgebraic, isIntegral, isPurelyInseparable_iff, isSeparable_adjoin_simple_iff_isSeparable, isSeparable_of_mem_isSeparable, mem_adjoin_simple_self, mem_separableClosure_iff, restrictScalars, separableClosure, tower_top
-/
instance separableClosure.isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable (separableClosure F E) E := isPurelyInseparable_iff.2 fun x => by
  set L := separableClosure F E
  refine ⟨(IsAlgebraic.tower_top L (Algebra.IsAlgebraic.isAlgebraic (R := F) x)).isIntegral,
    fun h => ?_⟩
  have := (isSeparable_adjoin_simple_iff_isSeparable L E).2 h
  have : Algebra.IsSeparable F (restrictScalars F L⟮x⟯) := Algebra.IsSeparable.trans F L L⟮x⟯
  have hx : x in L⟮x⟯.restrictScalars F := mem_adjoin_simple_self _ x
exact ⟨⟨x, mem_separableClosure_iff.2 isSeparable_of_mem_isSeparable F E hx⟩, rfl⟩

open Cardinal in
/--
theorem `Field.Emb.cardinal_separableClosure` / 定理 `Field.Emb.cardinal_separableClosure`

English:
theorem Field.Emb.cardinal_separableClosure
  given: [Algebra.IsAlgebraic F E]
  proof: by
  rw [← (embProdEmbOfIsAlgebraic F (separableClosure F E) E).cardinal_eq]; rw [mk_prod]; rw [mk_eq_one (Emb _ E)]; rw [lift_one]; rw [mul_one]; rw [lift_id]

中文:
定理 Field.Emb.cardinal_separableClosure
  条件: [Algebra.IsAlgebraic F E]
  证明: by
  rw [← (embProdEmbOfIsAlgebraic F (separableClosure F E) E).cardinal_eq]; rw [mk_prod]; rw [mk_eq_one (Emb _ E)]; rw [lift_one]; rw [mul_one]; rw [lift_id]

Depends on / 依赖: cardinal_eq, embProdEmbOfIsAlgebraic, lift_id, lift_one, mk_eq_one, mk_prod, mul_one, separableClosure
-/
theorem Field.Emb.cardinal_separableClosure [Algebra.IsAlgebraic F E] :
    #(Field.Emb F <| separableClosure F E) = #(Field.Emb F E) := by
  rw [← (embProdEmbOfIsAlgebraic F (separableClosure F E) E).cardinal_eq]; rw [mk_prod]; rw [mk_eq_one (Emb _ E)]; rw [lift_one]; rw [mul_one]; rw [lift_id]

/--
lemma `finInsepDegree_eq_pow` / 引理 `finInsepDegree_eq_pow`

English:
lemma finInsepDegree_eq_pow
  given: (q : Nat) [ExpChar F q] [FiniteDimensional F E]
  proof: IsPurelyInseparable.finrank_eq_pow ..

中文:
引理 finInsepDegree_eq_pow
  条件: (q : 自然数) [ExpChar F q] [FiniteDimensional F E]
  证明: IsPurelyInseparable.finrank_eq_pow ..

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.finrank_eq_pow, finrank_eq_pow
-/
lemma finInsepDegree_eq_pow (q : Nat) [ExpChar F q] [FiniteDimensional F E] :
    exists n, finInsepDegree F E = q ^ n :=
  IsPurelyInseparable.finrank_eq_pow ..

/--
theorem `separableClosure_le` / 定理 `separableClosure_le`

English:
theorem separableClosure_le
  statement: (L : IntermediateField F E)
  proof: fun x hx => by
obtain ⟨y, rfl⟩ := h.inseparable' _
    IsSeparable.tower_top L (mem_separableClosure_iff.1 hx)
  exact y.2

中文:
定理 separableClosure_le
  结论: (L : 整数ermediateField F E)
  证明: fun x hx => by
obtain ⟨y, rfl⟩ := h.inseparable' _
    IsSeparable.tower_top L (mem_separableClosure_iff.1 hx)
  exact y.2

Depends on / 依赖: IsSeparable, IsSeparable.tower_top, h.inseparable, inseparable, mem_separableClosure_iff, tower_top
-/
theorem separableClosure_le (L : IntermediateField F E)
    [h : IsPurelyInseparable L E] : separableClosure F E <= L := fun x hx => by
obtain ⟨y, rfl⟩ := h.inseparable' _
    IsSeparable.tower_top L (mem_separableClosure_iff.1 hx)
  exact y.2

/--
theorem `separableClosure_le_iff` / 定理 `separableClosure_le_iff`

English:
theorem separableClosure_le_iff
  given: [Algebra.IsAlgebraic F E] (L : IntermediateField F E)
  proof: by
  refine ⟨fun h => ?_, fun _ => separableClosure_le F E L⟩
  let := (inclusion h).toAlgebra
  let : SMul (separableClosure F E) L := Algebra.toSMul
  have : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableCl

中文:
定理 separableClosure_le_iff
  条件: [Algebra.IsAlgebraic F E] (L : 整数ermediateField F E)
  证明: by
  refine ⟨fun h => ?_, fun _ => separableClosure_le F E L⟩
  let := (inclusion h).toAlgebra
  let : SMul (separableClosure F E) L := Algebra.toSMul
  have : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableCl

Depends on / 依赖: Algebra, Algebra.toSMul, IsPurelyInseparable, IsPurelyInseparable.tower_top, IsScalarTower, IsScalarTower.of_algebraMap_eq, inclusion, of_algebraMap_eq, separableClosure, separableClosure_le, toAlgebra, toSMul, tower_top
-/
theorem separableClosure_le_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    separableClosure F E <= L ↔ IsPurelyInseparable L E := by
  refine ⟨fun h => ?_, fun _ => separableClosure_le F E L⟩
  let := (inclusion h).toAlgebra
  let : SMul (separableClosure F E) L := Algebra.toSMul
  have : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableClosure F E) L E

/--
theorem `eq_separableClosure` / 定理 `eq_separableClosure`

English:
theorem eq_separableClosure
  statement: (L : IntermediateField F E)
  proof: le_antisymm (le_separableClosure F E L) (separableClosure_le F E L)

中文:
定理 eq_separableClosure
  结论: (L : 整数ermediateField F E)
  证明: le_antisymm (le_separableClosure F E L) (separableClosure_le F E L)

Depends on / 依赖: le_antisymm, le_separableClosure, separableClosure_le
-/
theorem eq_separableClosure (L : IntermediateField F E)
    [Algebra.IsSeparable F L] [IsPurelyInseparable L E] : L = separableClosure F E :=
  le_antisymm (le_separableClosure F E L) (separableClosure_le F E L)

open separableClosure in
/--
theorem `eq_separableClosure_iff` / 定理 `eq_separableClosure_iff`

English:
theorem eq_separableClosure_iff
  given: [Algebra.IsAlgebraic F E] (L : IntermediateField F E)
  proof: ⟨by rintro rfl; exact ⟨isSeparable F E, isPurelyInseparable F E⟩,
   fun ⟨_, _⟩ => eq_separableClosure F E L⟩

中文:
定理 eq_separableClosure_iff
  条件: [Algebra.IsAlgebraic F E] (L : 整数ermediateField F E)
  证明: ⟨by rintro rfl; exact ⟨isSeparable F E, isPurelyInseparable F E⟩,
   fun ⟨_, _⟩ => eq_separableClosure F E L⟩

Depends on / 依赖: eq_separableClosure, isPurelyInseparable, isSeparable
-/
theorem eq_separableClosure_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    L = separableClosure F E ↔ Algebra.IsSeparable F L ∧ IsPurelyInseparable L E :=
  ⟨by rintro rfl; exact ⟨isSeparable F E, isPurelyInseparable F E⟩,
   fun ⟨_, _⟩ => eq_separableClosure F E L⟩

/--
theorem `IsPurelyInseparable.of_injective_comp_algebraMap` / 定理 `IsPurelyInseparable.of_injective_comp_algebraMap`

English:
theorem IsPurelyInseparable.of_injective_comp_algebraMap
  statement: (L : Type w) [Field L] [IsAlgClosed L]
  proof: by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one]; rw [finSepDegree]; rw [Nat.card_eq_one_iff_unique]
  let := (Classical.arbitrary (E ->+* L)).toAlgebra
  let j : AlgebraicClosure E ->ₐ[E] L := IsAlgClosed.lift
exact ⟨⟨fun f g => DFunLike.ext' j.injective.comp_left (congr_arg (⇑) <|
    @h (j.t

中文:
定理 IsPurelyInseparable.of_injective_comp_algebraMap
  结论: (L : Type w) [Field L] [IsAlgClosed L]
  证明: by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one]; rw [finSepDegree]; rw [Nat.card_eq_one_iff_unique]
  let := (Classical.arbitrary (E ->+* L)).toAlgebra
  let j : AlgebraicClosure E ->ₐ[E] L := IsAlgClosed.lift
exact ⟨⟨fun f g => DFunLike.ext' j.injective.comp_left (congr_arg (⇑) <|
    @h (j.t

Depends on / 依赖: AlgebraicClosure, Classical, Classical.arbitrary, DFunLike, DFunLike.ext, IsAlgClosed, IsAlgClosed.lift, Nat.card_eq_one_iff_unique, arbitrary, card_eq_one_iff_unique, comp_left, congr_arg, finSepDegree, injective, isPurelyInseparable_iff_finSepDegree_eq_one, j.injective.comp_left, j.toRingHom.comp, toAlgebra, toRingHom
-/
theorem IsPurelyInseparable.of_injective_comp_algebraMap (L : Type w) [Field L] [IsAlgClosed L]
    [Nonempty (E ->+* L)] (h : Function.Injective fun f : E ->+* L => f.comp (algebraMap F E)) :
    IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one]; rw [finSepDegree]; rw [Nat.card_eq_one_iff_unique]
  let := (Classical.arbitrary (E ->+* L)).toAlgebra
  let j : AlgebraicClosure E ->ₐ[E] L := IsAlgClosed.lift
exact ⟨⟨fun f g => DFunLike.ext' j.injective.comp_left (congr_arg (⇑) <|
    @h (j.toRingHom.comp f) (j.toRingHom.comp g) (by ext; simp))⟩, inferInstance⟩

end Field

namespace IntermediateField

/--
Instance `isPurelyInseparable_bot` / 实例 `isPurelyInseparable_bot`

English:
instance isPurelyInseparable_bot
  signature: : IsPurelyInseparable F (⊥ : IntermediateField F E)
  body: (botEquiv F E).symm.isPurelyInseparable

中文:
实例 isPurelyInseparable_bot
  签名: : IsPurelyInseparable F (⊥ : 整数ermediateField F E)
  定义体: (botEquiv F E).symm.isPurelyInseparable

Depends on / 依赖: botEquiv, isPurelyInseparable, symm.isPurelyInseparable
-/
instance isPurelyInseparable_bot : IsPurelyInseparable F (⊥ : IntermediateField F E) :=
  (botEquiv F E).symm.isPurelyInseparable

end IntermediateField

/--
theorem `isSepClosed_iff_isPurelyInseparable_algebraicClosure` / 定理 `isSepClosed_iff_isPurelyInseparable_algebraicClosure`

English:
theorem isSepClosed_iff_isPurelyInseparable_algebraicClosure
  given: [IsAlgClosure F E]
  proof: ⟨fun _ => inferInstance, fun H => by
    have := IsAlgClosure.isAlgClosed F (K := E)
    rwa [← separableClosure.eq_bot_iff, IsSepClosed.separableClosure_eq_bot_iff] at H⟩

中文:
定理 isSepClosed_iff_isPurelyInseparable_algebraicClosure
  条件: [IsAlgClosure F E]
  证明: ⟨fun _ => inferInstance, fun H => by
    have := IsAlgClosure.isAlgClosed F (K := E)
    rwa [← separableClosure.eq_bot_iff, IsSepClosed.separableClosure_eq_bot_iff] at H⟩

Depends on / 依赖: IsAlgClosure, IsAlgClosure.isAlgClosed, IsSepClosed, IsSepClosed.separableClosure_eq_bot_iff, eq_bot_iff, isAlgClosed, separableClosure, separableClosure.eq_bot_iff, separableClosure_eq_bot_iff
-/
theorem isSepClosed_iff_isPurelyInseparable_algebraicClosure [IsAlgClosure F E] :
    IsSepClosed F ↔ IsPurelyInseparable F E :=
  ⟨fun _ => inferInstance, fun H => by
    have := IsAlgClosure.isAlgClosed F (K := E)
    rwa [← separableClosure.eq_bot_iff, IsSepClosed.separableClosure_eq_bot_iff] at H⟩

variable {F E} in
/--
theorem `Algebra.IsAlgebraic.isSepClosed` / 定理 `Algebra.IsAlgebraic.isSepClosed`

English:
theorem Algebra.IsAlgebraic.isSepClosed
  statement: [Algebra.IsAlgebraic F E]
  proof: have : Algebra.IsAlgebraic F (AlgebraicClosure E) := .trans F E _
  (isSepClosed_iff_isPurelyInseparable_algebraicClosure E _).mpr
    (IsPurelyInseparable.tower_top F E <| AlgebraicClosure E)

中文:
定理 Algebra.IsAlgebraic.isSepClosed
  结论: [Algebra.IsAlgebraic F E]
  证明: have : Algebra.IsAlgebraic F (AlgebraicClosure E) := .trans F E _
  (isSepClosed_iff_isPurelyInseparable_algebraicClosure E _).mpr
    (IsPurelyInseparable.tower_top F E <| AlgebraicClosure E)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, AlgebraicClosure, IsAlgebraic, IsPurelyInseparable, IsPurelyInseparable.tower_top, isSepClosed_iff_isPurelyInseparable_algebraicClosure, tower_top
-/
theorem Algebra.IsAlgebraic.isSepClosed [Algebra.IsAlgebraic F E]
    [IsSepClosed F] : IsSepClosed E :=
  have : Algebra.IsAlgebraic F (AlgebraicClosure E) := .trans F E _
  (isSepClosed_iff_isPurelyInseparable_algebraicClosure E _).mpr
    (IsPurelyInseparable.tower_top F E <| AlgebraicClosure E)

namespace Field

/-- If `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to `Field.sepDegree F E`
as a natural number. This means that the cardinality of `Field.Emb F E` and the degree of
`(separableClosure F E) / F` are both finite or infinite, and when they are finite, they
coincide. -/
@[stacks 09HJ "`sepDegree` is defined as the right-hand side of 09HJ"]
/--
theorem `finSepDegree_eq` / 定理 `finSepDegree_eq`

English:
theorem finSepDegree_eq
  given: [Algebra.IsAlgebraic F E]
  proof: by
.symm have h := finSepDegree_mul_finSepDegree_of_isAlgebraic F (separableClosure F E) E
  rwa [finSepDegree_eq_finrank_of_isSeparable F (separableClosure F E),
    IsPurelyInseparable.finSepDegree_eq_one (separableClosure F E) E, mul_one] at h

中文:
定理 finSepDegree_eq
  条件: [Algebra.IsAlgebraic F E]
  证明: by
.symm have h := finSepDegree_mul_finSepDegree_of_isAlgebraic F (separableClosure F E) E
  rwa [finSepDegree_eq_finrank_of_isSeparable F (separableClosure F E),
    IsPurelyInseparable.finSepDegree_eq_one (separableClosure F E) E, mul_one] at h

Depends on / 依赖: IsPurelyInseparable, IsPurelyInseparable.finSepDegree_eq_one, finSepDegree_eq_finrank_of_isSeparable, finSepDegree_eq_one, finSepDegree_mul_finSepDegree_of_isAlgebraic, mul_one, separableClosure
-/
theorem finSepDegree_eq [Algebra.IsAlgebraic F E] :
    finSepDegree F E = Cardinal.toNat (sepDegree F E) := by
.symm have h := finSepDegree_mul_finSepDegree_of_isAlgebraic F (separableClosure F E) E
  rwa [finSepDegree_eq_finrank_of_isSeparable F (separableClosure F E),
    IsPurelyInseparable.finSepDegree_eq_one (separableClosure F E) E, mul_one] at h

/--
theorem `finSepDegree_mul_finInsepDegree` / 定理 `finSepDegree_mul_finInsepDegree`

English:
theorem finSepDegree_mul_finInsepDegree
  statement: finSepDegree F E * finInsepDegree F E = finrank F E
  proof: by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E] at this
  rw [finInsepDegree]; rw [finrank_of_infinite_dimensional (K := F) (V := E) fun _ =>
      halg (Algebra.IsAlgebraic.of_finit

中文:
定理 finSepDegree_mul_finInsepDegree
  结论: finSepDegree F E * finInsepDegree F E = finrank F E
  证明: by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E] at this
  rw [finInsepDegree]; rw [finrank_of_infinite_dimensional (K := F) (V := E) fun _ =>
      halg (Algebra.IsAlgebraic.of_finit

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.of_finite, Cardinal, Cardinal.toNat, Cardinal.toNat_mul, IsAlgebraic, congr_arg, finInsepDegree, finSepDegree_eq, finrank_of_infinite_dimensional, mul_zero, of_finite, sepDegree_mul_insepDegree, separableClosure, toNat_mul
-/
theorem finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = finrank F E := by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E] at this
  rw [finInsepDegree]; rw [finrank_of_infinite_dimensional (K := F) (V := E) fun _ =>
      halg (Algebra.IsAlgebraic.of_finite F E)]; rw [finrank_of_infinite_dimensional (K := separableClosure F E) (V := E) fun _ =>
      halg (.trans _ (separableClosure F E) _)]; rw [mul_zero]

end Field

namespace separableClosure

variable [Algebra E K] [IsScalarTower F E K] {F E}

/--
lemma `adjoin_eq_of_isAlgebraic_of_isSeparable` / 引理 `adjoin_eq_of_isAlgebraic_of_isSeparable`

English:
lemma adjoin_eq_of_isAlgebraic_of_isSeparable
  statement: [Algebra.IsAlgebraic F E]
  proof: top_unique fun x _ => by
    set S := separableClosure F K
    set L := adjoin E (S : Set K)
    have := Algebra.isSeparable_tower_top_of_isSeparable E L K
    let i : S ->+* L := Subsemiring.inclusion fun x hx => subset_adjoin E (S : Set K) hx
    let _ : Algebra S L := i.toAlgebra
    have : IsSca

中文:
引理 adjoin_eq_of_isAlgebraic_of_isSeparable
  结论: [Algebra.IsAlgebraic F E]
  证明: top_unique fun x _ => by
    set S := separableClosure F K
    set L := adjoin E (S : Set K)
    have := Algebra.isSeparable_tower_top_of_isSeparable E L K
    let i : S ->+* L := Subsemiring.inclusion fun x hx => subset_adjoin E (S : Set K) hx
    let _ : Algebra S L := i.toAlgebra
    have : IsSca

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.trans, Algebra.isSeparable_tower_top_of_isSeparable, IsAlgebraic, IsPurelyInseparable, IsPurelyInseparable.tower_top, IsScalarTower, IsScalarTower.of_algebraMap_eq, Subsemiring, Subsemiring.inclusion, adjoin, i.toAlgebra, inclusion, isPurelyInseparable, isSeparable_tower_top_of_isSeparable, of_algebraMap_eq, separableClosure, separableClosure.isPurelyInseparable, subset_adjoin, toAlgebra
-/
lemma adjoin_eq_of_isAlgebraic_of_isSeparable [Algebra.IsAlgebraic F E]
    [Algebra.IsSeparable E K] : adjoin E (separableClosure F K : Set K) = ⊤ :=
  top_unique fun x _ => by
    set S := separableClosure F K
    set L := adjoin E (S : Set K)
    have := Algebra.isSeparable_tower_top_of_isSeparable E L K
    let i : S ->+* L := Subsemiring.inclusion fun x hx => subset_adjoin E (S : Set K) hx
    let _ : Algebra S L := i.toAlgebra
    have : IsScalarTower S L K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    have := Algebra.IsAlgebraic.trans F E K
    have : IsPurelyInseparable S K := separableClosure.isPurelyInseparable F K
    have := IsPurelyInseparable.tower_top S L K
    obtain ⟨y, rfl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L K x
    exact y.2

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `adjoin_eq_of_isAlgebraic` / 定理 `adjoin_eq_of_isAlgebraic`

English:
theorem adjoin_eq_of_isAlgebraic
  given: [Algebra.IsAlgebraic F E]
  proof: by
  set S := separableClosure E K
  have h := congr_arg lift (adjoin_eq_of_isAlgebraic_of_isSeparable (F := F) S)
  rw [lift_top]; rw [lift_adjoin] at h
  have : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h]; rw [← map_eq_of_separableClosure_eq_bot F (separableClos

中文:
定理 adjoin_eq_of_isAlgebraic
  条件: [Algebra.IsAlgebraic F E]
  证明: by
  set S := separableClosure E K
  have h := congr_arg lift (adjoin_eq_of_isAlgebraic_of_isSeparable (F := F) S)
  rw [lift_top]; rw [lift_adjoin] at h
  have : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h]; rw [← map_eq_of_separableClosure_eq_bot F (separableClos

Depends on / 依赖: IntermediateField, IntermediateField.algebraMap_apply, IsScalarTower, IsScalarTower.coe_toAlgHom, IsScalarTower.of_algebraMap_eq, adjoin_eq_of_isAlgebraic_of_isSeparable, algebraMap_apply, coe_map, coe_toAlgHom, congr_arg, lift_adjoin, lift_top, map_eq_of_separableClosure_eq_bot, of_algebraMap_eq, separableClosure, separableClosure_eq_bot
-/
theorem adjoin_eq_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    adjoin E (separableClosure F K) = separableClosure E K := by
  set S := separableClosure E K
  have h := congr_arg lift (adjoin_eq_of_isAlgebraic_of_isSeparable (F := F) S)
  rw [lift_top]; rw [lift_adjoin] at h
  have : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h]; rw [← map_eq_of_separableClosure_eq_bot F (separableClosure_eq_bot E K)]
  simp only [S, coe_map, IsScalarTower.coe_toAlgHom', IntermediateField.algebraMap_apply]

end separableClosure

section

open TensorProduct

section Subalgebra

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] (p : Nat) [ExpChar A p]

/--
Definition of `Subalgebra.perfectClosure` / `Subalgebra.perfectClosure` 的定义

English:
definition Subalgebra.perfectClosure
  signature: : Subalgebra R A where
  body: {x : A | exists n : Nat, x ^ p ^ n in (algebraMap R A).rangeS}
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [add_pow_expChar_pow]; rw [pow_add]; rw [pow_mul]; rw [mul_comm (_ ^ n)]; rw [pow_mul]
    exact add_mem (pow_mem hx _) (pow_mem hy _)
  mul_mem' := by
    rintro x y ⟨

中文:
定义 Subalgebra.perfectClosure
  签名: : Subalgebra R A where
  定义体: {x : A | exists n : Nat, x ^ p ^ n in (algebraMap R A).rangeS}
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [add_pow_expChar_pow]; rw [pow_add]; rw [pow_mul]; rw [mul_comm (_ ^ n)]; rw [pow_mul]
    exact add_mem (pow_mem hx _) (pow_mem hy _)
  mul_mem' := by
    rintro x y ⟨

Depends on / 依赖: algebraMap, rangeS
-/
def Subalgebra.perfectClosure : Subalgebra R A where
  carrier := {x : A | exists n : Nat, x ^ p ^ n in (algebraMap R A).rangeS}
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [add_pow_expChar_pow]; rw [pow_add]; rw [pow_mul]; rw [mul_comm (_ ^ n)]; rw [pow_mul]
    exact add_mem (pow_mem hx _) (pow_mem hy _)
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [mul_pow]; rw [pow_add]; rw [pow_mul]; rw [mul_comm (_ ^ n)]; rw [pow_mul]
    exact mul_mem (pow_mem hx _) (pow_mem hy _)
  algebraMap_mem' := fun x => ⟨0, by rw [pow_zero, pow_one]; exact ⟨x, rfl⟩⟩

variable {R A p}

/--
theorem `Subalgebra.mem_perfectClosure_iff` / 定理 `Subalgebra.mem_perfectClosure_iff`

English:
theorem Subalgebra.mem_perfectClosure_iff
  given: {x : A}
  proof: Iff.rfl

中文:
定理 Subalgebra.mem_perfectClosure_iff
  条件: {x : A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Subalgebra.mem_perfectClosure_iff {x : A} :
    x in perfectClosure R A p ↔ exists n : Nat, x ^ p ^ n in (algebraMap R A).rangeS := Iff.rfl

end Subalgebra

variable {k K R : Type*} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R]

/--
lemma `IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar` / 引理 `IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar`

English:
lemma IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
  proof: by
  nontriviality (R otimes[k] K)
  obtain (hq | hq) := expChar_is_prime_or_one k q
  induction x with
  | zero => exact ⟨0, 0, by simp⟩
  | add x y h h' =>
    have : ExpChar (R otimes[k] K) q := expChar_of_injective_ringHom (algebraMap k _).injective q
    simp_rw [RingHom.mem_range, ← RingHom.me

中文:
引理 IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
  证明: by
  nontriviality (R otimes[k] K)
  obtain (hq | hq) := expChar_is_prime_or_one k q
  induction x with
  | zero => exact ⟨0, 0, by simp⟩
  | add x y h h' =>
    have : ExpChar (R otimes[k] K) q := expChar_of_injective_ringHom (algebraMap k _).injective q
    simp_rw [RingHom.mem_range, ← RingHom.me

Depends on / 依赖: ExpChar, IsPurelyInseparable, IsPurelyInseparable.pow_mem, RingHom, RingHom.mem_range, RingHom.mem_rangeS, Subalgebra, Subalgebra.mem_perfectClosure_iff, add_mem, algebraMap, expChar_is_prime_or_one, expChar_of_injective_ringHom, injective, mem_perfectClosure_iff, mem_range, mem_rangeS, nontriviality, otimes, pow_mem, simp_rw
-/
lemma IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
    [IsPurelyInseparable k K] (q : Nat) [ExpChar k q] (x : R otimes[k] K) :
    exists n, x ^ q ^ n in (algebraMap R (R otimes[k] K)).range := by
  nontriviality (R otimes[k] K)
  obtain (hq | hq) := expChar_is_prime_or_one k q
  induction x with
  | zero => exact ⟨0, 0, by simp⟩
  | add x y h h' =>
    have : ExpChar (R otimes[k] K) q := expChar_of_injective_ringHom (algebraMap k _).injective q
    simp_rw [RingHom.mem_range, ← RingHom.mem_rangeS, ← Subalgebra.mem_perfectClosure_iff] at h h' ⊢
    exact add_mem h h'
  | tmul x y =>
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k q y
    use n
    have : (x ^ q ^ n) otimesₜ[k] (y ^ q ^ n) =
        (x ^ q ^ n) otimesₜ[k] (1 : K) * (1 : R) otimesₜ[k] (y ^ q ^ n) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]
    rw [Algebra.TensorProduct.tmul_pow]; rw [this]
    refine Subring.mul_mem _ ⟨x ^ q ^ n, rfl⟩ ⟨algebraMap k R a, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]; rw [Algebra.TensorProduct.algebraMap_apply]; rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]; rw [ha]
  · subst hq
    have : CharZero k := charZero_of_expChar_one' k
    exact ⟨0, (Algebra.TensorProduct.includeLeft_surjective R _ <|
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable k K) _⟩

/--
lemma `IsPurelyInseparable.exists_pow_mem_range_tensorProduct` / 引理 `IsPurelyInseparable.exists_pow_mem_range_tensorProduct`

English:
lemma IsPurelyInseparable.exists_pow_mem_range_tensorProduct
  statement: [IsPurelyInseparable k K]
  proof: by
  let q := ringExpChar k
  obtain ⟨n, hr⟩ := exists_pow_pow_mem_range_tensorProduct_of_expChar q x
  refine ⟨q ^ n, pow_pos ?_ _, hr⟩
  obtain (hq | hq) := expChar_is_prime_or_one k q <;> simp [hq, Nat.Prime.pos]

中文:
引理 IsPurelyInseparable.exists_pow_mem_range_tensorProduct
  结论: [IsPurelyInseparable k K]
  证明: by
  let q := ringExpChar k
  obtain ⟨n, hr⟩ := exists_pow_pow_mem_range_tensorProduct_of_expChar q x
  refine ⟨q ^ n, pow_pos ?_ _, hr⟩
  obtain (hq | hq) := expChar_is_prime_or_one k q <;> simp [hq, Nat.Prime.pos]

Depends on / 依赖: Nat.Prime.pos, exists_pow_pow_mem_range_tensorProduct_of_expChar, expChar_is_prime_or_one, pow_pos, ringExpChar
-/
lemma IsPurelyInseparable.exists_pow_mem_range_tensorProduct [IsPurelyInseparable k K]
    (x : R otimes[k] K) : exists n > 0, x ^ n in (algebraMap R (R otimes[k] K)).range := by
  let q := ringExpChar k
  obtain ⟨n, hr⟩ := exists_pow_pow_mem_range_tensorProduct_of_expChar q x
  refine ⟨q ^ n, pow_pos ?_ _, hr⟩
  obtain (hq | hq) := expChar_is_prime_or_one k q <;> simp [hq, Nat.Prime.pos]

end
