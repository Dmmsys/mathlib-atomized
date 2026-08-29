/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.UnitInterval
public import Mathlib.Algebra.Star.Subalgebra

/-!
# Constructions relating polynomial functions and continuous functions.

## Main definitions

* `Polynomial.toContinuousMapOn p X`: for `X : Set R`, interprets a polynomial `p`
  as a bundled continuous function in `C(X, R)`.
* `Polynomial.toContinuousMapOnAlgHom`: the same, as an `R`-algebra homomorphism.
* `polynomialFunctions (X : Set R) : Subalgebra R C(X, R)`: polynomial functions as a subalgebra.
* `polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints`:
  the polynomial functions separate points.

-/

@[expose] public section


variable {R : Type*}

open Polynomial

namespace Polynomial

section

variable [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: (p : R[X])
  body: ⟨fun x : R => p.eval x, by fun_prop⟩

中文:
定义 toContinuousMap
  签名: (p : R[X])
  定义体: ⟨fun x : R => p.eval x, by fun_prop⟩

Depends on / 依赖: fun_prop, p.eval
-/
def toContinuousMap (p : R[X]) : C(R, R) :=
  ⟨fun x : R => p.eval x, by fun_prop⟩

open ContinuousMap in
/--
lemma `toContinuousMap_X_eq_id` / 引理 `toContinuousMap_X_eq_id`

English:
lemma toContinuousMap_X_eq_id
  statement: X.toContinuousMap = .id R
  proof: by
  ext; simp

中文:
引理 toContinuousMap_X_eq_id
  结论: X.toContinuousMap = .id R
  证明: by
  ext; simp
-/
lemma toContinuousMap_X_eq_id : X.toContinuousMap = .id R := by
  ext; simp

/-- A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
/--
Definition of `toContinuousMapOn` / `toContinuousMapOn` 的定义

English:
definition toContinuousMapOn
  signature: (p : R[X]) (X : Set R)
  body: ⟨fun x : X => p.toContinuousMap x, by fun_prop⟩

中文:
定义 toContinuousMapOn
  签名: (p : R[X]) (X : Set R)
  定义体: ⟨fun x : X => p.toContinuousMap x, by fun_prop⟩

Depends on / 依赖: fun_prop, p.toContinuousMap, toContinuousMap
-/
def toContinuousMapOn (p : R[X]) (X : Set R) : C(X, R) :=
  ⟨fun x : X => p.toContinuousMap x, by fun_prop⟩

open ContinuousMap in
/--
lemma `toContinuousMapOn_X_eq_restrict_id` / 引理 `toContinuousMapOn_X_eq_restrict_id`

English:
lemma toContinuousMapOn_X_eq_restrict_id
  given: (s : Set R)
  proof: by
  ext; simp

中文:
引理 toContinuousMapOn_X_eq_restrict_id
  条件: (s : Set R)
  证明: by
  ext; simp
-/
lemma toContinuousMapOn_X_eq_restrict_id (s : Set R) :
    X.toContinuousMapOn s = restrict s (.id R) := by
  ext; simp


-- TODO some lemmas about when `toContinuousMapOn` is injective?
end

section

variable {α : Type*} [TopologicalSpace α] [CommSemiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R]

@[simp]
/--
theorem `aeval_continuousMap_apply` / 定理 `aeval_continuousMap_apply`

English:
theorem aeval_continuousMap_apply
  given: (g : R[X]) (f : C(α, R)) (x : α)
  proof: by
  refine Polynomial.induction_on' g ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp

中文:
定理 aeval_continuousMap_apply
  条件: (g : R[X]) (f : C(α, R)) (x : α)
  证明: by
  refine Polynomial.induction_on' g ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp

Depends on / 依赖: Polynomial, Polynomial.induction_on, induction_on
-/
theorem aeval_continuousMap_apply (g : R[X]) (f : C(α, R)) (x : α) :
    ((Polynomial.aeval f) g) x = g.eval (f x) := by
  refine Polynomial.induction_on' g ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp

end

noncomputable section

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- The algebra map from `R[X]` to continuous functions `C(R, R)`.
-/
@[simps]
/--
Definition of `toContinuousMapAlgHom` / `toContinuousMapAlgHom` 的定义

English:
definition toContinuousMapAlgHom
  signature: : R[X] ->ₐ[R] C(R, R) where
  body: p.toContinuousMap
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

中文:
定义 toContinuousMapAlgHom
  签名: : R[X] ->ₐ[R] C(R, R) where
  定义体: p.toContinuousMap
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: p.toContinuousMap, toContinuousMap
-/
def toContinuousMapAlgHom : R[X] ->ₐ[R] C(R, R) where
  toFun p := p.toContinuousMap
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

/-- The algebra map from `R[X]` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
/--
Definition of `toContinuousMapOnAlgHom` / `toContinuousMapOnAlgHom` 的定义

English:
definition toContinuousMapOnAlgHom
  signature: (X : Set R)
  body: p.toContinuousMapOn X
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

中文:
定义 toContinuousMapOnAlgHom
  签名: (X : Set R)
  定义体: p.toContinuousMapOn X
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: p.toContinuousMapOn, toContinuousMapOn
-/
def toContinuousMapOnAlgHom (X : Set R) : R[X] ->ₐ[R] C(X, R) where
  toFun p := p.toContinuousMapOn X
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

end

end Polynomial

section

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological semiring
`R`.
-/
noncomputable
/--
Definition of `polynomialFunctions` / `polynomialFunctions` 的定义

English:
definition polynomialFunctions
  signature: (X : Set R)
  body: (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)

@[simp]

中文:
定义 polynomialFunctions
  签名: (X : Set R)
  定义体: (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)

@[simp]

Depends on / 依赖: Polynomial, Polynomial.toContinuousMapOnAlgHom, Subalgebra, toContinuousMapOnAlgHom
-/
def polynomialFunctions (X : Set R) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)

@[simp]
/--
theorem `polynomialFunctions_coe` / 定理 `polynomialFunctions_coe`

English:
theorem polynomialFunctions_coe
  given: (X : Set R)
  proof: by
  ext
  simp [polynomialFunctions]

中文:
定理 polynomialFunctions_coe
  条件: (X : Set R)
  证明: by
  ext
  simp [polynomialFunctions]

Depends on / 依赖: polynomialFunctions
-/
theorem polynomialFunctions_coe (X : Set R) :
    (polynomialFunctions X : Set C(X, R)) = Set.range (Polynomial.toContinuousMapOnAlgHom X) := by
  ext
  simp [polynomialFunctions]

set_option backward.defeqAttrib.useBackward true in
-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces a normed algebra isomorphism between `polynomialFunctions X` and
-- `polynomialFunctions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.
/--
theorem `polynomialFunctions_separatesPoints` / 定理 `polynomialFunctions_separatesPoints`

English:
theorem polynomialFunctions_separatesPoints
  given: (X : Set R)
  statement: (polynomialFunctions X).SeparatesPoints
  proof: fun x y h => by
  -- We use `Polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨Polynomial.X, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, ?_⟩⟩
  dsimp; simp only [Polynomial.eval_X]
  exact fun h' => h (Subtype.ext h')

中文:
定理 polynomialFunctions_separatesPoints
  条件: (X : Set R)
  结论: (polynomialFunctions X).SeparatesPoints
  证明: fun x y h => by
  -- We use `Polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨Polynomial.X, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, ?_⟩⟩
  dsimp; simp only [Polynomial.eval_X]
  exact fun h' => h (Subtype.ext h')
-/
theorem polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints :=
  fun x y h => by
  -- We use `Polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨Polynomial.X, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, ?_⟩⟩
  dsimp; simp only [Polynomial.eval_X]
  exact fun h' => h (Subtype.ext h')

open unitInterval

open ContinuousMap

set_option backward.defeqAttrib.useBackward true in
/--
theorem `polynomialFunctions.comap_compRightAlgHom_iccHomeoI` / 定理 `polynomialFunctions.comap_compRightAlgHom_iccHomeoI`

English:
theorem polynomialFunctions.comap_compRightAlgHom_iccHomeoI
  given: (a b : Real) (h : a < b)
  proof: by
  ext f
  fconstructor
  · rintro ⟨p, ⟨-, w⟩⟩
    rw [DFunLike.ext_iff] at w
    dsimp at w
    let q := p.comp ((b - a)⁻¹ • Polynomial.X + Polynomial.C (-a * (b - a)⁻¹))
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp only [q, neg_mul, map_neg, map_mul, AlgHom.coe_toRingHom,
        P

中文:
定理 polynomialFunctions.comap_compRightAlgHom_iccHomeoI
  条件: (a b : 实数) (h : a < b)
  证明: by
  ext f
  fconstructor
  · rintro ⟨p, ⟨-, w⟩⟩
    rw [DFunLike.ext_iff] at w
    dsimp at w
    let q := p.comp ((b - a)⁻¹ • Polynomial.X + Polynomial.C (-a * (b - a)⁻¹))
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp only [q, neg_mul, map_neg, map_mul, AlgHom.coe_toRingHom,
        P

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, DFunLike, DFunLike.ext_iff, Polynomia, Polynomial, Polynomial.C, Polynomial.X, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_smul, Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply, coe_toRingHom, eval_C, eval_X
-/
theorem polynomialFunctions.comap_compRightAlgHom_iccHomeoI (a b : Real) (h : a < b) :
    (polynomialFunctions I).comap (compRightAlgHom Real Real (iccHomeoI a b h).symm) =
      polynomialFunctions (Set.Icc a b) := by
  ext f
  fconstructor
  · rintro ⟨p, ⟨-, w⟩⟩
    rw [DFunLike.ext_iff] at w
    dsimp at w
    let q := p.comp ((b - a)⁻¹ • Polynomial.X + Polynomial.C (-a * (b - a)⁻¹))
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp only [q, neg_mul, map_neg, map_mul, AlgHom.coe_toRingHom,
        Polynomial.eval_X, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_smul,
        smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_comp, Polynomial.toContinuousMapOnAlgHom_apply,
        Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply]
      convert! w ⟨_, _⟩
      · ext
        simp only [iccHomeoI_symm_apply_coe]
        replace h : b - a != 0 := sub_ne_zero_of_ne h.ne.symm
        field
      · rw [mul_comm (b - a)⁻¹, ← neg_mul, ← add_mul, ← sub_eq_add_neg]
        have w₁ : 0 < (b - a)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
        have w₂ : 0 <= (x : Real) - a := sub_nonneg.mpr x.2.1
        have w₃ : (x : Real) - a <= b - a := sub_le_sub_right x.2.2 a
        fconstructor
        · exact mul_nonneg w₂ (le_of_lt w₁)
        · rw [← div_eq_mul_inv, div_le_one (sub_pos.mpr h)]
          exact w₃
  · rintro ⟨p, ⟨-, rfl⟩⟩
    let q := p.comp ((b - a) • Polynomial.X + Polynomial.C a)
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp [q, mul_comm]

/--
theorem `polynomialFunctions.eq_adjoin_X` / 定理 `polynomialFunctions.eq_adjoin_X`

English:
theorem polynomialFunctions.eq_adjoin_X
  given: (s : Set R)
  proof: by
  refine le_antisymm ?_
    (Algebra.adjoin_le fun _ h => ⟨X, trivial, (Set.mem_singleton_iff.1 h).symm⟩)
  rintro - ⟨p, -, rfl⟩
  rw [AlgHom.coe_toRingHom]
  refine p.induction_on (fun r => ?_) (fun f g hf hg => ?_) fun n r hn => ?_
  · rw [Polynomial.C_eq_algebraMap, AlgHomClass.commutes]
    e

中文:
定理 polynomialFunctions.eq_adjoin_X
  条件: (s : Set R)
  证明: by
  refine le_antisymm ?_
    (Algebra.adjoin_le fun _ h => ⟨X, trivial, (Set.mem_singleton_iff.1 h).symm⟩)
  rintro - ⟨p, -, rfl⟩
  rw [AlgHom.coe_toRingHom]
  refine p.induction_on (fun r => ?_) (fun f g hf hg => ?_) fun n r hn => ?_
  · rw [Polynomial.C_eq_algebraMap, AlgHomClass.commutes]
    e

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, AlgHomClass, AlgHomClass.commutes, Algebra, Algebra.adjoin_le, Algebra.subset_adjoin, C_eq_algebraMap, Polynomial, Polynomial.C_eq_algebraMap, Set.mem_singleton, Set.mem_singleton_iff, Subalgebra, Subalgebra.algebraMap_mem, add_mem, adjoin_le, algebraMap_mem, coe_toRingHom, commutes, induction_on
-/
theorem polynomialFunctions.eq_adjoin_X (s : Set R) :
    polynomialFunctions s = Algebra.adjoin R {toContinuousMapOnAlgHom s X} := by
  refine le_antisymm ?_
    (Algebra.adjoin_le fun _ h => ⟨X, trivial, (Set.mem_singleton_iff.1 h).symm⟩)
  rintro - ⟨p, -, rfl⟩
  rw [AlgHom.coe_toRingHom]
  refine p.induction_on (fun r => ?_) (fun f g hf hg => ?_) fun n r hn => ?_
  · rw [Polynomial.C_eq_algebraMap, AlgHomClass.commutes]
    exact Subalgebra.algebraMap_mem _ r
  · rw [map_add]
    exact add_mem hf hg
  · rw [pow_succ, ← mul_assoc, map_mul]
    exact mul_mem hn (Algebra.subset_adjoin <| Set.mem_singleton _)

/--
theorem `polynomialFunctions.le_equalizer` / 定理 `polynomialFunctions.le_equalizer`

English:
theorem polynomialFunctions.le_equalizer
  statement: {A : Type*} [Semiring A] [Algebra R A] (s : Set R)
  proof: by
  rw [polynomialFunctions.eq_adjoin_X s]
  exact φ.adjoin_le_equalizer ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

中文:
定理 polynomialFunctions.le_equalizer
  结论: {A : 类型} [Semiring A] [Algebra R A] (s : Set R)
  证明: by
  rw [polynomialFunctions.eq_adjoin_X s]
  exact φ.adjoin_le_equalizer ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

Depends on / 依赖: Set.mem_singleton_iff, adjoin_le_equalizer, eq_adjoin_X, mem_singleton_iff, polynomialFunctions, polynomialFunctions.eq_adjoin_X
-/
theorem polynomialFunctions.le_equalizer {A : Type*} [Semiring A] [Algebra R A] (s : Set R)
    (φ ψ : C(s, R) ->ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    polynomialFunctions s <= AlgHom.equalizer φ ψ := by
  rw [polynomialFunctions.eq_adjoin_X s]
  exact φ.adjoin_le_equalizer ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

open StarAlgebra

/--
theorem `polynomialFunctions.starClosure_eq_adjoin_X` / 定理 `polynomialFunctions.starClosure_eq_adjoin_X`

English:
theorem polynomialFunctions.starClosure_eq_adjoin_X
  given: [StarRing R] [ContinuousStar R] (s : Set R)
  proof: by
  rw [polynomialFunctions.eq_adjoin_X s]; rw [adjoin_eq_starClosure_adjoin]

中文:
定理 polynomialFunctions.starClosure_eq_adjoin_X
  条件: [StarRing R] [ContinuousStar R] (s : Set R)
  证明: by
  rw [polynomialFunctions.eq_adjoin_X s]; rw [adjoin_eq_starClosure_adjoin]

Depends on / 依赖: adjoin_eq_starClosure_adjoin, eq_adjoin_X, polynomialFunctions, polynomialFunctions.eq_adjoin_X
-/
theorem polynomialFunctions.starClosure_eq_adjoin_X [StarRing R] [ContinuousStar R] (s : Set R) :
    (polynomialFunctions s).starClosure = adjoin R {toContinuousMapOnAlgHom s X} := by
  rw [polynomialFunctions.eq_adjoin_X s]; rw [adjoin_eq_starClosure_adjoin]

/--
theorem `polynomialFunctions.starClosure_le_equalizer` / 定理 `polynomialFunctions.starClosure_le_equalizer`

English:
theorem polynomialFunctions.starClosure_le_equalizer
  statement: {A : Type*} [StarRing R] [ContinuousStar R]
  proof: by
  rw [polynomialFunctions.starClosure_eq_adjoin_X s]
  exact StarAlgHom.adjoin_le_equalizer φ ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

中文:
定理 polynomialFunctions.starClosure_le_equalizer
  结论: {A : 类型} [StarRing R] [ContinuousStar R]
  证明: by
  rw [polynomialFunctions.starClosure_eq_adjoin_X s]
  exact StarAlgHom.adjoin_le_equalizer φ ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

Depends on / 依赖: Set.mem_singleton_iff, StarAlgHom, StarAlgHom.adjoin_le_equalizer, adjoin_le_equalizer, mem_singleton_iff, polynomialFunctions, polynomialFunctions.starClosure_eq_adjoin_X, starClosure_eq_adjoin_X
-/
theorem polynomialFunctions.starClosure_le_equalizer {A : Type*} [StarRing R] [ContinuousStar R]
    [Semiring A] [StarRing A] [Algebra R A] (s : Set R) (φ ψ : C(s, R) ->⋆ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    (polynomialFunctions s).starClosure <= StarAlgHom.equalizer φ ψ := by
  rw [polynomialFunctions.starClosure_eq_adjoin_X s]
  exact StarAlgHom.adjoin_le_equalizer φ ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

end
