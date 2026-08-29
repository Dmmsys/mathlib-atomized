/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Bases of dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.
This file concerns bases on dual vector spaces.

## Main definitions

* Bases:
  * `Basis.toDual` produces the map `M →ₗ[R] Dual R M` associated to a basis for an `R`-module `M`.
  * `Basis.toDualEquiv` is the equivalence `M ≃ₗ[R] Dual R M` associated to a finite basis.
  * `Basis.dualBasis` is a basis for `Dual R M` given a finite basis for `M`.
  * `Module.DualBases e ε` is the proposition that the families `e` of vectors and `ε` of dual
    vectors have the characteristic properties of a basis and a dual.

## Main results

* Bases:
  * `Module.DualBases.basis` and `Module.DualBases.coe_basis`: if `e` and `ε` form a dual pair,
    then `e` is a basis.
  * `Module.DualBases.coe_dualBasis`: if `e` and `ε` form a dual pair,
    then `ε` is a basis.
-/

@[expose] public section

open Module Dual Submodule LinearMap Function

noncomputable section

namespace Module.Basis

universe u v w uR uM uK uV uι
variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]
variable (b : Basis ι R M)

/--
Definition of `toDual` / `toDual` 的定义

English:
definition toDual
  signature: : M ->ₗ[R] Module.Dual R M
  body: b.constr Nat fun v => b.constr Nat fun w => if w = v then (1 : R) else 0

中文:
定义 toDual
  签名: : M ->ₗ[R] Module.Dual R M
  定义体: b.constr Nat fun v => b.constr Nat fun w => if w = v then (1 : R) else 0

Depends on / 依赖: b.constr, constr
-/
def toDual : M ->ₗ[R] Module.Dual R M :=
  b.constr Nat fun v => b.constr Nat fun w => if w = v then (1 : R) else 0

/--
theorem `toDual_apply` / 定理 `toDual_apply`

English:
theorem toDual_apply
  given: (i j : ι)
  statement: b.toDual (b i) (b j) = if i = j then 1 else 0
  proof: by
  rw [toDual]; rw [constr_basis b]; rw [constr_basis b]
  simp only [eq_comm]

中文:
定理 toDual_apply
  条件: (i j : ι)
  结论: b.toDual (b i) (b j) = if i = j then 1 else 0
  证明: by
  rw [toDual]; rw [constr_basis b]; rw [constr_basis b]
  simp only [eq_comm]

Depends on / 依赖: constr_basis, eq_comm, toDual
-/
theorem toDual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 := by
  rw [toDual]; rw [constr_basis b]; rw [constr_basis b]
  simp only [eq_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toDual_linearCombination_left` / 定理 `toDual_linearCombination_left`

English:
theorem toDual_linearCombination_left
  given: (f : ι ->₀ R) (i : ι)
  proof: by
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]; rw [LinearMap.sum_apply]
  simp_rw [map_smul, LinearMap.smul_apply, toDual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq', Finsupp.if_mem_support]

中文:
定理 toDual_linearCombination_left
  条件: (f : ι ->₀ R) (i : ι)
  证明: by
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]; rw [LinearMap.sum_apply]
  simp_rw [map_smul, LinearMap.smul_apply, toDual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq', Finsupp.if_mem_support]

Depends on / 依赖: Finset, Finset.sum_ite_eq, Finsupp, Finsupp.if_mem_support, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap, LinearMap.smul_apply, LinearMap.sum_apply, if_mem_support, linearCombination_apply, map_smul, map_sum, mul_boole, simp_rw, smul_apply, smul_eq_mul, sum_apply, sum_ite_eq, toDual_apply
-/
theorem toDual_linearCombination_left (f : ι ->₀ R) (i : ι) :
    b.toDual (Finsupp.linearCombination R b f) (b i) = f i := by
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]; rw [LinearMap.sum_apply]
  simp_rw [map_smul, LinearMap.smul_apply, toDual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq', Finsupp.if_mem_support]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toDual_linearCombination_right` / 定理 `toDual_linearCombination_right`

English:
theorem toDual_linearCombination_right
  given: (f : ι ->₀ R) (i : ι)
  proof: by
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]
  simp_rw [map_smul, toDual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq,
    Finsupp.if_mem_support]

中文:
定理 toDual_linearCombination_right
  条件: (f : ι ->₀ R) (i : ι)
  证明: by
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]
  simp_rw [map_smul, toDual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq,
    Finsupp.if_mem_support]

Depends on / 依赖: Finset, Finset.sum_ite_eq, Finsupp, Finsupp.if_mem_support, Finsupp.linearCombination_apply, Finsupp.sum, _eq_zero, _eq_zero_of_ae_zero, ae_eq_zero_of_eLpNorm, eLpNorm, hq0_lt, if_mem_support, le_of_lt, linearCombination_apply, map_smul, map_sum, mul_boole, simp_rw, smul_eq_mul, sum_ite_eq
-/
theorem toDual_linearCombination_right (f : ι ->₀ R) (i : ι) :
    b.toDual (b i) (Finsupp.linearCombination R b f) = f i := by
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [map_sum]
  simp_rw [map_smul, toDual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq,
    Finsupp.if_mem_support]

/--
theorem `toDual_apply_left` / 定理 `toDual_apply_left`

English:
theorem toDual_apply_left
  given: (m : M) (i : ι)
  statement: b.toDual m (b i) = b.repr m i
  proof: by
  rw [← b.toDual_linearCombination_left]; rw [b.linearCombination_repr]

中文:
定理 toDual_apply_left
  条件: (m : M) (i : ι)
  结论: b.toDual m (b i) = b.repr m i
  证明: by
  rw [← b.toDual_linearCombination_left]; rw [b.linearCombination_repr]

Depends on / 依赖: b.linearCombination_repr, b.toDual_linearCombination_left, linearCombination_repr, toDual_linearCombination_left
-/
theorem toDual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i := by
  rw [← b.toDual_linearCombination_left]; rw [b.linearCombination_repr]

/--
theorem `toDual_apply_right` / 定理 `toDual_apply_right`

English:
theorem toDual_apply_right
  given: (i : ι) (m : M)
  statement: b.toDual (b i) m = b.repr m i
  proof: by
  rw [← b.toDual_linearCombination_right]; rw [b.linearCombination_repr]

中文:
定理 toDual_apply_right
  条件: (i : ι) (m : M)
  结论: b.toDual (b i) m = b.repr m i
  证明: by
  rw [← b.toDual_linearCombination_right]; rw [b.linearCombination_repr]

Depends on / 依赖: b.linearCombination_repr, b.toDual_linearCombination_right, linearCombination_repr, toDual_linearCombination_right
-/
theorem toDual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i := by
  rw [← b.toDual_linearCombination_right]; rw [b.linearCombination_repr]

/--
theorem `coe_toDual_self` / 定理 `coe_toDual_self`

English:
theorem coe_toDual_self
  given: (i : ι)
  statement: b.toDual (b i) = b.coord i
  proof: by
  ext
  apply toDual_apply_right

中文:
定理 coe_toDual_self
  条件: (i : ι)
  结论: b.toDual (b i) = b.coord i
  证明: by
  ext
  apply toDual_apply_right

Depends on / 依赖: toDual_apply_right
-/
theorem coe_toDual_self (i : ι) : b.toDual (b i) = b.coord i := by
  ext
  apply toDual_apply_right

/--
Definition of `toDualFlip` / `toDualFlip` 的定义

English:
definition toDualFlip
  signature: (m : M)
  body: b.toDual.flip m

中文:
定义 toDualFlip
  签名: (m : M)
  定义体: b.toDual.flip m

Depends on / 依赖: b.toDual.flip, toDual
-/
def toDualFlip (m : M) : M ->ₗ[R] R :=
  b.toDual.flip m

/--
theorem `toDualFlip_apply` / 定理 `toDualFlip_apply`

English:
theorem toDualFlip_apply
  given: (m₁ m₂ : M)
  statement: b.toDualFlip m₁ m₂ = b.toDual m₂ m₁
  proof: rfl

中文:
定理 toDualFlip_apply
  条件: (m₁ m₂ : M)
  结论: b.toDualFlip m₁ m₂ = b.toDual m₂ m₁
  证明: rfl
-/
theorem toDualFlip_apply (m₁ m₂ : M) : b.toDualFlip m₁ m₂ = b.toDual m₂ m₁ :=
  rfl

/--
theorem `toDual_eq_repr` / 定理 `toDual_eq_repr`

English:
theorem toDual_eq_repr
  given: (m : M) (i : ι)
  statement: b.toDual m (b i) = b.repr m i
  proof: b.toDual_apply_left m i

中文:
定理 toDual_eq_repr
  条件: (m : M) (i : ι)
  结论: b.toDual m (b i) = b.repr m i
  证明: b.toDual_apply_left m i

Depends on / 依赖: b.toDual_apply_left, toDual_apply_left
-/
theorem toDual_eq_repr (m : M) (i : ι) : b.toDual m (b i) = b.repr m i :=
  b.toDual_apply_left m i

/--
theorem `toDual_eq_equivFun` / 定理 `toDual_eq_equivFun`

English:
theorem toDual_eq_equivFun
  given: [Finite ι] (m : M) (i : ι)
  statement: b.toDual m (b i) = b.equivFun m i
  proof: by
  rw [b.equivFun_apply]; rw [toDual_eq_repr]

中文:
定理 toDual_eq_equivFun
  条件: [Finite ι] (m : M) (i : ι)
  结论: b.toDual m (b i) = b.equivFun m i
  证明: by
  rw [b.equivFun_apply]; rw [toDual_eq_repr]

Depends on / 依赖: b.equivFun_apply, equivFun_apply, toDual_eq_repr
-/
theorem toDual_eq_equivFun [Finite ι] (m : M) (i : ι) : b.toDual m (b i) = b.equivFun m i := by
  rw [b.equivFun_apply]; rw [toDual_eq_repr]

/--
theorem `toDual_injective` / 定理 `toDual_injective`

English:
theorem toDual_injective
  statement: Injective b.toDual
  proof: fun x y h => b.ext_elem_iff.mpr fun i => by
  simp_rw [← toDual_eq_repr]; exact DFunLike.congr_fun h _

中文:
定理 toDual_injective
  结论: Injective b.toDual
  证明: fun x y h => b.ext_elem_iff.mpr fun i => by
  simp_rw [← toDual_eq_repr]; exact DFunLike.congr_fun h _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, b.ext_elem_iff.mpr, congr_fun, ext_elem_iff, simp_rw, toDual_eq_repr
-/
theorem toDual_injective : Injective b.toDual := fun x y h => b.ext_elem_iff.mpr fun i => by
  simp_rw [← toDual_eq_repr]; exact DFunLike.congr_fun h _

/--
theorem `toDual_inj` / 定理 `toDual_inj`

English:
theorem toDual_inj
  given: (m : M) (a : b.toDual m = 0)
  statement: m = 0
  proof: b.toDual_injective (by rwa [map_zero])

中文:
定理 toDual_inj
  条件: (m : M) (a : b.toDual m = 0)
  结论: m = 0
  证明: b.toDual_injective (by rwa [map_zero])

Depends on / 依赖: b.toDual_injective, map_zero, toDual_injective
-/
theorem toDual_inj (m : M) (a : b.toDual m = 0) : m = 0 :=
  b.toDual_injective (by rwa [map_zero])

/--
theorem `toDual_ker` / 定理 `toDual_ker`

English:
theorem toDual_ker
  statement: LinearMap.ker b.toDual = ⊥
  proof: ker_eq_bot'.mpr b.toDual_inj

中文:
定理 toDual_ker
  结论: LinearMap.ker b.toDual = ⊥
  证明: ker_eq_bot'.mpr b.toDual_inj

Depends on / 依赖: b.toDual_inj, ker_eq_bot, toDual_inj
-/
theorem toDual_ker : LinearMap.ker b.toDual = ⊥ :=
  ker_eq_bot'.mpr b.toDual_inj

/--
theorem `toDual_range` / 定理 `toDual_range`

English:
theorem toDual_range
  given: [Finite ι]
  statement: LinearMap.range b.toDual = ⊤
  proof: eq_top_iff'.2 fun f => ⟨Finsupp.linearCombination R b
    Finsupp.equivFunOnFinite.symm fun i => f (b i), b.ext fun i => by simp⟩

omit [DecidableEq ι] in
@[simp]

中文:
定理 toDual_range
  条件: [Finite ι]
  结论: LinearMap.range b.toDual = ⊤
  证明: eq_top_iff'.2 fun f => ⟨Finsupp.linearCombination R b
    Finsupp.equivFunOnFinite.symm fun i => f (b i), b.ext fun i => by simp⟩

omit [DecidableEq ι] in
@[simp]

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.symm, Finsupp.linearCombination, b.ext, eq_top_iff, equivFunOnFinite, linearCombination
-/
theorem toDual_range [Finite ι] : LinearMap.range b.toDual = ⊤ :=
eq_top_iff'.2 fun f => ⟨Finsupp.linearCombination R b
    Finsupp.equivFunOnFinite.symm fun i => f (b i), b.ext fun i => by simp⟩

omit [DecidableEq ι] in
@[simp]
/--
theorem `sum_dual_apply_smul_coord` / 定理 `sum_dual_apply_smul_coord`

English:
theorem sum_dual_apply_smul_coord
  given: [Fintype ι] (f : Module.Dual R M)
  proof: by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul,
    ← f.map_smul, ← map_sum, Basis.coord_apply, Basis.sum_repr]

中文:
定理 sum_dual_apply_smul_coord
  条件: [Fintype ι] (f : Module.Dual R M)
  证明: by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul,
    ← f.map_smul, ← map_sum, Basis.coord_apply, Basis.sum_repr]

Depends on / 依赖: Basis.coord_apply, Basis.sum_repr, LinearMap, LinearMap.smul_apply, LinearMap.sum_apply, coord_apply, f.map_smul, map_smul, map_sum, mul_comm, simp_rw, smul_apply, smul_eq_mul, sum_apply, sum_repr
-/
theorem sum_dual_apply_smul_coord [Fintype ι] (f : Module.Dual R M) :
    (∑ x, f (b x) • b.coord x) = f := by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul,
    ← f.map_smul, ← map_sum, Basis.coord_apply, Basis.sum_repr]

section Finite

variable [Finite ι]

/--
Definition of `toDualEquiv` / `toDualEquiv` 的定义

English:
definition toDualEquiv
  signature: : M ≃ₗ[R] Dual R M
  body: .ofBijective b.toDual ⟨b.toDual_injective, range_eq_top.mp b.toDual_range⟩

中文:
定义 toDualEquiv
  签名: : M ≃ₗ[R] Dual R M
  定义体: .ofBijective b.toDual ⟨b.toDual_injective, range_eq_top.mp b.toDual_range⟩

Depends on / 依赖: b.toDual, b.toDual_injective, b.toDual_range, ofBijective, range_eq_top, range_eq_top.mp, toDual, toDual_injective, toDual_range
-/
def toDualEquiv : M ≃ₗ[R] Dual R M :=
  .ofBijective b.toDual ⟨b.toDual_injective, range_eq_top.mp b.toDual_range⟩

-- `simps` times out when generating this
@[simp]
/--
theorem `toDualEquiv_apply` / 定理 `toDualEquiv_apply`

English:
theorem toDualEquiv_apply
  given: (m : M)
  statement: b.toDualEquiv m = b.toDual m
  proof: rfl

中文:
定理 toDualEquiv_apply
  条件: (m : M)
  结论: b.toDualEquiv m = b.toDual m
  证明: rfl
-/
theorem toDualEquiv_apply (m : M) : b.toDualEquiv m = b.toDual m :=
  rfl

/--
Definition of `dualBasis` / `dualBasis` 的定义

English:
definition dualBasis
  signature: : Basis ι R (Dual R M)
  body: b.map b.toDualEquiv

中文:
定义 dualBasis
  签名: : Basis ι R (Dual R M)
  定义体: b.map b.toDualEquiv

Depends on / 依赖: b.map, b.toDualEquiv, toDualEquiv
-/
def dualBasis : Basis ι R (Dual R M) :=
  b.map b.toDualEquiv

-- We use `j = i` to match `Basis.repr_self`
/--
theorem `dualBasis_apply_self` / 定理 `dualBasis_apply_self`

English:
theorem dualBasis_apply_self
  given: (i j : ι)
  statement: b.dualBasis i (b j) =
  proof: by
  convert! b.toDual_apply i j using 2
  rw [@eq_comm _ j i]

中文:
定理 dualBasis_apply_self
  条件: (i j : ι)
  结论: b.dualBasis i (b j) =
  证明: by
  convert! b.toDual_apply i j using 2
  rw [@eq_comm _ j i]

Depends on / 依赖: b.toDual_apply, convert, eq_comm, toDual_apply
-/
theorem dualBasis_apply_self (i j : ι) : b.dualBasis i (b j) =
    if j = i then 1 else 0 := by
  convert! b.toDual_apply i j using 2
  rw [@eq_comm _ j i]

/--
theorem `linearCombination_dualBasis` / 定理 `linearCombination_dualBasis`

English:
theorem linearCombination_dualBasis
  given: (f : ι ->₀ R) (i : ι)
  proof: by
  cases nonempty_fintype ι
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_fintype]; rw [LinearMap.sum_apply]
  · simp_rw [LinearMap.smul_apply, smul_eq_mul, dualBasis_apply_self, mul_boole,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  · intro
    rw [zero_smul]

中文:
定理 linearCombination_dualBasis
  条件: (f : ι ->₀ R) (i : ι)
  证明: by
  cases nonempty_fintype ι
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_fintype]; rw [LinearMap.sum_apply]
  · simp_rw [LinearMap.smul_apply, smul_eq_mul, dualBasis_apply_self, mul_boole,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  · intro
    rw [zero_smul]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_ite_eq, Finsupp, Finsupp.linearCombination_apply, Finsupp.sum_fintype, LinearMap, LinearMap.smul_apply, LinearMap.sum_apply, dualBasis_apply_self, if_pos, linearCombination_apply, mem_univ, mul_boole, nonempty_fintype, simp_rw, smul_apply, smul_eq_mul, sum_apply, sum_fintype
-/
theorem linearCombination_dualBasis (f : ι ->₀ R) (i : ι) :
    Finsupp.linearCombination R b.dualBasis f (b i) = f i := by
  cases nonempty_fintype ι
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_fintype]; rw [LinearMap.sum_apply]
  · simp_rw [LinearMap.smul_apply, smul_eq_mul, dualBasis_apply_self, mul_boole,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  · intro
    rw [zero_smul]

/--
theorem `dualBasis_repr` / 定理 `dualBasis_repr`

English:
theorem dualBasis_repr
  given: (l : Dual R M) (i : ι)
  statement: b.dualBasis.repr l i = l (b i)
  proof: by
  rw [← linearCombination_dualBasis b]; rw [Basis.linearCombination_repr b.dualBasis l]

中文:
定理 dualBasis_repr
  条件: (l : Dual R M) (i : ι)
  结论: b.dualBasis.repr l i = l (b i)
  证明: by
  rw [← linearCombination_dualBasis b]; rw [Basis.linearCombination_repr b.dualBasis l]
-/
@[simp] theorem dualBasis_repr (l : Dual R M) (i : ι) : b.dualBasis.repr l i = l (b i) := by
  rw [← linearCombination_dualBasis b]; rw [Basis.linearCombination_repr b.dualBasis l]

/--
theorem `dualBasis_apply` / 定理 `dualBasis_apply`

English:
theorem dualBasis_apply
  given: (i : ι) (m : M)
  statement: b.dualBasis i m = b.repr m i
  proof: b.toDual_apply_right i m

@[simp]

中文:
定理 dualBasis_apply
  条件: (i : ι) (m : M)
  结论: b.dualBasis i m = b.repr m i
  证明: b.toDual_apply_right i m

@[simp]

Depends on / 依赖: b.toDual_apply_right, toDual_apply_right
-/
theorem dualBasis_apply (i : ι) (m : M) : b.dualBasis i m = b.repr m i :=
  b.toDual_apply_right i m

@[simp]
/--
theorem `coe_dualBasis` / 定理 `coe_dualBasis`

English:
theorem coe_dualBasis
  statement: ⇑b.dualBasis = b.coord
  proof: by
  ext i x
  apply dualBasis_apply

@[simp]

中文:
定理 coe_dualBasis
  结论: ⇑b.dualBasis = b.coord
  证明: by
  ext i x
  apply dualBasis_apply

@[simp]

Depends on / 依赖: dualBasis_apply
-/
theorem coe_dualBasis : ⇑b.dualBasis = b.coord := by
  ext i x
  apply dualBasis_apply

@[simp]
/--
theorem `toDual_toDual` / 定理 `toDual_toDual`

English:
theorem toDual_toDual
  statement: b.dualBasis.toDual.comp b.toDual = Dual.eval R M
  proof: by
  refine b.ext fun i => b.dualBasis.ext fun j => ?_
  rw [LinearMap.comp_apply]; rw [toDual_apply_left]; rw [coe_toDual_self]; rw [← coe_dualBasis]; rw [Dual.eval_apply]; rw [Basis.repr_self]; rw [Finsupp.single_apply]; rw [dualBasis_apply_self]

中文:
定理 toDual_toDual
  结论: b.dualBasis.toDual.comp b.toDual = Dual.eval R M
  证明: by
  refine b.ext fun i => b.dualBasis.ext fun j => ?_
  rw [LinearMap.comp_apply]; rw [toDual_apply_left]; rw [coe_toDual_self]; rw [← coe_dualBasis]; rw [Dual.eval_apply]; rw [Basis.repr_self]; rw [Finsupp.single_apply]; rw [dualBasis_apply_self]

Depends on / 依赖: Basis.repr_self, Dual.eval_apply, Finsupp, Finsupp.single_apply, LinearMap, LinearMap.comp_apply, b.dualBasis.ext, b.ext, coe_dualBasis, coe_toDual_self, comp_apply, dualBasis, dualBasis_apply_self, eval_apply, repr_self, single_apply, toDual_apply_left
-/
theorem toDual_toDual : b.dualBasis.toDual.comp b.toDual = Dual.eval R M := by
  refine b.ext fun i => b.dualBasis.ext fun j => ?_
  rw [LinearMap.comp_apply]; rw [toDual_apply_left]; rw [coe_toDual_self]; rw [← coe_dualBasis]; rw [Dual.eval_apply]; rw [Basis.repr_self]; rw [Finsupp.single_apply]; rw [dualBasis_apply_self]

end Finite

/--
theorem `dualBasis_equivFun` / 定理 `dualBasis_equivFun`

English:
theorem dualBasis_equivFun
  given: [Finite ι] (l : Dual R M) (i : ι)
  proof: by rw [Basis.equivFun_apply, dualBasis_repr]

中文:
定理 dualBasis_equivFun
  条件: [Finite ι] (l : Dual R M) (i : ι)
  证明: by rw [Basis.equivFun_apply, dualBasis_repr]

Depends on / 依赖: Basis.equivFun_apply, dualBasis_repr, equivFun_apply
-/
theorem dualBasis_equivFun [Finite ι] (l : Dual R M) (i : ι) :
    b.dualBasis.equivFun l i = l (b i) := by rw [Basis.equivFun_apply, dualBasis_repr]

/--
theorem `eval_injective` / 定理 `eval_injective`

English:
theorem eval_injective
  given: {ι : Type*} (b : Basis ι R M)
  statement: Function.Injective (Dual.eval R M)
  proof: by
  intro m m' eq
  simp_rw [LinearMap.ext_iff, Dual.eval_apply] at eq
  exact b.ext_elem fun i => eq (b.coord i)

中文:
定理 eval_injective
  条件: {ι : 类型} (b : Basis ι R M)
  结论: Function.Injective (Dual.eval R M)
  证明: by
  intro m m' eq
  simp_rw [LinearMap.ext_iff, Dual.eval_apply] at eq
  exact b.ext_elem fun i => eq (b.coord i)

Depends on / 依赖: Dual.eval_apply, LinearMap, LinearMap.ext_iff, _enorm, b.coord, b.ext_elem, eval_apply, ext_elem, ext_iff, hp_ne_top, hp_ne_zero, meas_ge_lt_top, p.meas_ge_lt_top, simp_rw
-/
theorem eval_injective {ι : Type*} (b : Basis ι R M) : Function.Injective (Dual.eval R M) := by
  intro m m' eq
  simp_rw [LinearMap.ext_iff, Dual.eval_apply] at eq
  exact b.ext_elem fun i => eq (b.coord i)

/--
theorem `eval_ker` / 定理 `eval_ker`

English:
theorem eval_ker
  given: {ι : Type*} (b : Basis ι R M)
  statement: LinearMap.ker (Dual.eval R M) = ⊥
  proof: ker_eq_bot_of_injective (eval_injective b)

中文:
定理 eval_ker
  条件: {ι : 类型} (b : Basis ι R M)
  结论: LinearMap.ker (Dual.eval R M) = ⊥
  证明: ker_eq_bot_of_injective (eval_injective b)

Depends on / 依赖: eval_injective, ker_eq_bot_of_injective
-/
theorem eval_ker {ι : Type*} (b : Basis ι R M) : LinearMap.ker (Dual.eval R M) = ⊥ :=
  ker_eq_bot_of_injective (eval_injective b)

/--
theorem `eval_range` / 定理 `eval_range`

English:
theorem eval_range
  given: {ι : Type*} [Finite ι] (b : Basis ι R M)
  proof: by
  classical
    cases nonempty_fintype ι
    rw [← b.toDual_toDual]; rw [range_comp]; rw [b.toDual_range]; rw [Submodule.map_top]; rw [toDual_range _]

中文:
定理 eval_range
  条件: {ι : 类型} [Finite ι] (b : Basis ι R M)
  证明: by
  classical
    cases nonempty_fintype ι
    rw [← b.toDual_toDual]; rw [range_comp]; rw [b.toDual_range]; rw [Submodule.map_top]; rw [toDual_range _]

Depends on / 依赖: Submodule, Submodule.map_top, b.toDual_range, b.toDual_toDual, classical, map_top, nonempty_fintype, range_comp, toDual_range, toDual_toDual
-/
theorem eval_range {ι : Type*} [Finite ι] (b : Basis ι R M) :
    LinearMap.range (Dual.eval R M) = ⊤ := by
  classical
    cases nonempty_fintype ι
    rw [← b.toDual_toDual]; rw [range_comp]; rw [b.toDual_range]; rw [Submodule.map_top]; rw [toDual_range _]

/--
lemma `dualBasis_coord_toDualEquiv_apply` / 引理 `dualBasis_coord_toDualEquiv_apply`

English:
lemma dualBasis_coord_toDualEquiv_apply
  given: [Finite ι] (i : ι) (f : M)
  proof: by
  simp [-toDualEquiv_apply, Basis.dualBasis]

中文:
引理 dualBasis_coord_toDualEquiv_apply
  条件: [Finite ι] (i : ι) (f : M)
  证明: by
  simp [-toDualEquiv_apply, Basis.dualBasis]

Depends on / 依赖: Basis.dualBasis, ENNReal, ENNReal.rpow_zero, _eq_lintegral_enorm, dualBasis, eLpNorm, h_rw, hp0_lt, hpq_eq, hq0_lt, lintegral_congr, lt_of_le_of_ne, lt_of_lt_of_le, mul_one, repeat, rpow_zero, sub_self, toDualEquiv_apply
-/
lemma dualBasis_coord_toDualEquiv_apply [Finite ι] (i : ι) (f : M) :
    b.dualBasis.coord i (b.toDualEquiv f) = b.coord i f := by
  simp [-toDualEquiv_apply, Basis.dualBasis]

/--
lemma `coord_toDualEquiv_symm_apply` / 引理 `coord_toDualEquiv_symm_apply`

English:
lemma coord_toDualEquiv_symm_apply
  given: [Finite ι] (i : ι) (f : Module.Dual R M)
  proof: by
  simp [Basis.dualBasis]

omit [DecidableEq ι]

中文:
引理 coord_toDualEquiv_symm_apply
  条件: [Finite ι] (i : ι) (f : Module.Dual R M)
  证明: by
  simp [Basis.dualBasis]

omit [DecidableEq ι]

Depends on / 依赖: Basis.dualBasis, ENNReal, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_mul, ENNReal.rpow_one, dualBasis, eLpNorm, eLpNormEssSup, enorm_ae_le_eLpNormEssSup, h_le, h_nnnorm_le_eLpNorm_ess_sup, h_nnnorm_le_eLpNorm_ess_sup.mono, hq_pos, hq_pos.le, lintegral_const, lintegral_mono_ae, mul_rpow_of_nonneg, ne_of_lt, nth_rw, one_div
-/
lemma coord_toDualEquiv_symm_apply [Finite ι] (i : ι) (f : Module.Dual R M) :
    b.coord i (b.toDualEquiv.symm f) = b.dualBasis.coord i f := by
  simp [Basis.dualBasis]

omit [DecidableEq ι]

/-- `simp` normal form version of `linearCombination_dualBasis` -/
@[simp]
/--
theorem `linearCombination_coord` / 定理 `linearCombination_coord`

English:
theorem linearCombination_coord
  given: [Finite ι] (b : Basis ι R M) (f : ι ->₀ R) (i : ι)
  proof: by
  have := Classical.decEq ι
  rw [← coe_dualBasis]; rw [linearCombination_dualBasis]

中文:
定理 linearCombination_coord
  条件: [Finite ι] (b : Basis ι R M) (f : ι ->₀ R) (i : ι)
  证明: by
  have := Classical.decEq ι
  rw [← coe_dualBasis]; rw [linearCombination_dualBasis]

Depends on / 依赖: Classical, Classical.decEq, coe_dualBasis, linearCombination_dualBasis
-/
theorem linearCombination_coord [Finite ι] (b : Basis ι R M) (f : ι ->₀ R) (i : ι) :
    Finsupp.linearCombination R b.coord f (b i) = f i := by
  have := Classical.decEq ι
  rw [← coe_dualBasis]; rw [linearCombination_dualBasis]

end CommSemiring

end Module.Basis

section DualBases

variable {R M ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

open Lean.Elab.Tactic in
/-- Try using `Set.toFinite` to dispatch a `Set.Finite` goal. -/
meta def evalUseFiniteInstance : TacticM Unit := do
  evalTactic (← `(tactic| intros; apply Set.toFinite))

@[inherit_doc evalUseFiniteInstance]
elab "use_finite_instance" : tactic => evalUseFiniteInstance

/--
Definition of `Module.DualBases` / `Module.DualBases` 的定义

English:
structure Module.DualBases
  parameters: (e : ι -> M) (ε : ι -> Dual R M)
  axioms and operations (4):
    - eval_same : forall i, ε i (e i) = 1
    - eval_of_ne : Pairwise fun i j => ε i (e j) = 0
    - total : forall {m₁ m₂ : M}, (forall i, ε i m₁ = ε i m₂) -> m₁ = m₂
    - finite : forall m : M, {i | ε i m != 0}.Finite  [default: by use_finite_instance]

中文:
结构 Module.DualBases
  参数: (e : ι -> M) (ε : ι -> Dual R M)
  公理与运算 (4 个):
    - eval_same : 对任意 i, ε i (e i) = 1
    - eval_of_ne : Pairwise fun i j => ε i (e j) = 0
    - total : 对任意 {m₁ m₂ : M}, (对任意 i, ε i m₁ = ε i m₂) -> m₁ = m₂
    - finite : 对任意 m : M, {i | ε i m != 0}.Finite  [默认: by use_finite_instance]

Depends on / 依赖: ENNReal, ENNReal.one_rpow, _le_eLpNorm, _mul_rpow_measure_univ, eLpNorm, hp0_lt, measure_univ, mul_one, one_rpow, use_finite_instance
-/
structure Module.DualBases (e : ι -> M) (ε : ι -> Dual R M) : Prop where
  eval_same : forall i, ε i (e i) = 1
  eval_of_ne : Pairwise fun i j => ε i (e j) = 0
  protected total : forall {m₁ m₂ : M}, (forall i, ε i m₁ = ε i m₂) -> m₁ = m₂
  protected finite : forall m : M, {i | ε i m != 0}.Finite := by use_finite_instance

end DualBases

namespace Module.DualBases

open LinearMap Function

variable {R M ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {e : ι -> M} {ε : ι -> Dual R M}

/--
Definition of `coeffs` / `coeffs` 的定义

English:
definition coeffs
  signature: (h : DualBases e ε) (m : M)
  body: ε i m
  support := (h.finite m).toFinset
  mem_support_toFun i := by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

@[simp]

中文:
定义 coeffs
  签名: (h : DualBases e ε) (m : M)
  定义体: ε i m
  support := (h.finite m).toFinset
  mem_support_toFun i := by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

@[simp]

Depends on / 依赖: _le_eLpNormEssSup_mul_rpow_measure_univ, eLpNorm, hq_pos, measure_univ, trans_eq
-/
def coeffs (h : DualBases e ε) (m : M) : ι ->₀ R where
  toFun i := ε i m
  support := (h.finite m).toFinset
  mem_support_toFun i := by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

@[simp]
/--
theorem `coeffs_apply` / 定理 `coeffs_apply`

English:
theorem coeffs_apply
  given: (h : DualBases e ε) (m : M) (i : ι)
  statement: h.coeffs m i = ε i m
  proof: rfl

中文:
定理 coeffs_apply
  条件: (h : DualBases e ε) (m : M) (i : ι)
  结论: h.coeffs m i = ε i m
  证明: rfl
-/
theorem coeffs_apply (h : DualBases e ε) (m : M) (i : ι) : h.coeffs m i = ε i m :=
  rfl

/--
Definition of `lc` / `lc` 的定义

English:
definition lc
  signature: {ι} (e : ι -> M) (l : ι ->₀ R)
  body: l.sum fun (i : ι) (a : R) => a • e i

中文:
定义 lc
  签名: {ι} (e : ι -> M) (l : ι ->₀ R)
  定义体: l.sum fun (i : ι) (a : R) => a • e i

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top_iff, ENNReal.rpow_lt_top_of_nonneg, Or.inl, Set.univ, _le_eLpNorm, _mul_rpow_measure_univ, eLpNorm, finiteness, hfq_lt_top, hp_nonneg, hp_nonpos, hp_pos, hq_pos, l.sum, le_antisymm, le_or_gt, le_sub_comm, lt_of_lt_of_le, mul_lt_top_iff
-/
def lc {ι} (e : ι -> M) (l : ι ->₀ R) : M :=
  l.sum fun (i : ι) (a : R) => a • e i

/--
theorem `lc_def` / 定理 `lc_def`

English:
theorem lc_def
  given: (e : ι -> M) (l : ι ->₀ R)
  statement: lc e l = Finsupp.linearCombination R e l
  proof: rfl

中文:
定理 lc_def
  条件: (e : ι -> M) (l : ι ->₀ R)
  结论: lc e l = Finsupp.linearCombination R e l
  证明: rfl
-/
theorem lc_def (e : ι -> M) (l : ι ->₀ R) : lc e l = Finsupp.linearCombination R e l :=
  rfl

open Module

variable (h : DualBases e ε)
include h

/--
theorem `dual_lc` / 定理 `dual_lc`

English:
theorem dual_lc
  given: (l : ι ->₀ R) (i : ι)
  statement: ε i (DualBases.lc e l) = l i
  proof: by
  rw [lc]; rw [map_finsuppSum]; rw [Finsupp.sum_eq_single i (g := fun a b => (ε i) (b • e a))]
  · simp [h.eval_same, smul_eq_mul]
  · intro q _ q_ne
    simp [h.eval_of_ne q_ne.symm, smul_eq_mul]
  · simp

@[simp]

中文:
定理 dual_lc
  条件: (l : ι ->₀ R) (i : ι)
  结论: ε i (DualBases.lc e l) = l i
  证明: by
  rw [lc]; rw [map_finsuppSum]; rw [Finsupp.sum_eq_single i (g := fun a b => (ε i) (b • e a))]
  · simp [h.eval_same, smul_eq_mul]
  · intro q _ q_ne
    simp [h.eval_of_ne q_ne.symm, smul_eq_mul]
  · simp

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_eq_single, eval_of_ne, eval_same, h.eval_of_ne, h.eval_same, map_finsuppSum, q_ne, q_ne.symm, smul_eq_mul, sum_eq_single
-/
theorem dual_lc (l : ι ->₀ R) (i : ι) : ε i (DualBases.lc e l) = l i := by
  rw [lc]; rw [map_finsuppSum]; rw [Finsupp.sum_eq_single i (g := fun a b => (ε i) (b • e a))]
  · simp [h.eval_same, smul_eq_mul]
  · intro q _ q_ne
    simp [h.eval_of_ne q_ne.symm, smul_eq_mul]
  · simp

@[simp]
/--
theorem `coeffs_lc` / 定理 `coeffs_lc`

English:
theorem coeffs_lc
  given: (l : ι ->₀ R)
  statement: h.coeffs (DualBases.lc e l) = l
  proof: by
  ext i
  rw [h.coeffs_apply]; rw [h.dual_lc]

中文:
定理 coeffs_lc
  条件: (l : ι ->₀ R)
  结论: h.coeffs (DualBases.lc e l) = l
  证明: by
  ext i
  rw [h.coeffs_apply]; rw [h.dual_lc]

Depends on / 依赖: coeffs_apply, dual_lc, h.coeffs_apply, h.dual_lc
-/
theorem coeffs_lc (l : ι ->₀ R) : h.coeffs (DualBases.lc e l) = l := by
  ext i
  rw [h.coeffs_apply]; rw [h.dual_lc]

/-- For any `m : M n`, $\sum_{p ∈ Q n} (ε p m) • e p = m$ -/
@[simp]
/--
theorem `lc_coeffs` / 定理 `lc_coeffs`

English:
theorem lc_coeffs
  given: (m : M)
  statement: DualBases.lc e (h.coeffs m) = m
  proof: h.total by simp [h.dual_lc]

中文:
定理 lc_coeffs
  条件: (m : M)
  结论: DualBases.lc e (h.coeffs m) = m
  证明: h.total by simp [h.dual_lc]

Depends on / 依赖: dual_lc, h.dual_lc, h.total
-/
theorem lc_coeffs (m : M) : DualBases.lc e (h.coeffs m) = m := h.total by simp [h.dual_lc]

/-- `(h : DualBases e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps repr_apply, simps -isSimp repr_symm_apply]
/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Basis ι R M
  body: Basis.ofRepr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }

@[simp]

中文:
定义 basis
  签名: : Basis ι R M
  定义体: Basis.ofRepr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }

@[simp]

Depends on / 依赖: Basis.ofRepr, ENNReal, ENNReal.coe_le_coe, ENNReal.ofReal_coe_nnreal, Pi.smul_def, Real.enorm_eq_ofReal, _const_smul, c.coe_nonneg, coe_le_coe, coe_nonneg, coeffs, coeffs_lc, eLpNorm, enorm_, enorm_eq_nnnorm, enorm_eq_ofReal, h.mono, hro_lt, invFun, lc_coeffs
-/
def basis : Basis ι R M :=
  Basis.ofRepr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }

@[simp]
/--
theorem `coe_basis` / 定理 `coe_basis`

English:
theorem coe_basis
  statement: ⇑h.basis = e
  proof: by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rcases eq_or_ne i j with rfl | hne
  · simp [h.eval_same]
  · simp [hne, h.eval_of_ne hne.symm]

中文:
定理 coe_basis
  结论: ⇑h.basis = e
  证明: by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rcases eq_or_ne i j with rfl | hne
  · simp [h.eval_same]
  · simp [hne, h.eval_of_ne hne.symm]

Depends on / 依赖: Basis.apply_eq_iff, apply_eq_iff, eq_or_ne, eval_of_ne, eval_same, h.eval_of_ne, h.eval_same, hne.symm
-/
theorem coe_basis : ⇑h.basis = e := by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rcases eq_or_ne i j with rfl | hne
  · simp [h.eval_same]
  · simp [hne, h.eval_of_ne hne.symm]

/--
theorem `mem_of_mem_span` / 定理 `mem_of_mem_span`

English:
theorem mem_of_mem_span
  given: {H : Set ι} {x : M} (hmem : x in Submodule.span R (e '' H))
  proof: by
  intro i hi
  rcases (Finsupp.mem_span_image_iff_linearCombination _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi

中文:
定理 mem_of_mem_span
  条件: {H : Set ι} {x : M} (hmem : x in Submodule.span R (e '' H))
  证明: by
  intro i hi
  rcases (Finsupp.mem_span_image_iff_linearCombination _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi

Depends on / 依赖: Finsupp, Finsupp.mem_span_image_iff_linearCombination, Finsupp.mem_supported, dual_lc, h.dual_lc, lc_def, mem_span_image_iff_linearCombination, mem_supported, not_imp_comm, not_imp_comm.mp, supp_l
-/
theorem mem_of_mem_span {H : Set ι} {x : M} (hmem : x in Submodule.span R (e '' H)) :
    forall i : ι, ε i x != 0 -> i in H := by
  intro i hi
  rcases (Finsupp.mem_span_image_iff_linearCombination _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi

/--
theorem `coe_dualBasis` / 定理 `coe_dualBasis`

English:
theorem coe_dualBasis
  given: [DecidableEq ι] [Finite ι]
  statement: ⇑h.basis.dualBasis = ε
  proof: funext fun i => h.basis.ext fun j => by simp

中文:
定理 coe_dualBasis
  条件: [DecidableEq ι] [Finite ι]
  结论: ⇑h.basis.dualBasis = ε
  证明: funext fun i => h.basis.ext fun j => by simp

Depends on / 依赖: h.basis.ext
-/
theorem coe_dualBasis [DecidableEq ι] [Finite ι] : ⇑h.basis.dualBasis = ε :=
  funext fun i => h.basis.ext fun j => by simp

end Module.DualBases
