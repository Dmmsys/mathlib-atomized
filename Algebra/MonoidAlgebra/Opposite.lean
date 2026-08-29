/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Finsupp.Basic

/-!
# Monoid algebras and the opposite ring
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

@[expose] public noncomputable section

open Finsupp MulOpposite

variable {R M : Type*} [Semiring R] [Mul M]

namespace MonoidAlgebra

/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/
@[to_additive (dont_translate := R) (attr := simps! +simpRhs apply symm_apply)
/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def opRingEquiv
  body: opAddEquiv.symm.trans (mapDomainAddEquiv _ opEquiv).trans mapAddEquiv _ opAddEquiv
  map_mul' := by
    classical
    simp [coeff_mul, MonoidAlgebra.ext_iff, Finsupp.ext_iff, ← MulOpposite.unop_inj,
      unop_finsuppSum, sum_mapRange_index, apply_ite unop, mapAddEquiv]
    simpa using fun _ _ _ => 

中文:
定义 noncomputable
  签名: def opRingEquiv
  定义体: opAddEquiv.symm.trans (mapDomainAddEquiv _ opEquiv).trans mapAddEquiv _ opAddEquiv
  map_mul' := by
    classical
    simp [coeff_mul, MonoidAlgebra.ext_iff, Finsupp.ext_iff, ← MulOpposite.unop_inj,
      unop_finsuppSum, sum_mapRange_index, apply_ite unop, mapAddEquiv]
    simpa using fun _ _ _ => 
-/
protected noncomputable def opRingEquiv : R[M]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[Mᵐᵒᵖ] where
  toAddEquiv :=
opAddEquiv.symm.trans (mapDomainAddEquiv _ opEquiv).trans mapAddEquiv _ opAddEquiv
  map_mul' := by
    classical
    simp [coeff_mul, MonoidAlgebra.ext_iff, Finsupp.ext_iff, ← MulOpposite.unop_inj,
      unop_finsuppSum, sum_mapRange_index, apply_ite unop, mapAddEquiv]
    simpa using fun _ _ _ => Finsupp.sum_comm ..

@[to_additive (dont_translate := R)]
/--
lemma `opRingEquiv_single` / 引理 `opRingEquiv_single`

English:
lemma opRingEquiv_single
  given: (r : R) (x : M)
  proof: by ext; simp

@[to_additive (dont_translate := R)]

中文:
引理 opRingEquiv_single
  条件: (r : R) (x : M)
  证明: by ext; simp

@[to_additive (dont_translate := R)]
-/
lemma opRingEquiv_single (r : R) (x : M) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by ext; simp

@[to_additive (dont_translate := R)]
/--
lemma `opRingEquiv_symm_single` / 引理 `opRingEquiv_symm_single`

English:
lemma opRingEquiv_symm_single
  given: (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ)
  proof: by
  apply MulOpposite.unop_injective; ext; simp

中文:
引理 opRingEquiv_symm_single
  条件: (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ)
  证明: by
  apply MulOpposite.unop_injective; ext; simp

Depends on / 依赖: MulOpposite, MulOpposite.unop_injective, unop_injective
-/
lemma opRingEquiv_symm_single (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by
  apply MulOpposite.unop_injective; ext; simp

end MonoidAlgebra
