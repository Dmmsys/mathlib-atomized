/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finitely generated product (sub)modules

-/

public section

open Function (Surjective)

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

variable {P : Type*} [AddCommMonoid P] [Module R P]

/--
theorem `FG.prod` / 定理 `FG.prod`

English:
theorem FG.prod
  given: {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.FG) (hsc : sc.FG)
  proof: let ⟨tb, htb⟩ := fg_def.1 hsb
  let ⟨tc, htc⟩ := fg_def.1 hsc
  fg_def.2
    ⟨LinearMap.inl R M P '' tb union LinearMap.inr R M P '' tc, (htb.1.image _).union (htc.1.image _),
      by rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩

中文:
定理 FG.prod
  条件: {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.FG) (hsc : sc.FG)
  证明: let ⟨tb, htb⟩ := fg_def.1 hsb
  let ⟨tc, htc⟩ := fg_def.1 hsc
  fg_def.2
    ⟨LinearMap.inl R M P '' tb union LinearMap.inr R M P '' tc, (htb.1.image _).union (htc.1.image _),
      by rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩
-/
theorem FG.prod {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.FG) (hsc : sc.FG) :
    (sb.prod sc).FG :=
  let ⟨tb, htb⟩ := fg_def.1 hsb
  let ⟨tc, htc⟩ := fg_def.1 hsc
  fg_def.2
    ⟨LinearMap.inl R M P '' tb union LinearMap.inr R M P '' tc, (htb.1.image _).union (htc.1.image _),
      by rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩

end Submodule

namespace Module

namespace Finite

variable {R M N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: [hM : Module.Finite R M] [hN : Module.Finite R N]
  body: ⟨by
    rw [← Submodule.prod_top]
    exact hM.1.prod hN.1⟩

中文:
实例 prod
  签名: [hM : Module.Finite R M] [hN : Module.Finite R N]
  定义体: ⟨by
    rw [← Submodule.prod_top]
    exact hM.1.prod hN.1⟩

Depends on / 依赖: Submodule, Submodule.prod_top, prod_top
-/
instance prod [hM : Module.Finite R M] [hN : Module.Finite R N] : Module.Finite R (M × N) :=
  ⟨by
    rw [← Submodule.prod_top]
    exact hM.1.prod hN.1⟩

end Finite

end Module
