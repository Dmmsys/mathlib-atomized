/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Jacobson radical of modules and rings

## Main definitions

`Module.jacobson R M`: the Jacobson radical of a module `M` over a ring `R` is defined to be the
intersection of all maximal submodules of `M`.

`Ring.jacobson R`: the Jacobson radical of a ring `R` is the Jacobson radical of `R` as
an `R`-module, which is equal to the intersection of all maximal left ideals of `R`. It turns out
it is in fact a two-sided ideal, and equals the intersection of all maximal right ideals of `R`.

## Reference
* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

@[expose] public section

assert_not_exists Cardinal

namespace Module

open Submodule

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂]
variable (f : M ->ₛₗ[τ₁₂] M₂)

/--
Definition of `jacobson` / `jacobson` 的定义

English:
definition jacobson
  signature: : Submodule R M
  body: sInf { m : Submodule R M | IsCoatom m }

中文:
定义 jacobson
  签名: : Submodule R M
  定义体: sInf { m : Submodule R M | IsCoatom m }

Depends on / 依赖: IsCoatom, Submodule
-/
def jacobson : Submodule R M :=
  sInf { m : Submodule R M | IsCoatom m }

variable {R R₂ M M₂}

/--
theorem `le_comap_jacobson` / 定理 `le_comap_jacobson`

English:
theorem le_comap_jacobson
  statement: jacobson R M <= comap f (jacobson R₂ M₂)
  proof: by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm => ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top

中文:
定理 le_comap_jacobson
  结论: jacobson R M <= comap f (jacobson R₂ M₂)
  证明: by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm => ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top

Depends on / 依赖: comap_iInf, conv_rhs, isCoatom_comap_or_eq_top, jacobson, le_iInf_iff, le_iInf_iff.mpr, mem_sInf, mem_sInf.mp, mem_top, sInf_eq_iInf
-/
theorem le_comap_jacobson : jacobson R M <= comap f (jacobson R₂ M₂) := by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm => ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top

/--
theorem `map_jacobson_le` / 定理 `map_jacobson_le`

English:
theorem map_jacobson_le
  statement: map f (jacobson R M) <= jacobson R₂ M₂
  proof: map_le_iff_le_comap.mpr (le_comap_jacobson f)

中文:
定理 map_jacobson_le
  结论: map f (jacobson R M) <= jacobson R₂ M₂
  证明: map_le_iff_le_comap.mpr (le_comap_jacobson f)

Depends on / 依赖: le_comap_jacobson, map_le_iff_le_comap, map_le_iff_le_comap.mpr
-/
theorem map_jacobson_le : map f (jacobson R M) <= jacobson R₂ M₂ :=
  map_le_iff_le_comap.mpr (le_comap_jacobson f)

/--
theorem `jacobson_eq_bot_of_injective` / 定理 `jacobson_eq_bot_of_injective`

English:
theorem jacobson_eq_bot_of_injective
  given: (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥)
  proof: le_bot_iff.mp (le_comap_jacobson f).trans by
    simp_rw [h, comap_bot, (LinearMap.ker_eq_bot.mpr inj).le]

中文:
定理 jacobson_eq_bot_of_injective
  条件: (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥)
  证明: le_bot_iff.mp (le_comap_jacobson f).trans by
    simp_rw [h, comap_bot, (LinearMap.ker_eq_bot.mpr inj).le]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mpr, comap_bot, ker_eq_bot, le_bot_iff, le_bot_iff.mp, le_comap_jacobson, simp_rw
-/
theorem jacobson_eq_bot_of_injective (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥) :
    jacobson R M = ⊥ :=
le_bot_iff.mp (le_comap_jacobson f).trans by
    simp_rw [h, comap_bot, (LinearMap.ker_eq_bot.mpr inj).le]

variable {f}

/--
theorem `map_jacobson_of_ker_le` / 定理 `map_jacobson_of_ker_le`

English:
theorem map_jacobson_of_ker_le
  statement: (surj : Function.Surjective f)
  proof: le_antisymm (map_jacobson_le f) by
    rw [jacobson]; rw [sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m => sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)

中文:
定理 map_jacobson_of_ker_le
  结论: (surj : Function.Surjective f)
  证明: le_antisymm (map_jacobson_le f) by
    rw [jacobson]; rw [sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m => sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)

Depends on / 依赖: conv_rhs, isCoatom_map_of_ker_le, jacobson, le_antisymm, le_iInf, le_iInf_iff, le_iInf_iff.mp, map_iInf_of_ker_le, map_jacobson_le, sInf_eq_iInf, sInf_le
-/
theorem map_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f <= jacobson R M) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
le_antisymm (map_jacobson_le f) by
    rw [jacobson]; rw [sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m => sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)

/--
theorem `comap_jacobson_of_ker_le` / 定理 `comap_jacobson_of_ker_le`

English:
theorem comap_jacobson_of_ker_le
  statement: (surj : Function.Surjective f)
  proof: by
  rw [← map_jacobson_of_ker_le surj le]; rw [comap_map_eq_self le]

中文:
定理 comap_jacobson_of_ker_le
  结论: (surj : Function.Surjective f)
  证明: by
  rw [← map_jacobson_of_ker_le surj le]; rw [comap_map_eq_self le]

Depends on / 依赖: comap_map_eq_self, map_jacobson_of_ker_le
-/
theorem comap_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f <= jacobson R M) :
    comap f (jacobson R₂ M₂) = jacobson R M := by
  rw [← map_jacobson_of_ker_le surj le]; rw [comap_map_eq_self le]

/--
theorem `map_jacobson_of_bijective` / 定理 `map_jacobson_of_bijective`

English:
theorem map_jacobson_of_bijective
  given: (hf : Function.Bijective f)
  proof: map_jacobson_of_ker_le hf.2 by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

中文:
定理 map_jacobson_of_bijective
  条件: (hf : Function.Bijective f)
  证明: map_jacobson_of_ker_le hf.2 by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mpr, bot_le, ker_eq_bot, map_jacobson_of_ker_le, simp_rw
-/
theorem map_jacobson_of_bijective (hf : Function.Bijective f) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
map_jacobson_of_ker_le hf.2 by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

/--
theorem `comap_jacobson_of_bijective` / 定理 `comap_jacobson_of_bijective`

English:
theorem comap_jacobson_of_bijective
  given: (hf : Function.Bijective f)
  proof: comap_jacobson_of_ker_le hf.2 by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

中文:
定理 comap_jacobson_of_bijective
  条件: (hf : Function.Bijective f)
  证明: comap_jacobson_of_ker_le hf.2 by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mpr, bot_le, comap_jacobson_of_ker_le, ker_eq_bot, simp_rw
-/
theorem comap_jacobson_of_bijective (hf : Function.Bijective f) :
    comap f (jacobson R₂ M₂) = jacobson R M :=
comap_jacobson_of_ker_le hf.2 by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

/--
theorem `jacobson_quotient_of_le` / 定理 `jacobson_quotient_of_le`

English:
theorem jacobson_quotient_of_le
  given: {N : Submodule R M} (le : N <= jacobson R M)
  proof: (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm

中文:
定理 jacobson_quotient_of_le
  条件: {N : Submodule R M} (le : N <= jacobson R M)
  证明: (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm

Depends on / 依赖: N.mkQ_surjective, ker_mkQ, map_jacobson_of_ker_le, mkQ_surjective
-/
theorem jacobson_quotient_of_le {N : Submodule R M} (le : N <= jacobson R M) :
    jacobson R (M ⧸ N) = map N.mkQ (jacobson R M) :=
  (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm

/--
theorem `jacobson_le_of_eq_bot` / 定理 `jacobson_le_of_eq_bot`

English:
theorem jacobson_le_of_eq_bot
  given: {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥)
  proof: by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

中文:
定理 jacobson_le_of_eq_bot
  条件: {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥)
  证明: by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

Depends on / 依赖: N.ker_mkQ, comap_bot, ker_mkQ, le_comap_jacobson, simp_rw
-/
theorem jacobson_le_of_eq_bot {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥) :
    jacobson R M <= N := by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

variable (R M)

@[simp]
/--
theorem `jacobson_quotient_jacobson` / 定理 `jacobson_quotient_jacobson`

English:
theorem jacobson_quotient_jacobson
  statement: jacobson R (M ⧸ jacobson R M) = ⊥
  proof: by
  rw [jacobson_quotient_of_le le_rfl]; rw [mkQ_map_self]

中文:
定理 jacobson_quotient_jacobson
  结论: jacobson R (M ⧸ jacobson R M) = ⊥
  证明: by
  rw [jacobson_quotient_of_le le_rfl]; rw [mkQ_map_self]

Depends on / 依赖: jacobson_quotient_of_le, le_rfl, mkQ_map_self
-/
theorem jacobson_quotient_jacobson : jacobson R (M ⧸ jacobson R M) = ⊥ := by
  rw [jacobson_quotient_of_le le_rfl]; rw [mkQ_map_self]

/--
theorem `jacobson_lt_top` / 定理 `jacobson_lt_top`

English:
theorem jacobson_lt_top
  given: [Nontrivial M] [IsCoatomic (Submodule R M)]
  statement: jacobson R M < ⊤
  proof: by
  obtain ⟨m, hm, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  exact (sInf_le <| Set.mem_ofPred.mpr hm).trans_lt hm.1.lt_top

example [Nontrivial M] [Module.Finite R M] : jacobson R M < ⊤ := jacobson_lt_top R M

中文:
定理 jacobson_lt_top
  条件: [Nontrivial M] [IsCoatomic (Submodule R M)]
  结论: jacobson R M < ⊤
  证明: by
  obtain ⟨m, hm, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  exact (sInf_le <| Set.mem_ofPred.mpr hm).trans_lt hm.1.lt_top

example [Nontrivial M] [Module.Finite R M] : jacobson R M < ⊤ := jacobson_lt_top R M

Depends on / 依赖: Set.mem_ofPred.mpr, Submodule, bot_ne_top, eq_top_or_exists_le_coatom, lt_top, mem_ofPred, resolve_left, sInf_le, trans_lt
-/
theorem jacobson_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] : jacobson R M < ⊤ := by
  obtain ⟨m, hm, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  exact (sInf_le <| Set.mem_ofPred.mpr hm).trans_lt hm.1.lt_top

example [Nontrivial M] [Module.Finite R M] : jacobson R M < ⊤ := jacobson_lt_top R M

variable {ι} (M : ι -> Type*) [forall i, AddCommGroup (M i)] [forall i, Module R (M i)]

/--
theorem `jacobson_pi_le` / 定理 `jacobson_pi_le`

English:
theorem jacobson_pi_le
  statement: jacobson R (Π i, M i) <= Submodule.pi Set.univ (jacobson R <| M ·)
  proof: by
  simp_rw [← iInf_comap_proj, jacobson, sInf_eq_iInf', comap_iInf, le_iInf_iff]
  intro i m
  exact iInf_le_of_le ⟨_, (isCoatom_comap_iff <| LinearMap.proj_surjective i).mpr m.2⟩ le_rfl

中文:
定理 jacobson_pi_le
  结论: jacobson R (Π i, M i) <= Submodule.pi Set.univ (jacobson R <| M ·)
  证明: by
  simp_rw [← iInf_comap_proj, jacobson, sInf_eq_iInf', comap_iInf, le_iInf_iff]
  intro i m
  exact iInf_le_of_le ⟨_, (isCoatom_comap_iff <| LinearMap.proj_surjective i).mpr m.2⟩ le_rfl

Depends on / 依赖: LinearMap, LinearMap.proj_surjective, comap_iInf, iInf_comap_proj, iInf_le_of_le, isCoatom_comap_iff, jacobson, le_iInf_iff, le_rfl, proj_surjective, sInf_eq_iInf, simp_rw
-/
theorem jacobson_pi_le : jacobson R (Π i, M i) <= Submodule.pi Set.univ (jacobson R <| M ·) := by
  simp_rw [← iInf_comap_proj, jacobson, sInf_eq_iInf', comap_iInf, le_iInf_iff]
  intro i m
  exact iInf_le_of_le ⟨_, (isCoatom_comap_iff <| LinearMap.proj_surjective i).mpr m.2⟩ le_rfl

/--
theorem `jacobson_pi_eq_bot` / 定理 `jacobson_pi_eq_bot`

English:
theorem jacobson_pi_eq_bot
  given: (h : forall i, jacobson R (M i) = ⊥)
  statement: jacobson R (Π i, M i) = ⊥
  proof: le_bot_iff.mp (jacobson_pi_le R M).trans by simp_rw [h, pi_univ_bot, le_rfl]

中文:
定理 jacobson_pi_eq_bot
  条件: (h : 对任意 i, jacobson R (M i) = ⊥)
  结论: jacobson R (Π i, M i) = ⊥
  证明: le_bot_iff.mp (jacobson_pi_le R M).trans by simp_rw [h, pi_univ_bot, le_rfl]

Depends on / 依赖: jacobson_pi_le, le_bot_iff, le_bot_iff.mp, le_rfl, pi_univ_bot, simp_rw
-/
theorem jacobson_pi_eq_bot (h : forall i, jacobson R (M i) = ⊥) : jacobson R (Π i, M i) = ⊥ :=
le_bot_iff.mp (jacobson_pi_le R M).trans by simp_rw [h, pi_univ_bot, le_rfl]

end Module

section

variable (R R₂ : Type*) [Ring R] [Ring R₂] (f : R ->+* R₂) [RingHomSurjective f]
variable (M : Type*) [AddCommGroup M] [Module R M]

namespace Ring

-- TODO: replace all `Ideal.jacobson ⊥` by this.
/--
Definition of `jacobson` / `jacobson` 的定义

English:
abbreviation jacobson
  signature: : Ideal R
  body: Module.jacobson R R

中文:
缩写 jacobson
  签名: : Ideal R
  定义体: Module.jacobson R R

Depends on / 依赖: Module, Module.jacobson, jacobson
-/
abbrev jacobson : Ideal R := Module.jacobson R R

/--
theorem `jacobson_eq_sInf_isMaximal` / 定理 `jacobson_eq_sInf_isMaximal`

English:
theorem jacobson_eq_sInf_isMaximal
  statement: jacobson R = sInf {I : Ideal R | I.IsMaximal}
  proof: by
  simp_rw [jacobson, Module.jacobson, Ideal.isMaximal_def]

中文:
定理 jacobson_eq_sInf_isMaximal
  结论: jacobson R = sInf {I : Ideal R | I.IsMaximal}
  证明: by
  simp_rw [jacobson, Module.jacobson, Ideal.isMaximal_def]

Depends on / 依赖: Ideal.isMaximal_def, Module, Module.jacobson, isMaximal_def, jacobson, simp_rw
-/
theorem jacobson_eq_sInf_isMaximal : jacobson R = sInf {I : Ideal R | I.IsMaximal} := by
  simp_rw [jacobson, Module.jacobson, Ideal.isMaximal_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (jacobson R).IsTwoSided
  body: ⟨fun b ha => Module.le_comap_jacobson (f := LinearMap.toSpanSingleton R R b) ha⟩

中文:
实例 :
  签名: (jacobson R).IsTwoSided
  定义体: ⟨fun b ha => Module.le_comap_jacobson (f := LinearMap.toSpanSingleton R R b) ha⟩

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, Module, Module.le_comap_jacobson, le_comap_jacobson, toSpanSingleton
-/
instance : (jacobson R).IsTwoSided :=
  ⟨fun b ha => Module.le_comap_jacobson (f := LinearMap.toSpanSingleton R R b) ha⟩

variable {R R₂}

/--
lemma `jacobson_le_of_isMaximal` / 引理 `jacobson_le_of_isMaximal`

English:
lemma jacobson_le_of_isMaximal
  given: (m : Ideal R) [m.IsMaximal]
  statement: jacobson R <= m
  proof: by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  exact sInf_le ‹_›

中文:
引理 jacobson_le_of_isMaximal
  条件: (m : Ideal R) [m.IsMaximal]
  结论: jacobson R <= m
  证明: by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  exact sInf_le ‹_›

Depends on / 依赖: Ring.jacobson_eq_sInf_isMaximal, jacobson_eq_sInf_isMaximal, sInf_le
-/
lemma jacobson_le_of_isMaximal (m : Ideal R) [m.IsMaximal] : jacobson R <= m := by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  exact sInf_le ‹_›

/--
theorem `le_comap_jacobson` / 定理 `le_comap_jacobson`

English:
theorem le_comap_jacobson
  statement: jacobson R <= Ideal.comap f (jacobson R₂)
  proof: Module.le_comap_jacobson f.toSemilinearMap

中文:
定理 le_comap_jacobson
  结论: jacobson R <= Ideal.comap f (jacobson R₂)
  证明: Module.le_comap_jacobson f.toSemilinearMap

Depends on / 依赖: Module, Module.le_comap_jacobson, f.toSemilinearMap, le_comap_jacobson, toSemilinearMap
-/
theorem le_comap_jacobson : jacobson R <= Ideal.comap f (jacobson R₂) :=
  Module.le_comap_jacobson f.toSemilinearMap

/--
theorem `map_jacobson_le` / 定理 `map_jacobson_le`

English:
theorem map_jacobson_le
  statement: Submodule.map f.toSemilinearMap (jacobson R) <= jacobson R₂
  proof: Module.map_jacobson_le f.toSemilinearMap

中文:
定理 map_jacobson_le
  结论: Submodule.map f.toSemilinearMap (jacobson R) <= jacobson R₂
  证明: Module.map_jacobson_le f.toSemilinearMap

Depends on / 依赖: Module, Module.map_jacobson_le, f.toSemilinearMap, map_jacobson_le, toSemilinearMap
-/
theorem map_jacobson_le : Submodule.map f.toSemilinearMap (jacobson R) <= jacobson R₂ :=
  Module.map_jacobson_le f.toSemilinearMap

variable {f} in
/--
theorem `map_jacobson_of_ker_le` / 定理 `map_jacobson_of_ker_le`

English:
theorem map_jacobson_of_ker_le
  given: (le : RingHom.ker f <= jacobson R)
  proof: Module.map_jacobson_of_ker_le f.surjective le

中文:
定理 map_jacobson_of_ker_le
  条件: (le : RingHom.ker f <= jacobson R)
  证明: Module.map_jacobson_of_ker_le f.surjective le

Depends on / 依赖: Module, Module.map_jacobson_of_ker_le, f.surjective, map_jacobson_of_ker_le, surjective
-/
theorem map_jacobson_of_ker_le (le : RingHom.ker f <= jacobson R) :
    Submodule.map f.toSemilinearMap (jacobson R) = jacobson R₂ :=
  Module.map_jacobson_of_ker_le f.surjective le

/--
theorem `coe_jacobson_quotient` / 定理 `coe_jacobson_quotient`

English:
theorem coe_jacobson_quotient
  given: (I : Ideal R) [I.IsTwoSided]
  proof: by
  let f : R ⧸ I ->ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨AddHom.id _, fun _ _ => rfl⟩
  rw [jacobson]; rw [← Module.map_jacobson_of_ker_le (f := f) Function.surjective_id]
  · apply Set.image_id
  · rintro _ rfl; exact zero_mem _

中文:
定理 coe_jacobson_quotient
  条件: (I : Ideal R) [I.IsTwoSided]
  证明: by
  let f : R ⧸ I ->ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨AddHom.id _, fun _ _ => rfl⟩
  rw [jacobson]; rw [← Module.map_jacobson_of_ker_le (f := f) Function.surjective_id]
  · apply Set.image_id
  · rintro _ rfl; exact zero_mem _

Depends on / 依赖: AddHom, AddHom.id, Function, Function.surjective_id, Ideal.Quotient.mk, Module, Module.map_jacobson_of_ker_le, Quotient, Set.image_id, image_id, jacobson, map_jacobson_of_ker_le, surjective_id, zero_mem
-/
theorem coe_jacobson_quotient (I : Ideal R) [I.IsTwoSided] :
    (jacobson (R ⧸ I) : Set (R ⧸ I)) = Module.jacobson R (R ⧸ I) := by
  let f : R ⧸ I ->ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨AddHom.id _, fun _ _ => rfl⟩
  rw [jacobson]; rw [← Module.map_jacobson_of_ker_le (f := f) Function.surjective_id]
  · apply Set.image_id
  · rintro _ rfl; exact zero_mem _

/--
theorem `jacobson_quotient_of_le` / 定理 `jacobson_quotient_of_le`

English:
theorem jacobson_quotient_of_le
  given: {I : Ideal R} [I.IsTwoSided] (le : I <= jacobson R)
  proof: .symm Module.map_jacobson_of_ker_le (by exact Ideal.Quotient.mk_surjective) by
    rwa [← I.ker_mkQ] at le

中文:
定理 jacobson_quotient_of_le
  条件: {I : Ideal R} [I.IsTwoSided] (le : I <= jacobson R)
  证明: .symm Module.map_jacobson_of_ker_le (by exact Ideal.Quotient.mk_surjective) by
    rwa [← I.ker_mkQ] at le

Depends on / 依赖: I.ker_mkQ, Ideal.Quotient.mk_surjective, Module, Module.map_jacobson_of_ker_le, Quotient, ker_mkQ, map_jacobson_of_ker_le, mk_surjective
-/
theorem jacobson_quotient_of_le {I : Ideal R} [I.IsTwoSided] (le : I <= jacobson R) :
    jacobson (R ⧸ I) = Submodule.map (Ideal.Quotient.mk I).toSemilinearMap (jacobson R) :=
.symm Module.map_jacobson_of_ker_le (by exact Ideal.Quotient.mk_surjective) by
    rwa [← I.ker_mkQ] at le

/--
theorem `jacobson_le_of_eq_bot` / 定理 `jacobson_le_of_eq_bot`

English:
theorem jacobson_le_of_eq_bot
  given: {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) = ⊥)
  proof: Module.jacobson_le_of_eq_bot by
    rw [← le_bot_iff]; rw [← SetLike.coe_subset_coe] at h ⊢
    rwa [← coe_jacobson_quotient]

中文:
定理 jacobson_le_of_eq_bot
  条件: {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) = ⊥)
  证明: Module.jacobson_le_of_eq_bot by
    rw [← le_bot_iff]; rw [← SetLike.coe_subset_coe] at h ⊢
    rwa [← coe_jacobson_quotient]

Depends on / 依赖: Module, Module.jacobson_le_of_eq_bot, SetLike, SetLike.coe_subset_coe, coe_jacobson_quotient, coe_subset_coe, jacobson_le_of_eq_bot, le_bot_iff
-/
theorem jacobson_le_of_eq_bot {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) = ⊥) :
    jacobson R <= I :=
Module.jacobson_le_of_eq_bot by
    rw [← le_bot_iff]; rw [← SetLike.coe_subset_coe] at h ⊢
    rwa [← coe_jacobson_quotient]

variable (R)

@[simp]
/--
theorem `jacobson_quotient_jacobson` / 定理 `jacobson_quotient_jacobson`

English:
theorem jacobson_quotient_jacobson
  statement: jacobson (R ⧸ jacobson R) = ⊥
  proof: (jacobson_quotient_of_le le_rfl).trans SetLike.ext' by
    apply SetLike.ext'_iff.mp (jacobson R).mkQ_map_self

中文:
定理 jacobson_quotient_jacobson
  结论: jacobson (R ⧸ jacobson R) = ⊥
  证明: (jacobson_quotient_of_le le_rfl).trans SetLike.ext' by
    apply SetLike.ext'_iff.mp (jacobson R).mkQ_map_self

Depends on / 依赖: SetLike, SetLike.ext, _iff, _iff.mp, jacobson, jacobson_quotient_of_le, le_rfl, mkQ_map_self
-/
theorem jacobson_quotient_jacobson : jacobson (R ⧸ jacobson R) = ⊥ :=
(jacobson_quotient_of_le le_rfl).trans SetLike.ext' by
    apply SetLike.ext'_iff.mp (jacobson R).mkQ_map_self

/--
theorem `jacobson_lt_top` / 定理 `jacobson_lt_top`

English:
theorem jacobson_lt_top
  given: [Nontrivial R]
  statement: jacobson R < ⊤
  proof: Module.jacobson_lt_top R R

中文:
定理 jacobson_lt_top
  条件: [Nontrivial R]
  结论: jacobson R < ⊤
  证明: Module.jacobson_lt_top R R

Depends on / 依赖: Module, Module.jacobson_lt_top, jacobson_lt_top
-/
theorem jacobson_lt_top [Nontrivial R] : jacobson R < ⊤ := Module.jacobson_lt_top R R

/--
theorem `jacobson_smul_top_le` / 定理 `jacobson_smul_top_le`

English:
theorem jacobson_smul_top_le
  statement: jacobson R • (⊤ : Submodule R M) <= Module.jacobson R M
  proof: Submodule.smul_le.mpr fun _ hr m _ => Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr

中文:
定理 jacobson_smul_top_le
  结论: jacobson R • (⊤ : Submodule R M) <= Module.jacobson R M
  证明: Submodule.smul_le.mpr fun _ hr m _ => Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, Module, Module.le_comap_jacobson, Submodule, Submodule.smul_le.mpr, le_comap_jacobson, smul_le, toSpanSingleton
-/
theorem jacobson_smul_top_le : jacobson R • (⊤ : Submodule R M) <= Module.jacobson R M :=
  Submodule.smul_le.mpr fun _ hr m _ => Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr

end Ring

namespace Submodule

variable {R M}

/--
theorem `jacobson_smul_lt_top` / 定理 `jacobson_smul_lt_top`

English:
theorem jacobson_smul_lt_top
  given: [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Submodule R M)
  proof: ((smul_mono_right _ le_top).trans <| Ring.jacobson_smul_top_le R M).trans_lt
    (Module.jacobson_lt_top R M)

中文:
定理 jacobson_smul_lt_top
  条件: [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Submodule R M)
  证明: ((smul_mono_right _ le_top).trans <| Ring.jacobson_smul_top_le R M).trans_lt
    (Module.jacobson_lt_top R M)

Depends on / 依赖: Module, Module.jacobson_lt_top, Ring.jacobson_smul_top_le, jacobson_lt_top, jacobson_smul_top_le, le_top, smul_mono_right, trans_lt
-/
theorem jacobson_smul_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Submodule R M) :
    Ring.jacobson R • N < ⊤ :=
  ((smul_mono_right _ le_top).trans <| Ring.jacobson_smul_top_le R M).trans_lt
    (Module.jacobson_lt_top R M)

/--
theorem `FG.jacobson_smul_lt` / 定理 `FG.jacobson_smul_lt`

English:
theorem FG.jacobson_smul_lt
  given: {N : Submodule R M} (ne_bot : N != ⊥) (fg : N.FG)
  proof: by
  rw [← Module.Finite.iff_fg] at fg
  rw [← nontrivial_iff_ne_bot] at ne_bot
  convert! map_strictMono_of_injective N.injective_subtype (jacobson_smul_lt_top ⊤)
  on_goal 1 => rw [map_smul'']
  all_goals rw [Submodule.map_top, range_subtype]

中文:
定理 FG.jacobson_smul_lt
  条件: {N : Submodule R M} (ne_bot : N != ⊥) (fg : N.FG)
  证明: by
  rw [← Module.Finite.iff_fg] at fg
  rw [← nontrivial_iff_ne_bot] at ne_bot
  convert! map_strictMono_of_injective N.injective_subtype (jacobson_smul_lt_top ⊤)
  on_goal 1 => rw [map_smul'']
  all_goals rw [Submodule.map_top, range_subtype]

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, N.injective_subtype, Submodule, Submodule.map_top, all_goals, convert, iff_fg, injective_subtype, jacobson_smul_lt_top, map_smul, map_strictMono_of_injective, map_top, ne_bot, nontrivial_iff_ne_bot, on_goal, range_subtype
-/
theorem FG.jacobson_smul_lt {N : Submodule R M} (ne_bot : N != ⊥) (fg : N.FG) :
    Ring.jacobson R • N < N := by
  rw [← Module.Finite.iff_fg] at fg
  rw [← nontrivial_iff_ne_bot] at ne_bot
  convert! map_strictMono_of_injective N.injective_subtype (jacobson_smul_lt_top ⊤)
  on_goal 1 => rw [map_smul'']
  all_goals rw [Submodule.map_top, range_subtype]

/--
theorem `FG.eq_bot_of_le_jacobson_smul` / 定理 `FG.eq_bot_of_le_jacobson_smul`

English:
theorem FG.eq_bot_of_le_jacobson_smul
  statement: {N : Submodule R M} (fg : N.FG)
  proof: by
  contrapose! le; exact (jacobson_smul_lt le fg).not_ge

中文:
定理 FG.eq_bot_of_le_jacobson_smul
  结论: {N : Submodule R M} (fg : N.FG)
  证明: by
  contrapose! le; exact (jacobson_smul_lt le fg).not_ge

Depends on / 依赖: contrapose, jacobson_smul_lt, not_ge
-/
theorem FG.eq_bot_of_le_jacobson_smul {N : Submodule R M} (fg : N.FG)
    (le : N <= Ring.jacobson R • N) : N = ⊥ := by
  contrapose! le; exact (jacobson_smul_lt le fg).not_ge

end Submodule

end
