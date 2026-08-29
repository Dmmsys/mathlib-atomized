/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.Lie.Weights.Cartan
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.RingTheory.Finiteness.Nilpotent
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Filter.Cofinite

/-!
# Chains of roots and weights

Given roots `α` and `β` of a Lie algebra, together with elements `x` in the `α`-root space and
`y` in the `β`-root space, it follows from the Leibniz identity that `⁅x, y⁆` is either zero or
belongs to the `α + β`-root space. Iterating this operation leads to the study of families of
roots of the form `k • α + β`. Such a family is known as the `α`-chain through `β` (or sometimes,
the `α`-string through `β`) and the study of the sum of the corresponding root spaces is an
important technique.

More generally if `α` is a root and `χ` is a weight of a representation, it is useful to study the
`α`-chain through `χ`.

We provide basic definitions and results to support `α`-chain techniques in this file.

## Main definitions / results

* `LieModule.exists₂_genWeightSpace_smul_add_eq_bot`: given weights `χ₁`, `χ₂` if `χ₁ ≠ 0`, we can
  find `p < 0` and `q > 0` such that the weight spaces `p • χ₁ + χ₂` and `q • χ₁ + χ₂` are both
  trivial.
* `LieModule.genWeightSpaceChain`: given weights `χ₁`, `χ₂` together with integers `p` and `q`,
  this is the sum of the weight spaces `k • χ₁ + χ₂` for `p < k < q`.
* `LieModule.trace_toEnd_genWeightSpaceChain_eq_zero`: given a root `α` relative to a Cartan
  subalgebra `H`, there is a natural ideal `corootSpace α` in `H`. This lemma
  states that this ideal acts by trace-zero endomorphisms on the sum of root spaces of any
  `α`-chain, provided the weight spaces at the endpoints are both trivial.
* `LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero`: given a (potential) root
  `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
  `corootSpace α` of `H`, we may find an integral linear combination between
  `α` and any weight `χ` of a representation.

## TODO

It should be possible to unify some of the definitions here such as `LieModule.chainBotCoeff`,
`LieModule.chainTopCoeff` with corresponding definitions such as `RootPairing.chainBotCoeff`,
`RootPairing.chainTopCoeff`. This is not quite trivial since:
* The definitions here allow for chains in representations of Lie algebras.
* The proof that the roots of a Lie algebra are a root system currently depends on these results.
  (This can be resolved by proving the root reflection formula using the approach outlined in
  Bourbaki Ch. VIII §2.2 Lemma 1 (page 80 of English translation, 88 of English PDF).)

-/

@[expose] public section

open Module Function Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section IsNilpotent

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L -> R) (p q : Int)

section

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M] (hχ₁ : χ₁ != 0)
include hχ₁

/--
lemma `eventually_genWeightSpace_smul_add_eq_bot` / 引理 `eventually_genWeightSpace_smul_add_eq_bot`

English:
lemma eventually_genWeightSpace_smul_add_eq_bot
  proof: by
  let f : Nat -> L -> R := fun k => k • χ₁ + χ₂
  suffices Injective f by
    rw [← Nat.cofinite_eq_atTop]; rw [Filter.eventually_cofinite]; rw [← finite_image_iff this.injOn]
    apply (finite_genWeightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : Int) • χ₁ = (l : 

中文:
引理 eventually_genWeightSpace_smul_add_eq_bot
  证明: by
  let f : Nat -> L -> R := fun k => k • χ₁ + χ₂
  suffices Injective f by
    rw [← Nat.cofinite_eq_atTop]; rw [Filter.eventually_cofinite]; rw [← finite_image_iff this.injOn]
    apply (finite_genWeightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : Int) • χ₁ = (l : 

Depends on / 依赖: Filter, Filter.eventually_cofinite, Injective, Nat.cast_inj.mp, Nat.cofinite_eq_atTop, add_left_inj, cast_inj, cofinite_eq_atTop, eventually_cofinite, finite_genWeightSpace_ne_bot, finite_image_iff, natCast_zsmul, replace, smul_left_injective, subset, this.injOn
-/
lemma eventually_genWeightSpace_smul_add_eq_bot :
    forallᶠ (k : Nat) in Filter.atTop, genWeightSpace M (k • χ₁ + χ₂) = ⊥ := by
  let f : Nat -> L -> R := fun k => k • χ₁ + χ₂
  suffices Injective f by
    rw [← Nat.cofinite_eq_atTop]; rw [Filter.eventually_cofinite]; rw [← finite_image_iff this.injOn]
    apply (finite_genWeightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : Int) • χ₁ = (l : Int) • χ₁ := by
    simpa only [f, add_left_inj, natCast_zsmul] using hkl
exact Nat.cast_inj.mp smul_left_injective Int hχ₁ hkl

/--
lemma `exists_genWeightSpace_smul_add_eq_bot` / 引理 `exists_genWeightSpace_smul_add_eq_bot`

English:
lemma exists_genWeightSpace_smul_add_eq_bot
  proof: (Nat.eventually_pos.and <| eventually_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists

中文:
引理 exists_genWeightSpace_smul_add_eq_bot
  证明: (Nat.eventually_pos.and <| eventually_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists

Depends on / 依赖: Nat.eventually_pos.and, eventually_genWeightSpace_smul_add_eq_bot, eventually_pos
-/
lemma exists_genWeightSpace_smul_add_eq_bot :
    exists k > 0, genWeightSpace M (k • χ₁ + χ₂) = ⊥ :=
  (Nat.eventually_pos.and <| eventually_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists

/--
lemma `exists₂_genWeightSpace_smul_add_eq_bot` / 引理 `exists₂_genWeightSpace_smul_add_eq_bot`

English:
lemma exists₂_genWeightSpace_smul_add_eq_bot
  proof: by
  obtain ⟨q, hq₀, hq⟩ := exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : Int), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast

中文:
引理 exists₂_genWeightSpace_smul_add_eq_bot
  证明: by
  obtain ⟨q, hq₀, hq⟩ := exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : Int), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast

Depends on / 依赖: exists_genWeightSpace_smul_add_eq_bot, natCast_zsmul, neg_ne_zero, neg_ne_zero.mpr, neg_smul, smul_neg
-/
lemma exists₂_genWeightSpace_smul_add_eq_bot :
    existsᵉ (p < (0 : Int)) (q > (0 : Int)),
      genWeightSpace M (p • χ₁ + χ₂) = ⊥ ∧
      genWeightSpace M (q • χ₁ + χ₂) = ⊥ := by
  obtain ⟨q, hq₀, hq⟩ := exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : Int), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast_zsmul]
    exact hq

end

/--
Definition of `genWeightSpaceChain` / `genWeightSpaceChain` 的定义

English:
definition genWeightSpaceChain
  signature: : LieSubmodule R L M
  body: ⨆ k in Ioo p q, genWeightSpace M (k • χ₁ + χ₂)

中文:
定义 genWeightSpaceChain
  签名: : LieSubmodule R L M
  定义体: ⨆ k in Ioo p q, genWeightSpace M (k • χ₁ + χ₂)

Depends on / 依赖: genWeightSpace
-/
def genWeightSpaceChain : LieSubmodule R L M :=
  ⨆ k in Ioo p q, genWeightSpace M (k • χ₁ + χ₂)

/--
lemma `genWeightSpaceChain_def` / 引理 `genWeightSpaceChain_def`

English:
lemma genWeightSpaceChain_def
  proof: rfl

中文:
引理 genWeightSpaceChain_def
  证明: rfl
-/
lemma genWeightSpaceChain_def :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k in Ioo p q, genWeightSpace M (k • χ₁ + χ₂) :=
  rfl

/--
lemma `genWeightSpaceChain_def'` / 引理 `genWeightSpaceChain_def'`

English:
lemma genWeightSpaceChain_def'
  proof: by
  have : forall (k : Int), k in Ioo p q ↔ k in Finset.Ioo p q := by simp
  simp_rw [genWeightSpaceChain_def, this]

@[simp]

中文:
引理 genWeightSpaceChain_def'
  证明: by
  have : forall (k : Int), k in Ioo p q ↔ k in Finset.Ioo p q := by simp
  simp_rw [genWeightSpaceChain_def, this]

@[simp]

Depends on / 依赖: Finset, Finset.Ioo, genWeightSpaceChain_def, simp_rw
-/
lemma genWeightSpaceChain_def' :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k in Finset.Ioo p q, genWeightSpace M (k • χ₁ + χ₂) := by
  have : forall (k : Int), k in Ioo p q ↔ k in Finset.Ioo p q := by simp
  simp_rw [genWeightSpaceChain_def, this]

@[simp]
/--
lemma `genWeightSpaceChain_neg` / 引理 `genWeightSpaceChain_neg`

English:
lemma genWeightSpaceChain_neg
  proof: by
  let e : Int ≃ Int := neg_involutive.toPerm
  simp_rw [genWeightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [e, -mem_Ioo]

中文:
引理 genWeightSpaceChain_neg
  证明: by
  let e : Int ≃ Int := neg_involutive.toPerm
  simp_rw [genWeightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [e, -mem_Ioo]

Depends on / 依赖: biSup_comp, e.biSup_comp, genWeightSpaceChain, mem_Ioo, neg_involutive, neg_involutive.toPerm, simp_rw, toPerm
-/
lemma genWeightSpaceChain_neg :
    genWeightSpaceChain M (-χ₁) χ₂ (-q) (-p) = genWeightSpaceChain M χ₁ χ₂ p q := by
  let e : Int ≃ Int := neg_involutive.toPerm
  simp_rw [genWeightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [e, -mem_Ioo]

/--
lemma `genWeightSpace_le_genWeightSpaceChain` / 引理 `genWeightSpace_le_genWeightSpaceChain`

English:
lemma genWeightSpace_le_genWeightSpaceChain
  given: {k : Int} (hk : k in Ioo p q)
  proof: le_biSup (fun i => genWeightSpace M (i • χ₁ + χ₂)) hk

中文:
引理 genWeightSpace_le_genWeightSpaceChain
  条件: {k : 整数} (hk : k in Ioo p q)
  证明: le_biSup (fun i => genWeightSpace M (i • χ₁ + χ₂)) hk

Depends on / 依赖: genWeightSpace, le_biSup
-/
lemma genWeightSpace_le_genWeightSpaceChain {k : Int} (hk : k in Ioo p q) :
    genWeightSpace M (k • χ₁ + χ₂) <= genWeightSpaceChain M χ₁ χ₂ p q :=
  le_biSup (fun i => genWeightSpace M (i • χ₁ + χ₂)) hk

end IsNilpotent

section LieSubalgebra

open LieAlgebra

variable {H : LieSubalgebra R L} (α χ : H -> R) (p q : Int)

/--
lemma `lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right` / 引理 `lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right`

English:
lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right
  statement: [LieRing.IsNilpotent H]
  proof: by
  rw [genWeightSpaceChain]; rw [iSup_subtype'] at hy
  induction hy using LieSubmodule.iSup_induction' with
  | mem k z hz =>
    obtain ⟨k, hk⟩ := k
    suffices genWeightSpace M ((k + 1) • α + χ) <= genWeightSpaceChain M α χ p q by
      apply this
      -- was `simpa using! [...]` and very slo

中文:
引理 lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right
  结论: [LieRing.IsNilpotent H]
  证明: by
  rw [genWeightSpaceChain]; rw [iSup_subtype'] at hy
  induction hy using LieSubmodule.iSup_induction' with
  | mem k z hz =>
    obtain ⟨k, hk⟩ := k
    suffices genWeightSpace M ((k + 1) • α + χ) <= genWeightSpaceChain M α χ p q by
      apply this
      -- was `simpa using! [...]` and very slo

Depends on / 依赖: LieSubmodule, LieSubmodule.iSup_induction, genWeightSpace, genWeightSpaceChain, iSup_induction, iSup_subtype
-/
lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilpotent H]
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : L} (hx : x in rootSpace H α)
    {y : M} (hy : y in genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ in genWeightSpaceChain M α χ p q := by
  rw [genWeightSpaceChain]; rw [iSup_subtype'] at hy
  induction hy using LieSubmodule.iSup_induction' with
  | mem k z hz =>
    obtain ⟨k, hk⟩ := k
    suffices genWeightSpace M ((k + 1) • α + χ) <= genWeightSpaceChain M α χ p q by
      apply this
      -- was `simpa using! [...]` and very slow
      -- (https://github.com/leanprover-community/mathlib4/issues/19751)
      simpa only [zsmul_eq_mul, Int.cast_add, Pi.intCast_def, Int.cast_one] using!
        (rootSpaceWeightSpaceProduct R L H M α (k • α + χ) ((k + 1) • α + χ)
            (by rw [add_smul]; abel) (⟨x, hx⟩ otimesₜ ⟨z, hz⟩)).property
    rw [genWeightSpaceChain]
    rcases eq_or_ne (k + 1) q with rfl | hk'; · simp only [hq, bot_le]
    replace hk' : k + 1 in Ioo p q := ⟨by linarith [hk.1], lt_of_le_of_ne hk.2 hk'⟩
    exact le_biSup (fun k => genWeightSpace M (k • α + χ)) hk'
  | zero => simp
  | add _ _ _ _ hz₁ hz₂ => rw [lie_add]; exact add_mem hz₁ hz₂

/--
lemma `lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left` / 引理 `lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left`

English:
lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left
  statement: [LieRing.IsNilpotent H]
  proof: by
  replace hp : genWeightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← genWeightSpaceChain_neg] at hy ⊢
  exact lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy

中文:
引理 lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left
  结论: [LieRing.IsNilpotent H]
  证明: by
  replace hp : genWeightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← genWeightSpaceChain_neg] at hy ⊢
  exact lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy

Depends on / 依赖: genWeightSpace, genWeightSpaceChain_neg, lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right, neg_neg, neg_smul, replace, smul_neg
-/
lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left [LieRing.IsNilpotent H]
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    {x : L} (hx : x in rootSpace H (-α))
    {y : M} (hy : y in genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ in genWeightSpaceChain M α χ p q := by
  replace hp : genWeightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← genWeightSpaceChain_neg] at hy ⊢
  exact lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy

section IsCartanSubalgebra

variable [H.IsCartanSubalgebra] [IsNoetherian R L]
attribute [local instance 100] LieRing.ofAssociativeRing

/--
lemma `trace_toEnd_genWeightSpaceChain_eq_zero` / 引理 `trace_toEnd_genWeightSpaceChain_eq_zero`

English:
lemma trace_toEnd_genWeightSpaceChain_eq_zero
  proof: by
  rw [LieAlgebra.mem_corootSpace'] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, z, hz, hyz⟩ := hu
    let f : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ => ⟨⁅(y : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genW

中文:
引理 trace_toEnd_genWeightSpaceChain_eq_zero
  证明: by
  rw [LieAlgebra.mem_corootSpace'] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, z, hz, hyz⟩ := hu
    let f : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ => ⟨⁅(y : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genW

Depends on / 依赖: LieAlgebra, LieAlgebra.mem_corootSpace, Module, Module.End, Submodule, Submodule.span_induction, genWeightSpaceChain, lie_mem_genWeightSpaceCh, lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right, map_add, map_smul, mem_corootSpace, span_induction
-/
lemma trace_toEnd_genWeightSpaceChain_eq_zero
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : H} (hx : x in corootSpace α) :
    LinearMap.trace R _ (toEnd R H (genWeightSpaceChain M α χ p q) x) = 0 := by
  rw [LieAlgebra.mem_corootSpace'] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, z, hz, hyz⟩ := hu
    let f : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ => ⟨⁅(y : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M α χ p q hq hy hm⟩
        map_add' := fun _ _ => by simp
        map_smul' := fun t m => by simp }
    let g : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ => ⟨⁅(z : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left M α χ p q hp hz hm⟩
        map_add' := fun _ _ => by simp
        map_smul' := fun t m => by simp }
    have hfg : toEnd R H _ u = ⁅f, g⁆ := by
      ext
      rw [toEnd_apply_apply]; rw [LieSubmodule.coe_bracket]; rw [LieSubalgebra.coe_bracket_of_module]; rw [← hyz]
      simp only [lie_lie, LieHom.lie_apply, LinearMap.coe_mk, AddHom.coe_mk, Module.End.lie_apply,
        AddSubgroupClass.coe_sub, f, g]
    simp [hfg]
  | zero => simp
  | add => simp_all
  | smul => simp_all

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_forall_mem_corootSpace_smul_add_eq_zero` / 引理 `exists_forall_mem_corootSpace_smul_add_eq_zero`

English:
lemma exists_forall_mem_corootSpace_smul_add_eq_zero
  proof: by
  obtain ⟨p, hp₀, q, hq₀, hp, hq⟩ := exists₂_genWeightSpace_smul_add_eq_bot M α χ hα
  let a := ∑ i in Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ)) • i
  let b := ∑ i in Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ))
  have hb : 0 < b := by
    replace hχ : Nontrivial (genWe

中文:
引理 exists_forall_mem_corootSpace_smul_add_eq_zero
  证明: by
  obtain ⟨p, hp₀, q, hq₀, hp, hq⟩ := exists₂_genWeightSpace_smul_add_eq_bot M α χ hα
  let a := ∑ i in Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ)) • i
  let b := ∑ i in Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ))
  have hb : 0 < b := by
    replace hχ : Nontrivial (genWe

Depends on / 依赖: Finset, Finset.Ioo, Finset.mem_Ioo.mpr, Finset.sum_pos, Int.n, LieSubmodule, LieSubmodule.nontrivial_iff_ne_bot, Nontrivial, finrank, finrank_pos, genWeightSpace, mem_Ioo, nontrivial_iff_ne_bot, replace, sum_pos, zero_add, zero_le, zero_smul
-/
lemma exists_forall_mem_corootSpace_smul_add_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [Module.IsTorsionFree R M] [IsNoetherian R M]
    (hα : α != 0) (hχ : genWeightSpace M χ != ⊥) :
    exists a b : Int, 0 < b ∧ forall x in corootSpace α, (a • α + b • χ) x = 0 := by
  obtain ⟨p, hp₀, q, hq₀, hp, hq⟩ := exists₂_genWeightSpace_smul_add_eq_bot M α χ hα
  let a := ∑ i in Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ)) • i
  let b := ∑ i in Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ))
  have hb : 0 < b := by
    replace hχ : Nontrivial (genWeightSpace M χ) := by rwa [LieSubmodule.nontrivial_iff_ne_bot]
    refine Finset.sum_pos' (fun _ _ => zero_le) ⟨0, Finset.mem_Ioo.mpr ⟨hp₀, hq₀⟩, ?_⟩
    rw [zero_smul]; rw [zero_add]
    exact finrank_pos
  refine ⟨a, b, Int.natCast_pos.mpr hb, fun x hx => ?_⟩
  let N : Int -> Submodule R M := fun k => genWeightSpace M (k • α + χ)
  have h₁ : iSupIndep fun (i : Finset.Ioo p q) => N i := by
    rw [LieSubmodule.iSupIndep_toSubmodule]
    refine (iSupIndep_genWeightSpace R H M).comp fun i j hij => ?_
exact SetCoe.ext smul_left_injective Int hα by rwa [add_left_inj] at hij
  have h₂ : forall i, MapsTo (toEnd R H M x) ↑(N i) ↑(N i) := fun _ _ => LieSubmodule.lie_mem _
  have h₃ : genWeightSpaceChain M α χ p q = ⨆ i in Finset.Ioo p q, N i := by
    simp_rw [N, genWeightSpaceChain_def', LieSubmodule.iSup_toSubmodule]
  rw [← trace_toEnd_genWeightSpaceChain_eq_zero M α χ p q hp hq hx]; rw [← LieSubmodule.toEnd_restrict_eq_toEnd]
  -- The lines below illustrate the cost of treating `LieSubmodule` as both a
  -- `Submodule` and a `LieSubmodule` simultaneously.
  #adaptation_note /-- 2025-06-18 (https://github.com/leanprover/lean4/issues/8804).
    The `erw` causes a kernel timeout if there is no `subst`. -/
  subst a b N
  erw [LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ h₁ h₂ (genWeightSpaceChain M α χ p q) h₃]
  simp_rw [LieSubmodule.toEnd_restrict_eq_toEnd]
  convert_to! _ =
    ∑ k in Finset.Ioo p q, (LinearMap.trace R { x // x in (genWeightSpace M (k • α + χ)) })
      ((toEnd R { x // x in H } { x // x in genWeightSpace M (k • α + χ) }) x)
  simp_rw [trace_toEnd_genWeightSpace, Pi.add_apply, Pi.smul_apply, smul_add,
    ← smul_assoc, Finset.sum_add_distrib, ← Finset.sum_smul, natCast_zsmul]

end IsCartanSubalgebra

end LieSubalgebra

section

variable {M}
variable [LieRing.IsNilpotent L]
variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]
variable (α : L -> R) (β : Weight R L M)

/-- This is the largest `n : ℕ` such that `i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
/--
Definition of `chainTopCoeff` / `chainTopCoeff` 的定义

English:
definition chainTopCoeff
  signature: : Nat
  body: letI := Classical.propDecidable
  if hα : α = 0 then 0 else
Nat.pred Nat.find (show exists n, genWeightSpace M (n • α + β : L -> R) = ⊥ from
    (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists)

中文:
定义 chainTopCoeff
  签名: : 自然数
  定义体: letI := Classical.propDecidable
  if hα : α = 0 then 0 else
Nat.pred Nat.find (show exists n, genWeightSpace M (n • α + β : L -> R) = ⊥ from
    (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists)

Depends on / 依赖: Classical, Classical.propDecidable, Nat.find, Nat.pred, eventually_genWeightSpace_smul_add_eq_bot, genWeightSpace, propDecidable
-/
def chainTopCoeff : Nat :=
  letI := Classical.propDecidable
  if hα : α = 0 then 0 else
Nat.pred Nat.find (show exists n, genWeightSpace M (n • α + β : L -> R) = ⊥ from
    (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists)

/-- This is the largest `n : ℕ` such that `-i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
/--
Definition of `chainBotCoeff` / `chainBotCoeff` 的定义

English:
definition chainBotCoeff
  signature: : Nat
  body: chainTopCoeff (-α) β

中文:
定义 chainBotCoeff
  签名: : 自然数
  定义体: chainTopCoeff (-α) β

Depends on / 依赖: chainTopCoeff
-/
def chainBotCoeff : Nat := chainTopCoeff (-α) β

/--
lemma `chainTopCoeff_neg` / 引理 `chainTopCoeff_neg`

English:
lemma chainTopCoeff_neg
  statement: chainTopCoeff (-α) β = chainBotCoeff α β
  proof: rfl

中文:
引理 chainTopCoeff_neg
  结论: chainTopCoeff (-α) β = chainBotCoeff α β
  证明: rfl
-/
@[simp] lemma chainTopCoeff_neg : chainTopCoeff (-α) β = chainBotCoeff α β := rfl
/--
lemma `chainBotCoeff_neg` / 引理 `chainBotCoeff_neg`

English:
lemma chainBotCoeff_neg
  statement: chainBotCoeff (-α) β = chainTopCoeff α β
  proof: by
  rw [← chainTopCoeff_neg]; rw [neg_neg]

中文:
引理 chainBotCoeff_neg
  结论: chainBotCoeff (-α) β = chainTopCoeff α β
  证明: by
  rw [← chainTopCoeff_neg]; rw [neg_neg]
-/
@[simp] lemma chainBotCoeff_neg : chainBotCoeff (-α) β = chainTopCoeff α β := by
  rw [← chainTopCoeff_neg]; rw [neg_neg]

/--
lemma `chainTopCoeff_zero` / 引理 `chainTopCoeff_zero`

English:
lemma chainTopCoeff_zero
  statement: chainTopCoeff 0 β = 0
  proof: dif_pos rfl

中文:
引理 chainTopCoeff_zero
  结论: chainTopCoeff 0 β = 0
  证明: dif_pos rfl
-/
@[simp] lemma chainTopCoeff_zero : chainTopCoeff 0 β = 0 := dif_pos rfl
/--
lemma `chainBotCoeff_zero` / 引理 `chainBotCoeff_zero`

English:
lemma chainBotCoeff_zero
  statement: chainBotCoeff 0 β = 0
  proof: dif_pos neg_zero

中文:
引理 chainBotCoeff_zero
  结论: chainBotCoeff 0 β = 0
  证明: dif_pos neg_zero
-/
@[simp] lemma chainBotCoeff_zero : chainBotCoeff 0 β = 0 := dif_pos neg_zero

section
variable (hα : α != 0)
include hα

/--
lemma `chainTopCoeff_add_one` / 引理 `chainTopCoeff_add_one`

English:
lemma chainTopCoeff_add_one
  proof: Classical.propDecidable
    chainTopCoeff α β + 1 =
      Nat.find (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists := by
  classical
  rw [chainTopCoeff]; rw [dif_neg hα]
  apply Nat.succ_pred_eq_of_pos
  rw [zero_lt_iff]
  intro e
  have : genWeightSpace M (0 • α + β : L -> R) = ⊥ := by

中文:
引理 chainTopCoeff_add_one
  证明: Classical.propDecidable
    chainTopCoeff α β + 1 =
      Nat.find (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists := by
  classical
  rw [chainTopCoeff]; rw [dif_neg hα]
  apply Nat.succ_pred_eq_of_pos
  rw [zero_lt_iff]
  intro e
  have : genWeightSpace M (0 • α + β : L -> R) = ⊥ := by

Depends on / 依赖: Classical, Classical.propDecidable, propDecidable
-/
lemma chainTopCoeff_add_one :
    letI := Classical.propDecidable
    chainTopCoeff α β + 1 =
      Nat.find (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists := by
  classical
  rw [chainTopCoeff]; rw [dif_neg hα]
  apply Nat.succ_pred_eq_of_pos
  rw [zero_lt_iff]
  intro e
  have : genWeightSpace M (0 • α + β : L -> R) = ⊥ := by
    rw [← e]
    exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists
  exact β.genWeightSpace_ne_bot _ (by simpa only [zero_smul, zero_add] using this)

/--
lemma `genWeightSpace_chainTopCoeff_add_one_nsmul_add` / 引理 `genWeightSpace_chainTopCoeff_add_one_nsmul_add`

English:
lemma genWeightSpace_chainTopCoeff_add_one_nsmul_add
  proof: by
  classical
  rw [chainTopCoeff_add_one _ _ hα]
  exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists

中文:
引理 genWeightSpace_chainTopCoeff_add_one_nsmul_add
  证明: by
  classical
  rw [chainTopCoeff_add_one _ _ hα]
  exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists

Depends on / 依赖: Nat.find_spec, chainTopCoeff_add_one, classical, eventually_genWeightSpace_smul_add_eq_bot, find_spec
-/
lemma genWeightSpace_chainTopCoeff_add_one_nsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1) • α + β : L -> R) = ⊥ := by
  classical
  rw [chainTopCoeff_add_one _ _ hα]
  exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists

/--
lemma `genWeightSpace_chainTopCoeff_add_one_zsmul_add` / 引理 `genWeightSpace_chainTopCoeff_add_one_zsmul_add`

English:
lemma genWeightSpace_chainTopCoeff_add_one_zsmul_add
  proof: by
  rw [← genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα]; rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_add]; rw [Nat.cast_one]

中文:
引理 genWeightSpace_chainTopCoeff_add_one_zsmul_add
  证明: by
  rw [← genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα]; rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_add]; rw [Nat.cast_one]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Nat.cast_smul_eq_nsmul, cast_add, cast_one, cast_smul_eq_nsmul, genWeightSpace_chainTopCoeff_add_one_nsmul_add
-/
lemma genWeightSpace_chainTopCoeff_add_one_zsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1 : Int) • α + β : L -> R) = ⊥ := by
  rw [← genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα]; rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_add]; rw [Nat.cast_one]

/--
lemma `genWeightSpace_chainBotCoeff_sub_one_zsmul_sub` / 引理 `genWeightSpace_chainBotCoeff_sub_one_zsmul_sub`

English:
lemma genWeightSpace_chainBotCoeff_sub_one_zsmul_sub
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_add]; rw [neg_smul]; rw [← smul_neg]; rw [chainBotCoeff]; rw [genWeightSpace_chainTopCoeff_add_one_zsmul_add _ _ (by simpa using hα)]

中文:
引理 genWeightSpace_chainBotCoeff_sub_one_zsmul_sub
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_add]; rw [neg_smul]; rw [← smul_neg]; rw [chainBotCoeff]; rw [genWeightSpace_chainTopCoeff_add_one_zsmul_add _ _ (by simpa using hα)]

Depends on / 依赖: chainBotCoeff, genWeightSpace_chainTopCoeff_add_one_zsmul_add, neg_add, neg_smul, smul_neg, sub_eq_add_neg
-/
lemma genWeightSpace_chainBotCoeff_sub_one_zsmul_sub :
    genWeightSpace M ((-chainBotCoeff α β - 1 : Int) • α + β : L -> R) = ⊥ := by
  rw [sub_eq_add_neg]; rw [← neg_add]; rw [neg_smul]; rw [← smul_neg]; rw [chainBotCoeff]; rw [genWeightSpace_chainTopCoeff_add_one_zsmul_add _ _ (by simpa using hα)]

end

/--
lemma `genWeightSpace_nsmul_add_ne_bot_of_le` / 引理 `genWeightSpace_nsmul_add_ne_bot_of_le`

English:
lemma genWeightSpace_nsmul_add_ne_bot_of_le
  given: {n} (hn : n <= chainTopCoeff α β)
  proof: by
  by_cases hα : α = 0
  · rw [hα, smul_zero, zero_add]; exact β.genWeightSpace_ne_bot
  classical
  rw [← Nat.lt_succ_iff]; rw [Nat.succ_eq_add_one]; rw [chainTopCoeff_add_one _ _ hα] at hn
  exact Nat.find_min (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists hn

中文:
引理 genWeightSpace_nsmul_add_ne_bot_of_le
  条件: {n} (hn : n <= chainTopCoeff α β)
  证明: by
  by_cases hα : α = 0
  · rw [hα, smul_zero, zero_add]; exact β.genWeightSpace_ne_bot
  classical
  rw [← Nat.lt_succ_iff]; rw [Nat.succ_eq_add_one]; rw [chainTopCoeff_add_one _ _ hα] at hn
  exact Nat.find_min (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists hn

Depends on / 依赖: Nat.find_min, Nat.lt_succ_iff, Nat.succ_eq_add_one, chainTopCoeff_add_one, classical, eventually_genWeightSpace_smul_add_eq_bot, find_min, genWeightSpace_ne_bot, lt_succ_iff, smul_zero, succ_eq_add_one, zero_add
-/
lemma genWeightSpace_nsmul_add_ne_bot_of_le {n} (hn : n <= chainTopCoeff α β) :
    genWeightSpace M (n • α + β : L -> R) != ⊥ := by
  by_cases hα : α = 0
  · rw [hα, smul_zero, zero_add]; exact β.genWeightSpace_ne_bot
  classical
  rw [← Nat.lt_succ_iff]; rw [Nat.succ_eq_add_one]; rw [chainTopCoeff_add_one _ _ hα] at hn
  exact Nat.find_min (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists hn

/--
lemma `genWeightSpace_zsmul_add_ne_bot` / 引理 `genWeightSpace_zsmul_add_ne_bot`

English:
lemma genWeightSpace_zsmul_add_ne_bot
  statement: {n : Int}
  proof: by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_natCast, Nat.cast_le, Nat.cast_smul_eq_nsmul] at hn' ⊢
    exact genWeightSpace_nsmul_add_ne_bot_of_le α β hn'
  · simp only [Int.negSucc_eq, ← Nat.cast_succ, neg_le_neg_iff, Nat.cast_le] at hn ⊢
    rw [neg_smul]; rw [← smul_neg]; rw [Nat.cast_

中文:
引理 genWeightSpace_zsmul_add_ne_bot
  结论: {n : 整数}
  证明: by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_natCast, Nat.cast_le, Nat.cast_smul_eq_nsmul] at hn' ⊢
    exact genWeightSpace_nsmul_add_ne_bot_of_le α β hn'
  · simp only [Int.negSucc_eq, ← Nat.cast_succ, neg_le_neg_iff, Nat.cast_le] at hn ⊢
    rw [neg_smul]; rw [← smul_neg]; rw [Nat.cast_

Depends on / 依赖: Int.negSucc_eq, Int.ofNat_eq_natCast, Nat.cast_le, Nat.cast_smul_eq_nsmul, Nat.cast_succ, cast_le, cast_smul_eq_nsmul, cast_succ, genWeightSpace_nsmul_add_ne_bot_of_le, negSucc_eq, neg_le_neg_iff, neg_smul, ofNat_eq_natCast, smul_neg
-/
lemma genWeightSpace_zsmul_add_ne_bot {n : Int}
    (hn : -chainBotCoeff α β <= n) (hn' : n <= chainTopCoeff α β) :
      genWeightSpace M (n • α + β : L -> R) != ⊥ := by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_natCast, Nat.cast_le, Nat.cast_smul_eq_nsmul] at hn' ⊢
    exact genWeightSpace_nsmul_add_ne_bot_of_le α β hn'
  · simp only [Int.negSucc_eq, ← Nat.cast_succ, neg_le_neg_iff, Nat.cast_le] at hn ⊢
    rw [neg_smul]; rw [← smul_neg]; rw [Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_nsmul_add_ne_bot_of_le (-α) β hn

/--
lemma `genWeightSpace_neg_zsmul_add_ne_bot` / 引理 `genWeightSpace_neg_zsmul_add_ne_bot`

English:
lemma genWeightSpace_neg_zsmul_add_ne_bot
  given: {n : Nat} (hn : n <= chainBotCoeff α β)
  proof: by
  apply genWeightSpace_zsmul_add_ne_bot α β <;> lia

中文:
引理 genWeightSpace_neg_zsmul_add_ne_bot
  条件: {n : 自然数} (hn : n <= chainBotCoeff α β)
  证明: by
  apply genWeightSpace_zsmul_add_ne_bot α β <;> lia

Depends on / 依赖: genWeightSpace_zsmul_add_ne_bot
-/
lemma genWeightSpace_neg_zsmul_add_ne_bot {n : Nat} (hn : n <= chainBotCoeff α β) :
    genWeightSpace M ((-n : Int) • α + β : L -> R) != ⊥ := by
  apply genWeightSpace_zsmul_add_ne_bot α β <;> lia

/-- The last weight in an `α`-chain through `β`. -/
noncomputable
/--
Definition of `chainTop` / `chainTop` 的定义

English:
definition chainTop
  signature: (α : L -> R) (β : Weight R L M)
  body: ⟨chainTopCoeff α β • α + β, genWeightSpace_nsmul_add_ne_bot_of_le α β le_rfl⟩

中文:
定义 chainTop
  签名: (α : L -> R) (β : Weight R L M)
  定义体: ⟨chainTopCoeff α β • α + β, genWeightSpace_nsmul_add_ne_bot_of_le α β le_rfl⟩

Depends on / 依赖: chainTopCoeff, genWeightSpace_nsmul_add_ne_bot_of_le, le_rfl
-/
def chainTop (α : L -> R) (β : Weight R L M) : Weight R L M :=
  ⟨chainTopCoeff α β • α + β, genWeightSpace_nsmul_add_ne_bot_of_le α β le_rfl⟩

/-- The first weight in an `α`-chain through `β`. -/
noncomputable
/--
Definition of `chainBot` / `chainBot` 的定义

English:
definition chainBot
  signature: (α : L -> R) (β : Weight R L M)
  body: ⟨(- chainBotCoeff α β : Int) • α + β, genWeightSpace_neg_zsmul_add_ne_bot α β le_rfl⟩

中文:
定义 chainBot
  签名: (α : L -> R) (β : Weight R L M)
  定义体: ⟨(- chainBotCoeff α β : Int) • α + β, genWeightSpace_neg_zsmul_add_ne_bot α β le_rfl⟩

Depends on / 依赖: chainBotCoeff, genWeightSpace_neg_zsmul_add_ne_bot, le_rfl
-/
def chainBot (α : L -> R) (β : Weight R L M) : Weight R L M :=
  ⟨(- chainBotCoeff α β : Int) • α + β, genWeightSpace_neg_zsmul_add_ne_bot α β le_rfl⟩

/--
lemma `coe_chainTop'` / 引理 `coe_chainTop'`

English:
lemma coe_chainTop'
  statement: (chainTop α β : L -> R) = chainTopCoeff α β • α + β
  proof: rfl

中文:
引理 coe_chainTop'
  结论: (chainTop α β : L -> R) = chainTopCoeff α β • α + β
  证明: rfl
-/
lemma coe_chainTop' : (chainTop α β : L -> R) = chainTopCoeff α β • α + β := rfl

/--
lemma `coe_chainTop` / 引理 `coe_chainTop`

English:
lemma coe_chainTop
  statement: (chainTop α β : L -> R) = (chainTopCoeff α β : Int) • α + β
  proof: by
  rw [Nat.cast_smul_eq_nsmul Int]; rfl

中文:
引理 coe_chainTop
  结论: (chainTop α β : L -> R) = (chainTopCoeff α β : 整数) • α + β
  证明: by
  rw [Nat.cast_smul_eq_nsmul Int]; rfl
-/
@[simp] lemma coe_chainTop : (chainTop α β : L -> R) = (chainTopCoeff α β : Int) • α + β := by
  rw [Nat.cast_smul_eq_nsmul Int]; rfl
/--
lemma `coe_chainBot` / 引理 `coe_chainBot`

English:
lemma coe_chainBot
  statement: (chainBot α β : L -> R) = (-chainBotCoeff α β : Int) • α + β
  proof: rfl

中文:
引理 coe_chainBot
  结论: (chainBot α β : L -> R) = (-chainBotCoeff α β : 整数) • α + β
  证明: rfl
-/
@[simp] lemma coe_chainBot : (chainBot α β : L -> R) = (-chainBotCoeff α β : Int) • α + β := rfl

/--
lemma `chainTop_neg` / 引理 `chainTop_neg`

English:
lemma chainTop_neg
  statement: chainTop (-α) β = chainBot α β
  proof: by ext; simp

中文:
引理 chainTop_neg
  结论: chainTop (-α) β = chainBot α β
  证明: by ext; simp
-/
@[simp] lemma chainTop_neg : chainTop (-α) β = chainBot α β := by ext; simp
/--
lemma `chainBot_neg` / 引理 `chainBot_neg`

English:
lemma chainBot_neg
  statement: chainBot (-α) β = chainTop α β
  proof: by ext; simp

中文:
引理 chainBot_neg
  结论: chainBot (-α) β = chainTop α β
  证明: by ext; simp
-/
@[simp] lemma chainBot_neg : chainBot (-α) β = chainTop α β := by ext; simp

/--
lemma `chainTop_zero` / 引理 `chainTop_zero`

English:
lemma chainTop_zero
  statement: chainTop 0 β = β
  proof: by ext; simp

中文:
引理 chainTop_zero
  结论: chainTop 0 β = β
  证明: by ext; simp
-/
@[simp] lemma chainTop_zero : chainTop 0 β = β := by ext; simp
/--
lemma `chainBot_zero` / 引理 `chainBot_zero`

English:
lemma chainBot_zero
  statement: chainBot 0 β = β
  proof: by ext; simp

中文:
引理 chainBot_zero
  结论: chainBot 0 β = β
  证明: by ext; simp
-/
@[simp] lemma chainBot_zero : chainBot 0 β = β := by ext; simp

section
variable (hα : α != 0)
include hα

/--
lemma `genWeightSpace_add_chainTop` / 引理 `genWeightSpace_add_chainTop`

English:
lemma genWeightSpace_add_chainTop
  proof: by
  rw [coe_chainTop']; rw [← add_assoc]; rw [← succ_nsmul']; rw [genWeightSpace_chainTopCoeff_add_one_nsmul_add _ _ hα]

中文:
引理 genWeightSpace_add_chainTop
  证明: by
  rw [coe_chainTop']; rw [← add_assoc]; rw [← succ_nsmul']; rw [genWeightSpace_chainTopCoeff_add_one_nsmul_add _ _ hα]

Depends on / 依赖: add_assoc, coe_chainTop, genWeightSpace_chainTopCoeff_add_one_nsmul_add, succ_nsmul
-/
lemma genWeightSpace_add_chainTop :
    genWeightSpace M (α + chainTop α β : L -> R) = ⊥ := by
  rw [coe_chainTop']; rw [← add_assoc]; rw [← succ_nsmul']; rw [genWeightSpace_chainTopCoeff_add_one_nsmul_add _ _ hα]

/--
lemma `genWeightSpace_neg_add_chainBot` / 引理 `genWeightSpace_neg_add_chainBot`

English:
lemma genWeightSpace_neg_add_chainBot
  proof: by
  rw [← chainTop_neg]; rw [genWeightSpace_add_chainTop _ _ (by simpa using hα)]

中文:
引理 genWeightSpace_neg_add_chainBot
  证明: by
  rw [← chainTop_neg]; rw [genWeightSpace_add_chainTop _ _ (by simpa using hα)]

Depends on / 依赖: chainTop_neg, genWeightSpace_add_chainTop
-/
lemma genWeightSpace_neg_add_chainBot :
    genWeightSpace M (-α + chainBot α β : L -> R) = ⊥ := by
  rw [← chainTop_neg]; rw [genWeightSpace_add_chainTop _ _ (by simpa using hα)]

/--
lemma `chainTop_isNonZero'` / 引理 `chainTop_isNonZero'`

English:
lemma chainTop_isNonZero'
  given: (hα' : genWeightSpace M α != ⊥)
  proof: by
  by_contra e
  apply hα'
  rw [← add_zero (α : L -> R)]; rw [← e]; rw [genWeightSpace_add_chainTop _ _ hα]

中文:
引理 chainTop_isNonZero'
  条件: (hα' : genWeightSpace M α != ⊥)
  证明: by
  by_contra e
  apply hα'
  rw [← add_zero (α : L -> R)]; rw [← e]; rw [genWeightSpace_add_chainTop _ _ hα]

Depends on / 依赖: add_zero, genWeightSpace_add_chainTop
-/
lemma chainTop_isNonZero' (hα' : genWeightSpace M α != ⊥) :
    (chainTop α β).IsNonZero := by
  by_contra e
  apply hα'
  rw [← add_zero (α : L -> R)]; rw [← e]; rw [genWeightSpace_add_chainTop _ _ hα]

end

/--
lemma `chainTop_isNonZero` / 引理 `chainTop_isNonZero`

English:
lemma chainTop_isNonZero
  given: (α β : Weight R L M) (hα : α.IsNonZero)
  proof: chainTop_isNonZero' α β hα α.2

中文:
引理 chainTop_isNonZero
  条件: (α β : Weight R L M) (hα : α.IsNonZero)
  证明: chainTop_isNonZero' α β hα α.2

Depends on / 依赖: chainTop_isNonZero
-/
lemma chainTop_isNonZero (α β : Weight R L M) (hα : α.IsNonZero) :
    (chainTop α β).IsNonZero :=
  chainTop_isNonZero' α β hα α.2

end

end LieModule

section Field

open LieAlgebra LieModule

variable {K : Type*} [Field K] [CharZero K] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
  [Module K M] [LieModule K L M]
  [IsTriangularizable K H M] [FiniteDimensional K M]

/--
lemma `LieModule.isNilpotent_toEnd_of_mem_rootSpace` / 引理 `LieModule.isNilpotent_toEnd_of_mem_rootSpace`

English:
lemma LieModule.isNilpotent_toEnd_of_mem_rootSpace
  proof: by
  refine Module.End.isNilpotent_iff_of_finite.mpr fun m => ?_
  have hm : m in ⨆ χ : LieModule.Weight K H M, genWeightSpace M χ := by
    simp [iSup_genWeightSpace_eq_top' K H M]
  induction hm using LieSubmodule.iSup_induction' with
  | zero => exact ⟨0, map_zero _⟩
  | mem χ₂ m₂ hm₂ =>
    obta

中文:
引理 LieModule.isNilpotent_toEnd_of_mem_rootSpace
  证明: by
  refine Module.End.isNilpotent_iff_of_finite.mpr fun m => ?_
  have hm : m in ⨆ χ : LieModule.Weight K H M, genWeightSpace M χ := by
    simp [iSup_genWeightSpace_eq_top' K H M]
  induction hm using LieSubmodule.iSup_induction' with
  | zero => exact ⟨0, map_zero _⟩
  | mem χ₂ m₂ hm₂ =>
    obta

Depends on / 依赖: LieModule, LieModule.Weight, LieSubmodule, LieSubmodule.iSup_induction, LieSubmodule.mem_bot, Module, Module.End.isNilpotent_iff_of_finite.mpr, Weight, exists_genWeightSpace_smul_add_eq_bot, genWeightSpace, iSup_genWeightSpace_eq_top, iSup_induction, isNilpotent_iff_of_finite, map_zero, mem_bot, toEnd_pow_apply_mem
-/
lemma LieModule.isNilpotent_toEnd_of_mem_rootSpace
    {x : L} {χ : H -> K} (hχ : χ != 0) (hx : x in rootSpace H χ) :
    _root_.IsNilpotent (toEnd K L M x) := by
  refine Module.End.isNilpotent_iff_of_finite.mpr fun m => ?_
  have hm : m in ⨆ χ : LieModule.Weight K H M, genWeightSpace M χ := by
    simp [iSup_genWeightSpace_eq_top' K H M]
  induction hm using LieSubmodule.iSup_induction' with
  | zero => exact ⟨0, map_zero _⟩
  | mem χ₂ m₂ hm₂ =>
    obtain ⟨n, -, hn⟩ := exists_genWeightSpace_smul_add_eq_bot M χ χ₂ hχ
    use n
    have := toEnd_pow_apply_mem hx hm₂ n
    rwa [hn, LieSubmodule.mem_bot] at this
  | add m₁ m₂ hm₁ hm₂ hm₁' hm₂' =>
    obtain ⟨n₁, hn₁⟩ := hm₁'
    obtain ⟨n₂, hn₂⟩ := hm₂'
    refine ⟨max n₁ n₂, ?_⟩
    rw [map_add]; rw [Module.End.pow_map_zero_of_le le_sup_left hn₁]; rw [Module.End.pow_map_zero_of_le le_sup_right hn₂]; rw [add_zero]

/--
lemma `LieAlgebra.isNilpotent_ad_of_mem_rootSpace` / 引理 `LieAlgebra.isNilpotent_ad_of_mem_rootSpace`

English:
lemma LieAlgebra.isNilpotent_ad_of_mem_rootSpace
  proof: isNilpotent_toEnd_of_mem_rootSpace (M := L) H hχ hx

中文:
引理 LieAlgebra.isNilpotent_ad_of_mem_rootSpace
  证明: isNilpotent_toEnd_of_mem_rootSpace (M := L) H hχ hx

Depends on / 依赖: isNilpotent_toEnd_of_mem_rootSpace
-/
lemma LieAlgebra.isNilpotent_ad_of_mem_rootSpace
    [IsTriangularizable K H L] [FiniteDimensional K L]
    {x : L} {χ : H -> K} (hχ : χ != 0) (hx : x in rootSpace H χ) :
    _root_.IsNilpotent (ad K L x) :=
  isNilpotent_toEnd_of_mem_rootSpace (M := L) H hχ hx

end Field
