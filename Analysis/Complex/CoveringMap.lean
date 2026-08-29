/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.LocalAtTarget

/-!
# Covering maps involving the complex plane

In this file, we show that `Complex.exp` and `(· ^ n)` (for `n ≠ 0`) are a covering map on `{0}ᶜ`.
We also show that any complex polynomial is a covering map on the set of regular values.
-/

public section

open Topology

namespace Complex

/--
theorem `isAddQuotientCoveringMap_exp` / 定理 `isAddQuotientCoveringMap_exp`

English:
theorem isAddQuotientCoveringMap_exp
  proof: by
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_
    _ ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} => ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z => ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.

中文:
定理 isAddQuotientCoveringMap_exp
  证明: by
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_
    _ ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} => ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z => ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff, IsOpen, IsOpen.isOpenEmbedding_subtypeVal, IsOpenMap, IsOpenMap.isQuotientMap, IsQuotientMap, NormedSpace, NormedSpace.discreteTopology_zmultiples, Subtype, Subtype.ext, Subtype.ext_iff, Topology, Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup, add_comm, discreteTopology_zmultiples, eq_add_neg_iff_add_eq, eq_comm, exp_eq_exp_iff_exists_int, exp_log
-/
theorem isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap (fun z : Complex => (⟨_, z.exp_ne_zero⟩ : {z : Complex // z != 0}))
      (AddSubgroup.zmultiples (2 * Real.pi * I)) := by
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_
    _ ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} => ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z => ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr isOpenMap_exp
  · simp_rw [Subtype.ext_iff, eq_comm (a := exp z), exp_eq_exp_iff_exists_int,
      AddSubgroup.mem_zmultiples_iff, eq_add_neg_iff_add_eq, eq_comm, add_comm, zsmul_eq_mul]

/--
theorem `isCoveringMap_exp` / 定理 `isCoveringMap_exp`

English:
theorem isCoveringMap_exp
  statement: IsCoveringMap fun z : Complex => (⟨_, z.exp_ne_zero⟩ : {z : Complex // z != 0})
  proof: isAddQuotientCoveringMap_exp.isCoveringMap

中文:
定理 isCoveringMap_exp
  结论: IsCoveringMap fun z : Complex => (⟨_, z.exp_ne_zero⟩ : {z : Complex // z != 0})
  证明: isAddQuotientCoveringMap_exp.isCoveringMap

Depends on / 依赖: isAddQuotientCoveringMap_exp, isAddQuotientCoveringMap_exp.isCoveringMap, isCoveringMap
-/
theorem isCoveringMap_exp : IsCoveringMap fun z : Complex => (⟨_, z.exp_ne_zero⟩ : {z : Complex // z != 0}) :=
  isAddQuotientCoveringMap_exp.isCoveringMap

/--
theorem `isCoveringMapOn_exp` / 定理 `isCoveringMapOn_exp`

English:
theorem isCoveringMapOn_exp
  statement: IsCoveringMapOn Complex.exp {0}ᶜ
  proof: .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

中文:
定理 isCoveringMapOn_exp
  结论: IsCoveringMapOn Complex.exp {0}ᶜ
  证明: .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

Depends on / 依赖: isCoveringMap_exp, of_isCoveringMap_subtype
-/
theorem isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ :=
  .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

end Complex

section

open Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

/--
theorem `Polynomial.isCoveringMapOn_eval` / 定理 `Polynomial.isCoveringMapOn_eval`

English:
theorem Polynomial.isCoveringMapOn_eval
  given: (p : 𝕜[X])
  proof: by
  refine p.isClosedMap_eval.isCoveringMapOn_of_isLocalHomeomorphOn (fun x hx => ?_)
    fun x hx => ⟨_, ((p.hasStrictDerivAt x).hasStrictFDerivAt_equiv
      fun h => hx ⟨x, h, rfl⟩).mem_toOpenPartialHomeomorph_source, by simp⟩
  obtain rfl | ne := eq_or_ne p (C x)
  · simp at hx
  · simpa only [

中文:
定理 Polynomial.isCoveringMapOn_eval
  条件: (p : 𝕜[X])
  证明: by
  refine p.isClosedMap_eval.isCoveringMapOn_of_isLocalHomeomorphOn (fun x hx => ?_)
    fun x hx => ⟨_, ((p.hasStrictDerivAt x).hasStrictFDerivAt_equiv
      fun h => hx ⟨x, h, rfl⟩).mem_toOpenPartialHomeomorph_source, by simp⟩
  obtain rfl | ne := eq_or_ne p (C x)
  · simp at hx
  · simpa only [

Depends on / 依赖: eq_or_ne, hasStrictDerivAt, hasStrictFDerivAt_equiv, isClosedMap_eval, isCoveringMapOn_of_isLocalHomeomorphOn, mem_toOpenPartialHomeomorph_source, p.hasStrictDerivAt, p.isClosedMap_eval.isCoveringMapOn_of_isLocalHomeomorphOn, preimage_eval_singleton, rootSet_finite
-/
theorem Polynomial.isCoveringMapOn_eval (p : 𝕜[X]) :
    IsCoveringMapOn p.eval (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
  refine p.isClosedMap_eval.isCoveringMapOn_of_isLocalHomeomorphOn (fun x hx => ?_)
    fun x hx => ⟨_, ((p.hasStrictDerivAt x).hasStrictFDerivAt_equiv
      fun h => hx ⟨x, h, rfl⟩).mem_toOpenPartialHomeomorph_source, by simp⟩
  obtain rfl | ne := eq_or_ne p (C x)
  · simp at hx
  · simpa only [preimage_eval_singleton ne] using rootSet_finite ..

/--
theorem `isCoveringMapOn_npow` / 定理 `isCoveringMapOn_npow`

English:
theorem isCoveringMapOn_npow
  given: (n : Nat) (hn : (n : 𝕜) != 0)
  proof: by
  convert! (X ^ n).isCoveringMapOn_eval.mono fun x' h => _ with x
  · simp
  · assumption
  · simpa [derivative_X_pow, hn, show n != 0 by aesop] using fun _ => Ne.symm h

中文:
定理 isCoveringMapOn_npow
  条件: (n : 自然数) (hn : (n : 𝕜) != 0)
  证明: by
  convert! (X ^ n).isCoveringMapOn_eval.mono fun x' h => _ with x
  · simp
  · assumption
  · simpa [derivative_X_pow, hn, show n != 0 by aesop] using fun _ => Ne.symm h

Depends on / 依赖: Ne.symm, convert, derivative_X_pow, isCoveringMapOn_eval, isCoveringMapOn_eval.mono
-/
theorem isCoveringMapOn_npow (n : Nat) (hn : (n : 𝕜) != 0) :
    IsCoveringMapOn (fun x : 𝕜 => x ^ n) {0}ᶜ := by
  convert! (X ^ n).isCoveringMapOn_eval.mono fun x' h => _ with x
  · simp
  · assumption
  · simpa [derivative_X_pow, hn, show n != 0 by aesop] using fun _ => Ne.symm h

/--
theorem `isCoveringMap_npow` / 定理 `isCoveringMap_npow`

English:
theorem isCoveringMap_npow
  given: (n : Nat) (hn : (n : 𝕜) != 0)
  proof: by
  convert!
    (isCoveringMapOn_npow n hn).isCoveringMap_restrictPreimage.comp_homeomorph
      (.setCongr (s := {x | x != 0}) _) using 1
  ext; simp [show n != 0 by aesop]

中文:
定理 isCoveringMap_npow
  条件: (n : 自然数) (hn : (n : 𝕜) != 0)
  证明: by
  convert!
    (isCoveringMapOn_npow n hn).isCoveringMap_restrictPreimage.comp_homeomorph
      (.setCongr (s := {x | x != 0}) _) using 1
  ext; simp [show n != 0 by aesop]

Depends on / 依赖: comp_homeomorph, convert, isCoveringMapOn_npow, isCoveringMap_restrictPreimage, isCoveringMap_restrictPreimage.comp_homeomorph, setCongr
-/
theorem isCoveringMap_npow (n : Nat) (hn : (n : 𝕜) != 0) :
    IsCoveringMap fun x : {x : 𝕜 // x != 0} => (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x != 0}) := by
  convert!
    (isCoveringMapOn_npow n hn).isCoveringMap_restrictPreimage.comp_homeomorph
      (.setCongr (s := {x | x != 0}) _) using 1
  ext; simp [show n != 0 by aesop]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isCoveringMap_zpow` / 定理 `isCoveringMap_zpow`

English:
theorem isCoveringMap_zpow
  given: (n : Int) (hn : (n : 𝕜) != 0)
  proof: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · convert! isCoveringMap_npow n _ <;> aesop
  · convert! (isCoveringMap_npow n _).comp_homeomorph (.inv₀ 𝕜)
    · simp [Homeomorph.inv₀]
    · simpa using hn

中文:
定理 isCoveringMap_zpow
  条件: (n : 整数) (hn : (n : 𝕜) != 0)
  证明: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · convert! isCoveringMap_npow n _ <;> aesop
  · convert! (isCoveringMap_npow n _).comp_homeomorph (.inv₀ 𝕜)
    · simp [Homeomorph.inv₀]
    · simpa using hn

Depends on / 依赖: Homeomorph, Homeomorph.inv, comp_homeomorph, convert, eq_nat_or_neg, isCoveringMap_npow, n.eq_nat_or_neg
-/
theorem isCoveringMap_zpow (n : Int) (hn : (n : 𝕜) != 0) :
    IsCoveringMap fun x : {x : 𝕜 // x != 0} => (⟨x ^ n, zpow_ne_zero n x.2⟩ : {x : 𝕜 // x != 0}) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · convert! isCoveringMap_npow n _ <;> aesop
  · convert! (isCoveringMap_npow n _).comp_homeomorph (.inv₀ 𝕜)
    · simp [Homeomorph.inv₀]
    · simpa using hn

/--
theorem `isCoveringMapOn_zpow` / 定理 `isCoveringMapOn_zpow`

English:
theorem isCoveringMapOn_zpow
  given: (n : Int) (hn : (n : 𝕜) != 0)
  proof: by
  have (x : 𝕜) : x ^ n = 0 ↔ x = 0 := zpow_eq_zero_iff (by aesop)
  refine .of_isCoveringMap_restrictPreimage _ (by simp) ?_ ?_
  · convert isClosed_singleton (x := (0 : 𝕜)).isOpen_compl
    ext; simp [this]
  · convert! (isCoveringMap_zpow n hn).comp_homeomorph (.setCongr _) using 1
    ext; sim

中文:
定理 isCoveringMapOn_zpow
  条件: (n : 整数) (hn : (n : 𝕜) != 0)
  证明: by
  have (x : 𝕜) : x ^ n = 0 ↔ x = 0 := zpow_eq_zero_iff (by aesop)
  refine .of_isCoveringMap_restrictPreimage _ (by simp) ?_ ?_
  · convert isClosed_singleton (x := (0 : 𝕜)).isOpen_compl
    ext; simp [this]
  · convert! (isCoveringMap_zpow n hn).comp_homeomorph (.setCongr _) using 1
    ext; sim

Depends on / 依赖: comp_homeomorph, convert, isClosed_singleton, isCoveringMap_zpow, isOpen_compl, of_isCoveringMap_restrictPreimage, setCongr, zpow_eq_zero_iff
-/
theorem isCoveringMapOn_zpow (n : Int) (hn : (n : 𝕜) != 0) :
    IsCoveringMapOn (fun x : 𝕜 => x ^ n) {0}ᶜ := by
  have (x : 𝕜) : x ^ n = 0 ↔ x = 0 := zpow_eq_zero_iff (by aesop)
  refine .of_isCoveringMap_restrictPreimage _ (by simp) ?_ ?_
  · convert isClosed_singleton (x := (0 : 𝕜)).isOpen_compl
    ext; simp [this]
  · convert! (isCoveringMap_zpow n hn).comp_homeomorph (.setCongr _) using 1
    ext; simpa using! (this _).not

attribute [-instance] Units.mulAction'

/--
theorem `isQuotientCoveringMap_npow` / 定理 `isQuotientCoveringMap_npow`

English:
theorem isQuotientCoveringMap_npow
  statement: (n : Nat) (hn : (n : 𝕜) != 0)
  proof: by
  rw [← rootsOfUnity_eq_ker]
  have : NeZero n := ⟨by aesop⟩
  have := ((isClosedMap_pow 𝕜 n).restrictPreimage {0}ᶜ).isQuotientMap
    (by fun_prop) (.restrictPreimage _ surj)
  have : IsQuotientMap fun x : 𝕜ˣ => x ^ n := by
    let e := unitsHomeomorphNeZero (G₀ := 𝕜)
    convert! (e.symm.isQuot

中文:
定理 isQuotientCoveringMap_npow
  结论: (n : 自然数) (hn : (n : 𝕜) != 0)
  证明: by
  rw [← rootsOfUnity_eq_ker]
  have : NeZero n := ⟨by aesop⟩
  have := ((isClosedMap_pow 𝕜 n).restrictPreimage {0}ᶜ).isQuotientMap
    (by fun_prop) (.restrictPreimage _ surj)
  have : IsQuotientMap fun x : 𝕜ˣ => x ^ n := by
    let e := unitsHomeomorphNeZero (G₀ := 𝕜)
    convert! (e.symm.isQuot

Depends on / 依赖: Finite, IsQuotientMap, NeZero, NeZero.ne, Set.Finite.isDiscrete, convert, e.left_inv, e.symm.isQuotientMap.comp, e.trans, fun_prop, inferInstanceA, isClosedMap_pow, isDiscrete, isQuotientCoveringMap_of_subgroup, isQuotientMap, left_inv, ofEqSubtypes, restrictPreimage, rootsOfUnity_eq_ker, this.isQuotientCoveringMap_of_subgroup
-/
theorem isQuotientCoveringMap_npow (n : Nat) (hn : (n : 𝕜) != 0)
    (surj : (fun x : 𝕜 => x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ => x ^ n) (powMonoidHom (α := 𝕜ˣ) n).ker := by
  rw [← rootsOfUnity_eq_ker]
  have : NeZero n := ⟨by aesop⟩
  have := ((isClosedMap_pow 𝕜 n).restrictPreimage {0}ᶜ).isQuotientMap
    (by fun_prop) (.restrictPreimage _ surj)
  have : IsQuotientMap fun x : 𝕜ˣ => x ^ n := by
    let e := unitsHomeomorphNeZero (G₀ := 𝕜)
    convert! (e.symm.isQuotientMap.comp this).comp (e.trans (.ofEqSubtypes _)).isQuotientMap
    · exact (e.left_inv _).symm
    · ext; simp [NeZero.ne]
  refine this.isQuotientCoveringMap_of_subgroup _
    (Set.Finite.isDiscrete <| inferInstanceAs (Finite (rootsOfUnity ..))) ?_
  simp [mul_pow, mul_inv_eq_one, eq_comm]

/--
theorem `Complex.isQuotientCoveringMap_npow` / 定理 `Complex.isQuotientCoveringMap_npow`

English:
theorem Complex.isQuotientCoveringMap_npow
  given: (n : Nat) [NeZero n]
  proof: isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ => ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩

中文:
定理 Complex.isQuotientCoveringMap_npow
  条件: (n : 自然数) [NeZero n]
  证明: isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ => ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩
-/
protected theorem Complex.isQuotientCoveringMap_npow (n : Nat) [NeZero n] :
    IsQuotientCoveringMap (fun z : Complexˣ => z ^ n) (powMonoidHom (α := Complexˣ) n).ker :=
  isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ => ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩

/--
theorem `isQuotientCoveringMap_zpow` / 定理 `isQuotientCoveringMap_zpow`

English:
theorem isQuotientCoveringMap_zpow
  statement: (n : Int) (hn : (n : 𝕜) != 0)
  proof: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact isQuotientCoveringMap_npow n (by aesop) (by simpa using surj)
  rw [show (zpowGroupHom (α := 𝕜ˣ) (-n)).ker = (powMonoidHom n).ker by ext; simp]
  convert (isQuotientCoveringMap_npow n (by aesop) _).homeomorph_comp (.inv 𝕜ˣ)
  · ext; simp
  conv

中文:
定理 isQuotientCoveringMap_zpow
  结论: (n : 整数) (hn : (n : 𝕜) != 0)
  证明: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact isQuotientCoveringMap_npow n (by aesop) (by simpa using surj)
  rw [show (zpowGroupHom (α := 𝕜ˣ) (-n)).ker = (powMonoidHom n).ker by ext; simp]
  convert (isQuotientCoveringMap_npow n (by aesop) _).homeomorph_comp (.inv 𝕜ˣ)
  · ext; simp
  conv

Depends on / 依赖: convert, eq_nat_or_neg, homeomorph_comp, inv_involutive, inv_involutive.surjective.comp, isQuotientCoveringMap_npow, n.eq_nat_or_neg, powMonoidHom, surjective, zpowGroupHom
-/
theorem isQuotientCoveringMap_zpow (n : Int) (hn : (n : 𝕜) != 0)
    (surj : (fun x : 𝕜 => x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ => x ^ n) (zpowGroupHom (α := 𝕜ˣ) n).ker := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact isQuotientCoveringMap_npow n (by aesop) (by simpa using surj)
  rw [show (zpowGroupHom (α := 𝕜ˣ) (-n)).ker = (powMonoidHom n).ker by ext; simp]
  convert (isQuotientCoveringMap_npow n (by aesop) _).homeomorph_comp (.inv 𝕜ˣ)
  · ext; simp
  convert! inv_involutive.surjective.comp surj; simp

end
