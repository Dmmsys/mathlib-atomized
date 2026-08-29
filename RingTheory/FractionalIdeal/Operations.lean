/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Field

/-!
# More operations on fractional ideals

## Main definitions
* `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
* `FractionalIdeal R⁰ K` is the type of fractional ideals in the field of fractions
* `Div (FractionalIdeal R⁰ K)` instance:
  the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statement

  * `isNoetherian` states that every fractional ideal of a Noetherian integral domain is Noetherian

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

@[expose] public section


open IsLocalization Pointwise nonZeroDivisors

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P]

section

variable {P' : Type*} [CommRing P'] [Algebra R P']
variable {P'' : Type*} [CommRing P''] [Algebra R P'']

/--
theorem `_root_.IsFractional.map` / 定理 `_root_.IsFractional.map`

English:
theorem _root_.IsFractional.map
  given: (g : P ->ₐ[R] P') {I : Submodule R P}
  proof: Submodule.mem_map.mp hb
      rw [AlgHom.toLinearMap_apply] at hb'
      obtain ⟨x, hx⟩ := hI b' b'_mem
      use x
      rw [← g.commutes]; rw [hx]; rw [map_smul]; rw [hb']⟩

中文:
定理 _root_.IsFractional.map
  条件: (g : P ->ₐ[R] P') {I : 子模 R P}
  证明: Submodule.mem_map.mp hb
      rw [AlgHom.toLinearMap_apply] at hb'
      obtain ⟨x, hx⟩ := hI b' b'_mem
      use x
      rw [← g.commutes]; rw [hx]; rw [map_smul]; rw [hb']⟩

Depends on / 依赖: Submodule, Submodule.mem_map.mp, mem_map
-/
theorem _root_.IsFractional.map (g : P ->ₐ[R] P') {I : Submodule R P} :
    IsFractional S I -> IsFractional S (Submodule.map g.toLinearMap I)
  | ⟨a, a_nonzero, hI⟩ =>
    ⟨a, a_nonzero, fun b hb => by
      obtain ⟨b', b'_mem, hb'⟩ := Submodule.mem_map.mp hb
      rw [AlgHom.toLinearMap_apply] at hb'
      obtain ⟨x, hx⟩ := hI b' b'_mem
      use x
      rw [← g.commutes]; rw [hx]; rw [map_smul]; rw [hb']⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (g : P ->ₐ[R] P')
  body: fun I =>
  ⟨Submodule.map g.toLinearMap I, I.isFractional.map g⟩

@[simp, norm_cast]

中文:
定义 map
  签名: (g : P ->ₐ[R] P')
  定义体: fun I =>
  ⟨Submodule.map g.toLinearMap I, I.isFractional.map g⟩

@[simp, norm_cast]
-/
def map (g : P ->ₐ[R] P') : FractionalIdeal S P -> FractionalIdeal S P' := fun I =>
  ⟨Submodule.map g.toLinearMap I, I.isFractional.map g⟩

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (g : P ->ₐ[R] P') (I : FractionalIdeal S P)
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (g : P ->ₐ[R] P') (I : FractionalIdeal S P)
  证明: rfl

@[simp]
-/
theorem coe_map (g : P ->ₐ[R] P') (I : FractionalIdeal S P) :
    ↑(map g I) = Submodule.map g.toLinearMap I :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {I : FractionalIdeal S P} {g : P ->ₐ[R] P'} {y : P'}
  proof: Submodule.mem_map

中文:
定理 mem_map
  条件: {I : FractionalIdeal S P} {g : P ->ₐ[R] P'} {y : P'}
  证明: Submodule.mem_map

Depends on / 依赖: Submodule, Submodule.mem_map, mem_map
-/
theorem mem_map {I : FractionalIdeal S P} {g : P ->ₐ[R] P'} {y : P'} :
    y in I.map g ↔ exists x, x in I ∧ g x = y :=
  Submodule.mem_map

variable (I J : FractionalIdeal S P) (g : P ->ₐ[R] P')

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: I.map (AlgHom.id _ _) = I
  proof: coeToSubmodule_injective (Submodule.map_id (I : Submodule R P))

@[simp]

中文:
定理 map_id
  结论: I.map (代数态射.id _ _) = I
  证明: coeToSubmodule_injective (Submodule.map_id (I : Submodule R P))

@[simp]

Depends on / 依赖: Submodule, Submodule.map_id, coeToSubmodule_injective, map_id
-/
theorem map_id : I.map (AlgHom.id _ _) = I :=
  coeToSubmodule_injective (Submodule.map_id (I : Submodule R P))

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (g' : P' ->ₐ[R] P'')
  statement: I.map (g'.comp g) = (I.map g).map g'
  proof: coeToSubmodule_injective (Submodule.map_comp g.toLinearMap g'.toLinearMap I)

@[simp, norm_cast]

中文:
定理 map_comp
  条件: (g' : P' ->ₐ[R] P'')
  结论: I.map (g'.comp g) = (I.map g).map g'
  证明: coeToSubmodule_injective (Submodule.map_comp g.toLinearMap g'.toLinearMap I)

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.map_comp, coeToSubmodule_injective, g.toLinearMap, map_comp, toLinearMap
-/
theorem map_comp (g' : P' ->ₐ[R] P'') : I.map (g'.comp g) = (I.map g).map g' :=
  coeToSubmodule_injective (Submodule.map_comp g.toLinearMap g'.toLinearMap I)

@[simp, norm_cast]
/--
theorem `map_coeIdeal` / 定理 `map_coeIdeal`

English:
theorem map_coeIdeal
  given: (I : Ideal R)
  statement: (I : FractionalIdeal S P).map g = I
  proof: by
  ext x
  simp

@[simp]

中文:
定理 map_coeIdeal
  条件: (I : 理想 R)
  结论: (I : FractionalIdeal S P).map g = I
  证明: by
  ext x
  simp

@[simp]
-/
theorem map_coeIdeal (I : Ideal R) : (I : FractionalIdeal S P).map g = I := by
  ext x
  simp

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: (1 : FractionalIdeal S P).map g = 1
  proof: map_coeIdeal g ⊤

@[simp]

中文:
定理 map_one
  结论: (1 : FractionalIdeal S P).map g = 1
  证明: map_coeIdeal g ⊤

@[simp]
-/
protected theorem map_one : (1 : FractionalIdeal S P).map g = 1 :=
  map_coeIdeal g ⊤

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: (0 : FractionalIdeal S P).map g = 0
  proof: map_coeIdeal g 0

@[simp]

中文:
定理 map_zero
  结论: (0 : FractionalIdeal S P).map g = 0
  证明: map_coeIdeal g 0

@[simp]
-/
protected theorem map_zero : (0 : FractionalIdeal S P).map g = 0 :=
  map_coeIdeal g 0

@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: (I + J).map g = I.map g + J.map g
  proof: coeToSubmodule_injective (Submodule.map_sup _ _ _)

@[simp]

中文:
定理 map_add
  结论: (I + J).map g = I.map g + J.map g
  证明: coeToSubmodule_injective (Submodule.map_sup _ _ _)

@[simp]
-/
protected theorem map_add : (I + J).map g = I.map g + J.map g :=
  coeToSubmodule_injective (Submodule.map_sup _ _ _)

@[simp]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  statement: (I * J).map g = I.map g * J.map g
  proof: by
  simp only [mul_def]
  exact coeToSubmodule_injective (Submodule.map_mul _ _ _)

@[simp]

中文:
定理 map_mul
  结论: (I * J).map g = I.map g * J.map g
  证明: by
  simp only [mul_def]
  exact coeToSubmodule_injective (Submodule.map_mul _ _ _)

@[simp]
-/
protected theorem map_mul : (I * J).map g = I.map g * J.map g := by
  simp only [mul_def]
  exact coeToSubmodule_injective (Submodule.map_mul _ _ _)

@[simp]
/--
theorem `map_map_symm` / 定理 `map_map_symm`

English:
theorem map_map_symm
  given: (g : P ≃ₐ[R] P')
  statement: (I.map (g : P ->ₐ[R] P')).map (g.symm : P' ->ₐ[R] P) = I
  proof: by
  rw [← map_comp]; rw [g.symm_comp]; rw [map_id]

@[simp]

中文:
定理 map_map_symm
  条件: (g : P ≃ₐ[R] P')
  结论: (I.map (g : P ->ₐ[R] P')).map (g.symm : P' ->ₐ[R] P) = I
  证明: by
  rw [← map_comp]; rw [g.symm_comp]; rw [map_id]

@[simp]

Depends on / 依赖: g.symm_comp, map_comp, map_id, symm_comp
-/
theorem map_map_symm (g : P ≃ₐ[R] P') : (I.map (g : P ->ₐ[R] P')).map (g.symm : P' ->ₐ[R] P) = I := by
  rw [← map_comp]; rw [g.symm_comp]; rw [map_id]

@[simp]
/--
theorem `map_symm_map` / 定理 `map_symm_map`

English:
theorem map_symm_map
  given: (I : FractionalIdeal S P') (g : P ≃ₐ[R] P')
  proof: by
  rw [← map_comp]; rw [g.comp_symm]; rw [map_id]

中文:
定理 map_symm_map
  条件: (I : FractionalIdeal S P') (g : P ≃ₐ[R] P')
  证明: by
  rw [← map_comp]; rw [g.comp_symm]; rw [map_id]

Depends on / 依赖: comp_symm, g.comp_symm, map_comp, map_id
-/
theorem map_symm_map (I : FractionalIdeal S P') (g : P ≃ₐ[R] P') :
    (I.map (g.symm : P' ->ₐ[R] P)).map (g : P ->ₐ[R] P') = I := by
  rw [← map_comp]; rw [g.comp_symm]; rw [map_id]

/--
theorem `map_mem_map` / 定理 `map_mem_map`

English:
theorem map_mem_map
  given: {f : P ->ₐ[R] P'} (h : Function.Injective f) {x : P} {I : FractionalIdeal S P}
  proof: mem_map.trans ⟨fun ⟨_, hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

中文:
定理 map_mem_map
  条件: {f : P ->ₐ[R] P'} (h : 函数.单射 f) {x : P} {I : FractionalIdeal S P}
  证明: mem_map.trans ⟨fun ⟨_, hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

Depends on / 依赖: mem_map, mem_map.trans
-/
theorem map_mem_map {f : P ->ₐ[R] P'} (h : Function.Injective f) {x : P} {I : FractionalIdeal S P} :
    f x in map f I ↔ x in I :=
  mem_map.trans ⟨fun ⟨_, hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (f : P ->ₐ[R] P') (h : Function.Injective f)
  proof: fun _ _ hIJ =>
  ext fun _ => (map_mem_map h).symm.trans (hIJ.symm ▸ map_mem_map h)

中文:
定理 map_injective
  条件: (f : P ->ₐ[R] P') (h : 函数.单射 f)
  证明: fun _ _ hIJ =>
  ext fun _ => (map_mem_map h).symm.trans (hIJ.symm ▸ map_mem_map h)
-/
theorem map_injective (f : P ->ₐ[R] P') (h : Function.Injective f) :
    Function.Injective (map f : FractionalIdeal S P -> FractionalIdeal S P') := fun _ _ hIJ =>
  ext fun _ => (map_mem_map h).symm.trans (hIJ.symm ▸ map_mem_map h)

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (g : P ≃ₐ[R] P')
  body: map g
  invFun := map g.symm
  map_add' I J := FractionalIdeal.map_add I J _
  map_mul' I J := FractionalIdeal.map_mul I J _
  left_inv I := by rw [← map_comp, AlgEquiv.symm_comp, map_id]
  right_inv I := by rw [← map_comp, AlgEquiv.comp_symm, map_id]

@[simp]

中文:
定义 mapEquiv
  签名: (g : P ≃ₐ[R] P')
  定义体: map g
  invFun := map g.symm
  map_add' I J := FractionalIdeal.map_add I J _
  map_mul' I J := FractionalIdeal.map_mul I J _
  left_inv I := by rw [← map_comp, AlgEquiv.symm_comp, map_id]
  right_inv I := by rw [← map_comp, AlgEquiv.comp_symm, map_id]

@[simp]
-/
def mapEquiv (g : P ≃ₐ[R] P') : FractionalIdeal S P ≃+* FractionalIdeal S P' where
  toFun := map g
  invFun := map g.symm
  map_add' I J := FractionalIdeal.map_add I J _
  map_mul' I J := FractionalIdeal.map_mul I J _
  left_inv I := by rw [← map_comp, AlgEquiv.symm_comp, map_id]
  right_inv I := by rw [← map_comp, AlgEquiv.comp_symm, map_id]

@[simp]
/--
theorem `coeFun_mapEquiv` / 定理 `coeFun_mapEquiv`

English:
theorem coeFun_mapEquiv
  given: (g : P ≃ₐ[R] P')
  proof: rfl

@[simp]

中文:
定理 coeFun_mapEquiv
  条件: (g : P ≃ₐ[R] P')
  证明: rfl

@[simp]
-/
theorem coeFun_mapEquiv (g : P ≃ₐ[R] P') :
    (mapEquiv g : FractionalIdeal S P -> FractionalIdeal S P') = map g :=
  rfl

@[simp]
/--
theorem `mapEquiv_apply` / 定理 `mapEquiv_apply`

English:
theorem mapEquiv_apply
  given: (g : P ≃ₐ[R] P') (I : FractionalIdeal S P)
  statement: mapEquiv g I = map (↑g) I
  proof: rfl

@[simp]

中文:
定理 mapEquiv_apply
  条件: (g : P ≃ₐ[R] P') (I : FractionalIdeal S P)
  结论: mapEquiv g I = map (↑g) I
  证明: rfl

@[simp]
-/
theorem mapEquiv_apply (g : P ≃ₐ[R] P') (I : FractionalIdeal S P) : mapEquiv g I = map (↑g) I :=
  rfl

@[simp]
/--
theorem `mapEquiv_symm` / 定理 `mapEquiv_symm`

English:
theorem mapEquiv_symm
  given: (g : P ≃ₐ[R] P')
  proof: rfl

@[simp]

中文:
定理 mapEquiv_symm
  条件: (g : P ≃ₐ[R] P')
  证明: rfl

@[simp]
-/
theorem mapEquiv_symm (g : P ≃ₐ[R] P') :
    ((mapEquiv g).symm : FractionalIdeal S P' ≃+* _) = mapEquiv g.symm :=
  rfl

@[simp]
/--
theorem `mapEquiv_refl` / 定理 `mapEquiv_refl`

English:
theorem mapEquiv_refl
  statement: mapEquiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S P)
  proof: RingEquiv.ext fun x => by simp

中文:
定理 mapEquiv_refl
  结论: mapEquiv 代数等价.refl = 环等价.refl (FractionalIdeal S P)
  证明: RingEquiv.ext fun x => by simp

Depends on / 依赖: RingEquiv, RingEquiv.ext
-/
theorem mapEquiv_refl : mapEquiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S P) :=
  RingEquiv.ext fun x => by simp

/--
theorem `isFractional_span_iff` / 定理 `isFractional_span_iff`

English:
theorem isFractional_span_iff
  given: {s : Set P}
  proof: ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩, fun ⟨a, a_mem, h⟩ =>
    ⟨a, a_mem, fun _ hb =>
      span_induction (hx := hb) h
        (by
          rw [smul_zero]
          exact isInteger_zero)
        (fun x y _ _ hx hy => by
          rw [smul_add]
          exact isIntege

中文:
定理 isFractional_span_iff
  条件: {s : 集合 P}
  证明: ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩, fun ⟨a, a_mem, h⟩ =>
    ⟨a, a_mem, fun _ hb =>
      span_induction (hx := hb) h
        (by
          rw [smul_zero]
          exact isInteger_zero)
        (fun x y _ _ hx hy => by
          rw [smul_add]
          exact isIntege

Depends on / 依赖: a_mem, isInteger_add, isInteger_smul, isInteger_zero, smul_add, smul_comm, smul_zero, span_induction, subset_span
-/
theorem isFractional_span_iff {s : Set P} :
    IsFractional S (span R s) ↔ exists a in S, forall b : P, b in s -> IsInteger R (a • b) :=
  ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩, fun ⟨a, a_mem, h⟩ =>
    ⟨a, a_mem, fun _ hb =>
      span_induction (hx := hb) h
        (by
          rw [smul_zero]
          exact isInteger_zero)
        (fun x y _ _ hx hy => by
          rw [smul_add]
          exact isInteger_add hx hy)
        fun s x _ hx => by
        rw [smul_comm]
        exact isInteger_smul hx⟩⟩

/--
theorem `isFractional_of_fg` / 定理 `isFractional_of_fg`

English:
theorem isFractional_of_fg
  given: [IsLocalization S P] {I : Submodule R P} (hI : I.FG)
  proof: by
  rcases hI with ⟨I, rfl⟩
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
  rw [isFractional_span_iff]
  exact ⟨s, hs1, hs⟩

中文:
定理 isFractional_of_fg
  条件: [是Localization S P] {I : 子模 R P} (hI : I.FG)
  证明: by
  rcases hI with ⟨I, rfl⟩
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
  rw [isFractional_span_iff]
  exact ⟨s, hs1, hs⟩

Depends on / 依赖: exist_integer_multiples_of_finset, isFractional_span_iff
-/
theorem isFractional_of_fg [IsLocalization S P] {I : Submodule R P} (hI : I.FG) :
    IsFractional S I := by
  rcases hI with ⟨I, rfl⟩
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
  rw [isFractional_span_iff]
  exact ⟨s, hs1, hs⟩

/--
theorem `mem_span_mul_finite_of_mem_mul` / 定理 `mem_span_mul_finite_of_mem_mul`

English:
theorem mem_span_mul_finite_of_mem_mul
  given: {I J : FractionalIdeal S P} {x : P} (hx : x in I * J)
  proof: Submodule.mem_span_mul_finite_of_mem_mul (by simpa using mem_coe.mpr hx)

中文:
定理 mem_span_mul_finite_of_mem_mul
  条件: {I J : FractionalIdeal S P} {x : P} (hx : x in I * J)
  证明: Submodule.mem_span_mul_finite_of_mem_mul (by simpa using mem_coe.mpr hx)

Depends on / 依赖: Submodule, Submodule.mem_span_mul_finite_of_mem_mul, mem_coe, mem_coe.mpr, mem_span_mul_finite_of_mem_mul
-/
theorem mem_span_mul_finite_of_mem_mul {I J : FractionalIdeal S P} {x : P} (hx : x in I * J) :
    exists T T' : Finset P, (T : Set P) subseteq I ∧ (T' : Set P) subseteq J ∧ x in span R (T * T' : Set P) :=
  Submodule.mem_span_mul_finite_of_mem_mul (by simpa using mem_coe.mpr hx)

/--
lemma `_root_.Units.submodule_isFractional` / 引理 `_root_.Units.submodule_isFractional`

English:
lemma _root_.Units.submodule_isFractional
  given: [IsLocalization S P] (I : (Submodule R P)ˣ)
  proof: FractionalIdeal.isFractional_of_fg (fg_unit _)

中文:
引理 _root_.单位群.submodule_isFractional
  条件: [是Localization S P] (I : (子模 R P)ˣ)
  证明: FractionalIdeal.isFractional_of_fg (fg_unit _)

Depends on / 依赖: FractionalIdeal, FractionalIdeal.isFractional_of_fg, fg_unit, isFractional_of_fg
-/
lemma _root_.Units.submodule_isFractional [IsLocalization S P] (I : (Submodule R P)ˣ) :
    IsFractional S I.1 :=
  FractionalIdeal.isFractional_of_fg (fg_unit _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unitsMulEquivSubmodule` / `unitsMulEquivSubmodule` 的定义

English:
definition unitsMulEquivSubmodule
  signature: [IsLocalization S P]
  body: Units.map (coeSubmoduleHom S P)
  invFun I := ⟨⟨I, I.submodule_isFractional⟩, ⟨↑I⁻¹, I⁻¹.submodule_isFractional⟩,
coeToSubmodule_inj.mp by rw [coe_mul, coe_one]; exact I.mul_inv,
coeToSubmodule_inj.mp by rw [coe_mul, coe_one]; exact I.inv_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 unitsMulEquivSubmodule
  签名: [是Localization S P]
  定义体: Units.map (coeSubmoduleHom S P)
  invFun I := ⟨⟨I, I.submodule_isFractional⟩, ⟨↑I⁻¹, I⁻¹.submodule_isFractional⟩,
coeToSubmodule_inj.mp by rw [coe_mul, coe_one]; exact I.mul_inv,
coeToSubmodule_inj.mp by rw [coe_mul, coe_one]; exact I.inv_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: Units.map, coeSubmoduleHom
-/
def unitsMulEquivSubmodule [IsLocalization S P] :
    (FractionalIdeal S P)ˣ ≃* (Submodule R P)ˣ where
  __ := Units.map (coeSubmoduleHom S P)
  invFun I := ⟨⟨I, I.submodule_isFractional⟩, ⟨↑I⁻¹, I⁻¹.submodule_isFractional⟩,
coeToSubmodule_inj.mp by rw [coe_mul, coe_one]; exact I.mul_inv,
coeToSubmodule_inj.mp by rw [coe_mul, coe_one]; exact I.inv_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (S) in
/--
theorem `coeIdeal_fg` / 定理 `coeIdeal_fg`

English:
theorem coeIdeal_fg
  given: (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
  proof: coeSubmodule_fg _ inj _

中文:
定理 coeIdeal_fg
  条件: (inj : 函数.单射 (algebraMap R P)) (I : 理想 R)
  证明: coeSubmodule_fg _ inj _

Depends on / 依赖: coeSubmodule_fg
-/
theorem coeIdeal_fg (inj : Function.Injective (algebraMap R P)) (I : Ideal R) :
    FG ((I : FractionalIdeal S P) : Submodule R P) ↔ I.FG :=
  coeSubmodule_fg _ inj _

/--
theorem `fg_unit` / 定理 `fg_unit`

English:
theorem fg_unit
  given: (I : (FractionalIdeal S P)ˣ)
  statement: FG (I : Submodule R P)
  proof: Submodule.fg_unit Units.map (coeSubmoduleHom S P).toMonoidHom I

中文:
定理 fg_unit
  条件: (I : (FractionalIdeal S P)ˣ)
  结论: FG (I : 子模 R P)
  证明: Submodule.fg_unit Units.map (coeSubmoduleHom S P).toMonoidHom I

Depends on / 依赖: Submodule, Submodule.fg_unit, Units.map, coeSubmoduleHom, fg_unit, toMonoidHom
-/
theorem fg_unit (I : (FractionalIdeal S P)ˣ) : FG (I : Submodule R P) :=
Submodule.fg_unit Units.map (coeSubmoduleHom S P).toMonoidHom I

/--
theorem `fg_of_isUnit` / 定理 `fg_of_isUnit`

English:
theorem fg_of_isUnit
  given: (I : FractionalIdeal S P) (h : IsUnit I)
  statement: FG (I : Submodule R P)
  proof: fg_unit h.unit

中文:
定理 fg_of_isUnit
  条件: (I : FractionalIdeal S P) (h : 是单位 I)
  结论: FG (I : 子模 R P)
  证明: fg_unit h.unit

Depends on / 依赖: fg_unit, h.unit
-/
theorem fg_of_isUnit (I : FractionalIdeal S P) (h : IsUnit I) : FG (I : Submodule R P) :=
  fg_unit h.unit

/--
theorem `_root_.Ideal.fg_of_isUnit` / 定理 `_root_.Ideal.fg_of_isUnit`

English:
theorem _root_.Ideal.fg_of_isUnit
  statement: (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
  proof: by
  rw [← coeIdeal_fg S inj I]
  exact FractionalIdeal.fg_of_isUnit (R := R) I h

中文:
定理 _root_.理想.fg_of_isUnit
  结论: (inj : 函数.单射 (algebraMap R P)) (I : 理想 R)
  证明: by
  rw [← coeIdeal_fg S inj I]
  exact FractionalIdeal.fg_of_isUnit (R := R) I h

Depends on / 依赖: FractionalIdeal, FractionalIdeal.fg_of_isUnit, coeIdeal_fg, fg_of_isUnit
-/
theorem _root_.Ideal.fg_of_isUnit (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
    (h : IsUnit (I : FractionalIdeal S P)) : I.FG := by
  rw [← coeIdeal_fg S inj I]
  exact FractionalIdeal.fg_of_isUnit (R := R) I h

variable (S P P')

variable [IsLocalization S P] [IsLocalization S P']

/-- `canonicalEquiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'`, which are both localizations of `R` at `S`. -/
noncomputable irreducible_def canonicalEquiv : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  mapEquiv
    { ringEquivOfRingEquiv P P' (RingEquiv.refl R)
        (show S.map _ = S by rw [RingEquiv.toMonoidHom_refl, Submonoid.map_id]) with
      commutes' := fun _ => ringEquivOfRingEquiv_eq _ _ }

@[simp]
/--
theorem `mem_canonicalEquiv_apply` / 定理 `mem_canonicalEquiv_apply`

English:
theorem mem_canonicalEquiv_apply
  given: {I : FractionalIdeal S P} {x : P'}
  proof: by
  rw [canonicalEquiv]; rw [mapEquiv_apply]; rw [mem_map]
  exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]

中文:
定理 mem_canonicalEquiv_apply
  条件: {I : FractionalIdeal S P} {x : P'}
  证明: by
  rw [canonicalEquiv]; rw [mapEquiv_apply]; rw [mem_map]
  exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]

Depends on / 依赖: canonicalEquiv, mapEquiv_apply, mem_map
-/
theorem mem_canonicalEquiv_apply {I : FractionalIdeal S P} {x : P'} :
    x in canonicalEquiv S P P' I ↔
      exists y in I,
        IsLocalization.map P' (RingHom.id R) (fun y (hy : y in S) => show RingHom.id R y in S from hy)
            (y : P) =
          x := by
  rw [canonicalEquiv]; rw [mapEquiv_apply]; rw [mem_map]
  exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]
/--
theorem `canonicalEquiv_symm` / 定理 `canonicalEquiv_symm`

English:
theorem canonicalEquiv_symm
  statement: (canonicalEquiv S P P').symm = canonicalEquiv S P' P
  proof: RingEquiv.ext fun I =>
    SetLike.ext_iff.mpr fun x => by
      rw [mem_canonicalEquiv_apply]; rw [canonicalEquiv]; rw [mapEquiv_symm]; rw [mapEquiv_apply]; rw [mem_map]
      exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

中文:
定理 canonicalEquiv_symm
  结论: (canonicalEquiv S P P').symm = canonicalEquiv S P' P
  证明: RingEquiv.ext fun I =>
    SetLike.ext_iff.mpr fun x => by
      rw [mem_canonicalEquiv_apply]; rw [canonicalEquiv]; rw [mapEquiv_symm]; rw [mapEquiv_apply]; rw [mem_map]
      exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

Depends on / 依赖: RingEquiv, RingEquiv.ext, SetLike, SetLike.ext_iff.mpr, canonicalEquiv, ext_iff, mapEquiv_apply, mapEquiv_symm, mem_canonicalEquiv_apply, mem_map
-/
theorem canonicalEquiv_symm : (canonicalEquiv S P P').symm = canonicalEquiv S P' P :=
  RingEquiv.ext fun I =>
    SetLike.ext_iff.mpr fun x => by
      rw [mem_canonicalEquiv_apply]; rw [canonicalEquiv]; rw [mapEquiv_symm]; rw [mapEquiv_apply]; rw [mem_map]
      exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

/--
theorem `canonicalEquiv_flip` / 定理 `canonicalEquiv_flip`

English:
theorem canonicalEquiv_flip
  given: (I)
  statement: canonicalEquiv S P P' (canonicalEquiv S P' P I) = I
  proof: by
  rw [← canonicalEquiv_symm]; rw [RingEquiv.symm_apply_apply]

中文:
定理 canonicalEquiv_flip
  条件: (I)
  结论: canonicalEquiv S P P' (canonicalEquiv S P' P I) = I
  证明: by
  rw [← canonicalEquiv_symm]; rw [RingEquiv.symm_apply_apply]

Depends on / 依赖: RingEquiv, RingEquiv.symm_apply_apply, canonicalEquiv_symm, symm_apply_apply
-/
theorem canonicalEquiv_flip (I) : canonicalEquiv S P P' (canonicalEquiv S P' P I) = I := by
  rw [← canonicalEquiv_symm]; rw [RingEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `canonicalEquiv_canonicalEquiv` / 定理 `canonicalEquiv_canonicalEquiv`

English:
theorem canonicalEquiv_canonicalEquiv
  statement: (P'' : Type*) [CommRing P''] [Algebra R P'']
  proof: by
  ext
  simp [IsLocalization.map_map]

中文:
定理 canonicalEquiv_canonicalEquiv
  结论: (P'' : 类型) [交换环 P''] [代数 R P'']
  证明: by
  ext
  simp [IsLocalization.map_map]

Depends on / 依赖: IsLocalization, IsLocalization.map_map, map_map
-/
theorem canonicalEquiv_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] (I : FractionalIdeal S P) :
    canonicalEquiv S P' P'' (canonicalEquiv S P P' I) = canonicalEquiv S P P'' I := by
  ext
  simp [IsLocalization.map_map]

/--
theorem `canonicalEquiv_trans_canonicalEquiv` / 定理 `canonicalEquiv_trans_canonicalEquiv`

English:
theorem canonicalEquiv_trans_canonicalEquiv
  statement: (P'' : Type*) [CommRing P''] [Algebra R P'']
  proof: RingEquiv.ext (canonicalEquiv_canonicalEquiv S P P' P'')

中文:
定理 canonicalEquiv_trans_canonicalEquiv
  结论: (P'' : 类型) [交换环 P''] [代数 R P'']
  证明: RingEquiv.ext (canonicalEquiv_canonicalEquiv S P P' P'')

Depends on / 依赖: RingEquiv, RingEquiv.ext, canonicalEquiv_canonicalEquiv
-/
theorem canonicalEquiv_trans_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] :
    (canonicalEquiv S P P').trans (canonicalEquiv S P' P'') = canonicalEquiv S P P'' :=
  RingEquiv.ext (canonicalEquiv_canonicalEquiv S P P' P'')

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `canonicalEquiv_coeIdeal` / 定理 `canonicalEquiv_coeIdeal`

English:
theorem canonicalEquiv_coeIdeal
  given: (I : Ideal R)
  statement: canonicalEquiv S P P' I = I
  proof: by
  ext
  simp [IsLocalization.map_eq]

@[simp]

中文:
定理 canonicalEquiv_coeIdeal
  条件: (I : 理想 R)
  结论: canonicalEquiv S P P' I = I
  证明: by
  ext
  simp [IsLocalization.map_eq]

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.map_eq, map_eq
-/
theorem canonicalEquiv_coeIdeal (I : Ideal R) : canonicalEquiv S P P' I = I := by
  ext
  simp [IsLocalization.map_eq]

@[simp]
/--
theorem `canonicalEquiv_self` / 定理 `canonicalEquiv_self`

English:
theorem canonicalEquiv_self
  statement: canonicalEquiv S P P = RingEquiv.refl _
  proof: by
  rw [← canonicalEquiv_trans_canonicalEquiv S P P]
  convert! (canonicalEquiv S P P).symm_trans_self
  exact (canonicalEquiv_symm S P P).symm

中文:
定理 canonicalEquiv_self
  结论: canonicalEquiv S P P = 环等价.refl _
  证明: by
  rw [← canonicalEquiv_trans_canonicalEquiv S P P]
  convert! (canonicalEquiv S P P).symm_trans_self
  exact (canonicalEquiv_symm S P P).symm

Depends on / 依赖: canonicalEquiv, canonicalEquiv_symm, canonicalEquiv_trans_canonicalEquiv, convert, symm_trans_self
-/
theorem canonicalEquiv_self : canonicalEquiv S P P = RingEquiv.refl _ := by
  rw [← canonicalEquiv_trans_canonicalEquiv S P P]
  convert! (canonicalEquiv S P P).symm_trans_self
  exact (canonicalEquiv_symm S P P).symm

end

section IsFractionRing

/-!
### `IsFractionRing` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `FractionalIdeal R⁰ K` where `IsFractionRing R K`.
-/


variable {K K' : Type*} [Field K] [Field K']
variable [Algebra R K] [IsFractionRing R K] [Algebra R K'] [IsFractionRing R K']
variable {I J : FractionalIdeal R⁰ K} (h : K ->ₐ[R] K')

/--
theorem `exists_ne_zero_mem_isInteger` / 定理 `exists_ne_zero_mem_isInteger`

English:
theorem exists_ne_zero_mem_isInteger
  given: [Nontrivial R] (hI : I != 0)
  proof: by
  obtain ⟨y : K, y_mem, y_notMem⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  have y_ne_zero : y != 0 := by simpa using y_notMem
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y
  refine ⟨x, ?_, ?_⟩
  · rw [Ne, ← @IsFractionRing.to_map_eq_zero_iff R _ K, hx, Algebra.smul_def]
  

中文:
定理 存在_ne_zero_mem_is整数eger
  条件: [非平凡 R] (hI : I != 0)
  证明: by
  obtain ⟨y : K, y_mem, y_notMem⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  have y_ne_zero : y != 0 := by simpa using y_notMem
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y
  refine ⟨x, ?_, ?_⟩
  · rw [Ne, ← @IsFractionRing.to_map_eq_zero_iff R _ K, hx, Algebra.smul_def]
  

Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.to_map_eq_zero_iff, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors, SetLike, SetLike.exists_of_lt, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, exists_integer_multiple, exists_of_lt, mul_ne_zero, smul_def, smul_mem, to_map_eq_zero_iff, to_map_ne_zero_of_mem_nonZeroDivisors, y_mem, y_ne_zero, y_notMem
-/
theorem exists_ne_zero_mem_isInteger [Nontrivial R] (hI : I != 0) :
    exists x, x != 0 ∧ algebraMap R K x in I := by
  obtain ⟨y : K, y_mem, y_notMem⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  have y_ne_zero : y != 0 := by simpa using y_notMem
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y
  refine ⟨x, ?_, ?_⟩
  · rw [Ne, ← @IsFractionRing.to_map_eq_zero_iff R _ K, hx, Algebra.smul_def]
    exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2) y_ne_zero
  · rw [hx]
    exact smul_mem _ _ y_mem

/--
theorem `map_ne_zero` / 定理 `map_ne_zero`

English:
theorem map_ne_zero
  given: [Nontrivial R] (hI : I != 0)
  statement: I.map h != 0
  proof: by
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_isInteger hI
  contrapose x_ne_zero with map_eq_zero
  refine IsFractionRing.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr ?_))
  exact ⟨algebraMap R K x, hx, h.commutes x⟩

@[simp]

中文:
定理 map_ne_zero
  条件: [非平凡 R] (hI : I != 0)
  结论: I.map h != 0
  证明: by
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_isInteger hI
  contrapose x_ne_zero with map_eq_zero
  refine IsFractionRing.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr ?_))
  exact ⟨algebraMap R K x, hx, h.commutes x⟩

@[simp]

Depends on / 依赖: IsFractionRing, IsFractionRing.to_map_eq_zero_iff.mp, algebraMap, commutes, contrapose, eq_zero_iff, eq_zero_iff.mp, exists_ne_zero_mem_isInteger, h.commutes, map_eq_zero, mem_map, mem_map.mpr, to_map_eq_zero_iff, x_ne_zero
-/
theorem map_ne_zero [Nontrivial R] (hI : I != 0) : I.map h != 0 := by
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_isInteger hI
  contrapose x_ne_zero with map_eq_zero
  refine IsFractionRing.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr ?_))
  exact ⟨algebraMap R K x, hx, h.commutes x⟩

@[simp]
/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: [Nontrivial R]
  statement: I.map h = 0 ↔ I = 0
  proof: ⟨not_imp_not.mp (map_ne_zero _), fun hI => hI.symm ▸ FractionalIdeal.map_zero h⟩

中文:
定理 map_eq_zero_iff
  条件: [非平凡 R]
  结论: I.map h = 0 ↔ I = 0
  证明: ⟨not_imp_not.mp (map_ne_zero _), fun hI => hI.symm ▸ FractionalIdeal.map_zero h⟩

Depends on / 依赖: FractionalIdeal, FractionalIdeal.map_zero, hI.symm, map_ne_zero, map_zero, not_imp_not, not_imp_not.mp
-/
theorem map_eq_zero_iff [Nontrivial R] : I.map h = 0 ↔ I = 0 :=
  ⟨not_imp_not.mp (map_ne_zero _), fun hI => hI.symm ▸ FractionalIdeal.map_zero h⟩

/--
theorem `coeIdeal_injective` / 定理 `coeIdeal_injective`

English:
theorem coeIdeal_injective
  statement: Function.Injective (fun (I : Ideal R) => (I : FractionalIdeal R⁰ K))
  proof: coeIdeal_injective' le_rfl

中文:
定理 coeIdeal_injective
  结论: 函数.单射 (fun (I : 理想 R) => (I : FractionalIdeal R⁰ K))
  证明: coeIdeal_injective' le_rfl

Depends on / 依赖: coeIdeal_injective, le_rfl
-/
theorem coeIdeal_injective : Function.Injective (fun (I : Ideal R) => (I : FractionalIdeal R⁰ K)) :=
  coeIdeal_injective' le_rfl

/--
theorem `coeIdeal_inj` / 定理 `coeIdeal_inj`

English:
theorem coeIdeal_inj
  given: {I J : Ideal R}
  proof: coeIdeal_inj' le_rfl

@[simp]

中文:
定理 coeIdeal_inj
  条件: {I J : 理想 R}
  证明: coeIdeal_inj' le_rfl

@[simp]

Depends on / 依赖: coeIdeal_inj, le_rfl
-/
theorem coeIdeal_inj {I J : Ideal R} :
    (I : FractionalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J :=
  coeIdeal_inj' le_rfl

@[simp]
/--
theorem `coeIdeal_eq_zero` / 定理 `coeIdeal_eq_zero`

English:
theorem coeIdeal_eq_zero
  given: {I : Ideal R}
  statement: (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥
  proof: coeIdeal_eq_zero' le_rfl

中文:
定理 coeIdeal_eq_zero
  条件: {I : 理想 R}
  结论: (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥
  证明: coeIdeal_eq_zero' le_rfl

Depends on / 依赖: coeIdeal_eq_zero, le_rfl
-/
theorem coeIdeal_eq_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ :=
  coeIdeal_eq_zero' le_rfl

/--
theorem `coeIdeal_ne_zero` / 定理 `coeIdeal_ne_zero`

English:
theorem coeIdeal_ne_zero
  given: {I : Ideal R}
  statement: (I : FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
  proof: coeIdeal_ne_zero' le_rfl

@[simp]

中文:
定理 coeIdeal_ne_zero
  条件: {I : 理想 R}
  结论: (I : FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
  证明: coeIdeal_ne_zero' le_rfl

@[simp]

Depends on / 依赖: coeIdeal_ne_zero, le_rfl
-/
theorem coeIdeal_ne_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) != 0 ↔ I != ⊥ :=
  coeIdeal_ne_zero' le_rfl

@[simp]
/--
theorem `coeIdeal_eq_one` / 定理 `coeIdeal_eq_one`

English:
theorem coeIdeal_eq_one
  given: {I : Ideal R}
  statement: (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1
  proof: by
  simpa only [Ideal.one_eq_top] using! coeIdeal_inj

中文:
定理 coeIdeal_eq_one
  条件: {I : 理想 R}
  结论: (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1
  证明: by
  simpa only [Ideal.one_eq_top] using! coeIdeal_inj

Depends on / 依赖: Ideal.one_eq_top, coeIdeal_inj, one_eq_top
-/
theorem coeIdeal_eq_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1 := by
  simpa only [Ideal.one_eq_top] using! coeIdeal_inj

/--
theorem `coeIdeal_ne_one` / 定理 `coeIdeal_ne_one`

English:
theorem coeIdeal_ne_one
  given: {I : Ideal R}
  statement: (I : FractionalIdeal R⁰ K) != 1 ↔ I != 1
  proof: not_iff_not.mpr coeIdeal_eq_one

中文:
定理 coeIdeal_ne_one
  条件: {I : 理想 R}
  结论: (I : FractionalIdeal R⁰ K) != 1 ↔ I != 1
  证明: not_iff_not.mpr coeIdeal_eq_one

Depends on / 依赖: coeIdeal_eq_one, not_iff_not, not_iff_not.mpr
-/
theorem coeIdeal_ne_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) != 1 ↔ I != 1 :=
  not_iff_not.mpr coeIdeal_eq_one

/--
theorem `num_eq_zero_iff` / 定理 `num_eq_zero_iff`

English:
theorem num_eq_zero_iff
  given: [IsDomain R] {I : FractionalIdeal R⁰ K}
  statement: I.num = 0 ↔ I = 0 where
  proof: zero_of_num_eq_bot zero_notMem_nonZeroDivisors h
  mpr h := h ▸ num_zero_eq (IsFractionRing.injective R K)

中文:
定理 num_eq_zero_iff
  条件: [是整环 R] {I : FractionalIdeal R⁰ K}
  结论: I.num = 0 ↔ I = 0 where
  证明: zero_of_num_eq_bot zero_notMem_nonZeroDivisors h
  mpr h := h ▸ num_zero_eq (IsFractionRing.injective R K)

Depends on / 依赖: zero_notMem_nonZeroDivisors, zero_of_num_eq_bot
-/
theorem num_eq_zero_iff [IsDomain R] {I : FractionalIdeal R⁰ K} : I.num = 0 ↔ I = 0 where
  mp h := zero_of_num_eq_bot zero_notMem_nonZeroDivisors h
  mpr h := h ▸ num_zero_eq (IsFractionRing.injective R K)

end IsFractionRing

section Quotient

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = nonZeroDivisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]
variable [Algebra R₁ K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (FractionalIdeal R₁⁰ K)
  body: ⟨⟨0, 1, fun h =>
      have : (1 : K) in (0 : FractionalIdeal R₁⁰ K) := by
        rw [← (algebraMap R₁ K).map_one]
        simpa only [h] using coe_mem_one R₁⁰ 1
      one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

中文:
实例 :
  签名: 非平凡 (FractionalIdeal R₁⁰ K)
  定义体: ⟨⟨0, 1, fun h =>
      have : (1 : K) in (0 : FractionalIdeal R₁⁰ K) := by
        rw [← (algebraMap R₁ K).map_one]
        simpa only [h] using coe_mem_one R₁⁰ 1
      one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

Depends on / 依赖: FractionalIdeal, algebraMap, coe_mem_one, map_one, mem_zero_iff, one_ne_zero
-/
instance : Nontrivial (FractionalIdeal R₁⁰ K) :=
  ⟨⟨0, 1, fun h =>
      have : (1 : K) in (0 : FractionalIdeal R₁⁰ K) := by
        rw [← (algebraMap R₁ K).map_one]
        simpa only [h] using coe_mem_one R₁⁰ 1
      one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

/--
theorem `ne_zero_of_mul_eq_one` / 定理 `ne_zero_of_mul_eq_one`

English:
theorem ne_zero_of_mul_eq_one
  given: (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1)
  statement: I != 0
  proof: fun hI =>
  zero_ne_one' (FractionalIdeal R₁⁰ K)
    (by
      convert! h
      simp [hI])

中文:
定理 ne_zero_of_mul_eq_one
  条件: (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1)
  结论: I != 0
  证明: fun hI =>
  zero_ne_one' (FractionalIdeal R₁⁰ K)
    (by
      convert! h
      simp [hI])
-/
theorem ne_zero_of_mul_eq_one (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : I != 0 := fun hI =>
  zero_ne_one' (FractionalIdeal R₁⁰ K)
    (by
      convert! h
      simp [hI])

variable [IsFractionRing R₁ K] [IsDomain R₁]

/--
theorem `_root_.IsFractional.div_of_nonzero` / 定理 `_root_.IsFractional.div_of_nonzero`

English:
theorem _root_.IsFractional.div_of_nonzero
  given: {I J : Submodule R₁ K}
  proof: SetLike.exists_of_lt (show 0 < J by simpa only using! bot_lt_iff_ne_bot.mpr h)
    obtain ⟨y', hy'⟩ := hJ y mem_J
    use aI * y'
    constructor
    · apply (nonZeroDivisors R₁).mul_mem haI (mem_nonZeroDivisors_iff_ne_zero.mpr _)
      intro y'_eq_zero
      have : algebraMap R₁ K aJ * y = 0 := by


中文:
定理 _root_.IsFractional.div_of_nonzero
  条件: {I J : 子模 R₁ K}
  证明: SetLike.exists_of_lt (show 0 < J by simpa only using! bot_lt_iff_ne_bot.mpr h)
    obtain ⟨y', hy'⟩ := hJ y mem_J
    use aI * y'
    constructor
    · apply (nonZeroDivisors R₁).mul_mem haI (mem_nonZeroDivisors_iff_ne_zero.mpr _)
      intro y'_eq_zero
      have : algebraMap R₁ K aJ * y = 0 := by


Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.injective, SetLike, SetLike.exists_of_lt, _eq_zero, algebraMap, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, exists_of_lt, injective, injective_iff_map_eq_zero, map_zero, mem_J, mem_nonZeroDivisors_if, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mpr, mul_eq_zero, mul_eq_zero.mp
-/
theorem _root_.IsFractional.div_of_nonzero {I J : Submodule R₁ K} :
    IsFractional R₁⁰ I -> IsFractional R₁⁰ J -> J != 0 -> IsFractional R₁⁰ (I / J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩, h => by
    obtain ⟨y, mem_J, notMem_zero⟩ :=
      SetLike.exists_of_lt (show 0 < J by simpa only using! bot_lt_iff_ne_bot.mpr h)
    obtain ⟨y', hy'⟩ := hJ y mem_J
    use aI * y'
    constructor
    · apply (nonZeroDivisors R₁).mul_mem haI (mem_nonZeroDivisors_iff_ne_zero.mpr _)
      intro y'_eq_zero
      have : algebraMap R₁ K aJ * y = 0 := by
        rw [← Algebra.smul_def]; rw [← hy']; rw [y'_eq_zero]; rw [map_zero]
      have y_zero :=
        (mul_eq_zero.mp this).resolve_left
          (mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).1 (IsFractionRing.injective _ _) _)
            (mem_nonZeroDivisors_iff_ne_zero.mp haJ))
      apply notMem_zero
      simpa
    intro b hb
    convert! hI _ (hb _ (Submodule.smul_mem _ aJ mem_J)) using 1
    rw [← hy']; rw [mul_comm b]; rw [← Algebra.smul_def]; rw [mul_smul]

/--
theorem `isFractional_div_of_ne_zero` / 定理 `isFractional_div_of_ne_zero`

English:
theorem isFractional_div_of_ne_zero
  given: {I J : FractionalIdeal R₁⁰ K} (h : J != 0)
  proof: I.isFractional.div_of_nonzero J.isFractional fun H =>
h coeToSubmodule_injective H.trans coe_zero.symm

中文:
定理 isFractional_div_of_ne_zero
  条件: {I J : FractionalIdeal R₁⁰ K} (h : J != 0)
  证明: I.isFractional.div_of_nonzero J.isFractional fun H =>
h coeToSubmodule_injective H.trans coe_zero.symm

Depends on / 依赖: H.trans, I.isFractional.div_of_nonzero, J.isFractional, coeToSubmodule_injective, coe_zero, coe_zero.symm, div_of_nonzero, isFractional
-/
theorem isFractional_div_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J != 0) :
    IsFractional R₁⁰ (I / J : Submodule R₁ K) :=
  I.isFractional.div_of_nonzero J.isFractional fun H =>
h coeToSubmodule_injective H.trans coe_zero.symm

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (FractionalIdeal R₁⁰ K)
  body: ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, isFractional_div_of_ne_zero h⟩⟩

中文:
实例 :
  签名: 除法 (FractionalIdeal R₁⁰ K)
  定义体: ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, isFractional_div_of_ne_zero h⟩⟩

Depends on / 依赖: isFractional_div_of_ne_zero
-/
noncomputable instance : Div (FractionalIdeal R₁⁰ K) :=
  ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, isFractional_div_of_ne_zero h⟩⟩

variable {I J : FractionalIdeal R₁⁰ K}

@[simp]
/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: {I : FractionalIdeal R₁⁰ K}
  statement: I / 0 = 0
  proof: dif_pos rfl

中文:
定理 div_zero
  条件: {I : FractionalIdeal R₁⁰ K}
  结论: I / 0 = 0
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
theorem div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 = 0 :=
  dif_pos rfl

/--
theorem `div_of_ne_zero` / 定理 `div_of_ne_zero`

English:
theorem div_of_ne_zero
  given: {I J : FractionalIdeal R₁⁰ K} (h : J != 0)
  proof: dif_neg h

@[simp]

中文:
定理 div_of_ne_zero
  条件: {I J : FractionalIdeal R₁⁰ K} (h : J != 0)
  证明: dif_neg h

@[simp]

Depends on / 依赖: dif_neg
-/
theorem div_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J != 0) :
    I / J = ⟨I / J, isFractional_div_of_ne_zero h⟩ :=
  dif_neg h

@[simp]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: {I J : FractionalIdeal R₁⁰ K} (hJ : J != 0)
  proof: congr_arg _ (dif_neg hJ)

中文:
定理 coe_div
  条件: {I J : FractionalIdeal R₁⁰ K} (hJ : J != 0)
  证明: congr_arg _ (dif_neg hJ)

Depends on / 依赖: congr_arg, dif_neg
-/
theorem coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J != 0) :
    (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K) :=
  congr_arg _ (dif_neg hJ)

/--
theorem `mem_div_iff_of_ne_zero` / 定理 `mem_div_iff_of_ne_zero`

English:
theorem mem_div_iff_of_ne_zero
  given: {I J : FractionalIdeal R₁⁰ K} (h : J != 0) {x}
  proof: by
  rw [div_of_ne_zero h]
  exact Submodule.mem_div_iff_forall_mul_mem

中文:
定理 mem_div_iff_of_ne_zero
  条件: {I J : FractionalIdeal R₁⁰ K} (h : J != 0) {x}
  证明: by
  rw [div_of_ne_zero h]
  exact Submodule.mem_div_iff_forall_mul_mem

Depends on / 依赖: Submodule, Submodule.mem_div_iff_forall_mul_mem, div_of_ne_zero, mem_div_iff_forall_mul_mem
-/
theorem mem_div_iff_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J != 0) {x} :
    x in I / J ↔ forall y in J, x * y in I := by
  rw [div_of_ne_zero h]
  exact Submodule.mem_div_iff_forall_mul_mem

/--
theorem `mul_one_div_le_one` / 定理 `mul_one_div_le_one`

English:
theorem mul_one_div_le_one
  given: {I : FractionalIdeal R₁⁰ K}
  statement: I * (1 / I) <= 1
  proof: by
  by_cases hI : I = 0
  · rw [hI, div_zero, mul_zero]
    exact zero_le 1
  · rw [← coe_le_coe, coe_mul, coe_div hI, coe_one]
    apply Submodule.mul_one_div_le_one

中文:
定理 mul_one_div_le_one
  条件: {I : FractionalIdeal R₁⁰ K}
  结论: I * (1 / I) <= 1
  证明: by
  by_cases hI : I = 0
  · rw [hI, div_zero, mul_zero]
    exact zero_le 1
  · rw [← coe_le_coe, coe_mul, coe_div hI, coe_one]
    apply Submodule.mul_one_div_le_one

Depends on / 依赖: Submodule, Submodule.mul_one_div_le_one, coe_div, coe_le_coe, coe_mul, coe_one, div_zero, mul_one_div_le_one, mul_zero, zero_le
-/
theorem mul_one_div_le_one {I : FractionalIdeal R₁⁰ K} : I * (1 / I) <= 1 := by
  by_cases hI : I = 0
  · rw [hI, div_zero, mul_zero]
    exact zero_le 1
  · rw [← coe_le_coe, coe_mul, coe_div hI, coe_one]
    apply Submodule.mul_one_div_le_one

/--
theorem `le_self_mul_one_div` / 定理 `le_self_mul_one_div`

English:
theorem le_self_mul_one_div
  given: {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K))
  proof: by
  by_cases hI_nz : I = 0
  · rw [hI_nz, div_zero, mul_zero]
  · rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
    rw [← coe_le_coe]; rw [coe_one] at hI
    exact Submodule.le_self_mul_one_div hI

中文:
定理 le_self_mul_one_div
  条件: {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K))
  证明: by
  by_cases hI_nz : I = 0
  · rw [hI_nz, div_zero, mul_zero]
  · rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
    rw [← coe_le_coe]; rw [coe_one] at hI
    exact Submodule.le_self_mul_one_div hI

Depends on / 依赖: Submodule, Submodule.le_self_mul_one_div, coe_div, coe_le_coe, coe_mul, coe_one, div_zero, hI_nz, le_self_mul_one_div, mul_zero
-/
theorem le_self_mul_one_div {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K)) :
    I <= I * (1 / I) := by
  by_cases hI_nz : I = 0
  · rw [hI_nz, div_zero, mul_zero]
  · rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
    rw [← coe_le_coe]; rw [coe_one] at hI
    exact Submodule.le_self_mul_one_div hI

/--
theorem `le_div_iff_of_ne_zero` / 定理 `le_div_iff_of_ne_zero`

English:
theorem le_div_iff_of_ne_zero
  given: {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0)
  proof: ⟨fun h _ hx => (mem_div_iff_of_ne_zero hJ').mp (h hx), fun h x hx =>
    (mem_div_iff_of_ne_zero hJ').mpr (h x hx)⟩

中文:
定理 le_div_iff_of_ne_zero
  条件: {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0)
  证明: ⟨fun h _ hx => (mem_div_iff_of_ne_zero hJ').mp (h hx), fun h x hx =>
    (mem_div_iff_of_ne_zero hJ').mpr (h x hx)⟩

Depends on / 依赖: mem_div_iff_of_ne_zero
-/
theorem le_div_iff_of_ne_zero {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0) :
    I <= J / J' ↔ forall x in I, forall y in J', x * y in J :=
  ⟨fun h _ hx => (mem_div_iff_of_ne_zero hJ').mp (h hx), fun h x hx =>
    (mem_div_iff_of_ne_zero hJ').mpr (h x hx)⟩

/--
theorem `le_div_iff_mul_le` / 定理 `le_div_iff_mul_le`

English:
theorem le_div_iff_mul_le
  given: {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0)
  proof: by
  rw [div_of_ne_zero hJ']; rw [← coe_le_coe (I := I * J') (J := J)]; rw [coe_mul]
  exact Submodule.le_div_iff_mul_le

@[simp]

中文:
定理 le_div_iff_mul_le
  条件: {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0)
  证明: by
  rw [div_of_ne_zero hJ']; rw [← coe_le_coe (I := I * J') (J := J)]; rw [coe_mul]
  exact Submodule.le_div_iff_mul_le

@[simp]

Depends on / 依赖: Submodule, Submodule.le_div_iff_mul_le, coe_le_coe, coe_mul, div_of_ne_zero, le_div_iff_mul_le
-/
theorem le_div_iff_mul_le {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0) :
    I <= J / J' ↔ I * J' <= J := by
  rw [div_of_ne_zero hJ']; rw [← coe_le_coe (I := I * J') (J := J)]; rw [coe_mul]
  exact Submodule.le_div_iff_mul_le

@[simp]
/--
theorem `div_one` / 定理 `div_one`

English:
theorem div_one
  given: {I : FractionalIdeal R₁⁰ K}
  statement: I / 1 = I
  proof: by
  rw [div_of_ne_zero (one_ne_zero' (FractionalIdeal R₁⁰ K))]
  ext
  constructor <;> intro h
  · simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
  · apply mem_div_iff_forall_mul_mem.mpr
    rintro y ⟨y', _, rfl⟩
    convert! Submodule.smul_mem _ y' h 

中文:
定理 div_one
  条件: {I : FractionalIdeal R₁⁰ K}
  结论: I / 1 = I
  证明: by
  rw [div_of_ne_zero (one_ne_zero' (FractionalIdeal R₁⁰ K))]
  ext
  constructor <;> intro h
  · simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
  · apply mem_div_iff_forall_mul_mem.mpr
    rintro y ⟨y', _, rfl⟩
    convert! Submodule.smul_mem _ y' h 

Depends on / 依赖: Algebra, Algebra.linearMap_apply, Algebra.smul_def, FractionalIdeal, Submodule, Submodule.smul_mem, algebraMap, coe_mem_one, convert, div_of_ne_zero, linearMap_apply, map_one, mem_div_iff_forall_mul_mem, mem_div_iff_forall_mul_mem.mp, mem_div_iff_forall_mul_mem.mpr, mul_comm, one_ne_zero, smul_def, smul_mem
-/
theorem div_one {I : FractionalIdeal R₁⁰ K} : I / 1 = I := by
  rw [div_of_ne_zero (one_ne_zero' (FractionalIdeal R₁⁰ K))]
  ext
  constructor <;> intro h
  · simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
  · apply mem_div_iff_forall_mul_mem.mpr
    rintro y ⟨y', _, rfl⟩
    convert! Submodule.smul_mem _ y' h using 1
    rw [mul_comm]; rw [Algebra.linearMap_apply]; rw [← Algebra.smul_def]

/--
theorem `eq_one_div_of_mul_eq_one_right` / 定理 `eq_one_div_of_mul_eq_one_right`

English:
theorem eq_one_div_of_mul_eq_one_right
  given: (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1)
  proof: by
  have hI : I != 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1 from
congr_arg Units.inv @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_ne_zero h

中文:
定理 eq_one_div_of_mul_eq_one_right
  条件: (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1)
  证明: by
  have hI : I != 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1 from
congr_arg Units.inv @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_ne_zero h

Depends on / 依赖: Units.ext, Units.inv, Units.mkOfMulEqOne, congr_arg, le_antisymm, le_div_iff_of_ne_zero, mem_div_iff_of_ne_zero, mkOfMulEqOne, mul_comm, mul_le, mul_le.mpr, mul_mem_mul, ne_zero_of_mul_eq_one
-/
theorem eq_one_div_of_mul_eq_one_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) :
    J = 1 / I := by
  have hI : I != 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1 from
congr_arg Units.inv @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_ne_zero hI).mp hy x hx
  rw [← h]
  gcongr
  apply (le_div_iff_of_ne_zero hI).mpr _
  intro y hy x hx
  rw [mul_comm]
  exact mul_mem_mul hy hx

/--
theorem `mul_div_self_cancel_iff` / 定理 `mul_div_self_cancel_iff`

English:
theorem mul_div_self_cancel_iff
  given: {I : FractionalIdeal R₁⁰ K}
  statement: I * (1 / I) = 1 ↔ exists J, I * J = 1
  proof: ⟨fun h => ⟨1 / I, h⟩, fun ⟨J, hJ⟩ => by rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩

中文:
定理 mul_div_self_cancel_iff
  条件: {I : FractionalIdeal R₁⁰ K}
  结论: I * (1 / I) = 1 ↔ 存在 J, I * J = 1
  证明: ⟨fun h => ⟨1 / I, h⟩, fun ⟨J, hJ⟩ => by rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩

Depends on / 依赖: eq_one_div_of_mul_eq_one_right
-/
theorem mul_div_self_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * (1 / I) = 1 ↔ exists J, I * J = 1 :=
  ⟨fun h => ⟨1 / I, h⟩, fun ⟨J, hJ⟩ => by rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  given: (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K')
  proof: by
  by_cases H : J = 0
  · rw [H, div_zero, FractionalIdeal.map_zero, div_zero]
  · simp [← coeToSubmodule_inj, div_of_ne_zero H, div_of_ne_zero (map_ne_zero _ H)]

中文:
定理 map_div
  条件: (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K')
  证明: by
  by_cases H : J = 0
  · rw [H, div_zero, FractionalIdeal.map_zero, div_zero]
  · simp [← coeToSubmodule_inj, div_of_ne_zero H, div_of_ne_zero (map_ne_zero _ H)]
-/
protected theorem map_div (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (I / J).map (h : K ->ₐ[R₁] K') = I.map h / J.map h := by
  by_cases H : J = 0
  · rw [H, div_zero, FractionalIdeal.map_zero, div_zero]
  · simp [← coeToSubmodule_inj, div_of_ne_zero H, div_of_ne_zero (map_ne_zero _ H)]

/--
theorem `map_one_div` / 定理 `map_one_div`

English:
theorem map_one_div
  given: (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K')
  proof: by
  rw [FractionalIdeal.map_div]; rw [FractionalIdeal.map_one]

中文:
定理 map_one_div
  条件: (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K')
  证明: by
  rw [FractionalIdeal.map_div]; rw [FractionalIdeal.map_one]

Depends on / 依赖: FractionalIdeal, FractionalIdeal.map_div, FractionalIdeal.map_one, map_div, map_one
-/
theorem map_one_div (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (1 / I).map (h : K ->ₐ[R₁] K') = 1 / I.map h := by
  rw [FractionalIdeal.map_div]; rw [FractionalIdeal.map_one]

end Quotient

section Field

variable {R₁ K L : Type*} [CommRing R₁] [Field K] [Field L]
variable [Algebra R₁ K] [IsFractionRing R₁ K] [Algebra K L] [IsFractionRing K L]

/--
theorem `eq_zero_or_one` / 定理 `eq_zero_or_one`

English:
theorem eq_zero_or_one
  given: (I : FractionalIdeal K⁰ L)
  statement: I = 0 ∨ I = 1
  proof: by
  rw [or_iff_not_imp_left]
  intro hI
  simp_rw [@SetLike.ext_iff _ _ _ I 1, mem_one_iff]
  intro x
  constructor
  · intro x_mem
    obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq K⁰ x
    refine ⟨n / d, ?_⟩
    rw [map_div₀]; rw [IsFractionRing.mk'_eq_div]
  · rintro ⟨x, rfl⟩
    obtain ⟨y,

中文:
定理 eq_zero_or_one
  条件: (I : FractionalIdeal K⁰ L)
  结论: I = 0 ∨ I = 1
  证明: by
  rw [or_iff_not_imp_left]
  intro hI
  simp_rw [@SetLike.ext_iff _ _ _ I 1, mem_one_iff]
  intro x
  constructor
  · intro x_mem
    obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq K⁰ x
    refine ⟨n / d, ?_⟩
    rw [map_div₀]; rw [IsFractionRing.mk'_eq_div]
  · rintro ⟨x, rfl⟩
    obtain ⟨y,

Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.mk, IsLocalization, IsLocalization.exists_mk, SetLike, SetLike.ext_iff, _eq_div, exists_mk, exists_ne_zero_mem_isInteger, ext_iff, map_mul, mem_one_iff, or_iff_not_imp_left, simp_rw, smul_def, smul_mem, x_mem, y_mem
-/
theorem eq_zero_or_one (I : FractionalIdeal K⁰ L) : I = 0 ∨ I = 1 := by
  rw [or_iff_not_imp_left]
  intro hI
  simp_rw [@SetLike.ext_iff _ _ _ I 1, mem_one_iff]
  intro x
  constructor
  · intro x_mem
    obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq K⁰ x
    refine ⟨n / d, ?_⟩
    rw [map_div₀]; rw [IsFractionRing.mk'_eq_div]
  · rintro ⟨x, rfl⟩
    obtain ⟨y, y_ne, y_mem⟩ := exists_ne_zero_mem_isInteger hI
    rw [← div_mul_cancel₀ x y_ne]; rw [map_mul]; rw [← Algebra.smul_def]
    exact smul_mem (M := L) I (x / y) y_mem

/--
theorem `eq_zero_or_one_of_isField` / 定理 `eq_zero_or_one_of_isField`

English:
theorem eq_zero_or_one_of_isField
  given: (hF : IsField R₁) (I : FractionalIdeal R₁⁰ K)
  statement: I = 0 ∨ I = 1
  proof: letI : Field R₁ := hF.toField
  eq_zero_or_one I

中文:
定理 eq_zero_or_one_of_isField
  条件: (hF : 是域 R₁) (I : FractionalIdeal R₁⁰ K)
  结论: I = 0 ∨ I = 1
  证明: letI : Field R₁ := hF.toField
  eq_zero_or_one I

Depends on / 依赖: eq_zero_or_one, hF.toField, toField
-/
theorem eq_zero_or_one_of_isField (hF : IsField R₁) (I : FractionalIdeal R₁⁰ K) : I = 0 ∨ I = 1 :=
  letI : Field R₁ := hF.toField
  eq_zero_or_one I

end Field

section PrincipalIdeal

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]
variable [Algebra R₁ K] [IsFractionRing R₁ K]

variable (R₁)

-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
/--
Definition of `spanFinset` / `spanFinset` 的定义

English:
definition spanFinset
  signature: {ι : Type*} (s : Finset ι) (f : ι -> K)
  body: ⟨Submodule.span R₁ (f '' s), by
    obtain ⟨a', ha'⟩ := IsLocalization.exist_integer_multiples R₁⁰ s f
    refine ⟨a', a'.2, fun x hx => Submodule.span_induction ?_ ?_ ?_ ?_ hx⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ha' i hi
    · rw [smul_zero]
      exact IsLocalization.isInteger_zero
    · intr

中文:
定义 spanFinset
  签名: {ι : 类型} (s : 有限集 ι) (f : ι -> K)
  定义体: ⟨Submodule.span R₁ (f '' s), by
    obtain ⟨a', ha'⟩ := IsLocalization.exist_integer_multiples R₁⁰ s f
    refine ⟨a', a'.2, fun x hx => Submodule.span_induction ?_ ?_ ?_ ?_ hx⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ha' i hi
    · rw [smul_zero]
      exact IsLocalization.isInteger_zero
    · intr

Depends on / 依赖: IsLocalization, IsLocalization.exist_integer_multiples, IsLocalization.isInteger_add, IsLocalization.isInteger_smul, IsLocalization.isInteger_zero, Submodule, Submodule.span, Submodule.span_induction, exist_integer_multiples, isInteger_add, isInteger_smul, isInteger_zero, smul_add, smul_comm, smul_zero, span_induction
-/
def spanFinset {ι : Type*} (s : Finset ι) (f : ι -> K) : FractionalIdeal R₁⁰ K :=
  ⟨Submodule.span R₁ (f '' s), by
    obtain ⟨a', ha'⟩ := IsLocalization.exist_integer_multiples R₁⁰ s f
    refine ⟨a', a'.2, fun x hx => Submodule.span_induction ?_ ?_ ?_ ?_ hx⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ha' i hi
    · rw [smul_zero]
      exact IsLocalization.isInteger_zero
    · intro x y _ _ hx hy
      rw [smul_add]
      exact IsLocalization.isInteger_add hx hy
    · intro c x _ hx
      rw [smul_comm]
      exact IsLocalization.isInteger_smul hx⟩

/--
lemma `spanFinset_coe` / 引理 `spanFinset_coe`

English:
lemma spanFinset_coe
  given: {ι : Type*} (s : Finset ι) (f : ι -> K)
  proof: rfl

中文:
引理 spanFinset_coe
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> K)
  证明: rfl
-/
@[simp] lemma spanFinset_coe {ι : Type*} (s : Finset ι) (f : ι -> K) :
    (spanFinset R₁ s f : Submodule R₁ K) = Submodule.span R₁ (f '' s) :=
  rfl

variable {R₁}

@[simp]
/--
theorem `spanFinset_eq_zero` / 定理 `spanFinset_eq_zero`

English:
theorem spanFinset_eq_zero
  given: {ι : Type*} {s : Finset ι} {f : ι -> K}
  proof: by
  simp only [← coeToSubmodule_inj, spanFinset_coe, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

中文:
定理 spanFinset_eq_zero
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> K}
  证明: by
  simp only [← coeToSubmodule_inj, spanFinset_coe, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

Depends on / 依赖: Finset, Finset.mem_coe, Set.mem_image, Submodule, Submodule.span_eq_bot, and_imp, coeToSubmodule_inj, coe_zero, forall_exists_index, mem_coe, mem_image, spanFinset_coe, span_eq_bot
-/
theorem spanFinset_eq_zero {ι : Type*} {s : Finset ι} {f : ι -> K} :
    spanFinset R₁ s f = 0 ↔ forall j in s, f j = 0 := by
  simp only [← coeToSubmodule_inj, spanFinset_coe, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/--
theorem `spanFinset_ne_zero` / 定理 `spanFinset_ne_zero`

English:
theorem spanFinset_ne_zero
  given: {ι : Type*} {s : Finset ι} {f : ι -> K}
  proof: by simp

中文:
定理 spanFinset_ne_zero
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> K}
  证明: by simp
-/
theorem spanFinset_ne_zero {ι : Type*} {s : Finset ι} {f : ι -> K} :
    spanFinset R₁ s f != 0 ↔ exists j in s, f j != 0 := by simp

open Submodule.IsPrincipal

variable [IsLocalization S P]

/--
theorem `isFractional_span_singleton` / 定理 `isFractional_span_singleton`

English:
theorem isFractional_span_singleton
  given: (x : P)
  statement: IsFractional S (span R {x} : Submodule R P)
  proof: let ⟨a, ha⟩ := exists_integer_multiple S x
  isFractional_span_iff.mpr ⟨a, a.2, fun _ hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩

中文:
定理 isFractional_span_singleton
  条件: (x : P)
  结论: IsFractional S (span R {x} : 子模 R P)
  证明: let ⟨a, ha⟩ := exists_integer_multiple S x
  isFractional_span_iff.mpr ⟨a, a.2, fun _ hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩

Depends on / 依赖: Set.mem_singleton_iff.mp, exists_integer_multiple, isFractional_span_iff, isFractional_span_iff.mpr, mem_singleton_iff
-/
theorem isFractional_span_singleton (x : P) : IsFractional S (span R {x} : Submodule R P) :=
  let ⟨a, ha⟩ := exists_integer_multiple S x
  isFractional_span_iff.mpr ⟨a, a.2, fun _ hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩

variable (S)

/-- `spanSingleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
irreducible_def spanSingleton (x : P) : FractionalIdeal S P :=
  ⟨span R {x}, isFractional_span_singleton x⟩

-- local attribute [semireducible] span_singleton
@[simp]
/--
theorem `coe_spanSingleton` / 定理 `coe_spanSingleton`

English:
theorem coe_spanSingleton
  given: (x : P)
  statement: (spanSingleton S x : Submodule R P) = span R {x}
  proof: by
  rw [spanSingleton]
  rfl

@[simp]

中文:
定理 coe_spanSingleton
  条件: (x : P)
  结论: (spanSingleton S x : 子模 R P) = span R {x}
  证明: by
  rw [spanSingleton]
  rfl

@[simp]

Depends on / 依赖: spanSingleton
-/
theorem coe_spanSingleton (x : P) : (spanSingleton S x : Submodule R P) = span R {x} := by
  rw [spanSingleton]
  rfl

@[simp]
/--
theorem `mem_spanSingleton` / 定理 `mem_spanSingleton`

English:
theorem mem_spanSingleton
  given: {x y : P}
  statement: x in spanSingleton S y ↔ exists z : R, z • y = x
  proof: by
  rw [spanSingleton]
  exact Submodule.mem_span_singleton

中文:
定理 mem_spanSingleton
  条件: {x y : P}
  结论: x in spanSingleton S y ↔ 存在 z : R, z • y = x
  证明: by
  rw [spanSingleton]
  exact Submodule.mem_span_singleton

Depends on / 依赖: Submodule, Submodule.mem_span_singleton, mem_span_singleton, spanSingleton
-/
theorem mem_spanSingleton {x y : P} : x in spanSingleton S y ↔ exists z : R, z • y = x := by
  rw [spanSingleton]
  exact Submodule.mem_span_singleton

/--
theorem `mem_spanSingleton_self` / 定理 `mem_spanSingleton_self`

English:
theorem mem_spanSingleton_self
  given: (x : P)
  statement: x in spanSingleton S x
  proof: (mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩

中文:
定理 mem_spanSingleton_self
  条件: (x : P)
  结论: x in spanSingleton S x
  证明: (mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩

Depends on / 依赖: mem_spanSingleton, one_smul
-/
theorem mem_spanSingleton_self (x : P) : x in spanSingleton S x :=
  (mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩

set_option backward.isDefEq.respectTransparency false in
variable (P) in
/--
theorem `den_mul_self_eq_num'` / 定理 `den_mul_self_eq_num'`

English:
theorem den_mul_self_eq_num'
  given: (I : FractionalIdeal S P)
  proof: by
  apply coeToSubmodule_injective
  dsimp only
  rw [coe_mul]; rw [← smul_eq_mul]; rw [coe_spanSingleton]; rw [smul_eq_mul]; rw [Submodule.span_singleton_mul]
  convert! I.den_mul_self_eq_num using 1
  ext
  rw [mem_smul_pointwise_iff_exists]; rw [mem_smul_pointwise_iff_exists]
  simp [smul_eq_mul

中文:
定理 den_mul_self_eq_num'
  条件: (I : FractionalIdeal S P)
  证明: by
  apply coeToSubmodule_injective
  dsimp only
  rw [coe_mul]; rw [← smul_eq_mul]; rw [coe_spanSingleton]; rw [smul_eq_mul]; rw [Submodule.span_singleton_mul]
  convert! I.den_mul_self_eq_num using 1
  ext
  rw [mem_smul_pointwise_iff_exists]; rw [mem_smul_pointwise_iff_exists]
  simp [smul_eq_mul

Depends on / 依赖: Algebra, Algebra.smul_def, I.den_mul_self_eq_num, Submodule, Submodule.span_singleton_mul, Submonoid, Submonoid.smul_def, coeToSubmodule_injective, coe_mul, coe_spanSingleton, convert, den_mul_self_eq_num, mem_smul_pointwise_iff_exists, smul_def, smul_eq_mul, span_singleton_mul
-/
theorem den_mul_self_eq_num' (I : FractionalIdeal S P) :
    spanSingleton S (algebraMap R P I.den) * I = I.num := by
  apply coeToSubmodule_injective
  dsimp only
  rw [coe_mul]; rw [← smul_eq_mul]; rw [coe_spanSingleton]; rw [smul_eq_mul]; rw [Submodule.span_singleton_mul]
  convert! I.den_mul_self_eq_num using 1
  ext
  rw [mem_smul_pointwise_iff_exists]; rw [mem_smul_pointwise_iff_exists]
  simp [smul_eq_mul, Algebra.smul_def, Submonoid.smul_def]

variable {S}

@[simp]
/--
theorem `spanSingleton_le_iff_mem` / 定理 `spanSingleton_le_iff_mem`

English:
theorem spanSingleton_le_iff_mem
  given: {x : P} {I : FractionalIdeal S P}
  proof: by
  rw [← coe_le_coe]; rw [coe_spanSingleton]; rw [Submodule.span_singleton_le_iff_mem]; rw [mem_coe]

中文:
定理 spanSingleton_le_iff_mem
  条件: {x : P} {I : FractionalIdeal S P}
  证明: by
  rw [← coe_le_coe]; rw [coe_spanSingleton]; rw [Submodule.span_singleton_le_iff_mem]; rw [mem_coe]

Depends on / 依赖: Submodule, Submodule.span_singleton_le_iff_mem, coe_le_coe, coe_spanSingleton, mem_coe, span_singleton_le_iff_mem
-/
theorem spanSingleton_le_iff_mem {x : P} {I : FractionalIdeal S P} :
    spanSingleton S x <= I ↔ x in I := by
  rw [← coe_le_coe]; rw [coe_spanSingleton]; rw [Submodule.span_singleton_le_iff_mem]; rw [mem_coe]

/--
theorem `spanSingleton_eq_spanSingleton` / 定理 `spanSingleton_eq_spanSingleton`

English:
theorem spanSingleton_eq_spanSingleton
  given: [IsDomain R] [Module.IsTorsionFree R P] {x y : P}
  proof: by
  rw [← Submodule.span_singleton_eq_span_singleton]; rw [spanSingleton]; rw [spanSingleton]
  exact Subtype.mk_eq_mk

中文:
定理 spanSingleton_eq_spanSingleton
  条件: [是整环 R] [模.是无挠 R P] {x y : P}
  证明: by
  rw [← Submodule.span_singleton_eq_span_singleton]; rw [spanSingleton]; rw [spanSingleton]
  exact Subtype.mk_eq_mk

Depends on / 依赖: Submodule, Submodule.span_singleton_eq_span_singleton, Subtype, Subtype.mk_eq_mk, mk_eq_mk, spanSingleton, span_singleton_eq_span_singleton
-/
theorem spanSingleton_eq_spanSingleton [IsDomain R] [Module.IsTorsionFree R P] {x y : P} :
    spanSingleton S x = spanSingleton S y ↔ exists z : Rˣ, z • x = y := by
  rw [← Submodule.span_singleton_eq_span_singleton]; rw [spanSingleton]; rw [spanSingleton]
  exact Subtype.mk_eq_mk

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_spanSingleton_of_principal` / 定理 `eq_spanSingleton_of_principal`

English:
theorem eq_spanSingleton_of_principal
  given: (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)]
  proof: by
  -- Porting note: this used to be `coeToSubmodule_injective (span_singleton_generator ↑I).symm`
  -- but Lean 4 struggled to unify everything. Turned it into an explicit `rw`.
  rw [spanSingleton]; rw [← coeToSubmodule_inj]; rw [coe_mk]; rw [span_singleton_generator]

中文:
定理 eq_spanSingleton_of_principal
  条件: (I : FractionalIdeal S P) [是Principal (I : 子模 R P)]
  证明: by
  -- Porting note: this used to be `coeToSubmodule_injective (span_singleton_generator ↑I).symm`
  -- but Lean 4 struggled to unify everything. Turned it into an explicit `rw`.
  rw [spanSingleton]; rw [← coeToSubmodule_inj]; rw [coe_mk]; rw [span_singleton_generator]
-/
theorem eq_spanSingleton_of_principal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] :
    I = spanSingleton S (generator (I : Submodule R P)) := by
  -- Porting note: this used to be `coeToSubmodule_injective (span_singleton_generator ↑I).symm`
  -- but Lean 4 struggled to unify everything. Turned it into an explicit `rw`.
  rw [spanSingleton]; rw [← coeToSubmodule_inj]; rw [coe_mk]; rw [span_singleton_generator]

/--
theorem `isPrincipal_iff` / 定理 `isPrincipal_iff`

English:
theorem isPrincipal_iff
  given: (I : FractionalIdeal S P)
  proof: ⟨fun _ => ⟨generator (I : Submodule R P), eq_spanSingleton_of_principal I⟩,
    fun ⟨x, hx⟩ => { principal := ⟨x, Eq.trans (congr_arg _ hx) (coe_spanSingleton _ x)⟩ }⟩

@[simp]

中文:
定理 isPrincipal_iff
  条件: (I : FractionalIdeal S P)
  证明: ⟨fun _ => ⟨generator (I : Submodule R P), eq_spanSingleton_of_principal I⟩,
    fun ⟨x, hx⟩ => { principal := ⟨x, Eq.trans (congr_arg _ hx) (coe_spanSingleton _ x)⟩ }⟩

@[simp]

Depends on / 依赖: Eq.trans, Submodule, coe_spanSingleton, congr_arg, eq_spanSingleton_of_principal, generator, principal
-/
theorem isPrincipal_iff (I : FractionalIdeal S P) :
    IsPrincipal (I : Submodule R P) ↔ exists x, I = spanSingleton S x :=
  ⟨fun _ => ⟨generator (I : Submodule R P), eq_spanSingleton_of_principal I⟩,
    fun ⟨x, hx⟩ => { principal := ⟨x, Eq.trans (congr_arg _ hx) (coe_spanSingleton _ x)⟩ }⟩

@[simp]
/--
theorem `spanSingleton_zero` / 定理 `spanSingleton_zero`

English:
theorem spanSingleton_zero
  statement: spanSingleton S (0 : P) = 0
  proof: by
  ext
  simp [eq_comm]

中文:
定理 spanSingleton_zero
  结论: spanSingleton S (0 : P) = 0
  证明: by
  ext
  simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem spanSingleton_zero : spanSingleton S (0 : P) = 0 := by
  ext
  simp [eq_comm]

/--
theorem `spanSingleton_eq_zero_iff` / 定理 `spanSingleton_eq_zero_iff`

English:
theorem spanSingleton_eq_zero_iff
  given: {y : P}
  statement: spanSingleton S y = 0 ↔ y = 0
  proof: ⟨fun h =>
    span_eq_bot.mp (by simpa using congr_arg Subtype.val h : span R {y} = ⊥) y (mem_singleton y),
    fun h => by simp [h]⟩

中文:
定理 spanSingleton_eq_zero_iff
  条件: {y : P}
  结论: spanSingleton S y = 0 ↔ y = 0
  证明: ⟨fun h =>
    span_eq_bot.mp (by simpa using congr_arg Subtype.val h : span R {y} = ⊥) y (mem_singleton y),
    fun h => by simp [h]⟩

Depends on / 依赖: Subtype, Subtype.val, congr_arg, mem_singleton, span_eq_bot, span_eq_bot.mp
-/
theorem spanSingleton_eq_zero_iff {y : P} : spanSingleton S y = 0 ↔ y = 0 :=
  ⟨fun h =>
    span_eq_bot.mp (by simpa using congr_arg Subtype.val h : span R {y} = ⊥) y (mem_singleton y),
    fun h => by simp [h]⟩

/--
theorem `spanSingleton_ne_zero_iff` / 定理 `spanSingleton_ne_zero_iff`

English:
theorem spanSingleton_ne_zero_iff
  given: {y : P}
  statement: spanSingleton S y != 0 ↔ y != 0
  proof: not_congr spanSingleton_eq_zero_iff

@[simp]

中文:
定理 spanSingleton_ne_zero_iff
  条件: {y : P}
  结论: spanSingleton S y != 0 ↔ y != 0
  证明: not_congr spanSingleton_eq_zero_iff

@[simp]

Depends on / 依赖: not_congr, spanSingleton_eq_zero_iff
-/
theorem spanSingleton_ne_zero_iff {y : P} : spanSingleton S y != 0 ↔ y != 0 :=
  not_congr spanSingleton_eq_zero_iff

@[simp]
/--
theorem `spanSingleton_one` / 定理 `spanSingleton_one`

English:
theorem spanSingleton_one
  statement: spanSingleton S (1 : P) = 1
  proof: by
  ext
  refine (mem_spanSingleton S).trans ((exists_congr ?_).trans (mem_one_iff S).symm)
  intro x'
  rw [Algebra.smul_def]; rw [mul_one]

@[simp]

中文:
定理 spanSingleton_one
  结论: spanSingleton S (1 : P) = 1
  证明: by
  ext
  refine (mem_spanSingleton S).trans ((exists_congr ?_).trans (mem_one_iff S).symm)
  intro x'
  rw [Algebra.smul_def]; rw [mul_one]

@[simp]

Depends on / 依赖: Algebra, Algebra.smul_def, exists_congr, mem_one_iff, mem_spanSingleton, mul_one, smul_def
-/
theorem spanSingleton_one : spanSingleton S (1 : P) = 1 := by
  ext
  refine (mem_spanSingleton S).trans ((exists_congr ?_).trans (mem_one_iff S).symm)
  intro x'
  rw [Algebra.smul_def]; rw [mul_one]

@[simp]
/--
theorem `spanSingleton_mul_spanSingleton` / 定理 `spanSingleton_mul_spanSingleton`

English:
theorem spanSingleton_mul_spanSingleton
  given: (x y : P)
  proof: by
  apply coeToSubmodule_injective
  simp only [coe_mul, coe_spanSingleton, span_mul_span, singleton_mul_singleton]

@[simp]

中文:
定理 spanSingleton_mul_spanSingleton
  条件: (x y : P)
  证明: by
  apply coeToSubmodule_injective
  simp only [coe_mul, coe_spanSingleton, span_mul_span, singleton_mul_singleton]

@[simp]

Depends on / 依赖: coeToSubmodule_injective, coe_mul, coe_spanSingleton, singleton_mul_singleton, span_mul_span
-/
theorem spanSingleton_mul_spanSingleton (x y : P) :
    spanSingleton S x * spanSingleton S y = spanSingleton S (x * y) := by
  apply coeToSubmodule_injective
  simp only [coe_mul, coe_spanSingleton, span_mul_span, singleton_mul_singleton]

@[simp]
/--
theorem `spanSingleton_pow` / 定理 `spanSingleton_pow`

English:
theorem spanSingleton_pow
  given: (x : P) (n : Nat)
  statement: spanSingleton S x ^ n = spanSingleton S (x ^ n)
  proof: by
  induction n with
  | zero => rw [pow_zero, pow_zero, spanSingleton_one]
  | succ n hn => rw [pow_succ, hn, spanSingleton_mul_spanSingleton, pow_succ]

@[simp]

中文:
定理 spanSingleton_pow
  条件: (x : P) (n : 自然数)
  结论: spanSingleton S x ^ n = spanSingleton S (x ^ n)
  证明: by
  induction n with
  | zero => rw [pow_zero, pow_zero, spanSingleton_one]
  | succ n hn => rw [pow_succ, hn, spanSingleton_mul_spanSingleton, pow_succ]

@[simp]

Depends on / 依赖: pow_succ, pow_zero, spanSingleton_mul_spanSingleton, spanSingleton_one
-/
theorem spanSingleton_pow (x : P) (n : Nat) : spanSingleton S x ^ n = spanSingleton S (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, spanSingleton_one]
  | succ n hn => rw [pow_succ, hn, spanSingleton_mul_spanSingleton, pow_succ]

@[simp]
/--
theorem `coeIdeal_span_singleton` / 定理 `coeIdeal_span_singleton`

English:
theorem coeIdeal_span_singleton
  given: (x : R)
  proof: by
  ext y
  refine (mem_coeIdeal S).trans (Iff.trans ?_ (mem_spanSingleton S).symm)
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    use x'
    rw [smul_eq_mul]; rw [map_mul]; rw [Algebra.smul_def]
  · rintro ⟨y', rfl⟩
    refine ⟨y' * x, Submo

中文:
定理 coeIdeal_span_singleton
  条件: (x : R)
  证明: by
  ext y
  refine (mem_coeIdeal S).trans (Iff.trans ?_ (mem_spanSingleton S).symm)
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    use x'
    rw [smul_eq_mul]; rw [map_mul]; rw [Algebra.smul_def]
  · rintro ⟨y', rfl⟩
    refine ⟨y' * x, Submo

Depends on / 依赖: Algebra, Algebra.smul_def, Iff.trans, Submodule, Submodule.mem_span_singleton.mp, Submodule.mem_span_singleton.mpr, map_mul, mem_coeIdeal, mem_spanSingleton, mem_span_singleton, smul_def, smul_eq_mul
-/
theorem coeIdeal_span_singleton (x : R) :
    (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebraMap R P x) := by
  ext y
  refine (mem_coeIdeal S).trans (Iff.trans ?_ (mem_spanSingleton S).symm)
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    use x'
    rw [smul_eq_mul]; rw [map_mul]; rw [Algebra.smul_def]
  · rintro ⟨y', rfl⟩
    refine ⟨y' * x, Submodule.mem_span_singleton.mpr ⟨y', rfl⟩, ?_⟩
    rw [map_mul]; rw [Algebra.smul_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `canonicalEquiv_spanSingleton` / 定理 `canonicalEquiv_spanSingleton`

English:
theorem canonicalEquiv_spanSingleton
  statement: {P'} [CommRing P'] [Algebra R P'] [IsLocalization S P']
  proof: by
  apply SetLike.ext_iff.mpr
  intro y
  constructor <;> intro h
  · rw [mem_spanSingleton]
    obtain ⟨x', hx', rfl⟩ := (mem_canonicalEquiv_apply _ _ _).mp h
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp hx'
    use z
    rw [IsLocalization.map_smul]; rw [RingHom.id_apply]
  · rw [mem_canonical

中文:
定理 canonicalEquiv_spanSingleton
  结论: {P'} [交换环 P'] [代数 R P'] [是Localization S P']
  证明: by
  apply SetLike.ext_iff.mpr
  intro y
  constructor <;> intro h
  · rw [mem_spanSingleton]
    obtain ⟨x', hx', rfl⟩ := (mem_canonicalEquiv_apply _ _ _).mp h
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp hx'
    use z
    rw [IsLocalization.map_smul]; rw [RingHom.id_apply]
  · rw [mem_canonical

Depends on / 依赖: IsLocalization, IsLocalization.map_smul, RingHom, RingHom.id_apply, SetLike, SetLike.ext_iff.mpr, ext_iff, id_apply, map_smul, mem_canonicalEquiv_apply, mem_spanSingleton
-/
theorem canonicalEquiv_spanSingleton {P'} [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (x : P) :
    canonicalEquiv S P P' (spanSingleton S x) =
      spanSingleton S
        (IsLocalization.map P' (RingHom.id R)
          (fun y (hy : y in S) => show RingHom.id R y in S from hy) x) := by
  apply SetLike.ext_iff.mpr
  intro y
  constructor <;> intro h
  · rw [mem_spanSingleton]
    obtain ⟨x', hx', rfl⟩ := (mem_canonicalEquiv_apply _ _ _).mp h
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp hx'
    use z
    rw [IsLocalization.map_smul]; rw [RingHom.id_apply]
  · rw [mem_canonicalEquiv_apply]
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp h
    use z • x
    use (mem_spanSingleton _).mpr ⟨z, rfl⟩
    simp [IsLocalization.map_smul]

/--
theorem `mem_singleton_mul` / 定理 `mem_singleton_mul`

English:
theorem mem_singleton_mul
  given: {x y : P} {I : FractionalIdeal S P}
  proof: by
  constructor
  · intro h
    refine FractionalIdeal.mul_induction_on h ?_ ?_
    · intro x' hx' y' hy'
      obtain ⟨a, ha⟩ := (mem_spanSingleton S).mp hx'
      use a • y', Submodule.smul_mem (I : Submodule R P) a hy'
      rw [← ha]; rw [Algebra.mul_smul_comm]; rw [Algebra.smul_mul_assoc]
    

中文:
定理 mem_singleton_mul
  条件: {x y : P} {I : FractionalIdeal S P}
  证明: by
  constructor
  · intro h
    refine FractionalIdeal.mul_induction_on h ?_ ?_
    · intro x' hx' y' hy'
      obtain ⟨a, ha⟩ := (mem_spanSingleton S).mp hx'
      use a • y', Submodule.smul_mem (I : Submodule R P) a hy'
      rw [← ha]; rw [Algebra.mul_smul_comm]; rw [Algebra.smul_mul_assoc]
    

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, FractionalIdeal, FractionalIdeal.mul_induction_on, Submodule, Submodule.add_mem, Submodule.smul_mem, add_mem, mem_spanSingleton, mul_add, mul_induction_on, mul_mem_mul, mul_smul_comm, one_smul, smul_mem, smul_mul_assoc
-/
theorem mem_singleton_mul {x y : P} {I : FractionalIdeal S P} :
    y in spanSingleton S x * I ↔ exists y' in I, y = x * y' := by
  constructor
  · intro h
    refine FractionalIdeal.mul_induction_on h ?_ ?_
    · intro x' hx' y' hy'
      obtain ⟨a, ha⟩ := (mem_spanSingleton S).mp hx'
      use a • y', Submodule.smul_mem (I : Submodule R P) a hy'
      rw [← ha]; rw [Algebra.mul_smul_comm]; rw [Algebra.smul_mul_assoc]
    · rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      exact ⟨y + y', Submodule.add_mem (I : Submodule R P) hy hy', (mul_add _ _ _).symm⟩
  · rintro ⟨y', hy', rfl⟩
    exact mul_mem_mul ((mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩) hy'

variable (K) in
/--
theorem `mk'_mul_coeIdeal_eq_coeIdeal` / 定理 `mk'_mul_coeIdeal_eq_coeIdeal`

English:
theorem mk'_mul_coeIdeal_eq_coeIdeal
  given: {I J : Ideal R₁} {x y : R₁} (hy : y in R₁⁰)
  proof: by
  have :
    spanSingleton R₁⁰ (IsLocalization.mk' _ (1 : R₁) ⟨y, hy⟩) *
        spanSingleton R₁⁰ (algebraMap R₁ K y) =
      1 := by
    rw [spanSingleton_mul_spanSingleton]; rw [mul_comm]; rw [← IsLocalization.mk'_eq_mul_mk'_one]; rw [IsLocalization.mk'_self]; rw [spanSingleton_one]
  let y' :

中文:
定理 mk'_mul_coeIdeal_eq_coeIdeal
  条件: {I J : 理想 R₁} {x y : R₁} (hy : y in R₁⁰)
  证明: by
  have :
    spanSingleton R₁⁰ (IsLocalization.mk' _ (1 : R₁) ⟨y, hy⟩) *
        spanSingleton R₁⁰ (algebraMap R₁ K y) =
      1 := by
    rw [spanSingleton_mul_spanSingleton]; rw [mul_comm]; rw [← IsLocalization.mk'_eq_mul_mk'_one]; rw [IsLocalization.mk'_self]; rw [spanSingleton_one]
  let y' :

Depends on / 依赖: FractionalIdeal, Iff.trans, IsLocalization, IsLocalization.mk, Units.mkOfMulEqOne, _eq_mul_mk, _one, _self, algebraMap, coeIdeal_, coeIdeal_inj, coe_y, mkOfMulEqOne, mul_comm, mul_right_inj, mul_right_inj.trans, spanSingleton, spanSingleton_mul_spanSingleton, spanSingleton_one
-/
theorem mk'_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {x y : R₁} (hy : y in R₁⁰) :
    spanSingleton R₁⁰ (IsLocalization.mk' K x ⟨y, hy⟩) * I = (J : FractionalIdeal R₁⁰ K) ↔
      Ideal.span {x} * I = Ideal.span {y} * J := by
  have :
    spanSingleton R₁⁰ (IsLocalization.mk' _ (1 : R₁) ⟨y, hy⟩) *
        spanSingleton R₁⁰ (algebraMap R₁ K y) =
      1 := by
    rw [spanSingleton_mul_spanSingleton]; rw [mul_comm]; rw [← IsLocalization.mk'_eq_mul_mk'_one]; rw [IsLocalization.mk'_self]; rw [spanSingleton_one]
  let y' : (FractionalIdeal R₁⁰ K)ˣ := Units.mkOfMulEqOne _ _ this
  have coe_y' : ↑y' = spanSingleton R₁⁰ (IsLocalization.mk' K (1 : R₁) ⟨y, hy⟩) := rfl
  refine Iff.trans ?_ (y'.mul_right_inj.trans coeIdeal_inj)
  rw [coe_y']; rw [coeIdeal_mul]; rw [coeIdeal_span_singleton]; rw [coeIdeal_mul]; rw [coeIdeal_span_singleton]; rw [←
    mul_assoc]; rw [spanSingleton_mul_spanSingleton]; rw [← mul_assoc]; rw [spanSingleton_mul_spanSingleton]; rw [mul_comm (mk' _ _ _)]; rw [← IsLocalization.mk'_eq_mul_mk'_one]; rw [mul_comm (mk' _ _ _)]; rw [←
    IsLocalization.mk'_eq_mul_mk'_one]; rw [IsLocalization.mk'_self]; rw [spanSingleton_one]; rw [one_mul]

/--
theorem `spanSingleton_mul_coeIdeal_eq_coeIdeal` / 定理 `spanSingleton_mul_coeIdeal_eq_coeIdeal`

English:
theorem spanSingleton_mul_coeIdeal_eq_coeIdeal
  given: {I J : Ideal R₁} {z : K}
  proof: by
  rw [← mk'_mul_coeIdeal_eq_coeIdeal K (IsLocalization.sec R₁⁰ z).2.prop]; rw [IsLocalization.mk'_sec K z]

中文:
定理 spanSingleton_mul_coeIdeal_eq_coeIdeal
  条件: {I J : 理想 R₁} {z : K}
  证明: by
  rw [← mk'_mul_coeIdeal_eq_coeIdeal K (IsLocalization.sec R₁⁰ z).2.prop]; rw [IsLocalization.mk'_sec K z]

Depends on / 依赖: IsLocalization, IsLocalization.mk, IsLocalization.sec, _mul_coeIdeal_eq_coeIdeal, _sec
-/
theorem spanSingleton_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {z : K} :
    spanSingleton R₁⁰ z * (I : FractionalIdeal R₁⁰ K) = J ↔
      Ideal.span {((IsLocalization.sec R₁⁰ z).1 : R₁)} * I =
        Ideal.span {((IsLocalization.sec R₁⁰ z).2 : R₁)} * J := by
  rw [← mk'_mul_coeIdeal_eq_coeIdeal K (IsLocalization.sec R₁⁰ z).2.prop]; rw [IsLocalization.mk'_sec K z]

variable [IsDomain R₁]

/--
theorem `one_div_spanSingleton` / 定理 `one_div_spanSingleton`

English:
theorem one_div_spanSingleton
  given: (x : K)
  statement: 1 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹
  proof: by
  classical
  exact if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one_right _ _ (by simp [h])).symm

@[simp]

中文:
定理 one_div_spanSingleton
  条件: (x : K)
  结论: 1 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹
  证明: by
  classical
  exact if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one_right _ _ (by simp [h])).symm

@[simp]

Depends on / 依赖: classical, eq_one_div_of_mul_eq_one_right
-/
theorem one_div_spanSingleton (x : K) : 1 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹ := by
  classical
  exact if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one_right _ _ (by simp [h])).symm

@[simp]
/--
theorem `div_spanSingleton` / 定理 `div_spanSingleton`

English:
theorem div_spanSingleton
  given: (J : FractionalIdeal R₁⁰ K) (d : K)
  proof: by
  rw [← one_div_spanSingleton]
  by_cases hd : d = 0
  · simp only [hd, spanSingleton_zero, div_zero, zero_mul]
  have h_spand : spanSingleton R₁⁰ d != 0 := mt spanSingleton_eq_zero_iff.mp hd
  apply le_antisymm
  · intro x hx
    rw [← mem_coe]; rw [coe_div h_spand]; rw [Submodule.mem_div_iff_fo

中文:
定理 div_spanSingleton
  条件: (J : FractionalIdeal R₁⁰ K) (d : K)
  证明: by
  rw [← one_div_spanSingleton]
  by_cases hd : d = 0
  · simp only [hd, spanSingleton_zero, div_zero, zero_mul]
  have h_spand : spanSingleton R₁⁰ d != 0 := mt spanSingleton_eq_zero_iff.mp hd
  apply le_antisymm
  · intro x hx
    rw [← mem_coe]; rw [coe_div h_spand]; rw [Submodule.mem_div_iff_fo

Depends on / 依赖: Submodule, Submodule.mem_div_iff_forall_mul_mem, Submodule.mul_mem_mul, coe_div, coe_mul, div_zero, h_spand, h_xd, le_antisymm, mem_coe, mem_div_iff_forall_mul_mem, mem_spanSi, mem_spanSingleton_self, mul_mem_mul, one_div_spanSingleton, spanSingleton, spanSingleton_eq_zero_iff, spanSingleton_eq_zero_iff.mp, spanSingleton_zero, specialize
-/
theorem div_spanSingleton (J : FractionalIdeal R₁⁰ K) (d : K) :
    J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J := by
  rw [← one_div_spanSingleton]
  by_cases hd : d = 0
  · simp only [hd, spanSingleton_zero, div_zero, zero_mul]
  have h_spand : spanSingleton R₁⁰ d != 0 := mt spanSingleton_eq_zero_iff.mp hd
  apply le_antisymm
  · intro x hx
    rw [← mem_coe]; rw [coe_div h_spand]; rw [Submodule.mem_div_iff_forall_mul_mem] at hx
    specialize hx d (mem_spanSingleton_self R₁⁰ d)
    have h_xd : x = d⁻¹ * (x * d) := by field
    rw [← mem_coe]; rw [coe_mul]; rw [one_div_spanSingleton]; rw [h_xd]
    exact Submodule.mul_mem_mul (mem_spanSingleton_self R₁⁰ _) hx
  · rw [le_div_iff_mul_le h_spand, mul_assoc, mul_left_comm, one_div_spanSingleton,
      spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hd, spanSingleton_one, mul_one]

/--
theorem `exists_eq_spanSingleton_mul` / 定理 `exists_eq_spanSingleton_mul`

English:
theorem exists_eq_spanSingleton_mul
  given: (I : FractionalIdeal R₁⁰ K)
  proof: by
  obtain ⟨a_inv, nonzero, ha⟩ := I.isFractional
  have nonzero := mem_nonZeroDivisors_iff_ne_zero.mp nonzero
  have map_a_nonzero : algebraMap R₁ K a_inv != 0 :=
    mt IsFractionRing.to_map_eq_zero_iff.mp nonzero
  refine
    ⟨a_inv,
      Submodule.comap (Algebra.linearMap R₁ K) ↑(spanSingleton

中文:
定理 存在_eq_spanSingleton_mul
  条件: (I : FractionalIdeal R₁⁰ K)
  证明: by
  obtain ⟨a_inv, nonzero, ha⟩ := I.isFractional
  have nonzero := mem_nonZeroDivisors_iff_ne_zero.mp nonzero
  have map_a_nonzero : algebraMap R₁ K a_inv != 0 :=
    mt IsFractionRing.to_map_eq_zero_iff.mp nonzero
  refine
    ⟨a_inv,
      Submodule.comap (Algebra.linearMap R₁ K) ↑(spanSingleton

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.smul_def, I.isFractional, Iff.trans, IsFractionRing, IsFractionRing.to_map_eq_zero_iff.mp, Submodule, Submodule.comap, a_inv, algebraMap, isFractional, linearMap, map_a_nonzero, mem_coeIdeal, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mp, mem_singleton_mul, mem_singleton_mul.symm, nonzero
-/
theorem exists_eq_spanSingleton_mul (I : FractionalIdeal R₁⁰ K) :
    exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spanSingleton R₁⁰ (algebraMap R₁ K a)⁻¹ * aI := by
  obtain ⟨a_inv, nonzero, ha⟩ := I.isFractional
  have nonzero := mem_nonZeroDivisors_iff_ne_zero.mp nonzero
  have map_a_nonzero : algebraMap R₁ K a_inv != 0 :=
    mt IsFractionRing.to_map_eq_zero_iff.mp nonzero
  refine
    ⟨a_inv,
      Submodule.comap (Algebra.linearMap R₁ K) ↑(spanSingleton R₁⁰ (algebraMap R₁ K a_inv) * I),
      nonzero, ext fun x => Iff.trans ⟨?_, ?_⟩ mem_singleton_mul.symm⟩
  · intro hx
    obtain ⟨x', hx'⟩ := ha x hx
    rw [Algebra.smul_def] at hx'
    refine ⟨algebraMap R₁ K x', (mem_coeIdeal _).mpr ⟨x', mem_singleton_mul.mpr ?_, rfl⟩, ?_⟩
    · exact ⟨x, hx, hx'⟩
    · rw [hx', ← mul_assoc, inv_mul_cancel₀ map_a_nonzero, one_mul]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x', hx', rfl⟩ := (mem_coeIdeal _).mp hy
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx'
    rw [Algebra.linearMap_apply] at hx'
    rwa [hx', ← mul_assoc, inv_mul_cancel₀ map_a_nonzero, one_mul]


/--
theorem `ideal_factor_ne_zero` / 定理 `ideal_factor_ne_zero`

English:
theorem ideal_factor_ne_zero
  statement: {R} [CommRing R] {K : Type*} [Field K] [Algebra R K]
  proof: fun h => by
  rw [h]; rw [Ideal.zero_eq_bot]; rw [coeIdeal_bot]; rw [mul_zero] at haJ
  exact hI haJ

中文:
定理 ideal_factor_ne_zero
  结论: {R} [交换环 R] {K : 类型} [域 K] [代数 R K]
  证明: fun h => by
  rw [h]; rw [Ideal.zero_eq_bot]; rw [coeIdeal_bot]; rw [mul_zero] at haJ
  exact hI haJ

Depends on / 依赖: Ideal.zero_eq_bot, coeIdeal_bot, mul_zero, zero_eq_bot
-/
theorem ideal_factor_ne_zero {R} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : Ideal R}
    (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) : J != 0 := fun h => by
  rw [h]; rw [Ideal.zero_eq_bot]; rw [coeIdeal_bot]; rw [mul_zero] at haJ
  exact hI haJ

/--
theorem `constant_factor_ne_zero` / 定理 `constant_factor_ne_zero`

English:
theorem constant_factor_ne_zero
  statement: {R} [CommRing R] {K : Type*} [Field K] [Algebra R K]
  proof: fun h => by
  rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot] at h
  rw [h]; rw [map_zero]; rw [inv_zero]; rw [spanSingleton_zero]; rw [zero_mul] at haJ
  exact hI haJ

中文:
定理 constant_factor_ne_zero
  结论: {R} [交换环 R] {K : 类型} [域 K] [代数 R K]
  证明: fun h => by
  rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot] at h
  rw [h]; rw [map_zero]; rw [inv_zero]; rw [spanSingleton_zero]; rw [zero_mul] at haJ
  exact hI haJ

Depends on / 依赖: Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot, inv_zero, map_zero, spanSingleton_zero, span_singleton_eq_bot, zero_eq_bot, zero_mul
-/
theorem constant_factor_ne_zero {R} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : Ideal R}
    (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    (Ideal.span {a} : Ideal R) != 0 := fun h => by
  rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot] at h
  rw [h]; rw [map_zero]; rw [inv_zero]; rw [spanSingleton_zero]; rw [zero_mul] at haJ
  exact hI haJ

/--
Instance `isPrincipal` / 实例 `isPrincipal`

English:
instance isPrincipal
  signature: {R} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R K]
  body: by
  obtain ⟨a, aI, -, ha⟩ := exists_eq_spanSingleton_mul I
  use (algebraMap R K a)⁻¹ * algebraMap R K (generator aI)
  suffices I = spanSingleton R⁰ ((algebraMap R K a)⁻¹ * algebraMap R K (generator aI)) by
    rw [spanSingleton] at this
    exact congr_arg Subtype.val this
  conv_lhs => rw [ha, ←

中文:
实例 isPrincipal
  签名: {R} [交换环 R] [是整环 R] [是主理想环 R] [代数 R K]
  定义体: by
  obtain ⟨a, aI, -, ha⟩ := exists_eq_spanSingleton_mul I
  use (algebraMap R K a)⁻¹ * algebraMap R K (generator aI)
  suffices I = spanSingleton R⁰ ((algebraMap R K a)⁻¹ * algebraMap R K (generator aI)) by
    rw [spanSingleton] at this
    exact congr_arg Subtype.val this
  conv_lhs => rw [ha, ←

Depends on / 依赖: Ideal.submodule_span_eq, Subtype, Subtype.val, algebraMap, coeIdeal_span_singleton, congr_arg, conv_lhs, exists_eq_spanSingleton_mul, generator, spanSingleton, spanSingleton_mul_spanSingleton, span_singleton_generator, submodule_span_eq
-/
instance isPrincipal {R} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) : (I : Submodule R K).IsPrincipal := by
  obtain ⟨a, aI, -, ha⟩ := exists_eq_spanSingleton_mul I
  use (algebraMap R K a)⁻¹ * algebraMap R K (generator aI)
  suffices I = spanSingleton R⁰ ((algebraMap R K a)⁻¹ * algebraMap R K (generator aI)) by
    rw [spanSingleton] at this
    exact congr_arg Subtype.val this
  conv_lhs => rw [ha, ← span_singleton_generator aI]
  rw [Ideal.submodule_span_eq]; rw [coeIdeal_span_singleton (generator aI)]; rw [spanSingleton_mul_spanSingleton]

/--
theorem `le_spanSingleton_mul_iff` / 定理 `le_spanSingleton_mul_iff`

English:
theorem le_spanSingleton_mul_iff
  given: {x : P} {I J : FractionalIdeal S P}
  proof: show (forall {zI} (_ : zI in I), zI in spanSingleton _ x * J) ↔ forall zI in I, exists zJ in J, x * zJ = zI by
    simp only [mem_singleton_mul, eq_comm]

中文:
定理 le_spanSingleton_mul_iff
  条件: {x : P} {I J : FractionalIdeal S P}
  证明: show (forall {zI} (_ : zI in I), zI in spanSingleton _ x * J) ↔ forall zI in I, exists zJ in J, x * zJ = zI by
    simp only [mem_singleton_mul, eq_comm]

Depends on / 依赖: UsableInSimplexAlgorithm, UsableInSimplexAlgorithm.getElem, eq_comm, getElem, mem_singleton_mul, spanSingleton
-/
theorem le_spanSingleton_mul_iff {x : P} {I J : FractionalIdeal S P} :
    I <= spanSingleton S x * J ↔ forall zI in I, exists zJ in J, x * zJ = zI :=
  show (forall {zI} (_ : zI in I), zI in spanSingleton _ x * J) ↔ forall zI in I, exists zJ in J, x * zJ = zI by
    simp only [mem_singleton_mul, eq_comm]

/--
theorem `spanSingleton_mul_le_iff` / 定理 `spanSingleton_mul_le_iff`

English:
theorem spanSingleton_mul_le_iff
  given: {x : P} {I J : FractionalIdeal S P}
  proof: by
  simp only [mul_le, mem_spanSingleton]
  constructor
  · intro h zI hzI
    exact h x ⟨1, one_smul _ _⟩ zI hzI
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem J.1 _ (h zI hzI)

中文:
定理 spanSingleton_mul_le_iff
  条件: {x : P} {I J : FractionalIdeal S P}
  证明: by
  simp only [mul_le, mem_spanSingleton]
  constructor
  · intro h zI hzI
    exact h x ⟨1, one_smul _ _⟩ zI hzI
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem J.1 _ (h zI hzI)

Depends on / 依赖: Algebra, Algebra.smul_mul_assoc, Submodule, Submodule.smul_mem, mem_spanSingleton, mul_le, one_smul, smul_mem, smul_mul_assoc
-/
theorem spanSingleton_mul_le_iff {x : P} {I J : FractionalIdeal S P} :
    spanSingleton _ x * I <= J ↔ forall z in I, x * z in J := by
  simp only [mul_le, mem_spanSingleton]
  constructor
  · intro h zI hzI
    exact h x ⟨1, one_smul _ _⟩ zI hzI
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem J.1 _ (h zI hzI)

/--
theorem `eq_spanSingleton_mul` / 定理 `eq_spanSingleton_mul`

English:
theorem eq_spanSingleton_mul
  given: {x : P} {I J : FractionalIdeal S P}
  proof: by
  simp only [le_antisymm_iff, le_spanSingleton_mul_iff, spanSingleton_mul_le_iff]

中文:
定理 eq_spanSingleton_mul
  条件: {x : P} {I J : FractionalIdeal S P}
  证明: by
  simp only [le_antisymm_iff, le_spanSingleton_mul_iff, spanSingleton_mul_le_iff]

Depends on / 依赖: le_antisymm_iff, le_spanSingleton_mul_iff, spanSingleton_mul_le_iff
-/
theorem eq_spanSingleton_mul {x : P} {I J : FractionalIdeal S P} :
    I = spanSingleton _ x * J ↔ (forall zI in I, exists zJ in J, x * zJ = zI) ∧ forall z in J, x * z in I := by
  simp only [le_antisymm_iff, le_spanSingleton_mul_iff, spanSingleton_mul_le_iff]

/--
theorem `num_le` / 定理 `num_le`

English:
theorem num_le
  given: (I : FractionalIdeal S P)
  proof: by
  rw [← I.den_mul_self_eq_num']; rw [spanSingleton_mul_le_iff]
  intro _ h
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h

中文:
定理 num_le
  条件: (I : FractionalIdeal S P)
  证明: by
  rw [← I.den_mul_self_eq_num']; rw [spanSingleton_mul_le_iff]
  intro _ h
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h

Depends on / 依赖: Algebra, Algebra.smul_def, I.den_mul_self_eq_num, Submodule, Submodule.smul_mem, den_mul_self_eq_num, smul_def, smul_mem, spanSingleton_mul_le_iff
-/
theorem num_le (I : FractionalIdeal S P) :
    (I.num : FractionalIdeal S P) <= I := by
  rw [← I.den_mul_self_eq_num']; rw [spanSingleton_mul_le_iff]
  intro _ h
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h

/--
theorem `isPrincipal_of_isPrincipal_num` / 定理 `isPrincipal_of_isPrincipal_num`

English:
theorem isPrincipal_of_isPrincipal_num
  statement: [IsDomain R]
  proof: Module.isPrincipal_submodule_iff.mp
 (FractionalIdeal.equivNumOfIsLocalization I).isPrincipal_iff.mpr
 Module.isPrincipal_submodule_iff.mpr hI

中文:
定理 isPrincipal_of_isPrincipal_num
  结论: [是整环 R]
  证明: Module.isPrincipal_submodule_iff.mp
 (FractionalIdeal.equivNumOfIsLocalization I).isPrincipal_iff.mpr
 Module.isPrincipal_submodule_iff.mpr hI

Depends on / 依赖: FractionalIdeal, FractionalIdeal.equivNumOfIsLocalization, Module, Module.isPrincipal_submodule_iff.mp, Module.isPrincipal_submodule_iff.mpr, equivNumOfIsLocalization, isPrincipal_iff, isPrincipal_iff.mpr, isPrincipal_submodule_iff
-/
theorem isPrincipal_of_isPrincipal_num [IsDomain R]
    (I : FractionalIdeal R⁰ (FractionRing R)) (hI : I.num.IsPrincipal) :
    (I : Submodule R (FractionRing R)).IsPrincipal :=
  Module.isPrincipal_submodule_iff.mp
 (FractionalIdeal.equivNumOfIsLocalization I).isPrincipal_iff.mpr
 Module.isPrincipal_submodule_iff.mpr hI

end PrincipalIdeal

variable {R₁ : Type*} [CommRing R₁]
variable {K : Type*} [Field K] [Algebra R₁ K]

/--
theorem `isNoetherian_zero` / 定理 `isNoetherian_zero`

English:
theorem isNoetherian_zero
  statement: IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K)
  proof: isNoetherian_submodule.mpr fun I (hI : I <= (0 : FractionalIdeal R₁⁰ K)) => by
    rw [coe_zero]; rw [le_bot_iff] at hI
    rw [hI]
    exact fg_bot

中文:
定理 isNoetherian_zero
  结论: 是Noether R₁ (0 : FractionalIdeal R₁⁰ K)
  证明: isNoetherian_submodule.mpr fun I (hI : I <= (0 : FractionalIdeal R₁⁰ K)) => by
    rw [coe_zero]; rw [le_bot_iff] at hI
    rw [hI]
    exact fg_bot

Depends on / 依赖: FractionalIdeal, coe_zero, fg_bot, isNoetherian_submodule, isNoetherian_submodule.mpr, le_bot_iff
-/
theorem isNoetherian_zero : IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K) :=
  isNoetherian_submodule.mpr fun I (hI : I <= (0 : FractionalIdeal R₁⁰ K)) => by
    rw [coe_zero]; rw [le_bot_iff] at hI
    rw [hI]
    exact fg_bot

/--
theorem `isNoetherian_iff` / 定理 `isNoetherian_iff`

English:
theorem isNoetherian_iff
  given: {I : FractionalIdeal R₁⁰ K}
  proof: isNoetherian_submodule.trans ⟨fun h _ hJ => h _ hJ, fun h J hJ => h ⟨J, isFractional_of_le hJ⟩ hJ⟩

中文:
定理 isNoetherian_iff
  条件: {I : FractionalIdeal R₁⁰ K}
  证明: isNoetherian_submodule.trans ⟨fun h _ hJ => h _ hJ, fun h J hJ => h ⟨J, isFractional_of_le hJ⟩ hJ⟩

Depends on / 依赖: isFractional_of_le, isNoetherian_submodule, isNoetherian_submodule.trans
-/
theorem isNoetherian_iff {I : FractionalIdeal R₁⁰ K} :
    IsNoetherian R₁ I ↔ forall J <= I, (J : Submodule R₁ K).FG :=
  isNoetherian_submodule.trans ⟨fun h _ hJ => h _ hJ, fun h J hJ => h ⟨J, isFractional_of_le hJ⟩ hJ⟩

/--
theorem `isNoetherian_coeIdeal` / 定理 `isNoetherian_coeIdeal`

English:
theorem isNoetherian_coeIdeal
  given: [IsNoetherianRing R₁] (I : Ideal R₁)
  proof: by
  rw [isNoetherian_iff]
  intro J hJ
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp (le_trans hJ coeIdeal_le_one)
  exact (IsNoetherian.noetherian J).map _

中文:
定理 isNoetherian_coeIdeal
  条件: [是Noether环 R₁] (I : 理想 R₁)
  证明: by
  rw [isNoetherian_iff]
  intro J hJ
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp (le_trans hJ coeIdeal_le_one)
  exact (IsNoetherian.noetherian J).map _

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, coeIdeal_le_one, isNoetherian_iff, le_one_iff_exists_coeIdeal, le_one_iff_exists_coeIdeal.mp, le_trans, noetherian
-/
theorem isNoetherian_coeIdeal [IsNoetherianRing R₁] (I : Ideal R₁) :
    IsNoetherian R₁ (I : FractionalIdeal R₁⁰ K) := by
  rw [isNoetherian_iff]
  intro J hJ
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp (le_trans hJ coeIdeal_le_one)
  exact (IsNoetherian.noetherian J).map _

variable [IsFractionRing R₁ K] [IsDomain R₁]

/--
theorem `isNoetherian_spanSingleton_inv_to_map_mul` / 定理 `isNoetherian_spanSingleton_inv_to_map_mul`

English:
theorem isNoetherian_spanSingleton_inv_to_map_mul
  statement: (x : R₁) {I : FractionalIdeal R₁⁰ K}
  proof: by
  classical
  by_cases hx : x = 0
  · rw [hx, map_zero, inv_zero, spanSingleton_zero, zero_mul]
    exact isNoetherian_zero
  have h_gx : algebraMap R₁ K x != 0 :=
    mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).mp (IsFractionRing.injective _ _) x) hx
  have h_spanx : spanSingleton R₁⁰ (alg

中文:
定理 isNoetherian_spanSingleton_inv_to_map_mul
  结论: (x : R₁) {I : FractionalIdeal R₁⁰ K}
  证明: by
  classical
  by_cases hx : x = 0
  · rw [hx, map_zero, inv_zero, spanSingleton_zero, zero_mul]
    exact isNoetherian_zero
  have h_gx : algebraMap R₁ K x != 0 :=
    mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).mp (IsFractionRing.injective _ _) x) hx
  have h_spanx : spanSingleton R₁⁰ (alg

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, algebraMap, classical, div_spanSingleton, h_gx, h_spanx, injective, injective_iff_map_eq_zero, inv_zero, isNoetherian_iff, isNoetherian_zero, le_div_iff_mul_le, map_zero, spanSingleton, spanSingleton_ne_zero_iff, spanSingleton_ne_zero_iff.mpr, spanSingleton_zero, zero_mul
-/
theorem isNoetherian_spanSingleton_inv_to_map_mul (x : R₁) {I : FractionalIdeal R₁⁰ K}
    (hI : IsNoetherian R₁ I) :
    IsNoetherian R₁ (spanSingleton R₁⁰ (algebraMap R₁ K x)⁻¹ * I : FractionalIdeal R₁⁰ K) := by
  classical
  by_cases hx : x = 0
  · rw [hx, map_zero, inv_zero, spanSingleton_zero, zero_mul]
    exact isNoetherian_zero
  have h_gx : algebraMap R₁ K x != 0 :=
    mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).mp (IsFractionRing.injective _ _) x) hx
  have h_spanx : spanSingleton R₁⁰ (algebraMap R₁ K x) != 0 := spanSingleton_ne_zero_iff.mpr h_gx
  rw [isNoetherian_iff] at hI ⊢
  intro J hJ
  rw [← div_spanSingleton]; rw [le_div_iff_mul_le h_spanx] at hJ
  obtain ⟨s, hs⟩ := hI _ hJ
  use s * {(algebraMap R₁ K x)⁻¹}
  rw [Finset.coe_mul]; rw [Finset.coe_singleton]; rw [← span_mul_span]; rw [hs]; rw [← coe_spanSingleton R₁⁰]; rw [←
    coe_mul]; rw [mul_assoc]; rw [spanSingleton_mul_spanSingleton]; rw [mul_inv_cancel₀ h_gx]; rw [spanSingleton_one]; rw [mul_one]

/--
theorem `isNoetherian` / 定理 `isNoetherian`

English:
theorem isNoetherian
  given: [IsNoetherianRing R₁] (I : FractionalIdeal R₁⁰ K)
  statement: IsNoetherian R₁ I
  proof: by
  obtain ⟨d, J, _, rfl⟩ := exists_eq_spanSingleton_mul I
  apply isNoetherian_spanSingleton_inv_to_map_mul
  apply isNoetherian_coeIdeal

中文:
定理 isNoetherian
  条件: [是Noether环 R₁] (I : FractionalIdeal R₁⁰ K)
  结论: 是Noether R₁ I
  证明: by
  obtain ⟨d, J, _, rfl⟩ := exists_eq_spanSingleton_mul I
  apply isNoetherian_spanSingleton_inv_to_map_mul
  apply isNoetherian_coeIdeal

Depends on / 依赖: exists_eq_spanSingleton_mul, isNoetherian_coeIdeal, isNoetherian_spanSingleton_inv_to_map_mul
-/
theorem isNoetherian [IsNoetherianRing R₁] (I : FractionalIdeal R₁⁰ K) : IsNoetherian R₁ I := by
  obtain ⟨d, J, _, rfl⟩ := exists_eq_spanSingleton_mul I
  apply isNoetherian_spanSingleton_inv_to_map_mul
  apply isNoetherian_coeIdeal

section Adjoin

variable (S)
variable [IsLocalization S P] (x : P)

/--
theorem `isFractional_adjoin_integral` / 定理 `isFractional_adjoin_integral`

English:
theorem isFractional_adjoin_integral
  given: (hx : IsIntegral R x)
  proof: isFractional_of_fg hx.fg_adjoin_singleton

中文:
定理 isFractional_adjoin_integral
  条件: (hx : 是整 R x)
  证明: isFractional_of_fg hx.fg_adjoin_singleton

Depends on / 依赖: fg_adjoin_singleton, hx.fg_adjoin_singleton, isFractional_of_fg
-/
theorem isFractional_adjoin_integral (hx : IsIntegral R x) :
    IsFractional S (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  isFractional_of_fg hx.fg_adjoin_singleton

-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
/--
Definition of `adjoinIntegral` / `adjoinIntegral` 的定义

English:
definition adjoinIntegral
  signature: (hx : IsIntegral R x)
  body: ⟨_, isFractional_adjoin_integral S x hx⟩

@[simp]

中文:
定义 adjoin整数egral
  签名: (hx : 是整 R x)
  定义体: ⟨_, isFractional_adjoin_integral S x hx⟩

@[simp]

Depends on / 依赖: isFractional_adjoin_integral
-/
def adjoinIntegral (hx : IsIntegral R x) : FractionalIdeal S P :=
  ⟨_, isFractional_adjoin_integral S x hx⟩

@[simp]
/--
theorem `adjoinIntegral_coe` / 定理 `adjoinIntegral_coe`

English:
theorem adjoinIntegral_coe
  given: (hx : IsIntegral R x)
  proof: rfl

中文:
定理 adjoin整数egral_coe
  条件: (hx : 是整 R x)
  证明: rfl
-/
theorem adjoinIntegral_coe (hx : IsIntegral R x) :
    (adjoinIntegral S x hx : Submodule R P) =
      (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  rfl

/--
theorem `mem_adjoinIntegral_self` / 定理 `mem_adjoinIntegral_self`

English:
theorem mem_adjoinIntegral_self
  given: (hx : IsIntegral R x)
  statement: x in adjoinIntegral S x hx
  proof: Algebra.subset_adjoin (Set.mem_singleton x)

中文:
定理 mem_adjoin整数egral_self
  条件: (hx : 是整 R x)
  结论: x in adjoin整数egral S x hx
  证明: Algebra.subset_adjoin (Set.mem_singleton x)

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Set.mem_singleton, mem_singleton, subset_adjoin
-/
theorem mem_adjoinIntegral_self (hx : IsIntegral R x) : x in adjoinIntegral S x hx :=
  Algebra.subset_adjoin (Set.mem_singleton x)

end Adjoin

section RingEquiv

open IsFractionRing

variable {R S : Type*} (K L : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [CommRing K] [CommRing L] [Algebra R K] [Algebra S L] [IsFractionRing R K] [IsFractionRing S L]
  (f : R ≃+* S)

local instance (f : R ≃+* S) : RingHomInvPair (f : R ->+* S) f.symm :=
  RingHomInvPair.of_ringEquiv f

/--
theorem `_root_.IsFractional.mapEquiv` / 定理 `_root_.IsFractional.mapEquiv`

English:
theorem _root_.IsFractional.mapEquiv
  given: {I : Submodule R K} (hI : IsFractional R⁰ I)
  proof: by
  simp only [IsFractional, mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hI ⊢
  obtain ⟨r, hr0, hr⟩ := hI
  use f r
  refine ⟨by simp [hr0], ?_⟩
  intro x hx
  specialize hr x hx
  simp only [IsLocalization.IsInteger, Rin

中文:
定理 _root_.IsFractional.mapEquiv
  条件: {I : 子模 R K} (hI : IsFractional R⁰ I)
  证明: by
  simp only [IsFractional, mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hI ⊢
  obtain ⟨r, hr0, hr⟩ := hI
  use f r
  refine ⟨by simp [hr0], ?_⟩
  intro x hx
  specialize hr x hx
  simp only [IsLocalization.IsInteger, Rin

Depends on / 依赖: AddHom, AddHom.coe_mk, Equiv.invFun_as_coe, Equiv.toFun_as_coe, EquivLike, EquivLike.coe_coe, IsFractional, IsInteger, IsLocalization, IsLocalization.IsInteger, LinearMap, LinearMap.coe_mk, RingEquiv, RingEquiv.toEquiv_eq_coe, RingHom, RingHom.mem_rangeS, Submodule, Submodule.mem_map, and_imp, coe_coe
-/
theorem _root_.IsFractional.mapEquiv {I : Submodule R K} (hI : IsFractional R⁰ I) :
    IsFractional S⁰ (I.map (semilinearEquivOfRingEquiv K L f).toLinearMap) := by
  simp only [IsFractional, mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hI ⊢
  obtain ⟨r, hr0, hr⟩ := hI
  use f r
  refine ⟨by simp [hr0], ?_⟩
  intro x hx
  specialize hr x hx
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hr ⊢
  obtain ⟨r', hr'⟩ := hr
  use f r'
  simp only [semilinearEquivOfRingEquiv, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Algebra.smul_def]; rw [← ringEquivOfRingEquiv_algebraMap f (K := K) (L := L) r]; rw [← map_mul]; rw [← Algebra.smul_def]; rw [← hr']; rw [ringEquivOfRingEquiv_algebraMap]

set_option backward.isDefEq.respectTransparency.types false in
/-- The equiv `FractionalIdeal R⁰ K ≃+* FractionalIdeal S⁰ L`
  induced by a ring isomorphism `f : R ≃+* S`. -/
@[simps -isSimp]
/--
Definition of `ringEquivOfRingEquiv` / `ringEquivOfRingEquiv` 的定义

English:
definition ringEquivOfRingEquiv
  signature: :
  body: { toFun I := ⟨Submodule.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap I.val,
      IsFractional.mapEquiv K L f I.prop⟩
    invFun J := ⟨J.val.map (semilinearEquivOfRingEquiv _ _ f.symm).toLinearMap,
      IsFractional.mapEquiv L K f.symm J.prop⟩
    map_add' I J := by ext x; simp [← mem_coe]
  

中文:
定义 ringEquivOfRingEquiv
  签名: :
  定义体: { toFun I := ⟨Submodule.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap I.val,
      IsFractional.mapEquiv K L f I.prop⟩
    invFun J := ⟨J.val.map (semilinearEquivOfRingEquiv _ _ f.symm).toLinearMap,
      IsFractional.mapEquiv L K f.symm J.prop⟩
    map_add' I J := by ext x; simp [← mem_coe]
  

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coe_ext_iff, I.prop, I.val, IsFractional, IsFractional.mapEquiv, J.prop, J.val.map, Submodule, Submodule.map, Submodule.mul_le, coe_ext_iff, coe_mk, coe_mul, f.symm, invFun, le_antisymm, mapEquiv, map_add, map_le_iff_le_comap
-/
noncomputable def ringEquivOfRingEquiv :
    FractionalIdeal R⁰ K ≃+* FractionalIdeal S⁰ L :=
  { toFun I := ⟨Submodule.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap I.val,
      IsFractional.mapEquiv K L f I.prop⟩
    invFun J := ⟨J.val.map (semilinearEquivOfRingEquiv _ _ f.symm).toLinearMap,
      IsFractional.mapEquiv L K f.symm J.prop⟩
    map_add' I J := by ext x; simp [← mem_coe]
    map_mul' I J := by
      simp only [FractionalIdeal.coe_ext_iff, val_eq_coe, coe_mul, coe_mk]
      apply le_antisymm <;> simp only [map_le_iff_le_comap, Submodule.mul_le, mem_coe, mem_comap,
          semilinearEquivOfRingEquiv_apply, map_mul, mem_map_equiv,
          semilinearEquivOfRingEquiv_symm_apply, LinearEquiv.coe_coe]
      · exact fun m hm n hn => Submodule.mul_mem_mul (mem_map_of_mem hm) (mem_map_of_mem hn)
      · exact fun m hm n hn => Submodule.mul_mem_mul hm hn
    left_inv I := by
      simp only [RingEquiv.symm_symm, val_eq_coe, ← Submodule.map_comp, LinearEquiv.comp_coe,
        coe_ext_iff, coe_mk]
      convert! Submodule.map_id _
      ext; simp [semilinearEquivOfRingEquiv, IsLocalization.map_map]
    right_inv I := by
      simp only [RingEquiv.symm_symm, val_eq_coe, ← Submodule.map_comp, LinearEquiv.comp_coe,
        coe_ext_iff, coe_mk]
      convert! Submodule.map_id _
      ext; simp [semilinearEquivOfRingEquiv, IsLocalization.map_map]}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ringEquivOfRingEquiv_apply` / 引理 `ringEquivOfRingEquiv_apply`

English:
lemma ringEquivOfRingEquiv_apply
  given: (f : R ≃+* S) (I : FractionalIdeal (nonZeroDivisors R) K)
  proof: rfl

中文:
引理 ringEquivOfRingEquiv_apply
  条件: (f : R ≃+* S) (I : FractionalIdeal (nonZeroDivisors R) K)
  证明: rfl
-/
lemma ringEquivOfRingEquiv_apply (f : R ≃+* S) (I : FractionalIdeal (nonZeroDivisors R) K) :
    ringEquivOfRingEquiv K L f I =
      ⟨Submodule.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap I.val,
        IsFractional.mapEquiv K L f I.prop⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ringEquivOfRingEquiv_apply_val` / 引理 `ringEquivOfRingEquiv_apply_val`

English:
lemma ringEquivOfRingEquiv_apply_val
  given: (f : R ≃+* S) (I : FractionalIdeal R⁰ K)
  proof: rfl

中文:
引理 ringEquivOfRingEquiv_apply_val
  条件: (f : R ≃+* S) (I : FractionalIdeal R⁰ K)
  证明: rfl
-/
lemma ringEquivOfRingEquiv_apply_val (f : R ≃+* S) (I : FractionalIdeal R⁰ K) :
    (ringEquivOfRingEquiv K L f I).val =
      I.val.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ringEquivOfRingEquiv_trans` / 引理 `ringEquivOfRingEquiv_trans`

English:
lemma ringEquivOfRingEquiv_trans
  statement: {T : Type*} [CommRing T] [IsDomain T] (M : Type*) [CommRing M]
  proof: by
  have : RingHomCompTriple f (g : S ->+* T) (f.trans g : R ->+* T) := ⟨rfl⟩
  ext1 I
  simp only [ringEquivOfRingEquiv, RingEquiv.coe_ringHom_trans, Function.comp_apply,
    semilinearEquivOfRingEquiv_comp K L f M, LinearEquiv.coe_trans,
    Submodule.map_comp, RingEquiv.coe_mk, Equiv.coe_fn_mk, 

中文:
引理 ringEquivOfRingEquiv_trans
  结论: {T : 类型} [交换环 T] [是整环 T] (M : 类型) [交换环 M]
  证明: by
  have : RingHomCompTriple f (g : S ->+* T) (f.trans g : R ->+* T) := ⟨rfl⟩
  ext1 I
  simp only [ringEquivOfRingEquiv, RingEquiv.coe_ringHom_trans, Function.comp_apply,
    semilinearEquivOfRingEquiv_comp K L f M, LinearEquiv.coe_trans,
    Submodule.map_comp, RingEquiv.coe_mk, Equiv.coe_fn_mk, 

Depends on / 依赖: Equiv.coe_fn_mk, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_trans, RingEquiv, RingEquiv.coe_mk, RingEquiv.coe_ringHom_trans, RingEquiv.coe_trans, RingHomCompTriple, Submodule, Submodule.map_comp, coe_fn_mk, coe_mk, coe_ringHom_trans, coe_trans, comp_apply, f.trans, map_comp, ringEquivOfRingEquiv
-/
lemma ringEquivOfRingEquiv_trans {T : Type*} [CommRing T] [IsDomain T] (M : Type*) [CommRing M]
    [Algebra T M] [IsFractionRing T M] (f : R ≃+* S) (g : S ≃+* T) :
    ringEquivOfRingEquiv K M (f.trans g) =
      (ringEquivOfRingEquiv K L f).trans (ringEquivOfRingEquiv L M g) := by
  have : RingHomCompTriple f (g : S ->+* T) (f.trans g : R ->+* T) := ⟨rfl⟩
  ext1 I
  simp only [ringEquivOfRingEquiv, RingEquiv.coe_ringHom_trans, Function.comp_apply,
    semilinearEquivOfRingEquiv_comp K L f M, LinearEquiv.coe_trans,
    Submodule.map_comp, RingEquiv.coe_mk, Equiv.coe_fn_mk, RingEquiv.coe_trans]

/--
lemma `ringEquivOfRingEquiv_trans_apply` / 引理 `ringEquivOfRingEquiv_trans_apply`

English:
lemma ringEquivOfRingEquiv_trans_apply
  statement: {T : Type*} [CommRing T] [IsDomain T] (M : Type*)
  proof: by
  simp [ringEquivOfRingEquiv_trans K L M]

中文:
引理 ringEquivOfRingEquiv_trans_apply
  结论: {T : 类型} [交换环 T] [是整环 T] (M : 类型)
  证明: by
  simp [ringEquivOfRingEquiv_trans K L M]

Depends on / 依赖: ringEquivOfRingEquiv_trans
-/
lemma ringEquivOfRingEquiv_trans_apply {T : Type*} [CommRing T] [IsDomain T] (M : Type*)
    [CommRing M] [Algebra T M] [IsFractionRing T M]
    (f : R ≃+* S) (g : S ≃+* T) (I : FractionalIdeal R⁰ K) :
    ringEquivOfRingEquiv K M (f.trans g) I =
      ringEquivOfRingEquiv L M g (ringEquivOfRingEquiv K L f I) := by
  simp [ringEquivOfRingEquiv_trans K L M]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ringEquivOfRingEquiv_refl` / 引理 `ringEquivOfRingEquiv_refl`

English:
lemma ringEquivOfRingEquiv_refl
  proof: by
  ext I x
  simp only [ringEquivOfRingEquiv_apply, RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl,
    val_eq_coe, RingEquiv.refl_apply, ← mem_coe]
  simp [semilinearEquivOfRingEquiv]

中文:
引理 ringEquivOfRingEquiv_refl
  证明: by
  ext I x
  simp only [ringEquivOfRingEquiv_apply, RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl,
    val_eq_coe, RingEquiv.refl_apply, ← mem_coe]
  simp [semilinearEquivOfRingEquiv]

Depends on / 依赖: RingEquiv, RingEquiv.coe_ringHom_refl, RingEquiv.refl_apply, RingEquiv.symm_refl, coe_ringHom_refl, mem_coe, refl_apply, ringEquivOfRingEquiv_apply, semilinearEquivOfRingEquiv, symm_refl, val_eq_coe
-/
lemma ringEquivOfRingEquiv_refl :
    ringEquivOfRingEquiv K K (RingEquiv.refl R) = RingEquiv.refl (FractionalIdeal R⁰ K) := by
  ext I x
  simp only [ringEquivOfRingEquiv_apply, RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl,
    val_eq_coe, RingEquiv.refl_apply, ← mem_coe]
  simp [semilinearEquivOfRingEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ringEquivOfRingEquiv_spanSingleton` / 引理 `ringEquivOfRingEquiv_spanSingleton`

English:
lemma ringEquivOfRingEquiv_spanSingleton
  given: (x : K)
  proof: by
  simp only [ringEquivOfRingEquiv, val_eq_coe, RingEquiv.symm_symm, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_spanSingleton, IsFractionRing.ringEquivOfRingEquiv_apply]
  rw [SetLike.ext_iff]
  intro y
  simp only [← FractionalIdeal.mem_coe, coe_mk, mem_map_equiv, coe_spanSingleton,
    Submodule

中文:
引理 ringEquivOfRingEquiv_spanSingleton
  条件: (x : K)
  证明: by
  simp only [ringEquivOfRingEquiv, val_eq_coe, RingEquiv.symm_symm, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_spanSingleton, IsFractionRing.ringEquivOfRingEquiv_apply]
  rw [SetLike.ext_iff]
  intro y
  simp only [← FractionalIdeal.mem_coe, coe_mk, mem_map_equiv, coe_spanSingleton,
    Submodule

Depends on / 依赖: Algebra, Algebra.smul_def, Equiv.coe_fn_mk, FractionalIdeal, FractionalIdeal.mem_coe, IsFractionRing, IsFractionRing.ringEquivOfRingEquiv_apply, RingEquiv, RingEquiv.coe_mk, RingEquiv.symm_symm, SetLike, SetLike.ext_iff, Submodule, Submodule.mem_span_singleton, coe_fn_mk, coe_mk, coe_spanSingleton, eq_symm_apply, ext_iff, f.symm
-/
lemma ringEquivOfRingEquiv_spanSingleton (x : K) :
    FractionalIdeal.ringEquivOfRingEquiv K L f (spanSingleton R⁰ x) =
      spanSingleton S⁰ (IsFractionRing.ringEquivOfRingEquiv (L := L) f x) := by
  simp only [ringEquivOfRingEquiv, val_eq_coe, RingEquiv.symm_symm, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_spanSingleton, IsFractionRing.ringEquivOfRingEquiv_apply]
  rw [SetLike.ext_iff]
  intro y
  simp only [← FractionalIdeal.mem_coe, coe_mk, mem_map_equiv, coe_spanSingleton,
    Submodule.mem_span_singleton, (semilinearEquivOfRingEquiv K L f).eq_symm_apply]
  constructor
  · rintro ⟨r, rfl⟩
    use f r
    exact .symm (map_smulₛₗ _ r x)
  · rintro ⟨s, rfl⟩
    use f.symm s
    simp only [Algebra.smul_def, semilinearEquivOfRingEquiv_apply, map_mul, map_eq, RingHom.coe_coe,
      IsFractionRing.ringEquivOfRingEquiv_apply, RingEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ringEquivOfRingEquiv_symm_eq` / 引理 `ringEquivOfRingEquiv_symm_eq`

English:
lemma ringEquivOfRingEquiv_symm_eq
  proof: by
  exact (RingEquiv.coe_nonUnitalRingHom_inj_iff (ringEquivOfRingEquiv K L f).symm
          (ringEquivOfRingEquiv L K f.symm)).mpr rfl

中文:
引理 ringEquivOfRingEquiv_symm_eq
  证明: by
  exact (RingEquiv.coe_nonUnitalRingHom_inj_iff (ringEquivOfRingEquiv K L f).symm
          (ringEquivOfRingEquiv L K f.symm)).mpr rfl

Depends on / 依赖: RingEquiv, RingEquiv.coe_nonUnitalRingHom_inj_iff, coe_nonUnitalRingHom_inj_iff, f.symm, ringEquivOfRingEquiv
-/
lemma ringEquivOfRingEquiv_symm_eq :
    (FractionalIdeal.ringEquivOfRingEquiv K L f).symm =
      FractionalIdeal.ringEquivOfRingEquiv L K f.symm := by
  exact (RingEquiv.coe_nonUnitalRingHom_inj_iff (ringEquivOfRingEquiv K L f).symm
          (ringEquivOfRingEquiv L K f.symm)).mpr rfl

end RingEquiv

end FractionalIdeal
