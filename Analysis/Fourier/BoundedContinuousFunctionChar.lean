/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-!
# Definition of BoundedContinuousFunction.char

Definition and basic properties of `BoundedContinuousFunction.char he hL w := fun v ↦ e (L v w)`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear
map.

In the special case `e = Circle.exp`, this is used to define the characteristic function of a
measure.

## Main definitions

- `char he hL w : V →ᵇ ℂ`: Bounded continuous mapping `fun v ↦ e (L v w)` from `V` to `ℂ`, where
  `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear map.
- `charPoly he hL : W → ℂ`: The `StarSubalgebra ℂ (V →ᵇ ℂ)` consisting of `ℂ`-linear combinations of
  `char he hL w`, where `w : W`.

## Main statements

- `ext_of_char_eq`: If `e` and `L` are non-trivial, then `char he hL w, w : W` separates
  points in `V`.
- `star_mem_range_charAlgHom`: The family of `ℂ`-linear combinations of `char he hL w, w : W`, is
  closed under `star`.
- `separatesPoints_charPoly`: The family `charPoly he hL w, w : W` separates points in `V`.

-/

@[expose] public section

open Filter BoundedContinuousFunction Complex

namespace BoundedContinuousFunction

variable {V W : Type*} [AddCommGroup V] [Module Real V] [TopologicalSpace V]
    [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    {e : AddChar Real Circle} {L : V ->ₗ[Real] W ->ₗ[Real] Real}
    {he : Continuous e} {hL : Continuous fun p : V × W => L p.1 p.2}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `char` / `char` 的定义

English:
definition char
  signature: (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) (w : W)
  body: fun v => e (L v w)
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.prodMk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y => ?_⟩
    calc dist _ _
      <= (‖_‖ : Real) + ‖_‖ := dist_le_norm_add_norm _ _
    _ <= 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring

@[simp]

中文:
定义 char
  签名: (he : 连续 e) (hL : 连续 fun p : V × W => L p.1 p.2) (w : W)
  定义体: fun v => e (L v w)
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.prodMk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y => ?_⟩
    calc dist _ _
      <= (‖_‖ : Real) + ‖_‖ := dist_le_norm_add_norm _ _
    _ <= 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring

@[simp]
-/
noncomputable def char (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) (w : W) :
    V ->ᵇ Complex where
  toFun := fun v => e (L v w)
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.prodMk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y => ?_⟩
    calc dist _ _
      <= (‖_‖ : Real) + ‖_‖ := dist_le_norm_add_norm _ _
    _ <= 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring

@[simp]
/--
lemma `char_apply` / 引理 `char_apply`

English:
lemma char_apply
  given: (w : W) (v : V)
  proof: rfl

@[simp]

中文:
引理 char_apply
  条件: (w : W) (v : V)
  证明: rfl

@[simp]
-/
lemma char_apply (w : W) (v : V) :
    char he hL w v = e (L v w) := rfl

@[simp]
/--
lemma `char_zero_eq_one` / 引理 `char_zero_eq_one`

English:
lemma char_zero_eq_one
  statement: char he hL 0 = 1
  proof: by ext; simp

中文:
引理 char_zero_eq_one
  结论: char he hL 0 = 1
  证明: by ext; simp
-/
lemma char_zero_eq_one : char he hL 0 = 1 := by ext; simp

/--
lemma `char_add_eq_mul` / 引理 `char_add_eq_mul`

English:
lemma char_add_eq_mul
  given: (x y : W)
  proof: by
  ext
  simp [e.map_add_eq_mul]

中文:
引理 char_add_eq_mul
  条件: (x y : W)
  证明: by
  ext
  simp [e.map_add_eq_mul]

Depends on / 依赖: e.map_add_eq_mul, map_add_eq_mul
-/
lemma char_add_eq_mul (x y : W) :
    char he hL (x + y) = char he hL x * char he hL y := by
  ext
  simp [e.map_add_eq_mul]

/--
lemma `char_neg` / 引理 `char_neg`

English:
lemma char_neg
  given: (w : W)
  proof: by ext; simp

中文:
引理 char_neg
  条件: (w : W)
  证明: by ext; simp
-/
lemma char_neg (w : W) :
    char he hL (-w) = star (char he hL w) := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ext_of_char_eq` / 定理 `ext_of_char_eq`

English:
theorem ext_of_char_eq
  statement: (he : Continuous e) (he' : e != 1)
  proof: by
  contrapose! h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne h))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [map_sub, LinearMap.sub_apply, char_apply, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _)]; rw [div_eq_inv_mul]; rw [← Metric.unitSphere.coe_inv]; rw [← e.map_neg_eq_inv]; rw [← Submonoid.coe_mul]; rw [← e.map_add_eq_mul]; rw [OneMemClass.coe_eq_one]
  simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, AddChar.one_apply,
    map_smul, smul_eq_mul] at ha hw ⊢
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  ring_nf
  field_simp
  assumption

中文:
定理 ext_of_char_eq
  结论: (he : 连续 e) (he' : e != 1)
  证明: by
  contrapose! h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne h))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [map_sub, LinearMap.sub_apply, char_apply, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _)]; rw [div_eq_inv_mul]; rw [← Metric.unitSphere.coe_inv]; rw [← e.map_neg_eq_inv]; rw [← Submonoid.coe_mul]; rw [← e.map_add_eq_mul]; rw [OneMemClass.coe_eq_one]
  simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, AddChar.one_apply,
    map_smul, smul_eq_mul] at ha hw ⊢
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  ring_nf
  field_simp
  assumption

Depends on / 依赖: AddChar, Circle, Circle.coe_ne_zero, DFunLike, DFunLike.ne_iff.mp, LinearMap, LinearMap.sub_apply, LinearMap.zero_apply, Metric, Metric.unitSphere.coe_inv, OneMemClass, OneMemClass.coe_eq_one, Submonoid, Submonoid.coe_mul, char_apply, coe_eq_one, coe_inv, coe_mul, coe_ne_zero, contrapose
-/
theorem ext_of_char_eq (he : Continuous e) (he' : e != 1)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hL' : forall v != 0, L v != 0) {v v' : V}
    (h : forall w, char he hL w v = char he hL w v') :
    v = v' := by
  contrapose! h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne h))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [map_sub, LinearMap.sub_apply, char_apply, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _)]; rw [div_eq_inv_mul]; rw [← Metric.unitSphere.coe_inv]; rw [← e.map_neg_eq_inv]; rw [← Submonoid.coe_mul]; rw [← e.map_add_eq_mul]; rw [OneMemClass.coe_eq_one]
  simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, AddChar.one_apply,
    map_smul, smul_eq_mul] at ha hw ⊢
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  ring_nf
  field_simp
  assumption

/--
Definition of `charMonoidHom` / `charMonoidHom` 的定义

English:
definition charMonoidHom
  signature: (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
  body: char he hL w.toAdd
  map_one' := char_zero_eq_one
  map_mul' := char_add_eq_mul (he := he) (hL := hL)

中文:
定义 charMonoidHom
  签名: (he : 连续 e) (hL : 连续 fun p : V × W => L p.1 p.2)
  定义体: char he hL w.toAdd
  map_one' := char_zero_eq_one
  map_mul' := char_add_eq_mul (he := he) (hL := hL)

Depends on / 依赖: w.toAdd
-/
noncomputable def charMonoidHom (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) :
    Multiplicative W ->* (V ->ᵇ Complex) where
  toFun w := char he hL w.toAdd
  map_one' := char_zero_eq_one
  map_mul' := char_add_eq_mul (he := he) (hL := hL)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `charMonoidHom_apply` / 引理 `charMonoidHom_apply`

English:
lemma charMonoidHom_apply
  given: (w : Multiplicative W) (v : V)
  proof: by simp [charMonoidHom]

中文:
引理 charMonoidHom_apply
  条件: (w : Multiplicative W) (v : V)
  证明: by simp [charMonoidHom]

Depends on / 依赖: charMonoidHom
-/
lemma charMonoidHom_apply (w : Multiplicative W) (v : V) :
    charMonoidHom he hL w v = e (L v w.toAdd) := by simp [charMonoidHom]

/-- Algebra homomorphism mapping `w` to `fun v ↦ e (L v w)`. -/
noncomputable
/--
Definition of `charAlgHom` / `charAlgHom` 的定义

English:
definition charAlgHom
  signature: (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
  body: AddMonoidAlgebra.lift Complex (V ->ᵇ Complex) W (charMonoidHom he hL)

@[simp]

中文:
定义 charAlgHom
  签名: (he : 连续 e) (hL : 连续 fun p : V × W => L p.1 p.2)
  定义体: AddMonoidAlgebra.lift Complex (V ->ᵇ Complex) W (charMonoidHom he hL)

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.lift, charMonoidHom
-/
def charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) :
    AddMonoidAlgebra Complex W ->ₐ[Complex] (V ->ᵇ Complex) :=
  AddMonoidAlgebra.lift Complex (V ->ᵇ Complex) W (charMonoidHom he hL)

@[simp]
/--
lemma `charAlgHom_apply` / 引理 `charAlgHom_apply`

English:
lemma charAlgHom_apply
  given: (w : AddMonoidAlgebra Complex W) (v : V)
  proof: by
  simp [charAlgHom, charMonoidHom, char, AddMonoidAlgebra.lift_apply]
  simp [Finsupp.sum]

中文:
引理 charAlgHom_apply
  条件: (w : 加法幺半群代数 复形 W) (v : V)
  证明: by
  simp [charAlgHom, charMonoidHom, char, AddMonoidAlgebra.lift_apply]
  simp [Finsupp.sum]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.lift_apply, Finsupp, Finsupp.sum, charAlgHom, charMonoidHom, lift_apply
-/
lemma charAlgHom_apply (w : AddMonoidAlgebra Complex W) (v : V) :
    charAlgHom he hL w v = w.coeff.sum (fun a z => z • (e (L v a) : Complex)) := by
  simp [charAlgHom, charMonoidHom, char, AddMonoidAlgebra.lift_apply]
  simp [Finsupp.sum]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `star_mem_range_charAlgHom` / 引理 `star_mem_range_charAlgHom`

English:
lemma star_mem_range_charAlgHom
  statement: (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
  proof: by
  simp only [AlgHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  let z := y.map (starRingEnd _).toAddMonoidHom
  let f : W ↪ W := ⟨fun x => -x, (fun _ _ => neg_inj.mp)⟩
refine ⟨.ofCoeff z.coeff.embDomain f, ?_⟩
  ext
  simp [charAlgHom_apply, Finsupp.sum_embDomain, z, Finsupp.sum_mapRange_index, f]

中文:
引理 star_mem_range_charAlgHom
  结论: (he : 连续 e) (hL : 连续 fun p : V × W => L p.1 p.2)
  证明: by
  simp only [AlgHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  let z := y.map (starRingEnd _).toAddMonoidHom
  let f : W ↪ W := ⟨fun x => -x, (fun _ _ => neg_inj.mp)⟩
refine ⟨.ofCoeff z.coeff.embDomain f, ?_⟩
  ext
  simp [charAlgHom_apply, Finsupp.sum_embDomain, z, Finsupp.sum_mapRange_index, f]

Depends on / 依赖: AlgHom, AlgHom.mem_range, Finsupp, Finsupp.sum_embDomain, Finsupp.sum_mapRange_index, charAlgHom_apply, embDomain, mem_range, neg_inj, neg_inj.mp, ofCoeff, starRingEnd, sum_embDomain, sum_mapRange_index, toAddMonoidHom, y.map, z.coeff.embDomain
-/
lemma star_mem_range_charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
    {x : V ->ᵇ Complex} (hx : x in (charAlgHom he hL).range) :
    star x in (charAlgHom he hL).range := by
  simp only [AlgHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  let z := y.map (starRingEnd _).toAddMonoidHom
  let f : W ↪ W := ⟨fun x => -x, (fun _ _ => neg_inj.mp)⟩
refine ⟨.ofCoeff z.coeff.embDomain f, ?_⟩
  ext
  simp [charAlgHom_apply, Finsupp.sum_embDomain, z, Finsupp.sum_mapRange_index, f]

/-- The star-subalgebra of polynomials. -/
noncomputable
/--
Definition of `charPoly` / `charPoly` 的定义

English:
definition charPoly
  signature: (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
  body: (charAlgHom he hL).range
  star_mem' hx := star_mem_range_charAlgHom he hL hx

中文:
定义 charPoly
  签名: (he : 连续 e) (hL : 连续 fun p : V × W => L p.1 p.2)
  定义体: (charAlgHom he hL).range
  star_mem' hx := star_mem_range_charAlgHom he hL hx

Depends on / 依赖: charAlgHom
-/
def charPoly (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) :
    StarSubalgebra Complex (V ->ᵇ Complex) where
  toSubalgebra := (charAlgHom he hL).range
  star_mem' hx := star_mem_range_charAlgHom he hL hx

/--
lemma `mem_charPoly` / 引理 `mem_charPoly`

English:
lemma mem_charPoly
  given: (f : V ->ᵇ Complex)
  proof: by
  change f in (charAlgHom he hL).range ↔ _
  simp [BoundedContinuousFunction.ext_iff, funext_iff, eq_comm]

中文:
引理 mem_charPoly
  条件: (f : V ->ᵇ 复形)
  证明: by
  change f in (charAlgHom he hL).range ↔ _
  simp [BoundedContinuousFunction.ext_iff, funext_iff, eq_comm]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.ext_iff, charAlgHom, eq_comm, ext_iff, funext_iff
-/
lemma mem_charPoly (f : V ->ᵇ Complex) :
    f in charPoly he hL
      ↔ exists w : AddMonoidAlgebra Complex W, f = fun x => w.coeff.sum (fun a z => z * (e (L x a) : Complex)) := by
  change f in (charAlgHom he hL).range ↔ _
  simp [BoundedContinuousFunction.ext_iff, funext_iff, eq_comm]

/--
lemma `char_mem_charPoly` / 引理 `char_mem_charPoly`

English:
lemma char_mem_charPoly
  given: (w : W)
  statement: char he hL w in charPoly he hL
  proof: ⟨.single w 1, by ext; simp⟩

中文:
引理 char_mem_charPoly
  条件: (w : W)
  结论: char he hL w in charPoly he hL
  证明: ⟨.single w 1, by ext; simp⟩

Depends on / 依赖: single
-/
lemma char_mem_charPoly (w : W) : char he hL w in charPoly he hL := ⟨.single w 1, by ext; simp⟩

/--
lemma `separatesPoints_charPoly` / 引理 `separatesPoints_charPoly`

English:
lemma separatesPoints_charPoly
  statement: (he : Continuous e) (he' : e != 1)
  proof: by
  intro v v' hvv'
  obtain ⟨w, hw⟩ : exists w, char he hL w v != char he hL w v' := by
    contrapose! hvv'
    exact ext_of_char_eq he he' hL hL' hvv'
  use char he hL w
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  exact ⟨⟨char he hL w, char_mem_charPoly w, rfl⟩, hw⟩

中文:
引理 separatesPoints_charPoly
  结论: (he : 连续 e) (he' : e != 1)
  证明: by
  intro v v' hvv'
  obtain ⟨w, hw⟩ : exists w, char he hL w v != char he hL w v' := by
    contrapose! hvv'
    exact ext_of_char_eq he he' hL hL' hvv'
  use char he hL w
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  exact ⟨⟨char he hL w, char_mem_charPoly w, rfl⟩, hw⟩

Depends on / 依赖: Set.mem_image, SetLike, SetLike.mem_coe, StarSubalgebra, StarSubalgebra.coe_map, StarSubalgebra.coe_toSubalgebra, char_mem_charPoly, coe_map, coe_toSubalgebra, contrapose, exists_exists_and_eq_and, ext_of_char_eq, mem_coe, mem_image, ne_eq
-/
lemma separatesPoints_charPoly (he : Continuous e) (he' : e != 1)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hL' : forall v != 0, L v != 0) :
    ((charPoly he hL).map (toContinuousMapStarₐ Complex)).SeparatesPoints := by
  intro v v' hvv'
  obtain ⟨w, hw⟩ : exists w, char he hL w v != char he hL w v' := by
    contrapose! hvv'
    exact ext_of_char_eq he he' hL hL' hvv'
  use char he hL w
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  exact ⟨⟨char he hL w, char_mem_charPoly w, rfl⟩, hw⟩

end BoundedContinuousFunction
