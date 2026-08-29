/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Contraction in Clifford Algebras

This file contains some of the results from [grinberg_clifford_2016].
The key result is `CliffordAlgebra.equivExterior`.

## Main definitions

* `CliffordAlgebra.contractLeft`: contract a multivector by a `Module.Dual R M` on the left.
* `CliffordAlgebra.contractRight`: contract a multivector by a `Module.Dual R M` on the right.
* `CliffordAlgebra.changeForm`: convert between two algebras of different quadratic forms, sending
  vectors to vectors. The difference of the quadratic forms must be a bilinear form.
* `CliffordAlgebra.equivExterior`: in characteristic not-two, the `CliffordAlgebra Q` is
  isomorphic as a module to the exterior algebra.

## Implementation notes

This file somewhat follows [grinberg_clifford_2016], although we are missing some of the induction
principles needed to prove many of the results. Here, we avoid the quotient-based approach described
in [grinberg_clifford_2016], instead directly constructing our objects using the universal
property.

Note that [grinberg_clifford_2016] concludes that its contents are not novel, and are in fact just
a rehash of parts of [bourbaki2007]; we should at some point consider swapping our references to
refer to the latter.

Within this file, we use the local notation
* `x ⌊ d` for `contractRight x d`
* `d ⌋ x` for `contractLeft d x`

-/

@[expose] public section

open LinearMap (BilinMap BilinForm)

universe u1 u2 u3

variable {R : Type u1} [CommRing R]
variable {M : Type u2} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section contractLeft

variable (d d' : Module.Dual R M)

set_option backward.isDefEq.respectTransparency false in -- This is needed below
/-- Auxiliary construction for `CliffordAlgebra.contractLeft` -/
@[simps!]
/--
Definition of `contractLeftAux` / `contractLeftAux` 的定义

English:
definition contractLeftAux
  signature: (d : Module.Dual R M)
  body: haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  d.smulRight (LinearMap.fst _ (CliffordAlgebra Q) (CliffordAlgebra Q)) -
    v_mul.compl₂ (LinearMap.snd _ (CliffordAlgebra Q) _)

中文:
定义 contractLeftAux
  签名: (d : 模.对偶 R M)
  定义体: haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  d.smulRight (LinearMap.fst _ (CliffordAlgebra Q) (CliffordAlgebra Q)) -
    v_mul.compl₂ (LinearMap.snd _ (CliffordAlgebra Q) _)

Depends on / 依赖: Algebra, Algebra.lmul, CliffordAlgebra, LinearMap, LinearMap.fst, LinearMap.snd, d.smulRight, smulRight, toLinearMap, v_mul, v_mul.compl
-/
def contractLeftAux (d : Module.Dual R M) :
    M ->ₗ[R] CliffordAlgebra Q × CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  d.smulRight (LinearMap.fst _ (CliffordAlgebra Q) (CliffordAlgebra Q)) -
    v_mul.compl₂ (LinearMap.snd _ (CliffordAlgebra Q) _)

/--
theorem `contractLeftAux_contractLeftAux` / 定理 `contractLeftAux_contractLeftAux`

English:
theorem contractLeftAux_contractLeftAux
  given: (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q)
  proof: by
  simp only [contractLeftAux_apply_apply]
  rw [mul_sub]; rw [← mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [← sub_add]; rw [mul_smul_comm]; rw [sub_self]; rw [zero_add]

中文:
定理 contractLeftAux_contractLeftAux
  条件: (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q)
  证明: by
  simp only [contractLeftAux_apply_apply]
  rw [mul_sub]; rw [← mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [← sub_add]; rw [mul_smul_comm]; rw [sub_self]; rw [zero_add]

Depends on / 依赖: Algebra, Algebra.smul_def, contractLeftAux_apply_apply, mul_assoc, mul_smul_comm, mul_sub, smul_def, sub_add, sub_self, zero_add
-/
theorem contractLeftAux_contractLeftAux (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q) :
    contractLeftAux Q d v (ι Q v * x, contractLeftAux Q d v (x, fx)) = Q v • fx := by
  simp only [contractLeftAux_apply_apply]
  rw [mul_sub]; rw [← mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [← sub_add]; rw [mul_smul_comm]; rw [sub_self]; rw [zero_add]

variable {Q}

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `contractLeft` / `contractLeft` 的定义

English:
definition contractLeft
  signature: : Module.Dual R M ->ₗ[R] CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q where
  body: foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0
  map_add' d₁ d₂ :=
    LinearMap.ext fun x => by
      rw [LinearMap.add_apply]
      induction x using CliffordAlgebra.left_induction with
      | algebraMap => simp_rw [foldr'_algebraMap, smul_zero, zero_add]
      | add _ _ h

中文:
定义 contractLeft
  签名: : 模.对偶 R M ->ₗ[R] CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q where
  定义体: foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0
  map_add' d₁ d₂ :=
    LinearMap.ext fun x => by
      rw [LinearMap.add_apply]
      induction x using CliffordAlgebra.left_induction with
      | algebraMap => simp_rw [foldr'_algebraMap, smul_zero, zero_add]
      | add _ _ h

Depends on / 依赖: contractLeftAux, contractLeftAux_contractLeftAux
-/
def contractLeft : Module.Dual R M ->ₗ[R] CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q where
  toFun d := foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0
  map_add' d₁ d₂ :=
    LinearMap.ext fun x => by
      rw [LinearMap.add_apply]
      induction x using CliffordAlgebra.left_induction with
      | algebraMap => simp_rw [foldr'_algebraMap, smul_zero, zero_add]
      | add _ _ hx hy => rw [map_add, map_add, map_add, add_add_add_comm, hx, hy]
      | ι_mul _ _ hx =>
        rw [foldr'_ι_mul]; rw [foldr'_ι_mul]; rw [foldr'_ι_mul]; rw [hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [sub_add_sub_comm]; rw [mul_add]; rw [LinearMap.add_apply]; rw [add_smul]
  map_smul' c d :=
    LinearMap.ext fun x => by
      rw [LinearMap.smul_apply]; rw [RingHom.id_apply]
      induction x using CliffordAlgebra.left_induction with
      | algebraMap => simp_rw [foldr'_algebraMap, smul_zero]
      | add _ _ hx hy => rw [map_add, map_add, smul_add, hx, hy]
      | ι_mul _ _ hx =>
        rw [foldr'_ι_mul]; rw [foldr'_ι_mul]; rw [hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [LinearMap.smul_apply]; rw [smul_assoc]; rw [mul_smul_comm]; rw [smul_sub]

/--
Definition of `contractRight` / `contractRight` 的定义

English:
definition contractRight
  signature: : CliffordAlgebra Q ->ₗ[R] Module.Dual R M ->ₗ[R] CliffordAlgebra Q
  body: LinearMap.flip (LinearMap.compl₂ (LinearMap.compr₂ contractLeft reverse) reverse)

中文:
定义 contractRight
  签名: : CliffordAlgebra Q ->ₗ[R] 模.对偶 R M ->ₗ[R] CliffordAlgebra Q
  定义体: LinearMap.flip (LinearMap.compl₂ (LinearMap.compr₂ contractLeft reverse) reverse)

Depends on / 依赖: LinearMap, LinearMap.compl, LinearMap.compr, LinearMap.flip, contractLeft, reverse
-/
def contractRight : CliffordAlgebra Q ->ₗ[R] Module.Dual R M ->ₗ[R] CliffordAlgebra Q :=
  LinearMap.flip (LinearMap.compl₂ (LinearMap.compr₂ contractLeft reverse) reverse)

/--
theorem `contractRight_eq` / 定理 `contractRight_eq`

English:
theorem contractRight_eq
  given: (x : CliffordAlgebra Q)
  proof: rfl

local infixl:70 "⌋" => contractLeft (R := R) (M := M)

local infixl:70 "⌊" => contractRight (R := R) (M := M) (Q := Q)

中文:
定理 contractRight_eq
  条件: (x : CliffordAlgebra Q)
  证明: rfl

local infixl:70 "⌋" => contractLeft (R := R) (M := M)

local infixl:70 "⌊" => contractRight (R := R) (M := M) (Q := Q)

Depends on / 依赖: contractLeft, reverse
-/
theorem contractRight_eq (x : CliffordAlgebra Q) :
    contractRight (Q := Q) x d = reverse (contractLeft (R := R) (M := M) d <| reverse x) :=
  rfl

local infixl:70 "⌋" => contractLeft (R := R) (M := M)

local infixl:70 "⌊" => contractRight (R := R) (M := M) (Q := Q)

/--
theorem `contractLeft_ι_mul` / 定理 `contractLeft_ι_mul`

English:
theorem contractLeft_ι_mul
  given: (a : M) (b : CliffordAlgebra Q)
  proof: by

中文:
定理 contractLeft_ι_mul
  条件: (a : M) (b : CliffordAlgebra Q)
  证明: by
-/
theorem contractLeft_ι_mul (a : M) (b : CliffordAlgebra Q) :
    d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b) := by
-- Porting note: Lean cannot figure out anymore the third argument
  refine foldr'_ι_mul _ _ ?_ _ _ _
  exact fun m x fx => contractLeftAux_contractLeftAux Q d m x fx

/--
theorem `contractRight_mul_ι` / 定理 `contractRight_mul_ι`

English:
theorem contractRight_mul_ι
  given: (a : M) (b : CliffordAlgebra Q)
  proof: by
  rw [contractRight_eq]; rw [reverse.map_mul]; rw [reverse_ι]; rw [contractLeft_ι_mul]; rw [map_sub]; rw [map_smul]; rw [reverse_reverse]; rw [reverse.map_mul]; rw [reverse_ι]; rw [contractRight_eq]

中文:
定理 contractRight_mul_ι
  条件: (a : M) (b : CliffordAlgebra Q)
  证明: by
  rw [contractRight_eq]; rw [reverse.map_mul]; rw [reverse_ι]; rw [contractLeft_ι_mul]; rw [map_sub]; rw [map_smul]; rw [reverse_reverse]; rw [reverse.map_mul]; rw [reverse_ι]; rw [contractRight_eq]

Depends on / 依赖: contractRight_eq, map_mul, map_smul, map_sub, reverse, reverse.map_mul, reverse_reverse
-/
theorem contractRight_mul_ι (a : M) (b : CliffordAlgebra Q) :
    b * ι Q a⌊d = d a • b - b⌊d * ι Q a := by
  rw [contractRight_eq]; rw [reverse.map_mul]; rw [reverse_ι]; rw [contractLeft_ι_mul]; rw [map_sub]; rw [map_smul]; rw [reverse_reverse]; rw [reverse.map_mul]; rw [reverse_ι]; rw [contractRight_eq]

/--
theorem `contractLeft_algebraMap_mul` / 定理 `contractLeft_algebraMap_mul`

English:
theorem contractLeft_algebraMap_mul
  given: (r : R) (b : CliffordAlgebra Q)
  proof: by
  rw [← Algebra.smul_def]; rw [map_smul]; rw [Algebra.smul_def]

中文:
定理 contractLeft_algebraMap_mul
  条件: (r : R) (b : CliffordAlgebra Q)
  证明: by
  rw [← Algebra.smul_def]; rw [map_smul]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, map_smul, smul_def
-/
theorem contractLeft_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    d⌋(algebraMap _ _ r * b) = algebraMap _ _ r * (d⌋b) := by
  rw [← Algebra.smul_def]; rw [map_smul]; rw [Algebra.smul_def]

/--
theorem `contractLeft_mul_algebraMap` / 定理 `contractLeft_mul_algebraMap`

English:
theorem contractLeft_mul_algebraMap
  given: (a : CliffordAlgebra Q) (r : R)
  proof: by
  rw [← Algebra.commutes]; rw [contractLeft_algebraMap_mul]; rw [Algebra.commutes]

中文:
定理 contractLeft_mul_algebraMap
  条件: (a : CliffordAlgebra Q) (r : R)
  证明: by
  rw [← Algebra.commutes]; rw [contractLeft_algebraMap_mul]; rw [Algebra.commutes]

Depends on / 依赖: Algebra, Algebra.commutes, commutes, contractLeft_algebraMap_mul
-/
theorem contractLeft_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    d⌋(a * algebraMap _ _ r) = d⌋a * algebraMap _ _ r := by
  rw [← Algebra.commutes]; rw [contractLeft_algebraMap_mul]; rw [Algebra.commutes]

/--
theorem `contractRight_algebraMap_mul` / 定理 `contractRight_algebraMap_mul`

English:
theorem contractRight_algebraMap_mul
  given: (r : R) (b : CliffordAlgebra Q)
  proof: by
  rw [← Algebra.smul_def]; rw [LinearMap.map_smul₂]; rw [Algebra.smul_def]

中文:
定理 contractRight_algebraMap_mul
  条件: (r : R) (b : CliffordAlgebra Q)
  证明: by
  rw [← Algebra.smul_def]; rw [LinearMap.map_smul₂]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, LinearMap, LinearMap.map_smul, smul_def
-/
theorem contractRight_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    algebraMap _ _ r * b⌊d = algebraMap _ _ r * (b⌊d) := by
  rw [← Algebra.smul_def]; rw [LinearMap.map_smul₂]; rw [Algebra.smul_def]

/--
theorem `contractRight_mul_algebraMap` / 定理 `contractRight_mul_algebraMap`

English:
theorem contractRight_mul_algebraMap
  given: (a : CliffordAlgebra Q) (r : R)
  proof: by
  rw [← Algebra.commutes]; rw [contractRight_algebraMap_mul]; rw [Algebra.commutes]

中文:
定理 contractRight_mul_algebraMap
  条件: (a : CliffordAlgebra Q) (r : R)
  证明: by
  rw [← Algebra.commutes]; rw [contractRight_algebraMap_mul]; rw [Algebra.commutes]

Depends on / 依赖: Algebra, Algebra.commutes, commutes, contractRight_algebraMap_mul
-/
theorem contractRight_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    a * algebraMap _ _ r⌊d = a⌊d * algebraMap _ _ r := by
  rw [← Algebra.commutes]; rw [contractRight_algebraMap_mul]; rw [Algebra.commutes]

variable (Q)

@[simp]
/--
theorem `contractLeft_ι` / 定理 `contractLeft_ι`

English:
theorem contractLeft_ι
  given: (x : M)
  statement: d⌋ι Q x = algebraMap R _ (d x)
  proof: by

中文:
定理 contractLeft_ι
  条件: (x : M)
  结论: d⌋ι Q x = algebraMap R _ (d x)
  证明: by
-/
theorem contractLeft_ι (x : M) : d⌋ι Q x = algebraMap R _ (d x) := by
-- Porting note: Lean cannot figure out anymore the third argument
refine (foldr'_ι _ _ ?_ _ _).trans by
    simp_rw [contractLeftAux_apply_apply, mul_zero, sub_zero,
      Algebra.algebraMap_eq_smul_one]
  exact fun m x fx => contractLeftAux_contractLeftAux Q d m x fx

@[simp]
/--
theorem `contractRight_ι` / 定理 `contractRight_ι`

English:
theorem contractRight_ι
  given: (x : M)
  statement: ι Q x⌊d = algebraMap R _ (d x)
  proof: by
  rw [contractRight_eq]; rw [reverse_ι]; rw [contractLeft_ι]; rw [reverse.commutes]

@[simp]

中文:
定理 contractRight_ι
  条件: (x : M)
  结论: ι Q x⌊d = algebraMap R _ (d x)
  证明: by
  rw [contractRight_eq]; rw [reverse_ι]; rw [contractLeft_ι]; rw [reverse.commutes]

@[simp]

Depends on / 依赖: commutes, contractRight_eq, reverse, reverse.commutes
-/
theorem contractRight_ι (x : M) : ι Q x⌊d = algebraMap R _ (d x) := by
  rw [contractRight_eq]; rw [reverse_ι]; rw [contractLeft_ι]; rw [reverse.commutes]

@[simp]
/--
theorem `contractLeft_algebraMap` / 定理 `contractLeft_algebraMap`

English:
theorem contractLeft_algebraMap
  given: (r : R)
  statement: d⌋algebraMap R (CliffordAlgebra Q) r = 0
  proof: by

中文:
定理 contractLeft_algebraMap
  条件: (r : R)
  结论: d⌋algebraMap R (CliffordAlgebra Q) r = 0
  证明: by
-/
theorem contractLeft_algebraMap (r : R) : d⌋algebraMap R (CliffordAlgebra Q) r = 0 := by
-- Porting note: Lean cannot figure out anymore the third argument
refine (foldr'_algebraMap _ _ ?_ _ _).trans smul_zero _
  exact fun m x fx => contractLeftAux_contractLeftAux Q d m x fx

@[simp]
/--
theorem `contractRight_algebraMap` / 定理 `contractRight_algebraMap`

English:
theorem contractRight_algebraMap
  given: (r : R)
  statement: algebraMap R (CliffordAlgebra Q) r⌊d = 0
  proof: by
  rw [contractRight_eq]; rw [reverse.commutes]; rw [contractLeft_algebraMap]; rw [map_zero]

@[simp]

中文:
定理 contractRight_algebraMap
  条件: (r : R)
  结论: algebraMap R (CliffordAlgebra Q) r⌊d = 0
  证明: by
  rw [contractRight_eq]; rw [reverse.commutes]; rw [contractLeft_algebraMap]; rw [map_zero]

@[simp]

Depends on / 依赖: commutes, contractLeft_algebraMap, contractRight_eq, map_zero, reverse, reverse.commutes
-/
theorem contractRight_algebraMap (r : R) : algebraMap R (CliffordAlgebra Q) r⌊d = 0 := by
  rw [contractRight_eq]; rw [reverse.commutes]; rw [contractLeft_algebraMap]; rw [map_zero]

@[simp]
/--
theorem `contractLeft_one` / 定理 `contractLeft_one`

English:
theorem contractLeft_one
  statement: d⌋(1 : CliffordAlgebra Q) = 0
  proof: by
  simpa only [map_one] using contractLeft_algebraMap Q d 1

@[simp]

中文:
定理 contractLeft_one
  结论: d⌋(1 : CliffordAlgebra Q) = 0
  证明: by
  simpa only [map_one] using contractLeft_algebraMap Q d 1

@[simp]

Depends on / 依赖: contractLeft_algebraMap, map_one
-/
theorem contractLeft_one : d⌋(1 : CliffordAlgebra Q) = 0 := by
  simpa only [map_one] using contractLeft_algebraMap Q d 1

@[simp]
/--
theorem `contractRight_one` / 定理 `contractRight_one`

English:
theorem contractRight_one
  statement: (1 : CliffordAlgebra Q)⌊d = 0
  proof: by
  simpa only [map_one] using contractRight_algebraMap Q d 1

中文:
定理 contractRight_one
  结论: (1 : CliffordAlgebra Q)⌊d = 0
  证明: by
  simpa only [map_one] using contractRight_algebraMap Q d 1

Depends on / 依赖: contractRight_algebraMap, map_one
-/
theorem contractRight_one : (1 : CliffordAlgebra Q)⌊d = 0 := by
  simpa only [map_one] using contractRight_algebraMap Q d 1

variable {Q}

/--
theorem `contractLeft_contractLeft` / 定理 `contractLeft_contractLeft`

English:
theorem contractLeft_contractLeft
  given: (x : CliffordAlgebra Q)
  statement: d⌋(d⌋x) = 0
  proof: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | ι_mul _ _ hx =>
    rw [contractLeft_ι_mul]; rw [map_sub]; rw [contractLeft_ι_mul]; rw [hx]; rw [map_smul]; rw [mu

中文:
定理 contractLeft_contractLeft
  条件: (x : CliffordAlgebra Q)
  结论: d⌋(d⌋x) = 0
  证明: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | ι_mul _ _ hx =>
    rw [contractLeft_ι_mul]; rw [map_sub]; rw [contractLeft_ι_mul]; rw [hx]; rw [map_smul]; rw [mu

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.left_induction, add_zero, algebraMap, contractLeft_algebraMap, left_induction, map_add, map_smul, map_sub, map_zero, mul_zero, simp_rw, sub_self, sub_zero
-/
theorem contractLeft_contractLeft (x : CliffordAlgebra Q) : d⌋(d⌋x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | ι_mul _ _ hx =>
    rw [contractLeft_ι_mul]; rw [map_sub]; rw [contractLeft_ι_mul]; rw [hx]; rw [map_smul]; rw [mul_zero]; rw [sub_zero]; rw [sub_self]

/--
theorem `contractRight_contractRight` / 定理 `contractRight_contractRight`

English:
theorem contractRight_contractRight
  given: (x : CliffordAlgebra Q)
  statement: x⌊d⌊d = 0
  proof: by
  rw [contractRight_eq]; rw [contractRight_eq]; rw [reverse_reverse]; rw [contractLeft_contractLeft]; rw [map_zero]

中文:
定理 contractRight_contractRight
  条件: (x : CliffordAlgebra Q)
  结论: x⌊d⌊d = 0
  证明: by
  rw [contractRight_eq]; rw [contractRight_eq]; rw [reverse_reverse]; rw [contractLeft_contractLeft]; rw [map_zero]

Depends on / 依赖: contractLeft_contractLeft, contractRight_eq, map_zero, reverse_reverse
-/
theorem contractRight_contractRight (x : CliffordAlgebra Q) : x⌊d⌊d = 0 := by
  rw [contractRight_eq]; rw [contractRight_eq]; rw [reverse_reverse]; rw [contractLeft_contractLeft]; rw [map_zero]

/--
theorem `contractLeft_comm` / 定理 `contractLeft_comm`

English:
theorem contractLeft_comm
  given: (x : CliffordAlgebra Q)
  statement: d⌋(d'⌋x) = -(d'⌋(d⌋x))
  proof: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero, neg_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, map_sub, map_smul]
    rw [neg_sub];

中文:
定理 contractLeft_comm
  条件: (x : CliffordAlgebra Q)
  结论: d⌋(d'⌋x) = -(d'⌋(d⌋x))
  证明: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero, neg_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, map_sub, map_smul]
    rw [neg_sub];

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.left_induction, algebraMap, contractLeft_algebraMap, left_induction, map_add, map_smul, map_sub, map_zero, mul_neg, neg_add, neg_sub, neg_zero, simp_rw, sub_eq_add_neg, sub_sub_eq_add_sub
-/
theorem contractLeft_comm (x : CliffordAlgebra Q) : d⌋(d'⌋x) = -(d'⌋(d⌋x)) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero, neg_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, map_sub, map_smul]
    rw [neg_sub]; rw [sub_sub_eq_add_sub]; rw [hx]; rw [mul_neg]; rw [← sub_eq_add_neg]

/--
theorem `contractRight_comm` / 定理 `contractRight_comm`

English:
theorem contractRight_comm
  given: (x : CliffordAlgebra Q)
  statement: x⌊d⌊d' = -(x⌊d'⌊d)
  proof: by
  rw [contractRight_eq]; rw [contractRight_eq]; rw [contractRight_eq]; rw [contractRight_eq]; rw [reverse_reverse]; rw [reverse_reverse]; rw [contractLeft_comm]; rw [map_neg]

中文:
定理 contractRight_comm
  条件: (x : CliffordAlgebra Q)
  结论: x⌊d⌊d' = -(x⌊d'⌊d)
  证明: by
  rw [contractRight_eq]; rw [contractRight_eq]; rw [contractRight_eq]; rw [contractRight_eq]; rw [reverse_reverse]; rw [reverse_reverse]; rw [contractLeft_comm]; rw [map_neg]

Depends on / 依赖: contractLeft_comm, contractRight_eq, map_neg, reverse_reverse
-/
theorem contractRight_comm (x : CliffordAlgebra Q) : x⌊d⌊d' = -(x⌊d'⌊d) := by
  rw [contractRight_eq]; rw [contractRight_eq]; rw [contractRight_eq]; rw [contractRight_eq]; rw [reverse_reverse]; rw [reverse_reverse]; rw [contractLeft_comm]; rw [map_neg]

/- TODO:
lemma contractRight_contractLeft (x : CliffordAlgebra Q) : (d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d') :=
-/
end contractLeft

local infixl:70 "⌋" => contractLeft

local infixl:70 "⌊" => contractRight

/-- Auxiliary construction for `CliffordAlgebra.changeForm` -/
@[simps!]
/--
Definition of `changeFormAux` / `changeFormAux` 的定义

English:
definition changeFormAux
  signature: (B : BilinForm R M)
  body: haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  v_mul - contractLeft ∘ₗ B

中文:
定义 changeFormAux
  签名: (B : BilinForm R M)
  定义体: haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  v_mul - contractLeft ∘ₗ B

Depends on / 依赖: Algebra, Algebra.lmul, CliffordAlgebra, contractLeft, toLinearMap, v_mul
-/
def changeFormAux (B : BilinForm R M) : M ->ₗ[R] CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  v_mul - contractLeft ∘ₗ B

/--
theorem `changeFormAux_changeFormAux` / 定理 `changeFormAux_changeFormAux`

English:
theorem changeFormAux_changeFormAux
  given: (B : BilinForm R M) (v : M) (x : CliffordAlgebra Q)
  proof: by
  simp only [changeFormAux_apply_apply]
  rw [mul_sub]; rw [← mul_assoc]; rw [ι_sq_scalar]; rw [map_sub]; rw [contractLeft_ι_mul]; rw [← sub_add]; rw [sub_sub_sub_comm]; rw [← Algebra.smul_def]; rw [sub_self]; rw [sub_zero]; rw [contractLeft_contractLeft]; rw [add_zero]; rw [sub_smul]

中文:
定理 changeFormAux_changeFormAux
  条件: (B : BilinForm R M) (v : M) (x : CliffordAlgebra Q)
  证明: by
  simp only [changeFormAux_apply_apply]
  rw [mul_sub]; rw [← mul_assoc]; rw [ι_sq_scalar]; rw [map_sub]; rw [contractLeft_ι_mul]; rw [← sub_add]; rw [sub_sub_sub_comm]; rw [← Algebra.smul_def]; rw [sub_self]; rw [sub_zero]; rw [contractLeft_contractLeft]; rw [add_zero]; rw [sub_smul]

Depends on / 依赖: Algebra, Algebra.smul_def, add_zero, changeFormAux_apply_apply, contractLeft_contractLeft, map_sub, mul_assoc, mul_sub, smul_def, sub_add, sub_self, sub_smul, sub_sub_sub_comm, sub_zero
-/
theorem changeFormAux_changeFormAux (B : BilinForm R M) (v : M) (x : CliffordAlgebra Q) :
    changeFormAux Q B v (changeFormAux Q B v x) = (Q v - B v v) • x := by
  simp only [changeFormAux_apply_apply]
  rw [mul_sub]; rw [← mul_assoc]; rw [ι_sq_scalar]; rw [map_sub]; rw [contractLeft_ι_mul]; rw [← sub_add]; rw [sub_sub_sub_comm]; rw [← Algebra.smul_def]; rw [sub_self]; rw [sub_zero]; rw [contractLeft_contractLeft]; rw [add_zero]; rw [sub_smul]

variable {Q}
variable {Q' Q'' : QuadraticForm R M} {B B' : BilinForm R M}

/--
Definition of `changeForm` / `changeForm` 的定义

English:
definition changeForm
  signature: (h : B.toQuadraticMap = Q' - Q)
  body: foldr Q (changeFormAux Q' B)
    (fun m x =>
(changeFormAux_changeFormAux Q' B m x).trans by
        rw [← BilinMap.toQuadraticMap_apply]; rw [h]; rw [sub_apply]; rw [sub_sub_cancel])
    1

中文:
定义 changeForm
  签名: (h : B.toQuadraticMap = Q' - Q)
  定义体: foldr Q (changeFormAux Q' B)
    (fun m x =>
(changeFormAux_changeFormAux Q' B m x).trans by
        rw [← BilinMap.toQuadraticMap_apply]; rw [h]; rw [sub_apply]; rw [sub_sub_cancel])
    1

Depends on / 依赖: BilinMap, BilinMap.toQuadraticMap_apply, changeFormAux, changeFormAux_changeFormAux, sub_apply, sub_sub_cancel, toQuadraticMap_apply
-/
def changeForm (h : B.toQuadraticMap = Q' - Q) : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q' :=
  foldr Q (changeFormAux Q' B)
    (fun m x =>
(changeFormAux_changeFormAux Q' B m x).trans by
        rw [← BilinMap.toQuadraticMap_apply]; rw [h]; rw [sub_apply]; rw [sub_sub_cancel])
    1

/--
theorem `changeForm.zero_proof` / 定理 `changeForm.zero_proof`

English:
theorem changeForm.zero_proof
  statement: (0 : BilinForm R M).toQuadraticMap = Q - Q
  proof: (sub_self _).symm

中文:
定理 changeForm.zero_proof
  结论: (0 : BilinForm R M).toQuadraticMap = Q - Q
  证明: (sub_self _).symm

Depends on / 依赖: sub_self
-/
theorem changeForm.zero_proof : (0 : BilinForm R M).toQuadraticMap = Q - Q :=
  (sub_self _).symm

variable (h : B.toQuadraticMap = Q' - Q) (h' : B'.toQuadraticMap = Q'' - Q')

include h h' in
/--
theorem `changeForm.add_proof` / 定理 `changeForm.add_proof`

English:
theorem changeForm.add_proof
  statement: (B + B').toQuadraticMap = Q'' - Q
  proof: (congr_arg₂ (· + ·) h h').trans sub_add_sub_cancel' _ _ _

include h in

中文:
定理 changeForm.add_proof
  结论: (B + B').toQuadraticMap = Q'' - Q
  证明: (congr_arg₂ (· + ·) h h').trans sub_add_sub_cancel' _ _ _

include h in

Depends on / 依赖: sub_add_sub_cancel
-/
theorem changeForm.add_proof : (B + B').toQuadraticMap = Q'' - Q :=
(congr_arg₂ (· + ·) h h').trans sub_add_sub_cancel' _ _ _

include h in
/--
theorem `changeForm.neg_proof` / 定理 `changeForm.neg_proof`

English:
theorem changeForm.neg_proof
  statement: (-B).toQuadraticMap = Q - Q'
  proof: (congr_arg Neg.neg h).trans neg_sub _ _

中文:
定理 changeForm.neg_proof
  结论: (-B).toQuadraticMap = Q - Q'
  证明: (congr_arg Neg.neg h).trans neg_sub _ _

Depends on / 依赖: Neg.neg, congr_arg, neg_sub
-/
theorem changeForm.neg_proof : (-B).toQuadraticMap = Q - Q' :=
(congr_arg Neg.neg h).trans neg_sub _ _

/--
theorem `changeForm.associated_neg_proof` / 定理 `changeForm.associated_neg_proof`

English:
theorem changeForm.associated_neg_proof
  given: [Invertible (2 : R)]
  proof: by
  simp [QuadraticMap.toQuadraticMap_associated]

@[simp]

中文:
定理 changeForm.associated_neg_proof
  条件: [可逆 (2 : R)]
  证明: by
  simp [QuadraticMap.toQuadraticMap_associated]

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.toQuadraticMap_associated, toQuadraticMap, toQuadraticMap_associated
-/
theorem changeForm.associated_neg_proof [Invertible (2 : R)] :
    (QuadraticMap.associated (R := R) (M := M) (-Q)).toQuadraticMap = 0 - Q := by
  simp [QuadraticMap.toQuadraticMap_associated]

@[simp]
/--
theorem `changeForm_algebraMap` / 定理 `changeForm_algebraMap`

English:
theorem changeForm_algebraMap
  given: (r : R)
  statement: changeForm h (algebraMap R _ r) = algebraMap R _ r
  proof: (foldr_algebraMap _ _ _ _ _).trans Eq.symm Algebra.algebraMap_eq_smul_one r

@[simp]

中文:
定理 changeForm_algebraMap
  条件: (r : R)
  结论: changeForm h (algebraMap R _ r) = algebraMap R _ r
  证明: (foldr_algebraMap _ _ _ _ _).trans Eq.symm Algebra.algebraMap_eq_smul_one r

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Eq.symm, algebraMap_eq_smul_one, foldr_algebraMap
-/
theorem changeForm_algebraMap (r : R) : changeForm h (algebraMap R _ r) = algebraMap R _ r :=
(foldr_algebraMap _ _ _ _ _).trans Eq.symm Algebra.algebraMap_eq_smul_one r

@[simp]
/--
theorem `changeForm_one` / 定理 `changeForm_one`

English:
theorem changeForm_one
  statement: changeForm h (1 : CliffordAlgebra Q) = 1
  proof: by
  simpa using changeForm_algebraMap h (1 : R)

@[simp]

中文:
定理 changeForm_one
  结论: changeForm h (1 : CliffordAlgebra Q) = 1
  证明: by
  simpa using changeForm_algebraMap h (1 : R)

@[simp]

Depends on / 依赖: changeForm_algebraMap
-/
theorem changeForm_one : changeForm h (1 : CliffordAlgebra Q) = 1 := by
  simpa using changeForm_algebraMap h (1 : R)

@[simp]
/--
theorem `changeForm_ι` / 定理 `changeForm_ι`

English:
theorem changeForm_ι
  given: (m : M)
  statement: changeForm h (ι (M := M) Q m) = ι (M := M) Q' m
  proof: (foldr_ι _ _ _ _ _).trans
Eq.symm by rw [changeFormAux_apply_apply, mul_one, contractLeft_one, sub_zero]

中文:
定理 changeForm_ι
  条件: (m : M)
  结论: changeForm h (ι (M := M) Q m) = ι (M := M) Q' m
  证明: (foldr_ι _ _ _ _ _).trans
Eq.symm by rw [changeFormAux_apply_apply, mul_one, contractLeft_one, sub_zero]
-/
theorem changeForm_ι (m : M) : changeForm h (ι (M := M) Q m) = ι (M := M) Q' m :=
(foldr_ι _ _ _ _ _).trans
Eq.symm by rw [changeFormAux_apply_apply, mul_one, contractLeft_one, sub_zero]

/--
theorem `changeForm_ι_mul` / 定理 `changeForm_ι_mul`

English:
theorem changeForm_ι_mul
  given: (m : M) (x : CliffordAlgebra Q)
  proof: (foldr_mul _ _ _ _ _ _).trans by rw [foldr_ι]; rfl

中文:
定理 changeForm_ι_mul
  条件: (m : M) (x : CliffordAlgebra Q)
  证明: (foldr_mul _ _ _ _ _ _).trans by rw [foldr_ι]; rfl

Depends on / 依赖: foldr_mul
-/
theorem changeForm_ι_mul (m : M) (x : CliffordAlgebra Q) :
    changeForm h (ι Q m * x) = ι Q' m * changeForm h x - B m⌋changeForm h x :=
(foldr_mul _ _ _ _ _ _).trans by rw [foldr_ι]; rfl

/--
theorem `changeForm_ι_mul_ι` / 定理 `changeForm_ι_mul_ι`

English:
theorem changeForm_ι_mul_ι
  given: (m₁ m₂ : M)
  proof: by
  rw [changeForm_ι_mul]; rw [changeForm_ι]; rw [contractLeft_ι]

中文:
定理 changeForm_ι_mul_ι
  条件: (m₁ m₂ : M)
  证明: by
  rw [changeForm_ι_mul]; rw [changeForm_ι]; rw [contractLeft_ι]
-/
theorem changeForm_ι_mul_ι (m₁ m₂ : M) :
    changeForm h (ι Q m₁ * ι Q m₂) = ι Q' m₁ * ι Q' m₂ - algebraMap _ _ (B m₁ m₂) := by
  rw [changeForm_ι_mul]; rw [changeForm_ι]; rw [contractLeft_ι]

/--
theorem `changeForm_contractLeft` / 定理 `changeForm_contractLeft`

English:
theorem changeForm_contractLeft
  given: (d : Module.Dual R M) (x : CliffordAlgebra Q)
  proof: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp only [contractLeft_algebraMap, changeForm_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, changeForm_ι_mul, map_sub, map

中文:
定理 changeForm_contractLeft
  条件: (d : 模.对偶 R M) (x : CliffordAlgebra Q)
  证明: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp only [contractLeft_algebraMap, changeForm_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, changeForm_ι_mul, map_sub, map

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.left_induction, algebraMap, changeForm_algebraMap, contractLeft_algebraMap, contractLeft_comm, left_induction, map_add, map_smul, map_sub, map_zero, sub_add, sub_neg_eq_add
-/
theorem changeForm_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    changeForm h (d⌋x) = d⌋(changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp only [contractLeft_algebraMap, changeForm_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, changeForm_ι_mul, map_sub, map_smul]
    rw [← hx]; rw [contractLeft_comm]; rw [← sub_add]; rw [sub_neg_eq_add]; rw [← hx]

/--
theorem `changeForm_self_apply` / 定理 `changeForm_self_apply`

English:
theorem changeForm_self_apply
  given: (x : CliffordAlgebra Q)
  statement: changeForm (Q' := Q)
  proof: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]

@[simp]

中文:
定理 changeForm_self_apply
  条件: (x : CliffordAlgebra Q)
  结论: changeForm (Q' := Q)
  证明: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]

@[simp]
-/
theorem changeForm_self_apply (x : CliffordAlgebra Q) : changeForm (Q' := Q)
    changeForm.zero_proof x = x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]

@[simp]
/--
theorem `changeForm_self` / 定理 `changeForm_self`

English:
theorem changeForm_self
  proof: LinearMap.ext changeForm_self_apply

中文:
定理 changeForm_self
  证明: LinearMap.ext changeForm_self_apply

Depends on / 依赖: LinearMap, LinearMap.ext, changeForm_self_apply
-/
theorem changeForm_self :
    changeForm changeForm.zero_proof = (LinearMap.id : CliffordAlgebra Q ->ₗ[R] _) :=
LinearMap.ext changeForm_self_apply

/--
theorem `changeForm_changeForm` / 定理 `changeForm_changeForm`

English:
theorem changeForm_changeForm
  given: (x : CliffordAlgebra Q)
  proof: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, map_sub, changeForm_ι_mul, changeForm_ι_mul, hx, sub_sub,
      LinearMap.add_apply, map_

中文:
定理 changeForm_changeForm
  条件: (x : CliffordAlgebra Q)
  证明: by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, map_sub, changeForm_ι_mul, changeForm_ι_mul, hx, sub_sub,
      LinearMap.add_apply, map_

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.left_induction, LinearMap, LinearMap.add_apply, add_apply, add_comm, algebraMap, changeForm_algebraMap, changeForm_contractLeft, left_induction, map_add, map_sub, simp_rw, sub_sub
-/
theorem changeForm_changeForm (x : CliffordAlgebra Q) :
    changeForm h' (changeForm h x) = changeForm (changeForm.add_proof h h') x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, map_sub, changeForm_ι_mul, changeForm_ι_mul, hx, sub_sub,
      LinearMap.add_apply, map_add, LinearMap.add_apply, changeForm_contractLeft, hx,
      add_comm (_ : CliffordAlgebra Q'')]

/--
theorem `changeForm_comp_changeForm` / 定理 `changeForm_comp_changeForm`

English:
theorem changeForm_comp_changeForm
  proof: LinearMap.ext changeForm_changeForm _ h'

中文:
定理 changeForm_comp_changeForm
  证明: LinearMap.ext changeForm_changeForm _ h'

Depends on / 依赖: LinearMap, LinearMap.ext, changeForm_changeForm
-/
theorem changeForm_comp_changeForm :
    (changeForm h').comp (changeForm h) = changeForm (changeForm.add_proof h h') :=
LinearMap.ext changeForm_changeForm _ h'

/-- Any two algebras whose quadratic forms differ by a bilinear form are isomorphic as modules.

This is $\bar \lambda_B$ from [bourbaki2007] §9 Proposition 3. -/
@[simps apply]
/--
Definition of `changeFormEquiv` / `changeFormEquiv` 的定义

English:
definition changeFormEquiv
  signature: : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q'
  body: { changeForm h with
    toFun := changeForm h
    invFun := changeForm (changeForm.neg_proof h)
    left_inv := fun x => by
exact (changeForm_changeForm _ _ x).trans
        by simp_rw [(add_neg_cancel B), changeForm_self_apply]
    right_inv := fun x => by
exact (changeForm_changeForm _ _ x).trans


中文:
定义 changeFormEquiv
  签名: : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q'
  定义体: { changeForm h with
    toFun := changeForm h
    invFun := changeForm (changeForm.neg_proof h)
    left_inv := fun x => by
exact (changeForm_changeForm _ _ x).trans
        by simp_rw [(add_neg_cancel B), changeForm_self_apply]
    right_inv := fun x => by
exact (changeForm_changeForm _ _ x).trans


Depends on / 依赖: add_neg_cancel, changeForm, changeForm.neg_proof, changeForm_changeForm, changeForm_self_apply, invFun, left_inv, neg_add_cancel, neg_proof, right_inv, simp_rw
-/
def changeFormEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q' :=
  { changeForm h with
    toFun := changeForm h
    invFun := changeForm (changeForm.neg_proof h)
    left_inv := fun x => by
exact (changeForm_changeForm _ _ x).trans
        by simp_rw [(add_neg_cancel B), changeForm_self_apply]
    right_inv := fun x => by
exact (changeForm_changeForm _ _ x).trans
        by simp_rw [(neg_add_cancel B), changeForm_self_apply] }

@[simp]
/--
theorem `changeFormEquiv_symm` / 定理 `changeFormEquiv_symm`

English:
theorem changeFormEquiv_symm
  proof: LinearEquiv.ext fun _ => rfl

中文:
定理 changeFormEquiv_symm
  证明: LinearEquiv.ext fun _ => rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.ext
-/
theorem changeFormEquiv_symm :
    (changeFormEquiv h).symm = changeFormEquiv (changeForm.neg_proof h) :=
  LinearEquiv.ext fun _ => rfl

variable (Q)

/-- The module isomorphism to the exterior algebra.

Note that this holds more generally when `Q` is divisible by two, rather than only when `1` is
divisible by two; but that would be more awkward to use. -/
@[simp]
/--
Definition of `equivExterior` / `equivExterior` 的定义

English:
definition equivExterior
  signature: [Invertible (2 : R)]
  body: changeFormEquiv changeForm.associated_neg_proof

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/

中文:
定义 equivExterior
  签名: [可逆 (2 : R)]
  定义体: changeFormEquiv changeForm.associated_neg_proof

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/

Depends on / 依赖: associated_neg_proof, changeForm, changeForm.associated_neg_proof, changeFormEquiv
-/
def equivExterior [Invertible (2 : R)] : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M :=
  changeFormEquiv changeForm.associated_neg_proof

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] equivExterior.eq_1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] [Invertible (2 : R)] :
  body: (equivExterior Q).symm.injective.nontrivial

中文:
实例 [非平凡
  签名: R] [可逆 (2 : R)] :
  定义体: (equivExterior Q).symm.injective.nontrivial

Depends on / 依赖: equivExterior, injective, nontrivial, symm.injective.nontrivial
-/
instance [Nontrivial R] [Invertible (2 : R)] :
    Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial

end CliffordAlgebra
