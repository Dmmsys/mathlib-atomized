/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Wojciech Nawrocki
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.GroupTheory.Congruence.BigOperators
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Ideals in a matrix ring

This file defines left (resp. two-sided) ideals in a matrix semiring (resp. ring)
over left (resp. two-sided) ideals in the base semiring (resp. ring).
We also characterize Jacobson radicals of ideals in such rings.

## Main results

* `TwoSidedIdeal.equivMatrix` and `TwoSidedIdeal.orderIsoMatrix`
  establish an order isomorphism between two-sided ideals in $R$ and those in $Mₙ(R)$.
* `TwoSidedIdeal.jacobson_matrix` shows that $J(Mₙ(I)) = Mₙ(J(I))$
  for any two-sided ideal $I ≤ R$.
-/

@[expose] public section

/-! ### Left ideals in a matrix semiring -/

namespace Ideal
open Matrix

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (I : Ideal R)
  body: I.toAddSubmonoid.matrix
  smul_mem' M N hN := by
    intro i j
    rw [smul_eq_mul]; rw [mul_apply]
    apply sum_mem
    intro k _
    apply I.mul_mem_left _ (hN k j)

@[simp]

中文:
定义 matrix
  签名: (I : 理想 R)
  定义体: I.toAddSubmonoid.matrix
  smul_mem' M N hN := by
    intro i j
    rw [smul_eq_mul]; rw [mul_apply]
    apply sum_mem
    intro k _
    apply I.mul_mem_left _ (hN k j)

@[simp]

Depends on / 依赖: I.toAddSubmonoid.matrix, matrix, toAddSubmonoid
-/
def matrix (I : Ideal R) : Ideal (Matrix n n R) where
  __ := I.toAddSubmonoid.matrix
  smul_mem' M N hN := by
    intro i j
    rw [smul_eq_mul]; rw [mul_apply]
    apply sum_mem
    intro k _
    apply I.mul_mem_left _ (hN k j)

@[simp]
/--
theorem `mem_matrix` / 定理 `mem_matrix`

English:
theorem mem_matrix
  given: (I : Ideal R) (M : Matrix n n R)
  proof: by rfl

中文:
定理 mem_matrix
  条件: (I : 理想 R) (M : 矩阵 n n R)
  证明: by rfl
-/
theorem mem_matrix (I : Ideal R) (M : Matrix n n R) :
    M in I.matrix n ↔ forall i j, M i j in I := by rfl

/--
theorem `matrix_monotone` / 定理 `matrix_monotone`

English:
theorem matrix_monotone
  statement: Monotone (matrix (R := R) n)
  proof: fun _ _ IJ _ MI i j => IJ (MI i j)

中文:
定理 matrix_monotone
  结论: 递增 (matrix (R := R) n)
  证明: fun _ _ IJ _ MI i j => IJ (MI i j)
-/
theorem matrix_monotone : Monotone (matrix (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)

/--
theorem `matrix_strictMono_of_nonempty` / 定理 `matrix_strictMono_of_nonempty`

English:
theorem matrix_strictMono_of_nonempty
  given: [Nonempty n]
  proof: .strictMono_of_injective fun I J eq => by matrix_monotone n
    ext x
    have : (forall _ _, x in I) ↔ (forall _ _, x in J) := congr((Matrix.of fun _ _ => x) in $eq)
    simpa only [forall_const] using this

@[simp]

中文:
定理 matrix_strictMono_of_nonempty
  条件: [非空 n]
  证明: .strictMono_of_injective fun I J eq => by matrix_monotone n
    ext x
    have : (forall _ _, x in I) ↔ (forall _ _, x in J) := congr((Matrix.of fun _ _ => x) in $eq)
    simpa only [forall_const] using this

@[simp]
-/
theorem matrix_strictMono_of_nonempty [Nonempty n] :
    StrictMono (matrix (R := R) n) :=
.strictMono_of_injective fun I J eq => by matrix_monotone n
    ext x
    have : (forall _ _, x in I) ↔ (forall _ _, x in J) := congr((Matrix.of fun _ _ => x) in $eq)
    simpa only [forall_const] using this

@[simp]
/--
theorem `matrix_bot` / 定理 `matrix_bot`

English:
theorem matrix_bot
  statement: (⊥ : Ideal R).matrix n = ⊥
  proof: by
  ext M
  simp only [mem_matrix, mem_bot]
  constructor
  · intro H; ext; apply H
  · intro H; simp [H]

@[simp]

中文:
定理 matrix_bot
  结论: (⊥ : 理想 R).matrix n = ⊥
  证明: by
  ext M
  simp only [mem_matrix, mem_bot]
  constructor
  · intro H; ext; apply H
  · intro H; simp [H]

@[simp]

Depends on / 依赖: mem_bot, mem_matrix
-/
theorem matrix_bot : (⊥ : Ideal R).matrix n = ⊥ := by
  ext M
  simp only [mem_matrix, mem_bot]
  constructor
  · intro H; ext; apply H
  · intro H; simp [H]

@[simp]
/--
theorem `matrix_top` / 定理 `matrix_top`

English:
theorem matrix_top
  statement: (⊤ : Ideal R).matrix n = ⊤
  proof: by
  ext; simp

中文:
定理 matrix_top
  结论: (⊤ : 理想 R).matrix n = ⊤
  证明: by
  ext; simp
-/
theorem matrix_top : (⊤ : Ideal R).matrix n = ⊤ := by
  ext; simp

end Ideal

/-! ### Jacobson radicals of left ideals in a matrix ring -/

namespace Ideal
open Matrix

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

/--
theorem `single_mem_jacobson_matrix` / 定理 `single_mem_jacobson_matrix`

English:
theorem single_mem_jacobson_matrix
  given: (I : Ideal R)
  proof: by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  simp_rw [Ideal.mem_jacobson_iff]
  intro x xIJ p q M
  have ⟨z, zMx⟩ := xIJ (M q p)
  let N : Matrix n n R := 1 - ∑ i, single i q (if i = q then 1 - z else (M i p) * x * z)
  use N
  intro i j
  obtain rfl | qj := eq_or_ne q j
  · by_cases iq : i = q
    · simp [iq, N, zMx, single, mul_apply, sum_apply, ite_and, sub_mul]
    · convert! I.mul_mem_left (-M i p * x) zMx
      simp [iq, N, single, mul_apply, sum_apply, ite_and, sub_mul]
      simp [sub_add, mul_add, mul_sub, mul_assoc]
  · simp [N, qj, sum_apply, mul_apply]

中文:
定理 single_mem_jacobson_matrix
  条件: (I : 理想 R)
  证明: by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  simp_rw [Ideal.mem_jacobson_iff]
  intro x xIJ p q M
  have ⟨z, zMx⟩ := xIJ (M q p)
  let N : Matrix n n R := 1 - ∑ i, single i q (if i = q then 1 - z else (M i p) * x * z)
  use N
  intro i j
  obtain rfl | qj := eq_or_ne q j
  · by_cases iq : i = q
    · simp [iq, N, zMx, single, mul_apply, sum_apply, ite_and, sub_mul]
    · convert! I.mul_mem_left (-M i p * x) zMx
      simp [iq, N, single, mul_apply, sum_apply, ite_and, sub_mul]
      simp [sub_add, mul_add, mul_sub, mul_assoc]
  · simp [N, qj, sum_apply, mul_apply]
-/
theorem single_mem_jacobson_matrix (I : Ideal R) :
    forall x in I.jacobson, forall (i j : n), single i j x in (I.matrix n).jacobson := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  simp_rw [Ideal.mem_jacobson_iff]
  intro x xIJ p q M
  have ⟨z, zMx⟩ := xIJ (M q p)
  let N : Matrix n n R := 1 - ∑ i, single i q (if i = q then 1 - z else (M i p) * x * z)
  use N
  intro i j
  obtain rfl | qj := eq_or_ne q j
  · by_cases iq : i = q
    · simp [iq, N, zMx, single, mul_apply, sum_apply, ite_and, sub_mul]
    · convert! I.mul_mem_left (-M i p * x) zMx
      simp [iq, N, single, mul_apply, sum_apply, ite_and, sub_mul]
      simp [sub_add, mul_add, mul_sub, mul_assoc]
  · simp [N, qj, sum_apply, mul_apply]

/--
theorem `matrix_jacobson_le` / 定理 `matrix_jacobson_le`

English:
theorem matrix_jacobson_le
  given: (I : Ideal R)
  proof: by
  intro M MI
  rw [matrix_eq_sum_single M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  apply single_mem_jacobson_matrix I _ (MI i j)

中文:
定理 matrix_jacobson_le
  条件: (I : 理想 R)
  证明: by
  intro M MI
  rw [matrix_eq_sum_single M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  apply single_mem_jacobson_matrix I _ (MI i j)

Depends on / 依赖: matrix_eq_sum_single, single_mem_jacobson_matrix, sum_mem
-/
theorem matrix_jacobson_le (I : Ideal R) :
    I.jacobson.matrix n <= (I.matrix n).jacobson := by
  intro M MI
  rw [matrix_eq_sum_single M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  apply single_mem_jacobson_matrix I _ (MI i j)

end Ideal

/-! ### Two-sided ideals in a matrix ring -/

namespace RingCon
variable {R n : Type*}

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] [Fintype n]
variable (n)

/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (c : RingCon R)
  body: forall i j, c (M i j) (N i j)
  -- note: kept `fun` to distinguish `RingCon`'s binders from `r`'s binders.
  iseqv.refl _ := fun _ _ => c.refl _
iseqv.symm h := fun _ _ => c.symm h _ _
  iseqv.trans h₁ h₂ := fun _ _ => c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ => c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun _ _ => c.finsetSum _ fun _ _ => c.mul (h₁ _ _) (h₂ _ _)

@[simp low]

中文:
定义 matrix
  签名: (c : RingCon R)
  定义体: forall i j, c (M i j) (N i j)
  -- note: kept `fun` to distinguish `RingCon`'s binders from `r`'s binders.
  iseqv.refl _ := fun _ _ => c.refl _
iseqv.symm h := fun _ _ => c.symm h _ _
  iseqv.trans h₁ h₂ := fun _ _ => c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ => c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun _ _ => c.finsetSum _ fun _ _ => c.mul (h₁ _ _) (h₂ _ _)

@[simp low]
-/
def matrix (c : RingCon R) : RingCon (Matrix n n R) where
  r M N := forall i j, c (M i j) (N i j)
  -- note: kept `fun` to distinguish `RingCon`'s binders from `r`'s binders.
  iseqv.refl _ := fun _ _ => c.refl _
iseqv.symm h := fun _ _ => c.symm h _ _
  iseqv.trans h₁ h₂ := fun _ _ => c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ => c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun _ _ => c.finsetSum _ fun _ _ => c.mul (h₁ _ _) (h₂ _ _)

@[simp low]
/--
theorem `matrix_apply` / 定理 `matrix_apply`

English:
theorem matrix_apply
  given: {c : RingCon R} {M N : Matrix n n R}
  proof: Iff.rfl

@[simp]

中文:
定理 matrix_apply
  条件: {c : RingCon R} {M N : 矩阵 n n R}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem matrix_apply {c : RingCon R} {M N : Matrix n n R} :
    c.matrix n M N ↔ forall i j, c (M i j) (N i j) :=
  Iff.rfl

@[simp]
/--
theorem `matrix_apply_single` / 定理 `matrix_apply_single`

English:
theorem matrix_apply_single
  given: [DecidableEq n] {c : RingCon R} {i j : n} {x y : R}
  proof: by
  refine ⟨fun h => by simpa using h i j, fun h i' j' => ?_⟩
  obtain hi | rfl := ne_or_eq i i'
  · simpa [hi] using c.refl 0
  obtain hj | rfl := ne_or_eq j j'
  · simpa [hj] using c.refl _
  simpa using h

中文:
定理 matrix_apply_single
  条件: [DecidableEq n] {c : RingCon R} {i j : n} {x y : R}
  证明: by
  refine ⟨fun h => by simpa using h i j, fun h i' j' => ?_⟩
  obtain hi | rfl := ne_or_eq i i'
  · simpa [hi] using c.refl 0
  obtain hj | rfl := ne_or_eq j j'
  · simpa [hj] using c.refl _
  simpa using h

Depends on / 依赖: c.refl, ne_or_eq
-/
theorem matrix_apply_single [DecidableEq n] {c : RingCon R} {i j : n} {x y : R} :
    c.matrix n (Matrix.single i j x) (Matrix.single i j y) ↔ c x y := by
  refine ⟨fun h => by simpa using h i j, fun h i' j' => ?_⟩
  obtain hi | rfl := ne_or_eq i i'
  · simpa [hi] using c.refl 0
  obtain hj | rfl := ne_or_eq j j'
  · simpa [hj] using c.refl _
  simpa using h

/--
theorem `matrix_monotone` / 定理 `matrix_monotone`

English:
theorem matrix_monotone
  statement: Monotone (matrix (R := R) n)
  proof: fun _ _ hc _ _ h _ _ => hc (h _ _)

中文:
定理 matrix_monotone
  结论: 递增 (matrix (R := R) n)
  证明: fun _ _ hc _ _ h _ _ => hc (h _ _)
-/
theorem matrix_monotone : Monotone (matrix (R := R) n) :=
  fun _ _ hc _ _ h _ _ => hc (h _ _)

/--
theorem `matrix_injective` / 定理 `matrix_injective`

English:
theorem matrix_injective
  given: [Nonempty n]
  statement: Function.Injective (matrix (R := R) n)
  proof: fun I J eq => RingCon.ext fun r s => by
    have := congr_fun (DFunLike.congr_fun eq (Matrix.of fun _ _ => r)) (Matrix.of fun _ _ => s)
    simpa using this

中文:
定理 matrix_injective
  条件: [非空 n]
  结论: 函数.单射 (matrix (R := R) n)
  证明: fun I J eq => RingCon.ext fun r s => by
    have := congr_fun (DFunLike.congr_fun eq (Matrix.of fun _ _ => r)) (Matrix.of fun _ _ => s)
    simpa using this
-/
theorem matrix_injective [Nonempty n] : Function.Injective (matrix (R := R) n) :=
  fun I J eq => RingCon.ext fun r s => by
    have := congr_fun (DFunLike.congr_fun eq (Matrix.of fun _ _ => r)) (Matrix.of fun _ _ => s)
    simpa using this

/--
theorem `matrix_strictMono_of_nonempty` / 定理 `matrix_strictMono_of_nonempty`

English:
theorem matrix_strictMono_of_nonempty
  given: [Nonempty n]
  proof: .strictMono_of_injective matrix_injective _ matrix_monotone n

@[simp]

中文:
定理 matrix_strictMono_of_nonempty
  条件: [非空 n]
  证明: .strictMono_of_injective matrix_injective _ matrix_monotone n

@[simp]
-/
theorem matrix_strictMono_of_nonempty [Nonempty n] :
    StrictMono (matrix (R := R) n) :=
.strictMono_of_injective matrix_injective _ matrix_monotone n

@[simp]
/--
theorem `matrix_bot` / 定理 `matrix_bot`

English:
theorem matrix_bot
  statement: (⊥ : RingCon R).matrix n = ⊥
  proof: eq_bot_iff.2 fun _ _ h => Matrix.ext h

@[simp]

中文:
定理 matrix_bot
  结论: (⊥ : RingCon R).matrix n = ⊥
  证明: eq_bot_iff.2 fun _ _ h => Matrix.ext h

@[simp]

Depends on / 依赖: Matrix, Matrix.ext, eq_bot_iff
-/
theorem matrix_bot : (⊥ : RingCon R).matrix n = ⊥ :=
  eq_bot_iff.2 fun _ _ h => Matrix.ext h

@[simp]
/--
theorem `matrix_top` / 定理 `matrix_top`

English:
theorem matrix_top
  statement: (⊤ : RingCon R).matrix n = ⊤
  proof: eq_top_iff.2 fun _ _ _ _ _ => by simp

中文:
定理 matrix_top
  结论: (⊤ : RingCon R).matrix n = ⊤
  证明: eq_top_iff.2 fun _ _ _ _ _ => by simp

Depends on / 依赖: eq_top_iff
-/
theorem matrix_top : (⊤ : RingCon R).matrix n = ⊤ :=
  eq_top_iff.2 fun _ _ _ _ _ => by simp

open Matrix

variable {n}

/--
Definition of `ofMatrix` / `ofMatrix` 的定义

English:
definition ofMatrix
  signature: [DecidableEq n] (c : RingCon (Matrix n n R))
  body: forall i j, c (single i j x) (single i j y)
  iseqv.refl _ := fun _ _ => c.refl _
iseqv.symm h := fun _ _ => c.symm h _ _
  iseqv.trans h₁ h₂ := fun _ _ => c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ => by simpa [single_add] using c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun i j => by simpa using c.mul (h₁ i i) (h₂ i j)

@[simp]

中文:
定义 ofMatrix
  签名: [DecidableEq n] (c : RingCon (矩阵 n n R))
  定义体: forall i j, c (single i j x) (single i j y)
  iseqv.refl _ := fun _ _ => c.refl _
iseqv.symm h := fun _ _ => c.symm h _ _
  iseqv.trans h₁ h₂ := fun _ _ => c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ => by simpa [single_add] using c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun i j => by simpa using c.mul (h₁ i i) (h₂ i j)

@[simp]

Depends on / 依赖: single
-/
def ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) : RingCon R where
  r x y := forall i j, c (single i j x) (single i j y)
  iseqv.refl _ := fun _ _ => c.refl _
iseqv.symm h := fun _ _ => c.symm h _ _
  iseqv.trans h₁ h₂ := fun _ _ => c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ => by simpa [single_add] using c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun i j => by simpa using c.mul (h₁ i i) (h₂ i j)

@[simp]
/--
theorem `ofMatrix_rel` / 定理 `ofMatrix_rel`

English:
theorem ofMatrix_rel
  given: [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R}
  proof: Iff.rfl

中文:
定理 ofMatrix_rel
  条件: [DecidableEq n] {c : RingCon (矩阵 n n R)} {x y : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ofMatrix_rel [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} :
    ofMatrix c x y ↔ forall i j, c (single i j x) (single i j y) :=
  Iff.rfl

/--
theorem `ofMatrix_matrix` / 定理 `ofMatrix_matrix`

English:
theorem ofMatrix_matrix
  given: [DecidableEq n] [Nonempty n] (c : RingCon R)
  proof: by
  ext x y
  constructor
  · intro h
    inhabit n
    simpa using h default default default default
  · intro h i j
    rwa [matrix_apply_single]

中文:
定理 ofMatrix_matrix
  条件: [DecidableEq n] [非空 n] (c : RingCon R)
  证明: by
  ext x y
  constructor
  · intro h
    inhabit n
    simpa using h default default default default
  · intro h i j
    rwa [matrix_apply_single]
-/
@[simp] theorem ofMatrix_matrix [DecidableEq n] [Nonempty n] (c : RingCon R) :
    ofMatrix (matrix n c) = c := by
  ext x y
  constructor
  · intro h
    inhabit n
    simpa using h default default default default
  · intro h i j
    rwa [matrix_apply_single]

end NonUnitalNonAssocSemiring

section NonAssocSemiring
variable [NonAssocSemiring R] [Fintype n]
open Matrix

/-- Note that this does not apply to a non-unital ring, with counterexample where the elementwise
congruence relation `!![⊤,⊤;⊤,(· ≡ · [PMOD 4])]` is a ring congruence over
`Matrix (Fin 2) (Fin 2) 2ℤ`. -/
@[simp]
/--
theorem `matrix_ofMatrix` / 定理 `matrix_ofMatrix`

English:
theorem matrix_ofMatrix
  given: [DecidableEq n] (c : RingCon (Matrix n n R))
  proof: by
  ext x y
  constructor
  · intro h
    rw [matrix_eq_sum_single x]; rw [matrix_eq_sum_single y]
    refine c.finsetSum _ fun i _ => c.finsetSum _ fun j _ => h i j i j
  · intro h i' j' i j
    simpa using c.mul (c.mul (c.refl <| single i i' 1) h) (c.refl <| single j' j 1)

中文:
定理 matrix_ofMatrix
  条件: [DecidableEq n] (c : RingCon (矩阵 n n R))
  证明: by
  ext x y
  constructor
  · intro h
    rw [matrix_eq_sum_single x]; rw [matrix_eq_sum_single y]
    refine c.finsetSum _ fun i _ => c.finsetSum _ fun j _ => h i j i j
  · intro h i' j' i j
    simpa using c.mul (c.mul (c.refl <| single i i' 1) h) (c.refl <| single j' j 1)

Depends on / 依赖: c.finsetSum, c.mul, c.refl, finsetSum, matrix_eq_sum_single, single
-/
theorem matrix_ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) :
    matrix n (ofMatrix c) = c := by
  ext x y
  constructor
  · intro h
    rw [matrix_eq_sum_single x]; rw [matrix_eq_sum_single y]
    refine c.finsetSum _ fun i _ => c.finsetSum _ fun j _ => h i j i j
  · intro h i' j' i j
    simpa using c.mul (c.mul (c.refl <| single i i' 1) h) (c.refl <| single j' j 1)

/--
theorem `ofMatrix_rel'` / 定理 `ofMatrix_rel'`

English:
theorem ofMatrix_rel'
  given: [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} (i j : n)
  proof: by
  refine ⟨fun h => h i j, fun h i' j' => ?_⟩
  simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

中文:
定理 ofMatrix_rel'
  条件: [DecidableEq n] {c : RingCon (矩阵 n n R)} {x y : R} (i j : n)
  证明: by
  refine ⟨fun h => h i j, fun h i' j' => ?_⟩
  simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

Depends on / 依赖: c.mul, c.refl, single
-/
theorem ofMatrix_rel' [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} (i j : n) :
    ofMatrix c x y ↔ c (single i j x) (single i j y) := by
  refine ⟨fun h => h i j, fun h i' j' => ?_⟩
  simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

/--
theorem `coe_ofMatrix_eq_relationMap` / 定理 `coe_ofMatrix_eq_relationMap`

English:
theorem coe_ofMatrix_eq_relationMap
  given: [DecidableEq n] {c : RingCon (Matrix n n R)} (i j : n)
  proof: by
  ext x y
  constructor
  · intro h
    refine ⟨_,_, h i j, ?_⟩
    simp
  · rintro ⟨X, Y, h, rfl, rfl⟩ i' j'
    simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

中文:
定理 coe_ofMatrix_eq_relationMap
  条件: [DecidableEq n] {c : RingCon (矩阵 n n R)} (i j : n)
  证明: by
  ext x y
  constructor
  · intro h
    refine ⟨_,_, h i j, ?_⟩
    simp
  · rintro ⟨X, Y, h, rfl, rfl⟩ i' j'
    simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

Depends on / 依赖: c.mul, c.refl, single
-/
theorem coe_ofMatrix_eq_relationMap [DecidableEq n] {c : RingCon (Matrix n n R)} (i j : n) :
    ⇑(ofMatrix c) = Relation.Map c (· i j) (· i j) := by
  ext x y
  constructor
  · intro h
    refine ⟨_,_, h i j, ?_⟩
    simp
  · rintro ⟨X, Y, h, rfl, rfl⟩ i' j'
    simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

end NonAssocSemiring

end RingCon

namespace TwoSidedIdeal
open Matrix

variable {R : Type*} (n : Type*)

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] [Fintype n]

/-- The two-sided ideal of matrices with entries in `I ≤ R`. -/
@[simps]
/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (I : TwoSidedIdeal R)
  body: I.ringCon.matrix n

@[simp]

中文:
定义 matrix
  签名: (I : TwoSided理想 R)
  定义体: I.ringCon.matrix n

@[simp]

Depends on / 依赖: I.ringCon.matrix, matrix, ringCon
-/
def matrix (I : TwoSidedIdeal R) : TwoSidedIdeal (Matrix n n R) where
  ringCon := I.ringCon.matrix n

@[simp]
/--
lemma `mem_matrix` / 引理 `mem_matrix`

English:
lemma mem_matrix
  given: (I : TwoSidedIdeal R) (M : Matrix n n R)
  proof: Iff.rfl

中文:
引理 mem_matrix
  条件: (I : TwoSided理想 R) (M : 矩阵 n n R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_matrix (I : TwoSidedIdeal R) (M : Matrix n n R) :
    M in I.matrix n ↔ forall i j, M i j in I := Iff.rfl

/--
theorem `matrix_monotone` / 定理 `matrix_monotone`

English:
theorem matrix_monotone
  statement: Monotone (matrix (R := R) n)
  proof: fun _ _ IJ _ MI i j => IJ (MI i j)

中文:
定理 matrix_monotone
  结论: 递增 (matrix (R := R) n)
  证明: fun _ _ IJ _ MI i j => IJ (MI i j)
-/
theorem matrix_monotone : Monotone (matrix (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)

/--
theorem `matrix_strictMono_of_nonempty` / 定理 `matrix_strictMono_of_nonempty`

English:
theorem matrix_strictMono_of_nonempty
  given: [h : Nonempty n]
  proof: .strictMono_of_injective matrix_monotone n
.comp (fun _ _ => ofRingCon.inj) (RingCon.matrix_injective n).comp ringCon_injective

@[simp]

中文:
定理 matrix_strictMono_of_nonempty
  条件: [h : 非空 n]
  证明: .strictMono_of_injective matrix_monotone n
.comp (fun _ _ => ofRingCon.inj) (RingCon.matrix_injective n).comp ringCon_injective

@[simp]
-/
theorem matrix_strictMono_of_nonempty [h : Nonempty n] :
    StrictMono (matrix (R := R) n) :=
.strictMono_of_injective matrix_monotone n
.comp (fun _ _ => ofRingCon.inj) (RingCon.matrix_injective n).comp ringCon_injective

@[simp]
/--
theorem `matrix_bot` / 定理 `matrix_bot`

English:
theorem matrix_bot
  statement: (⊥ : TwoSidedIdeal R).matrix n = ⊥
  proof: ringCon_injective RingCon.matrix_bot _

@[simp]

中文:
定理 matrix_bot
  结论: (⊥ : TwoSided理想 R).matrix n = ⊥
  证明: ringCon_injective RingCon.matrix_bot _

@[simp]

Depends on / 依赖: RingCon, RingCon.matrix_bot, matrix_bot, ringCon_injective
-/
theorem matrix_bot : (⊥ : TwoSidedIdeal R).matrix n = ⊥ :=
ringCon_injective RingCon.matrix_bot _

@[simp]
/--
theorem `matrix_top` / 定理 `matrix_top`

English:
theorem matrix_top
  statement: (⊤ : TwoSidedIdeal R).matrix n = ⊤
  proof: ringCon_injective RingCon.matrix_top _

中文:
定理 matrix_top
  结论: (⊤ : TwoSided理想 R).matrix n = ⊤
  证明: ringCon_injective RingCon.matrix_top _

Depends on / 依赖: RingCon, RingCon.matrix_top, matrix_top, ringCon_injective
-/
theorem matrix_top : (⊤ : TwoSidedIdeal R).matrix n = ⊤ :=
ringCon_injective RingCon.matrix_top _

end NonUnitalNonAssocRing

section NonAssocRing
variable [NonAssocRing R] [Fintype n] [Nonempty n] [DecidableEq n]

variable {n}

/--
Two-sided ideals in $R$ correspond bijectively to those in $Mₙ(R)$.
Given an ideal $I ≤ R$, we send it to $Mₙ(I)$.
Given an ideal $J ≤ Mₙ(R)$, we send it to $\{Nᵢⱼ ∣ ∃ N ∈ J\}$.
-/
@[simps]
/--
Definition of `equivMatrix` / `equivMatrix` 的定义

English:
definition equivMatrix
  signature: : TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix n n R) where
  body: I.matrix n
  invFun J := { ringCon := J.ringCon.ofMatrix }
right_inv _ := ringCon_injective RingCon.matrix_ofMatrix _
left_inv _ := ringCon_injective RingCon.ofMatrix_matrix _

中文:
定义 equivMatrix
  签名: : TwoSided理想 R ≃ TwoSided理想 (矩阵 n n R) where
  定义体: I.matrix n
  invFun J := { ringCon := J.ringCon.ofMatrix }
right_inv _ := ringCon_injective RingCon.matrix_ofMatrix _
left_inv _ := ringCon_injective RingCon.ofMatrix_matrix _

Depends on / 依赖: I.matrix, matrix
-/
def equivMatrix : TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix n n R) where
  toFun I := I.matrix n
  invFun J := { ringCon := J.ringCon.ofMatrix }
right_inv _ := ringCon_injective RingCon.matrix_ofMatrix _
left_inv _ := ringCon_injective RingCon.ofMatrix_matrix _

/--
theorem `coe_equivMatrix_symm_apply` / 定理 `coe_equivMatrix_symm_apply`

English:
theorem coe_equivMatrix_symm_apply
  given: (I : TwoSidedIdeal (Matrix n n R)) (i j : n)
  proof: by
  ext r
  constructor
  · intro h
    exact ⟨single i j r, by simpa using! h i j, by simp⟩
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe]; rw [mem_iff]; rw [equivMatrix_symm_apply_ringCon]; rw [RingCon.coe_ofMatrix_eq_relationMap i j]
    exact ⟨n, 0, (I.mem_iff n).mp hn, rfl, rfl⟩

中文:
定理 coe_equivMatrix_symm_apply
  条件: (I : TwoSided理想 (矩阵 n n R)) (i j : n)
  证明: by
  ext r
  constructor
  · intro h
    exact ⟨single i j r, by simpa using! h i j, by simp⟩
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe]; rw [mem_iff]; rw [equivMatrix_symm_apply_ringCon]; rw [RingCon.coe_ofMatrix_eq_relationMap i j]
    exact ⟨n, 0, (I.mem_iff n).mp hn, rfl, rfl⟩

Depends on / 依赖: I.mem_iff, RingCon, RingCon.coe_ofMatrix_eq_relationMap, SetLike, SetLike.mem_coe, coe_ofMatrix_eq_relationMap, equivMatrix_symm_apply_ringCon, mem_coe, mem_iff, single
-/
theorem coe_equivMatrix_symm_apply (I : TwoSidedIdeal (Matrix n n R)) (i j : n) :
    equivMatrix.symm I = {N i j | N in I} := by
  ext r
  constructor
  · intro h
    exact ⟨single i j r, by simpa using! h i j, by simp⟩
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe]; rw [mem_iff]; rw [equivMatrix_symm_apply_ringCon]; rw [RingCon.coe_ofMatrix_eq_relationMap i j]
    exact ⟨n, 0, (I.mem_iff n).mp hn, rfl, rfl⟩

/--
Two-sided ideals in $R$ are order-isomorphic with those in $Mₙ(R)$.
See also `equivMatrix`.
-/
@[simps!]
/--
Definition of `orderIsoMatrix` / `orderIsoMatrix` 的定义

English:
definition orderIsoMatrix
  signature: : TwoSidedIdeal R ≃o TwoSidedIdeal (Matrix n n R) where
  body: equivMatrix
  map_rel_iff' {I J} := by
    simp only [equivMatrix_apply]
    constructor
    · intro le x xI
      specialize @le (of fun _ _ => x) (by simp [xI])
      simpa using le
    · intro IJ M MI i j
exact IJ MI i j

中文:
定义 orderIsoMatrix
  签名: : TwoSided理想 R ≃o TwoSided理想 (矩阵 n n R) where
  定义体: equivMatrix
  map_rel_iff' {I J} := by
    simp only [equivMatrix_apply]
    constructor
    · intro le x xI
      specialize @le (of fun _ _ => x) (by simp [xI])
      simpa using le
    · intro IJ M MI i j
exact IJ MI i j

Depends on / 依赖: equivMatrix
-/
def orderIsoMatrix : TwoSidedIdeal R ≃o TwoSidedIdeal (Matrix n n R) where
  __ := equivMatrix
  map_rel_iff' {I J} := by
    simp only [equivMatrix_apply]
    constructor
    · intro le x xI
      specialize @le (of fun _ _ => x) (by simp [xI])
      simpa using le
    · intro IJ M MI i j
exact IJ MI i j

end NonAssocRing

section Ring
variable [Ring R] [Fintype n]

/--
theorem `asIdeal_matrix` / 定理 `asIdeal_matrix`

English:
theorem asIdeal_matrix
  given: [DecidableEq n] (I : TwoSidedIdeal R)
  proof: by
  ext; simp

中文:
定理 asIdeal_matrix
  条件: [DecidableEq n] (I : TwoSided理想 R)
  证明: by
  ext; simp
-/
theorem asIdeal_matrix [DecidableEq n] (I : TwoSidedIdeal R) :
    asIdeal (I.matrix n) = (asIdeal I).matrix n := by
  ext; simp

end Ring

end TwoSidedIdeal

/-! ### Jacobson radicals of two-sided ideals in a matrix ring -/

namespace TwoSidedIdeal
open Matrix

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

/--
lemma `jacobson_matrix_le` / 引理 `jacobson_matrix_le`

English:
lemma jacobson_matrix_le
  given: (I : TwoSidedIdeal R)
  proof: by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  intro M Mmem p q
  simp only [zero_apply, ← mem_iff]
  rw [mem_jacobson_iff]
  replace Mmem := mul_mem_right _ _ (single q p 1) Mmem
  rw [mem_jacobson_iff] at Mmem
  intro y
  specialize Mmem (y • single p p 1)
  have ⟨N, NxMI⟩ := Mmem
  use N p p
  simpa [mul_apply, single, ite_and] using! NxMI p p

中文:
引理 jacobson_matrix_le
  条件: (I : TwoSided理想 R)
  证明: by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  intro M Mmem p q
  simp only [zero_apply, ← mem_iff]
  rw [mem_jacobson_iff]
  replace Mmem := mul_mem_right _ _ (single q p 1) Mmem
  rw [mem_jacobson_iff] at Mmem
  intro y
  specialize Mmem (y • single p p 1)
  have ⟨N, NxMI⟩ := Mmem
  use N p p
  simpa [mul_apply, single, ite_and] using! NxMI p p
-/
private lemma jacobson_matrix_le (I : TwoSidedIdeal R) :
    (I.matrix n).jacobson <= I.jacobson.matrix n := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  intro M Mmem p q
  simp only [zero_apply, ← mem_iff]
  rw [mem_jacobson_iff]
  replace Mmem := mul_mem_right _ _ (single q p 1) Mmem
  rw [mem_jacobson_iff] at Mmem
  intro y
  specialize Mmem (y • single p p 1)
  have ⟨N, NxMI⟩ := Mmem
  use N p p
  simpa [mul_apply, single, ite_and] using! NxMI p p

/--
theorem `jacobson_matrix` / 定理 `jacobson_matrix`

English:
theorem jacobson_matrix
  given: (I : TwoSidedIdeal R)
  proof: by
  apply le_antisymm
  · apply jacobson_matrix_le
  · change asIdeal (I.matrix n).jacobson >= asIdeal (I.jacobson.matrix n)
    simp [asIdeal_jacobson, asIdeal_matrix, Ideal.matrix_jacobson_le]

中文:
定理 jacobson_matrix
  条件: (I : TwoSided理想 R)
  证明: by
  apply le_antisymm
  · apply jacobson_matrix_le
  · change asIdeal (I.matrix n).jacobson >= asIdeal (I.jacobson.matrix n)
    simp [asIdeal_jacobson, asIdeal_matrix, Ideal.matrix_jacobson_le]

Depends on / 依赖: I.jacobson.matrix, I.matrix, Ideal.matrix_jacobson_le, asIdeal, asIdeal_jacobson, asIdeal_matrix, jacobson, jacobson_matrix_le, le_antisymm, matrix, matrix_jacobson_le
-/
theorem jacobson_matrix (I : TwoSidedIdeal R) :
    (I.matrix n).jacobson = I.jacobson.matrix n := by
  apply le_antisymm
  · apply jacobson_matrix_le
  · change asIdeal (I.matrix n).jacobson >= asIdeal (I.jacobson.matrix n)
    simp [asIdeal_jacobson, asIdeal_matrix, Ideal.matrix_jacobson_le]

/--
theorem `matrix_jacobson_bot` / 定理 `matrix_jacobson_bot`

English:
theorem matrix_jacobson_bot
  proof: matrix_bot n (R := R) ▸ (jacobson_matrix _).symm

中文:
定理 matrix_jacobson_bot
  证明: matrix_bot n (R := R) ▸ (jacobson_matrix _).symm

Depends on / 依赖: jacobson_matrix, matrix_bot
-/
theorem matrix_jacobson_bot :
    (⊥ : TwoSidedIdeal R).jacobson.matrix n = (⊥ : TwoSidedIdeal (Matrix n n R)).jacobson :=
  matrix_bot n (R := R) ▸ (jacobson_matrix _).symm

end TwoSidedIdeal
