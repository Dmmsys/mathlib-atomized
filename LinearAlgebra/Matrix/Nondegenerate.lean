/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `Matrix.Nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/

@[expose] public section


namespace Matrix

section Finite

variable {m n R A : Type*} [NonUnitalNonAssocSemiring R] [Finite m] [Finite n] (M : Matrix m n R)

attribute [local instance] Fintype.ofFinite

/--
Definition of `SeparatingRight` / `SeparatingRight` 的定义

English:
definition SeparatingRight
  signature: : Prop
  body: (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0)

中文:
定义 SeparatingRight
  签名: : 命题
  定义体: (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0)
-/
def SeparatingRight : Prop :=
  (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0)

/--
Definition of `SeparatingLeft` / `SeparatingLeft` 的定义

English:
definition SeparatingLeft
  signature: : Prop
  body: (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0)

中文:
定义 SeparatingLeft
  签名: : 命题
  定义体: (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0)
-/
def SeparatingLeft : Prop :=
  (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0)

/-- A matrix `M` is nondegenerate if it is both left-separating and right-separating.

See also `Matrix.Nonsingular`. -/
@[mk_iff]
/--
Definition of `Nondegenerate` / `Nondegenerate` 的定义

English:
structure Nondegenerate
  parameters: (M : Matrix m n R)
  axioms and operations (2):
    - separatingLeft : SeparatingLeft M
    - separatingRight : SeparatingRight M

中文:
结构 Nondegenerate
  参数: (M : Matrix m n R)
  公理与运算 (2 个):
    - separatingLeft : SeparatingLeft M
    - separatingRight : SeparatingRight M
-/
structure Nondegenerate (M : Matrix m n R) : Prop where
  separatingLeft : SeparatingLeft M
  separatingRight : SeparatingRight M

end Finite

section CommSemiring

variable {m n R : Type*} [CommSemiring R] {M : Matrix m n R}

/--
lemma `separatingRight_def` / 引理 `separatingRight_def`

English:
lemma separatingRight_def
  given: [Fintype m] [Fintype n]
  proof: by
  refine forall_congr' fun w => ⟨fun hM hw => hM ?_, fun hM hw => hM ?_⟩ <;>
  convert! hw

中文:
引理 separatingRight_def
  条件: [Fintype m] [Fintype n]
  证明: by
  refine forall_congr' fun w => ⟨fun hM hw => hM ?_, fun hM hw => hM ?_⟩ <;>
  convert! hw

Depends on / 依赖: convert, forall_congr
-/
lemma separatingRight_def [Fintype m] [Fintype n] :
    M.SeparatingRight ↔ (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0) := by
  refine forall_congr' fun w => ⟨fun hM hw => hM ?_, fun hM hw => hM ?_⟩ <;>
  convert! hw

/--
lemma `separatingLeft_def` / 引理 `separatingLeft_def`

English:
lemma separatingLeft_def
  given: [Fintype m] [Fintype n]
  proof: by
  refine forall_congr' fun v => ⟨fun hM hv => hM ?_, fun hM hv => hM ?_⟩ <;>
  convert! hv

中文:
引理 separatingLeft_def
  条件: [Fintype m] [Fintype n]
  证明: by
  refine forall_congr' fun v => ⟨fun hM hv => hM ?_, fun hM hv => hM ?_⟩ <;>
  convert! hv

Depends on / 依赖: convert, forall_congr
-/
lemma separatingLeft_def [Fintype m] [Fintype n] :
    M.SeparatingLeft ↔ (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0) := by
  refine forall_congr' fun v => ⟨fun hM hv => hM ?_, fun hM hv => hM ?_⟩ <;>
  convert! hv

/--
lemma `nondegenerate_def` / 引理 `nondegenerate_def`

English:
lemma nondegenerate_def
  given: [Fintype m] [Fintype n]
  proof: by
  rw [nondegenerate_iff]; rw [separatingLeft_def]; rw [separatingRight_def]

中文:
引理 nondegenerate_def
  条件: [Fintype m] [Fintype n]
  证明: by
  rw [nondegenerate_iff]; rw [separatingLeft_def]; rw [separatingRight_def]

Depends on / 依赖: nondegenerate_iff, separatingLeft_def, separatingRight_def
-/
lemma nondegenerate_def [Fintype m] [Fintype n] :
    M.Nondegenerate ↔
      (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0) ∧ (forall w, (forall v, v ⬝ᵥ M *ᵥ w = 0) -> w = 0) := by
  rw [nondegenerate_iff]; rw [separatingLeft_def]; rw [separatingRight_def]

/--
theorem `separatingLeft_iff_forall_vecMul_eq_zero` / 定理 `separatingLeft_iff_forall_vecMul_eq_zero`

English:
theorem separatingLeft_iff_forall_vecMul_eq_zero
  given: [Fintype m] [Finite n]
  proof: by
  have := Fintype.ofFinite n
  rw [separatingLeft_def]
refine ⟨fun h v hv => h v fun w => ?_, fun h w hw => h w funext fun i => ?_⟩
  · simp [dotProduct_mulVec, hv]
· classical simpa using! hw Pi.single i 1

中文:
定理 separatingLeft_iff_forall_vecMul_eq_zero
  条件: [Fintype m] [Finite n]
  证明: by
  have := Fintype.ofFinite n
  rw [separatingLeft_def]
refine ⟨fun h v hv => h v fun w => ?_, fun h w hw => h w funext fun i => ?_⟩
  · simp [dotProduct_mulVec, hv]
· classical simpa using! hw Pi.single i 1

Depends on / 依赖: Fintype, Fintype.ofFinite, Pi.single, classical, dotProduct_mulVec, ofFinite, separatingLeft_def, single
-/
theorem separatingLeft_iff_forall_vecMul_eq_zero [Fintype m] [Finite n] :
    M.SeparatingLeft ↔ forall v, v ᵥ* M = 0 -> v = 0 := by
  have := Fintype.ofFinite n
  rw [separatingLeft_def]
refine ⟨fun h v hv => h v fun w => ?_, fun h w hw => h w funext fun i => ?_⟩
  · simp [dotProduct_mulVec, hv]
· classical simpa using! hw Pi.single i 1

/--
theorem `separatingRight_iff_forall_mulVec_eq_zero` / 定理 `separatingRight_iff_forall_mulVec_eq_zero`

English:
theorem separatingRight_iff_forall_mulVec_eq_zero
  given: [Finite m] [Fintype n]
  proof: by
  have := Fintype.ofFinite m
  rw [separatingRight_def]
refine ⟨fun h v hv => h v fun w => ?_, fun h w hw => h w funext fun i => ?_⟩
  · simp [hv]
· classical simpa using hw Pi.single i 1

中文:
定理 separatingRight_iff_forall_mulVec_eq_zero
  条件: [Finite m] [Fintype n]
  证明: by
  have := Fintype.ofFinite m
  rw [separatingRight_def]
refine ⟨fun h v hv => h v fun w => ?_, fun h w hw => h w funext fun i => ?_⟩
  · simp [hv]
· classical simpa using hw Pi.single i 1

Depends on / 依赖: Fintype, Fintype.ofFinite, Pi.single, classical, ofFinite, separatingRight_def, single
-/
theorem separatingRight_iff_forall_mulVec_eq_zero [Finite m] [Fintype n] :
    M.SeparatingRight ↔ forall v, M *ᵥ v = 0 -> v = 0 := by
  have := Fintype.ofFinite m
  rw [separatingRight_def]
refine ⟨fun h v hv => h v fun w => ?_, fun h w hw => h w funext fun i => ?_⟩
  · simp [hv]
· classical simpa using hw Pi.single i 1

/--
theorem `SeparatingLeft.eq_zero_of_vecMul_eq_zero` / 定理 `SeparatingLeft.eq_zero_of_vecMul_eq_zero`

English:
theorem SeparatingLeft.eq_zero_of_vecMul_eq_zero
  statement: [Fintype m] [Finite n] (hM : M.SeparatingLeft)
  proof: separatingLeft_iff_forall_vecMul_eq_zero.mp hM v hv

中文:
定理 SeparatingLeft.eq_zero_of_vecMul_eq_zero
  结论: [Fintype m] [Finite n] (hM : M.SeparatingLeft)
  证明: separatingLeft_iff_forall_vecMul_eq_zero.mp hM v hv

Depends on / 依赖: separatingLeft_iff_forall_vecMul_eq_zero, separatingLeft_iff_forall_vecMul_eq_zero.mp
-/
theorem SeparatingLeft.eq_zero_of_vecMul_eq_zero [Fintype m] [Finite n] (hM : M.SeparatingLeft)
    {v : m -> R} (hv : v ᵥ* M = 0) : v = 0 :=
  separatingLeft_iff_forall_vecMul_eq_zero.mp hM v hv

/--
theorem `SeparatingRight.eq_zero_of_mulVec_eq_zero` / 定理 `SeparatingRight.eq_zero_of_mulVec_eq_zero`

English:
theorem SeparatingRight.eq_zero_of_mulVec_eq_zero
  statement: [Finite m] [Fintype n] (hM : M.SeparatingRight)
  proof: separatingRight_iff_forall_mulVec_eq_zero.mp hM v hv

中文:
定理 SeparatingRight.eq_zero_of_mulVec_eq_zero
  结论: [Finite m] [Fintype n] (hM : M.SeparatingRight)
  证明: separatingRight_iff_forall_mulVec_eq_zero.mp hM v hv

Depends on / 依赖: separatingRight_iff_forall_mulVec_eq_zero, separatingRight_iff_forall_mulVec_eq_zero.mp
-/
theorem SeparatingRight.eq_zero_of_mulVec_eq_zero [Finite m] [Fintype n] (hM : M.SeparatingRight)
    {v : n -> R} (hv : M *ᵥ v = 0) : v = 0 :=
  separatingRight_iff_forall_mulVec_eq_zero.mp hM v hv

/--
theorem `nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero` / 定理 `nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero`

English:
theorem nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero
  given: [Fintype m] [Fintype n]
  proof: by
  rw [nondegenerate_iff]; rw [separatingLeft_iff_forall_vecMul_eq_zero]; rw [separatingRight_iff_forall_mulVec_eq_zero]

@[simp]

中文:
定理 nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero
  条件: [Fintype m] [Fintype n]
  证明: by
  rw [nondegenerate_iff]; rw [separatingLeft_iff_forall_vecMul_eq_zero]; rw [separatingRight_iff_forall_mulVec_eq_zero]

@[simp]

Depends on / 依赖: nondegenerate_iff, separatingLeft_iff_forall_vecMul_eq_zero, separatingRight_iff_forall_mulVec_eq_zero
-/
theorem nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero [Fintype m] [Fintype n] :
    M.Nondegenerate ↔ (forall v, v ᵥ* M = 0 -> v = 0) ∧ (forall v, M *ᵥ v = 0 -> v = 0) := by
  rw [nondegenerate_iff]; rw [separatingLeft_iff_forall_vecMul_eq_zero]; rw [separatingRight_iff_forall_mulVec_eq_zero]

@[simp]
/--
theorem `separatingLeft_transpose_iff` / 定理 `separatingLeft_transpose_iff`

English:
theorem separatingLeft_transpose_iff
  given: [Finite m] [Finite n]
  proof: by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingLeft_def, separatingRight_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingRight.separatingLeft_transpose⟩ := separatingLeft_transpose_iff

@[simp]

中文:
定理 separatingLeft_transpose_iff
  条件: [Finite m] [Finite n]
  证明: by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingLeft_def, separatingRight_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingRight.separatingLeft_transpose⟩ := separatingLeft_transpose_iff

@[simp]

Depends on / 依赖: Fintype, Fintype.ofFinite, dotProduct_transpose_mulVec, ofFinite, separatingLeft_def, separatingRight_def, simp_rw
-/
theorem separatingLeft_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingLeft ↔ M.SeparatingRight := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingLeft_def, separatingRight_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingRight.separatingLeft_transpose⟩ := separatingLeft_transpose_iff

@[simp]
/--
theorem `separatingRight_transpose_iff` / 定理 `separatingRight_transpose_iff`

English:
theorem separatingRight_transpose_iff
  given: [Finite m] [Finite n]
  proof: by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingRight_def, separatingLeft_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingLeft.separatingRight_transpose⟩ := separatingRight_transpose_iff

@[simp]

中文:
定理 separatingRight_transpose_iff
  条件: [Finite m] [Finite n]
  证明: by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingRight_def, separatingLeft_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingLeft.separatingRight_transpose⟩ := separatingRight_transpose_iff

@[simp]

Depends on / 依赖: Fintype, Fintype.ofFinite, dotProduct_transpose_mulVec, ofFinite, separatingLeft_def, separatingRight_def, simp_rw
-/
theorem separatingRight_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingRight ↔ M.SeparatingLeft := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingRight_def, separatingLeft_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingLeft.separatingRight_transpose⟩ := separatingRight_transpose_iff

@[simp]
/--
theorem `nondegenerate_transpose_iff` / 定理 `nondegenerate_transpose_iff`

English:
theorem nondegenerate_transpose_iff
  given: [Finite m] [Finite n]
  statement: Mᵀ.Nondegenerate ↔ M.Nondegenerate
  proof: by
  simp [nondegenerate_iff, and_comm]

alias ⟨_, Nondegenerate.transpose⟩ := nondegenerate_transpose_iff

中文:
定理 nondegenerate_transpose_iff
  条件: [Finite m] [Finite n]
  结论: Mᵀ.Nondegenerate ↔ M.Nondegenerate
  证明: by
  simp [nondegenerate_iff, and_comm]

alias ⟨_, Nondegenerate.transpose⟩ := nondegenerate_transpose_iff

Depends on / 依赖: and_comm, nondegenerate_iff
-/
theorem nondegenerate_transpose_iff [Finite m] [Finite n] : Mᵀ.Nondegenerate ↔ M.Nondegenerate := by
  simp [nondegenerate_iff, and_comm]

alias ⟨_, Nondegenerate.transpose⟩ := nondegenerate_transpose_iff

variable [Fintype m] [Fintype n]

/--
theorem `Nondegenerate.eq_zero_of_ortho` / 定理 `Nondegenerate.eq_zero_of_ortho`

English:
theorem Nondegenerate.eq_zero_of_ortho
  statement: (hM : Nondegenerate M) {v : m -> R}
  proof: (nondegenerate_def.mp hM).1 v hv

中文:
定理 Nondegenerate.eq_zero_of_ortho
  结论: (hM : Nondegenerate M) {v : m -> R}
  证明: (nondegenerate_def.mp hM).1 v hv

Depends on / 依赖: nondegenerate_def, nondegenerate_def.mp
-/
theorem Nondegenerate.eq_zero_of_ortho (hM : Nondegenerate M) {v : m -> R}
    (hv : forall w, v ⬝ᵥ M *ᵥ w = 0) : v = 0 :=
  (nondegenerate_def.mp hM).1 v hv

/--
theorem `Nondegenerate.exists_not_ortho_of_ne_zero` / 定理 `Nondegenerate.exists_not_ortho_of_ne_zero`

English:
theorem Nondegenerate.exists_not_ortho_of_ne_zero
  statement: (hM : Nondegenerate M)
  proof: not_forall.mp (mt hM.eq_zero_of_ortho hv)

中文:
定理 Nondegenerate.exists_not_ortho_of_ne_zero
  结论: (hM : Nondegenerate M)
  证明: not_forall.mp (mt hM.eq_zero_of_ortho hv)

Depends on / 依赖: eq_zero_of_ortho, hM.eq_zero_of_ortho, not_forall, not_forall.mp
-/
theorem Nondegenerate.exists_not_ortho_of_ne_zero (hM : Nondegenerate M)
    {v : m -> R} (hv : v != 0) : exists w, v ⬝ᵥ M *ᵥ w != 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)

/--
theorem `Nondegenerate.eq_zero_of_ortho'` / 定理 `Nondegenerate.eq_zero_of_ortho'`

English:
theorem Nondegenerate.eq_zero_of_ortho'
  statement: (hM : Nondegenerate M) {w : n -> R}
  proof: (nondegenerate_def.mp hM).2 w hw

中文:
定理 Nondegenerate.eq_zero_of_ortho'
  结论: (hM : Nondegenerate M) {w : n -> R}
  证明: (nondegenerate_def.mp hM).2 w hw

Depends on / 依赖: nondegenerate_def, nondegenerate_def.mp
-/
theorem Nondegenerate.eq_zero_of_ortho' (hM : Nondegenerate M) {w : n -> R}
    (hw : forall v, v ⬝ᵥ M *ᵥ w = 0) : w = 0 :=
  (nondegenerate_def.mp hM).2 w hw

/--
theorem `Nondegenerate.exists_not_ortho_of_ne_zero'` / 定理 `Nondegenerate.exists_not_ortho_of_ne_zero'`

English:
theorem Nondegenerate.exists_not_ortho_of_ne_zero'
  given: (hM : Nondegenerate M) {w : n -> R} (hw : w != 0)
  proof: not_forall.mp (mt hM.eq_zero_of_ortho' hw)

中文:
定理 Nondegenerate.exists_not_ortho_of_ne_zero'
  条件: (hM : Nondegenerate M) {w : n -> R} (hw : w != 0)
  证明: not_forall.mp (mt hM.eq_zero_of_ortho' hw)

Depends on / 依赖: eq_zero_of_ortho, hM.eq_zero_of_ortho, not_forall, not_forall.mp
-/
theorem Nondegenerate.exists_not_ortho_of_ne_zero' (hM : Nondegenerate M) {w : n -> R} (hw : w != 0) :
    exists v, v ⬝ᵥ M *ᵥ w != 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho' hw)

end CommSemiring

section Determinant
variable {m R : Type*} [CommRing R] [Fintype m] [DecidableEq m] {M : Matrix m m R}

open scoped nonZeroDivisors

/--
theorem `SeparatingLeft.of_det_mem_nonZeroDivisors` / 定理 `SeparatingLeft.of_det_mem_nonZeroDivisors`

English:
theorem SeparatingLeft.of_det_mem_nonZeroDivisors
  given: (hM : M.det in R⁰)
  statement: M.SeparatingLeft
  proof: by
  refine separatingLeft_def.mpr fun v h => funext fun i => mem_nonZeroDivisors_iff_left.mp hM _ ?_
simpa using h M.cramer Pi.single i 1

中文:
定理 SeparatingLeft.of_det_mem_nonZeroDivisors
  条件: (hM : M.det in R⁰)
  结论: M.SeparatingLeft
  证明: by
  refine separatingLeft_def.mpr fun v h => funext fun i => mem_nonZeroDivisors_iff_left.mp hM _ ?_
simpa using h M.cramer Pi.single i 1
-/
private theorem SeparatingLeft.of_det_mem_nonZeroDivisors (hM : M.det in R⁰) : M.SeparatingLeft := by
  refine separatingLeft_def.mpr fun v h => funext fun i => mem_nonZeroDivisors_iff_left.mp hM _ ?_
simpa using h M.cramer Pi.single i 1

/--
theorem `Nondegenerate.of_det_mem_nonZeroDivisors` / 定理 `Nondegenerate.of_det_mem_nonZeroDivisors`

English:
theorem Nondegenerate.of_det_mem_nonZeroDivisors
  given: (hM : M.det in R⁰)
  statement: M.Nondegenerate where
  proof: .of_det_mem_nonZeroDivisors hM
separatingRight := separatingLeft_transpose_iff.mp .of_det_mem_nonZeroDivisors by simpa

中文:
定理 Nondegenerate.of_det_mem_nonZeroDivisors
  条件: (hM : M.det in R⁰)
  结论: M.Nondegenerate where
  证明: .of_det_mem_nonZeroDivisors hM
separatingRight := separatingLeft_transpose_iff.mp .of_det_mem_nonZeroDivisors by simpa

Depends on / 依赖: of_det_mem_nonZeroDivisors
-/
theorem Nondegenerate.of_det_mem_nonZeroDivisors (hM : M.det in R⁰) : M.Nondegenerate where
  separatingLeft := .of_det_mem_nonZeroDivisors hM
separatingRight := separatingLeft_transpose_iff.mp .of_det_mem_nonZeroDivisors by simpa

/--
theorem `nondegenerate_of_det_ne_zero` / 定理 `nondegenerate_of_det_ne_zero`

English:
theorem nondegenerate_of_det_ne_zero
  given: [NoZeroDivisors R] (hM : M.det != 0)
  statement: M.Nondegenerate
  proof: .of_det_mem_nonZeroDivisors mem_nonZeroDivisors_of_ne_zero hM

中文:
定理 nondegenerate_of_det_ne_zero
  条件: [NoZeroDivisors R] (hM : M.det != 0)
  结论: M.Nondegenerate
  证明: .of_det_mem_nonZeroDivisors mem_nonZeroDivisors_of_ne_zero hM

Depends on / 依赖: mem_nonZeroDivisors_of_ne_zero, of_det_mem_nonZeroDivisors
-/
theorem nondegenerate_of_det_ne_zero [NoZeroDivisors R] (hM : M.det != 0) : M.Nondegenerate :=
.of_det_mem_nonZeroDivisors mem_nonZeroDivisors_of_ne_zero hM

/--
theorem `eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero` / 定理 `eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero`

English:
theorem eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero
  statement: (hM : M.det in R⁰)
  proof: .separatingLeft.eq_zero_of_vecMul_eq_zero hv Nondegenerate.of_det_mem_nonZeroDivisors hM

中文:
定理 eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero
  结论: (hM : M.det in R⁰)
  证明: .separatingLeft.eq_zero_of_vecMul_eq_zero hv Nondegenerate.of_det_mem_nonZeroDivisors hM

Depends on / 依赖: Nondegenerate, Nondegenerate.of_det_mem_nonZeroDivisors, eq_zero_of_vecMul_eq_zero, of_det_mem_nonZeroDivisors, separatingLeft, separatingLeft.eq_zero_of_vecMul_eq_zero
-/
theorem eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero (hM : M.det in R⁰)
    {v : m -> R} (hv : v ᵥ* M = 0) : v = 0 :=
.separatingLeft.eq_zero_of_vecMul_eq_zero hv Nondegenerate.of_det_mem_nonZeroDivisors hM

/--
theorem `eq_zero_of_vecMul_eq_zero` / 定理 `eq_zero_of_vecMul_eq_zero`

English:
theorem eq_zero_of_vecMul_eq_zero
  statement: [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R}
  proof: .separatingLeft.eq_zero_of_vecMul_eq_zero hv nondegenerate_of_det_ne_zero hM

中文:
定理 eq_zero_of_vecMul_eq_zero
  结论: [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R}
  证明: .separatingLeft.eq_zero_of_vecMul_eq_zero hv nondegenerate_of_det_ne_zero hM

Depends on / 依赖: eq_zero_of_vecMul_eq_zero, nondegenerate_of_det_ne_zero, separatingLeft, separatingLeft.eq_zero_of_vecMul_eq_zero
-/
theorem eq_zero_of_vecMul_eq_zero [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R}
    (hv : v ᵥ* M = 0) : v = 0 :=
.separatingLeft.eq_zero_of_vecMul_eq_zero hv nondegenerate_of_det_ne_zero hM

/--
theorem `eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero` / 定理 `eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero`

English:
theorem eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
  statement: (hM : M.det in R⁰)
  proof: .separatingRight.eq_zero_of_mulVec_eq_zero hv Nondegenerate.of_det_mem_nonZeroDivisors hM

中文:
定理 eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
  结论: (hM : M.det in R⁰)
  证明: .separatingRight.eq_zero_of_mulVec_eq_zero hv Nondegenerate.of_det_mem_nonZeroDivisors hM

Depends on / 依赖: Nondegenerate, Nondegenerate.of_det_mem_nonZeroDivisors, eq_zero_of_mulVec_eq_zero, of_det_mem_nonZeroDivisors, separatingRight, separatingRight.eq_zero_of_mulVec_eq_zero
-/
theorem eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero (hM : M.det in R⁰)
    {v : m -> R} (hv : M *ᵥ v = 0) : v = 0 :=
.separatingRight.eq_zero_of_mulVec_eq_zero hv Nondegenerate.of_det_mem_nonZeroDivisors hM

/--
theorem `eq_zero_of_mulVec_eq_zero` / 定理 `eq_zero_of_mulVec_eq_zero`

English:
theorem eq_zero_of_mulVec_eq_zero
  statement: [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R}
  proof: .separatingRight.eq_zero_of_mulVec_eq_zero hv nondegenerate_of_det_ne_zero hM

中文:
定理 eq_zero_of_mulVec_eq_zero
  结论: [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R}
  证明: .separatingRight.eq_zero_of_mulVec_eq_zero hv nondegenerate_of_det_ne_zero hM

Depends on / 依赖: eq_zero_of_mulVec_eq_zero, nondegenerate_of_det_ne_zero, separatingRight, separatingRight.eq_zero_of_mulVec_eq_zero
-/
theorem eq_zero_of_mulVec_eq_zero [NoZeroDivisors R] (hM : M.det != 0) {v : m -> R}
    (hv : M *ᵥ v = 0) : v = 0 :=
.separatingRight.eq_zero_of_mulVec_eq_zero hv nondegenerate_of_det_ne_zero hM

/--
theorem `mulVec_injective_of_det_mem_nonZeroDivisors` / 定理 `mulVec_injective_of_det_mem_nonZeroDivisors`

English:
theorem mulVec_injective_of_det_mem_nonZeroDivisors
  given: (hM : M.det in R⁰)
  proof: fun _ _ hxy => sub_eq_zero.mp
    (eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hM (by rw [mulVec_sub, hxy, sub_self]))

中文:
定理 mulVec_injective_of_det_mem_nonZeroDivisors
  条件: (hM : M.det in R⁰)
  证明: fun _ _ hxy => sub_eq_zero.mp
    (eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hM (by rw [mulVec_sub, hxy, sub_self]))

Depends on / 依赖: eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero, mulVec_sub, sub_eq_zero, sub_eq_zero.mp, sub_self
-/
theorem mulVec_injective_of_det_mem_nonZeroDivisors (hM : M.det in R⁰) :
    Function.Injective M.mulVec :=
  fun _ _ hxy => sub_eq_zero.mp
    (eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hM (by rw [mulVec_sub, hxy, sub_self]))

/--
theorem `mulVec_injective_of_det_ne_zero` / 定理 `mulVec_injective_of_det_ne_zero`

English:
theorem mulVec_injective_of_det_ne_zero
  given: [NoZeroDivisors R] (hM : M.det != 0)
  proof: mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hM)

中文:
定理 mulVec_injective_of_det_ne_zero
  条件: [NoZeroDivisors R] (hM : M.det != 0)
  证明: mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hM)

Depends on / 依赖: mem_nonZeroDivisors_of_ne_zero, mulVec_injective_of_det_mem_nonZeroDivisors
-/
theorem mulVec_injective_of_det_ne_zero [NoZeroDivisors R] (hM : M.det != 0) :
    Function.Injective M.mulVec :=
  mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hM)

end Determinant

end Matrix

open scoped Matrix in
/--
lemma `LinearIndependent.sum_smul_of_nondegenerate` / 引理 `LinearIndependent.sum_smul_of_nondegenerate`

English:
lemma LinearIndependent.sum_smul_of_nondegenerate
  proof: by
  have : Fintype κ := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro w hw
  suffices w = 0 by aesop
  simp_rw [Finset.smul_sum, ← smul_assoc] at hw
  rw [Finset.sum_comm] at hw
  simp_rw [← Finset.sum_smul] at hw
replace hv : w ᵥ* A = 0 := funext hv _ hw
  replace hv (w' 

中文:
引理 LinearIndependent.sum_smul_of_nondegenerate
  证明: by
  have : Fintype κ := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro w hw
  suffices w = 0 by aesop
  simp_rw [Finset.smul_sum, ← smul_assoc] at hw
  rw [Finset.sum_comm] at hw
  simp_rw [← Finset.sum_smul] at hw
replace hv : w ᵥ* A = 0 := funext hv _ hw
  replace hv (w' 

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_comm, Finset.sum_smul, Fintype, Fintype.linearIndependent_iff, Fintype.ofFinite, Matrix, Matrix.dotProduct_mulVec, congr_arg, dotProduct, dotProduct_mulVec, eq_zero_of_ortho, hA.eq_zero_of_ortho, linearIndependent_iff, ofFinite, replace, simp_rw, smul_assoc, smul_sum
-/
lemma LinearIndependent.sum_smul_of_nondegenerate
    {ι κ R M : Type*} [Fintype ι] [Finite κ] [CommRing R] [AddCommGroup M] [Module R M]
    {v : ι -> M} (hv : LinearIndependent R v)
    {A : Matrix κ ι R} (hA : A.Nondegenerate) :
    LinearIndependent R fun i => ∑ j, A i j • v j := by
  have : Fintype κ := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro w hw
  suffices w = 0 by aesop
  simp_rw [Finset.smul_sum, ← smul_assoc] at hw
  rw [Finset.sum_comm] at hw
  simp_rw [← Finset.sum_smul] at hw
replace hv : w ᵥ* A = 0 := funext hv _ hw
  replace hv (w' : ι -> R) : w ⬝ᵥ A *ᵥ w' = 0 := by
    simpa [Matrix.dotProduct_mulVec] using congr_arg (fun x => dotProduct x w') hv
  exact hA.eq_zero_of_ortho hv
