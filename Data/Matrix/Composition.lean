/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie, Eric Wieser
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis

/-!
# Composition of matrices

This file shows that `Mₙ(Mₘ(R)) ≃ Mₙₘ(R)`, `Mₙ(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ`
and also different levels of equivalence when `R` is an `AddCommMonoid`,
`Semiring`, and `Algebra` over a `CommSemiring K`.

## Main definitions

* `Matrix.comp` is an equivalence between `Matrix I J (Matrix K L R)` and
  `I × K` by `J × L` matrices.
* `Matrix.compAddEquiv`: `Matrix.comp` as an `AddEquiv`
* `Matrix.compRingEquiv`: `Matrix.comp` as a `RingEquiv`
* `Matrix.compLinearEquiv`: `Matrix.comp` as a `LinearEquiv`
* `Matrix.compAlgEquiv`: `Matrix.comp` as an `AlgEquiv`
-/

@[expose] public section

namespace Matrix

variable (I J K L R R' : Type*)

/-- An `I` by `J` matrix where each entry is a `K` by `L` matrix is equivalent to
    an `I × K` by `J × L` matrix -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  body: m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)

中文:
定义 comp
  签名: : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  定义体: m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)
-/
def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  toFun m ik jl := m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)

section Basic
variable {R I J K L}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_one` / 定理 `comp_one`

English:
theorem comp_one
  given: [DecidableEq I] [DecidableEq J] [Zero R] [One R]
  statement: comp I I J J R 1 = 1
  proof: by
  ext; simp only [comp, Equiv.coe_fn_mk, one_apply, apply_ite]; aesop

中文:
定理 comp_one
  条件: [DecidableEq I] [DecidableEq J] [Zero R] [One R]
  结论: comp I I J J R 1 = 1
  证明: by
  ext; simp only [comp, Equiv.coe_fn_mk, one_apply, apply_ite]; aesop

Depends on / 依赖: Equiv.coe_fn_mk, apply_ite, coe_fn_mk, one_apply
-/
theorem comp_one [DecidableEq I] [DecidableEq J] [Zero R] [One R] : comp I I J J R 1 = 1 := by
  ext; simp only [comp, Equiv.coe_fn_mk, one_apply, apply_ite]; aesop

/--
theorem `comp_map_map` / 定理 `comp_map_map`

English:
theorem comp_map_map
  given: (M : Matrix I J (Matrix K L R)) (f : R -> R')
  proof: rfl

中文:
定理 comp_map_map
  条件: (M : Matrix I J (Matrix K L R)) (f : R -> R')
  证明: rfl
-/
theorem comp_map_map (M : Matrix I J (Matrix K L R)) (f : R -> R') :
    comp I J K L _ (M.map (fun M' => M'.map f)) = (comp I J K L _ M).map f := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `comp_single_single` / 定理 `comp_single_single`

English:
theorem comp_single_single
  proof: by
  ext ⟨i', k'⟩ ⟨j', l'⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i i'
  · rw [single_apply_of_row_ne hi,
      single_apply_of_row_ne (ne_of_apply_ne Prod.fst hi), Matrix.zero_apply]
  obtain hj | rfl := ne_or_eq j j'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _

中文:
定理 comp_single_single
  证明: by
  ext ⟨i', k'⟩ ⟨j', l'⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i i'
  · rw [single_apply_of_row_ne hi,
      single_apply_of_row_ne (ne_of_apply_ne Prod.fst hi), Matrix.zero_apply]
  obtain hj | rfl := ne_or_eq j j'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _

Depends on / 依赖: Matrix, Matrix.zero_apply, Prod.fst, Prod.snd, comp_apply, ne_of_apply_ne, ne_or_eq, single_apply_of_col_ne, single_apply_of_row_ne, single_apply_same, zero_apply
-/
theorem comp_single_single
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (i j k l r) :
    comp I J K L R (single i j (single k l r))
      = single (i, k) (j, l) r := by
  ext ⟨i', k'⟩ ⟨j', l'⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i i'
  · rw [single_apply_of_row_ne hi,
      single_apply_of_row_ne (ne_of_apply_ne Prod.fst hi), Matrix.zero_apply]
  obtain hj | rfl := ne_or_eq j j'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _ _ (ne_of_apply_ne Prod.fst hj), Matrix.zero_apply]
  rw [single_apply_same]
  obtain hk | rfl := ne_or_eq k k'
  · rw [single_apply_of_row_ne hk,
      single_apply_of_row_ne (ne_of_apply_ne Prod.snd hk)]
  obtain hj | rfl := ne_or_eq l l'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _ _ (ne_of_apply_ne Prod.snd hj)]
  rw [single_apply_same]; rw [single_apply_same]

@[simp]
/--
theorem `comp_symm_single` / 定理 `comp_symm_single`

English:
theorem comp_symm_single
  proof: (comp I J K L R).symm_apply_eq.2 .symm comp_single_single _ _ _ _ _

中文:
定理 comp_symm_single
  证明: (comp I J K L R).symm_apply_eq.2 .symm comp_single_single _ _ _ _ _

Depends on / 依赖: comp_single_single, symm_apply_eq
-/
theorem comp_symm_single
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (ii jj r) :
    (comp I J K L R).symm (single ii jj r) =
      (single ii.1 jj.1 (single ii.2 jj.2 r)) :=
(comp I J K L R).symm_apply_eq.2 .symm comp_single_single _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `comp_diagonal_diagonal` / 定理 `comp_diagonal_diagonal`

English:
theorem comp_diagonal_diagonal
  given: [DecidableEq I] [DecidableEq J] [Zero R] (d : I -> J -> R)
  proof: by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i₁ i₂
  · rw [diagonal_apply_ne _ hi, diagonal_apply_ne _ (ne_of_apply_ne Prod.fst hi),
      Matrix.zero_apply]
  rw [diagonal_apply_eq]
  obtain hj | rfl := ne_or_eq j₁ j₂
  · rw [diagonal_apply_ne _ hj, diagonal_apply_n

中文:
定理 comp_diagonal_diagonal
  条件: [DecidableEq I] [DecidableEq J] [Zero R] (d : I -> J -> R)
  证明: by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i₁ i₂
  · rw [diagonal_apply_ne _ hi, diagonal_apply_ne _ (ne_of_apply_ne Prod.fst hi),
      Matrix.zero_apply]
  rw [diagonal_apply_eq]
  obtain hj | rfl := ne_or_eq j₁ j₂
  · rw [diagonal_apply_ne _ hj, diagonal_apply_n

Depends on / 依赖: Matrix, Matrix.zero_apply, Prod.fst, Prod.snd, comp_apply, diagonal_apply_eq, diagonal_apply_ne, ne_of_apply_ne, ne_or_eq, zero_apply
-/
theorem comp_diagonal_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I -> J -> R) :
    comp I I J J R (diagonal fun i => diagonal fun j => d i j)
      = diagonal fun ij => d ij.1 ij.2 := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i₁ i₂
  · rw [diagonal_apply_ne _ hi, diagonal_apply_ne _ (ne_of_apply_ne Prod.fst hi),
      Matrix.zero_apply]
  rw [diagonal_apply_eq]
  obtain hj | rfl := ne_or_eq j₁ j₂
  · rw [diagonal_apply_ne _ hj, diagonal_apply_ne _ (ne_of_apply_ne Prod.snd hj)]
  rw [diagonal_apply_eq]; rw [diagonal_apply_eq]

@[simp]
/--
theorem `comp_symm_diagonal` / 定理 `comp_symm_diagonal`

English:
theorem comp_symm_diagonal
  given: [DecidableEq I] [DecidableEq J] [Zero R] (d : I × J -> R)
  proof: (comp I I J J R).symm_apply_eq.2 (comp_diagonal_diagonal fun i j => d (i, j)).symm

中文:
定理 comp_symm_diagonal
  条件: [DecidableEq I] [DecidableEq J] [Zero R] (d : I × J -> R)
  证明: (comp I I J J R).symm_apply_eq.2 (comp_diagonal_diagonal fun i j => d (i, j)).symm

Depends on / 依赖: comp_diagonal_diagonal, symm_apply_eq
-/
theorem comp_symm_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I × J -> R) :
    (comp I I J J R).symm (diagonal d) = diagonal fun i => diagonal fun j => d (i, j) :=
(comp I I J J R).symm_apply_eq.2 (comp_diagonal_diagonal fun i j => d (i, j)).symm

/--
theorem `comp_transpose` / 定理 `comp_transpose`

English:
theorem comp_transpose
  given: (M : Matrix I J (Matrix K L R))
  proof: rfl

中文:
定理 comp_transpose
  条件: (M : Matrix I J (Matrix K L R))
  证明: rfl
-/
theorem comp_transpose (M : Matrix I J (Matrix K L R)) :
    comp J I K L R Mᵀ = (comp _ _ _ _ R <| M.map (·ᵀ))ᵀ := rfl

/--
theorem `comp_map_transpose` / 定理 `comp_map_transpose`

English:
theorem comp_map_transpose
  given: (M : Matrix I J (Matrix K L R))
  proof: rfl

中文:
定理 comp_map_transpose
  条件: (M : Matrix I J (Matrix K L R))
  证明: rfl
-/
theorem comp_map_transpose (M : Matrix I J (Matrix K L R)) :
    comp I J L K R (M.map (·ᵀ)) = (comp _ _ _ _ R Mᵀ)ᵀ := rfl

/--
theorem `comp_symm_transpose` / 定理 `comp_symm_transpose`

English:
theorem comp_symm_transpose
  given: (M : Matrix (I × K) (J × L) R)
  proof: rfl

中文:
定理 comp_symm_transpose
  条件: (M : Matrix (I × K) (J × L) R)
  证明: rfl
-/
theorem comp_symm_transpose (M : Matrix (I × K) (J × L) R) :
    (comp J I L K R).symm Mᵀ = (((comp I J K L R).symm M).map (·ᵀ))ᵀ := rfl

/--
theorem `transpose_comp` / 定理 `transpose_comp`

English:
theorem transpose_comp
  given: (M : Matrix I J (Matrix K L R))
  proof: rfl

中文:
定理 transpose_comp
  条件: (M : Matrix I J (Matrix K L R))
  证明: rfl
-/
theorem transpose_comp (M : Matrix I J (Matrix K L R)) :
    (comp I J K L R M)ᵀ = comp J I L K R (Mᵀ.map (·ᵀ)) :=
  rfl

end Basic

section Add

variable [Add R]

/--
Definition of `compAddEquiv` / `compAddEquiv` 的定义

English:
definition compAddEquiv
  signature: : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
  body: comp I J K L R
  map_add' _ _ := rfl

@[simp]

中文:
定义 compAddEquiv
  签名: : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
  定义体: comp I J K L R
  map_add' _ _ := rfl

@[simp]
-/
def compAddEquiv : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
  __ := comp I J K L R
  map_add' _ _ := rfl

@[simp]
/--
theorem `compAddEquiv_apply` / 定理 `compAddEquiv_apply`

English:
theorem compAddEquiv_apply
  given: (M : Matrix I J (Matrix K L R))
  proof: rfl

@[simp]

中文:
定理 compAddEquiv_apply
  条件: (M : Matrix I J (Matrix K L R))
  证明: rfl

@[simp]
-/
theorem compAddEquiv_apply (M : Matrix I J (Matrix K L R)) :
    compAddEquiv I J K L R M = comp I J K L R M := rfl

@[simp]
/--
theorem `compAddEquiv_symm_apply` / 定理 `compAddEquiv_symm_apply`

English:
theorem compAddEquiv_symm_apply
  given: (M : Matrix (I × K) (J × L) R)
  proof: rfl

中文:
定理 compAddEquiv_symm_apply
  条件: (M : Matrix (I × K) (J × L) R)
  证明: rfl
-/
theorem compAddEquiv_symm_apply (M : Matrix (I × K) (J × L) R) :
    (compAddEquiv I J K L R).symm M = (comp I J K L R).symm M := rfl

end Add

section AddCommMonoid

variable [AddCommMonoid R] [Mul R] [Fintype I] [Fintype J]

/--
Definition of `compRingEquiv` / `compRingEquiv` 的定义

English:
definition compRingEquiv
  signature: : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R where
  body: compAddEquiv I I J J R
.trans .symm Fintype.sum_prod_type .. map_mul' _ _ := by ext; exact sum_apply ..

@[simp]

中文:
定义 compRingEquiv
  签名: : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R where
  定义体: compAddEquiv I I J J R
.trans .symm Fintype.sum_prod_type .. map_mul' _ _ := by ext; exact sum_apply ..

@[simp]

Depends on / 依赖: compAddEquiv
-/
def compRingEquiv : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R where
  __ := compAddEquiv I I J J R
.trans .symm Fintype.sum_prod_type .. map_mul' _ _ := by ext; exact sum_apply ..

@[simp]
/--
theorem `compRingEquiv_apply` / 定理 `compRingEquiv_apply`

English:
theorem compRingEquiv_apply
  given: (M : Matrix I I (Matrix J J R))
  proof: rfl

@[simp]

中文:
定理 compRingEquiv_apply
  条件: (M : Matrix I I (Matrix J J R))
  证明: rfl

@[simp]
-/
theorem compRingEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compRingEquiv I J R M = comp I I J J R M := rfl

@[simp]
/--
theorem `compRingEquiv_symm_apply` / 定理 `compRingEquiv_symm_apply`

English:
theorem compRingEquiv_symm_apply
  given: (M : Matrix (I × J) (I × J) R)
  proof: rfl

中文:
定理 compRingEquiv_symm_apply
  条件: (M : Matrix (I × J) (I × J) R)
  证明: rfl
-/
theorem compRingEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compRingEquiv I J R).symm M = (comp I I J J R).symm M := rfl

instance (R) [MulOne R] [AddCommMonoid R] [DecidableEq I] [IsStablyFiniteRing R] :
    IsStablyFiniteRing (Matrix I I R) :=
  ⟨fun n => .of_injective (MonoidHom.mk ⟨_, comp_one⟩ (compRingEquiv (Fin n) I R).map_mul)
    (RingEquiv.injective _)⟩

end AddCommMonoid

section LinearMap

variable (R₀ : Type*) [Semiring R₀] [AddCommMonoid R] [Module R₀ R]

/-- `Matrix.comp` as `LinearEquiv` -/
@[simps!]
/--
Definition of `compLinearEquiv` / `compLinearEquiv` 的定义

English:
definition compLinearEquiv
  signature: : Matrix I J (Matrix K L R) ≃ₗ[R₀] Matrix (I × K) (J × L) R where
  body: compAddEquiv I J K L R
  map_smul' _ _ := rfl

中文:
定义 compLinearEquiv
  签名: : Matrix I J (Matrix K L R) ≃ₗ[R₀] Matrix (I × K) (J × L) R where
  定义体: compAddEquiv I J K L R
  map_smul' _ _ := rfl

Depends on / 依赖: compAddEquiv
-/
def compLinearEquiv : Matrix I J (Matrix K L R) ≃ₗ[R₀] Matrix (I × K) (J × L) R where
  __ := compAddEquiv I J K L R
  map_smul' _ _ := rfl

end LinearMap

section Algebra

variable (K : Type*) [CommSemiring K] [Semiring R] [Fintype I] [Fintype J] [Algebra K R]

variable [DecidableEq I] [DecidableEq J]

/--
Definition of `compAlgEquiv` / `compAlgEquiv` 的定义

English:
definition compAlgEquiv
  signature: : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R where
  body: compRingEquiv I J R
  commutes' _ := comp_diagonal_diagonal _

@[simp]

中文:
定义 compAlgEquiv
  签名: : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R where
  定义体: compRingEquiv I J R
  commutes' _ := comp_diagonal_diagonal _

@[simp]

Depends on / 依赖: Eq.refl, HEq.refl, Iff.intro, PSigma, PSigma.mk.inj, compRingEquiv
-/
def compAlgEquiv : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R where
  __ := compRingEquiv I J R
  commutes' _ := comp_diagonal_diagonal _

@[simp]
/--
theorem `compAlgEquiv_apply` / 定理 `compAlgEquiv_apply`

English:
theorem compAlgEquiv_apply
  given: (M : Matrix I I (Matrix J J R))
  proof: rfl

@[simp]

中文:
定理 compAlgEquiv_apply
  条件: (M : Matrix I I (Matrix J J R))
  证明: rfl

@[simp]
-/
theorem compAlgEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compAlgEquiv I J R K M = comp I I J J R M := rfl

@[simp]
/--
theorem `compAlgEquiv_symm_apply` / 定理 `compAlgEquiv_symm_apply`

English:
theorem compAlgEquiv_symm_apply
  given: (M : Matrix (I × J) (I × J) R)
  proof: rfl

@[simp]

中文:
定理 compAlgEquiv_symm_apply
  条件: (M : Matrix (I × J) (I × J) R)
  证明: rfl

@[simp]
-/
theorem compAlgEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compAlgEquiv I J R K).symm M = (comp I I J J R).symm M := rfl

@[simp]
/--
theorem `isUnit_comp_iff` / 定理 `isUnit_comp_iff`

English:
theorem isUnit_comp_iff
  given: {M : Matrix I I (Matrix J J R)}
  statement: IsUnit (comp _ _ _ _ _ M) ↔ IsUnit M
  proof: isUnit_map_iff (compAlgEquiv _ _ _ Nat) M

@[simp]

中文:
定理 isUnit_comp_iff
  条件: {M : Matrix I I (Matrix J J R)}
  结论: IsUnit (comp _ _ _ _ _ M) ↔ IsUnit M
  证明: isUnit_map_iff (compAlgEquiv _ _ _ Nat) M

@[simp]

Depends on / 依赖: compAlgEquiv, isUnit_map_iff
-/
theorem isUnit_comp_iff {M : Matrix I I (Matrix J J R)} : IsUnit (comp _ _ _ _ _ M) ↔ IsUnit M :=
  isUnit_map_iff (compAlgEquiv _ _ _ Nat) M

@[simp]
/--
theorem `isUnit_comp_symm_iff` / 定理 `isUnit_comp_symm_iff`

English:
theorem isUnit_comp_symm_iff
  given: {M : Matrix (I × J) (I × J) R}
  proof: isUnit_map_iff (compAlgEquiv _ _ _ Nat).symm M

中文:
定理 isUnit_comp_symm_iff
  条件: {M : Matrix (I × J) (I × J) R}
  证明: isUnit_map_iff (compAlgEquiv _ _ _ Nat).symm M

Depends on / 依赖: compAlgEquiv, isUnit_map_iff
-/
theorem isUnit_comp_symm_iff {M : Matrix (I × J) (I × J) R} :
    IsUnit (comp _ _ _ _ _ |>.symm M) ↔ IsUnit M :=
  isUnit_map_iff (compAlgEquiv _ _ _ Nat).symm M

end Algebra

end Matrix
