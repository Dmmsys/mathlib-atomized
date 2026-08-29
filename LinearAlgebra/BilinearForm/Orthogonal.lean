/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# Bilinear form

This file defines orthogonal bilinear forms.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

@[expose] public section

open LinearMap (BilinForm)
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `BilinForm.iIsOrtho`. -/
@[deprecated "Use `B x y = 0`." (since := "2026-03-30")]
/--
Definition of `IsOrtho` / `IsOrtho` 的定义

English:
definition IsOrtho
  signature: (B : BilinForm R M) (x y : M)
  body: B x y = 0

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定义 IsOrtho
  签名: (B : BilinForm R M) (x y : M)
  定义体: B x y = 0

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
-/
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_def` / 定理 `isOrtho_def`

English:
theorem isOrtho_def
  given: {B : BilinForm R M} {x y : M}
  statement: B.IsOrtho x y ↔ B x y = 0
  proof: Iff.rfl

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定理 isOrtho_def
  条件: {B : BilinForm R M} {x y : M}
  结论: B.IsOrtho x y ↔ B x y = 0
  证明: Iff.rfl

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

Depends on / 依赖: Iff.rfl
-/
theorem isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_zero_left` / 定理 `isOrtho_zero_left`

English:
theorem isOrtho_zero_left
  given: (x : M)
  statement: IsOrtho B (0 : M) x
  proof: LinearMap.isOrtho_zero_left B x

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定理 isOrtho_zero_left
  条件: (x : M)
  结论: IsOrtho B (0 : M) x
  证明: LinearMap.isOrtho_zero_left B x

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

Depends on / 依赖: LinearMap, LinearMap.isOrtho_zero_left, isOrtho_zero_left
-/
theorem isOrtho_zero_left (x : M) : IsOrtho B (0 : M) x := LinearMap.isOrtho_zero_left B x

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_zero_right` / 定理 `isOrtho_zero_right`

English:
theorem isOrtho_zero_right
  given: (x : M)
  statement: IsOrtho B x (0 : M)
  proof: zero_right x

中文:
定理 isOrtho_zero_right
  条件: (x : M)
  结论: IsOrtho B x (0 : M)
  证明: zero_right x

Depends on / 依赖: zero_right
-/
theorem isOrtho_zero_right (x : M) : IsOrtho B x (0 : M) :=
  zero_right x

/--
theorem `ne_zero_of_not_isOrtho_self` / 定理 `ne_zero_of_not_isOrtho_self`

English:
theorem ne_zero_of_not_isOrtho_self
  given: {B : BilinForm K V} (x : V) (hx₁ : B x x != 0)
  statement: x != 0
  proof: by
  by_contra; simp [this] at hx₁

中文:
定理 ne_zero_of_not_isOrtho_self
  条件: {B : BilinForm K V} (x : V) (hx₁ : B x x != 0)
  结论: x != 0
  证明: by
  by_contra; simp [this] at hx₁
-/
theorem ne_zero_of_not_isOrtho_self {B : BilinForm K V} (x : V) (hx₁ : B x x != 0) : x != 0 := by
  by_contra; simp [this] at hx₁

/--
theorem `IsRefl.eq_iff` / 定理 `IsRefl.eq_iff`

English:
theorem IsRefl.eq_iff
  given: (H : B.IsRefl) {x y : M}
  statement: B x y = 0 ↔ B y x = 0
  proof: ⟨eq_zero H, eq_zero H⟩

@[deprecated (since := "2026-03-31")]
alias IsRefl.ortho_comm := IsRefl.eq_iff

中文:
定理 IsRefl.eq_iff
  条件: (H : B.IsRefl) {x y : M}
  结论: B x y = 0 ↔ B y x = 0
  证明: ⟨eq_zero H, eq_zero H⟩

@[deprecated (since := "2026-03-31")]
alias IsRefl.ortho_comm := IsRefl.eq_iff

Depends on / 依赖: eq_zero
-/
theorem IsRefl.eq_iff (H : B.IsRefl) {x y : M} : B x y = 0 ↔ B y x = 0 :=
  ⟨eq_zero H, eq_zero H⟩

@[deprecated (since := "2026-03-31")]
alias IsRefl.ortho_comm := IsRefl.eq_iff

/--
theorem `IsAlt.eq_iff` / 定理 `IsAlt.eq_iff`

English:
theorem IsAlt.eq_iff
  given: (H : B₁.IsAlt) {x y : M₁}
  statement: B₁ x y = 0 ↔ B₁ y x = 0
  proof: LinearMap.IsAlt.eq_iff H

@[deprecated (since := "2026-03-31")]
alias IsAlt.ortho_comm := IsAlt.eq_iff

中文:
定理 IsAlt.eq_iff
  条件: (H : B₁.IsAlt) {x y : M₁}
  结论: B₁ x y = 0 ↔ B₁ y x = 0
  证明: LinearMap.IsAlt.eq_iff H

@[deprecated (since := "2026-03-31")]
alias IsAlt.ortho_comm := IsAlt.eq_iff

Depends on / 依赖: LinearMap, LinearMap.IsAlt.eq_iff, eq_iff
-/
theorem IsAlt.eq_iff (H : B₁.IsAlt) {x y : M₁} : B₁ x y = 0 ↔ B₁ y x = 0 :=
  LinearMap.IsAlt.eq_iff H

@[deprecated (since := "2026-03-31")]
alias IsAlt.ortho_comm := IsAlt.eq_iff

/--
theorem `IsSymm.eq_iff` / 定理 `IsSymm.eq_iff`

English:
theorem IsSymm.eq_iff
  given: (H : B.IsSymm) {x y : M}
  statement: B x y = 0 ↔ B y x = 0
  proof: LinearMap.IsSymm.eq_iff (isSymm_iff.1 H)

@[deprecated (since := "2026-03-31")]
alias IsSymm.ortho_comm := IsSymm.eq_iff

中文:
定理 是Symm.eq_iff
  条件: (H : B.是Symm) {x y : M}
  结论: B x y = 0 ↔ B y x = 0
  证明: LinearMap.IsSymm.eq_iff (isSymm_iff.1 H)

@[deprecated (since := "2026-03-31")]
alias IsSymm.ortho_comm := IsSymm.eq_iff

Depends on / 依赖: IsSymm, LinearMap, LinearMap.IsSymm.eq_iff, eq_iff, isSymm_iff
-/
theorem IsSymm.eq_iff (H : B.IsSymm) {x y : M} : B x y = 0 ↔ B y x = 0 :=
  LinearMap.IsSymm.eq_iff (isSymm_iff.1 H)

@[deprecated (since := "2026-03-31")]
alias IsSymm.ortho_comm := IsSymm.eq_iff

/--
Definition of `iIsOrtho` / `iIsOrtho` 的定义

English:
definition iIsOrtho
  signature: {n : Type w} (B : BilinForm R M) (v : n -> M)
  body: B.IsOrthoᵢ v

中文:
定义 iIsOrtho
  签名: {n : 类型 w} (B : BilinForm R M) (v : n -> M)
  定义体: B.IsOrthoᵢ v

Depends on / 依赖: B.IsOrtho
-/
def iIsOrtho {n : Type w} (B : BilinForm R M) (v : n -> M) : Prop :=
  B.IsOrthoᵢ v

/--
theorem `iIsOrtho_def` / 定理 `iIsOrtho_def`

English:
theorem iIsOrtho_def
  given: {n : Type w} {B : BilinForm R M} {v : n -> M}
  proof: Iff.rfl

中文:
定理 iIsOrtho_def
  条件: {n : 类型 w} {B : BilinForm R M} {v : n -> M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem iIsOrtho_def {n : Type w} {B : BilinForm R M} {v : n -> M} :
    B.iIsOrtho v ↔ forall i j : n, i != j -> B (v i) (v j) = 0 :=
  Iff.rfl

section

variable {R₄ M₄ : Type*} [CommRing R₄] [IsDomain R₄]
variable [AddCommGroup M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_smul_left` / 定理 `isOrtho_smul_left`

English:
theorem isOrtho_smul_left
  given: {x y : M₄} {a : R₄} (ha : a != 0)
  proof: by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a => (ha a).elim

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

中文:
定理 isOrtho_smul_left
  条件: {x y : M₄} {a : R₄} (ha : a != 0)
  证明: by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a => (ha a).elim

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]

Depends on / 依赖: IsOrtho, LinearMap, LinearMap.smul_apply, map_smul, mul_eq_zero, or_iff_right_iff_imp, smul_apply, smul_eq_mul
-/
theorem isOrtho_smul_left {x y : M₄} {a : R₄} (ha : a != 0) :
    IsOrtho G (a • x) y ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a => (ha a).elim

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/--
theorem `isOrtho_smul_right` / 定理 `isOrtho_smul_right`

English:
theorem isOrtho_smul_right
  given: {x y : M₄} {a : R₄} (ha : a != 0)
  proof: by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a => (ha a).elim

中文:
定理 isOrtho_smul_right
  条件: {x y : M₄} {a : R₄} (ha : a != 0)
  证明: by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a => (ha a).elim

Depends on / 依赖: IsOrtho, map_smul, mul_eq_zero, or_iff_right_iff_imp, smul_eq_mul
-/
theorem isOrtho_smul_right {x y : M₄} {a : R₄} (ha : a != 0) :
    IsOrtho G x (a • y) ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a => (ha a).elim

/--
theorem `linearIndependent_of_iIsOrtho` / 定理 `linearIndependent_of_iIsOrtho`

English:
theorem linearIndependent_of_iIsOrtho
  statement: {n : Type w} {B : BilinForm K V} {v : n -> V}
  proof: by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
  have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _ hij
    rw [iIsOrtho_def.1 hv₁

中文:
定理 linearIndependent_of_iIsOrtho
  结论: {n : 类型 w} {B : BilinForm K V} {v : n -> V}
  证明: by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
  have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _ hij
    rw [iIsOrtho_def.1 hv₁

Depends on / 依赖: Finset, Finset.sum_eq_single_of_mem, eq_zero_of_ne_zero_of_mul_right_eq_zero, iIsOrtho_def, linearIndependent_iff, mul_zero, s.sum, simp_rw, smul_left, sum_eq_single_of_mem, sum_left, zero_left
-/
theorem linearIndependent_of_iIsOrtho {n : Type w} {B : BilinForm K V} {v : n -> V}
    (hv₁ : B.iIsOrtho v) (hv₂ : forall i, B (v i) (v i) != 0) : LinearIndependent K v := by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
  have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _ hij
    rw [iIsOrtho_def.1 hv₁ _ _ hij]; rw [mul_zero]
  simp_rw [sum_left, smul_left, hsum] at this
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this

end

section Orthogonal

/--
Definition of `orthogonal` / `orthogonal` 的定义

English:
definition orthogonal
  signature: (B : BilinForm R M) (N : Submodule R M)
  body: N.orthogonalBilin B

中文:
定义 orthogonal
  签名: (B : BilinForm R M) (N : 子模 R M)
  定义体: N.orthogonalBilin B

Depends on / 依赖: N.orthogonalBilin, orthogonalBilin
-/
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M := N.orthogonalBilin B

variable {N L : Submodule R M}

@[simp]
/--
theorem `mem_orthogonal_iff` / 定理 `mem_orthogonal_iff`

English:
theorem mem_orthogonal_iff
  given: {N : Submodule R M} {m : M}
  proof: Iff.rfl

中文:
定理 mem_orthogonal_iff
  条件: {N : 子模 R M} {m : M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_orthogonal_iff {N : Submodule R M} {m : M} :
    m in B.orthogonal N ↔ forall n in N, B n m = 0 :=
  Iff.rfl

/--
lemma `orthogonal_bot` / 引理 `orthogonal_bot`

English:
lemma orthogonal_bot
  statement: B.orthogonal ⊥ = ⊤
  proof: by ext; simp

中文:
引理 orthogonal_bot
  结论: B.orthogonal ⊥ = ⊤
  证明: by ext; simp
-/
@[simp] lemma orthogonal_bot : B.orthogonal ⊥ = ⊤ := by ext; simp

/--
theorem `orthogonal_le` / 定理 `orthogonal_le`

English:
theorem orthogonal_le
  given: (h : N <= L)
  statement: B.orthogonal L <= B.orthogonal N
  proof: fun _ hn l hl => hn l (h hl)

中文:
定理 orthogonal_le
  条件: (h : N <= L)
  结论: B.orthogonal L <= B.orthogonal N
  证明: fun _ hn l hl => hn l (h hl)
-/
theorem orthogonal_le (h : N <= L) : B.orthogonal L <= B.orthogonal N := fun _ hn l hl => hn l (h hl)

/--
theorem `le_orthogonal_orthogonal` / 定理 `le_orthogonal_orthogonal`

English:
theorem le_orthogonal_orthogonal
  given: (b : B.IsRefl)
  statement: N <= B.orthogonal (B.orthogonal N)
  proof: fun n hn _ hm => b _ _ (hm n hn)

中文:
定理 le_orthogonal_orthogonal
  条件: (b : B.IsRefl)
  结论: N <= B.orthogonal (B.orthogonal N)
  证明: fun n hn _ hm => b _ _ (hm n hn)
-/
theorem le_orthogonal_orthogonal (b : B.IsRefl) : N <= B.orthogonal (B.orthogonal N) :=
  fun n hn _ hm => b _ _ (hm n hn)

/--
lemma `orthogonal_top_eq_ker` / 引理 `orthogonal_top_eq_ker`

English:
lemma orthogonal_top_eq_ker
  given: (hB : B.IsRefl)
  proof: by
  ext; simp [LinearMap.ext_iff, hB.eq_iff]

中文:
引理 orthogonal_top_eq_ker
  条件: (hB : B.IsRefl)
  证明: by
  ext; simp [LinearMap.ext_iff, hB.eq_iff]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, eq_iff, ext_iff, hB.eq_iff
-/
lemma orthogonal_top_eq_ker (hB : B.IsRefl) :
    B.orthogonal ⊤ = LinearMap.ker B := by
  ext; simp [LinearMap.ext_iff, hB.eq_iff]

/--
lemma `orthogonal_top_eq_bot` / 引理 `orthogonal_top_eq_bot`

English:
lemma orthogonal_top_eq_bot
  given: (hB : B.Nondegenerate)
  proof: (Submodule.eq_bot_iff _).mpr fun x hx => hB.2 x (by simpa using! hx)

中文:
引理 orthogonal_top_eq_bot
  条件: (hB : B.非退化)
  证明: (Submodule.eq_bot_iff _).mpr fun x hx => hB.2 x (by simpa using! hx)

Depends on / 依赖: Submodule, Submodule.eq_bot_iff, eq_bot_iff
-/
lemma orthogonal_top_eq_bot (hB : B.Nondegenerate) :
    B.orthogonal ⊤ = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun x hx => hB.2 x (by simpa using! hx)

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
/--
theorem `span_singleton_inf_orthogonal_eq_bot` / 定理 `span_singleton_inf_orthogonal_eq_bot`

English:
theorem span_singleton_inf_orthogonal_eq_bot
  given: {B : BilinForm K V} {x : V} (hx : B x x != 0)
  proof: LinearMap.span_singleton_inf_orthogonal_eq_bot B _ hx

中文:
定理 span_singleton_inf_orthogonal_eq_bot
  条件: {B : BilinForm K V} {x : V} (hx : B x x != 0)
  证明: LinearMap.span_singleton_inf_orthogonal_eq_bot B _ hx

Depends on / 依赖: LinearMap, LinearMap.span_singleton_inf_orthogonal_eq_bot, span_singleton_inf_orthogonal_eq_bot
-/
theorem span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V} (hx : B x x != 0) :
    K ∙ x ⊓ B.orthogonal (K ∙ x) = ⊥ :=
  LinearMap.span_singleton_inf_orthogonal_eq_bot B _ hx

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
/--
theorem `orthogonal_span_singleton_eq_toLin_ker` / 定理 `orthogonal_span_singleton_eq_toLin_ker`

English:
theorem orthogonal_span_singleton_eq_toLin_ker
  given: {B : BilinForm K V} (x : V)
  proof: LinearMap.orthogonal_span_singleton_eq_to_lin_ker ..

中文:
定理 orthogonal_span_singleton_eq_toLin_ker
  条件: {B : BilinForm K V} (x : V)
  证明: LinearMap.orthogonal_span_singleton_eq_to_lin_ker ..

Depends on / 依赖: LinearMap, LinearMap.orthogonal_span_singleton_eq_to_lin_ker, orthogonal_span_singleton_eq_to_lin_ker
-/
theorem orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K ∙ x) = LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ B x) :=
  LinearMap.orthogonal_span_singleton_eq_to_lin_ker ..

/--
theorem `span_singleton_sup_orthogonal_eq_top` / 定理 `span_singleton_sup_orthogonal_eq_top`

English:
theorem span_singleton_sup_orthogonal_eq_top
  given: {B : BilinForm K V} {x : V} (hx : B x x != 0)
  proof: LinearMap.span_singleton_sup_orthogonal_eq_top hx

中文:
定理 span_singleton_sup_orthogonal_eq_top
  条件: {B : BilinForm K V} {x : V} (hx : B x x != 0)
  证明: LinearMap.span_singleton_sup_orthogonal_eq_top hx

Depends on / 依赖: LinearMap, LinearMap.span_singleton_sup_orthogonal_eq_top, span_singleton_sup_orthogonal_eq_top
-/
theorem span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : B x x != 0) :
    K ∙ x ⊔ B.orthogonal (K ∙ x) = ⊤ :=
  LinearMap.span_singleton_sup_orthogonal_eq_top hx

/--
theorem `isCompl_span_singleton_orthogonal` / 定理 `isCompl_span_singleton_orthogonal`

English:
theorem isCompl_span_singleton_orthogonal
  given: {B : BilinForm K V} {x : V} (hx : B x x != 0)
  proof: LinearMap.isCompl_span_singleton_orthogonal hx

中文:
定理 isCompl_span_singleton_orthogonal
  条件: {B : BilinForm K V} {x : V} (hx : B x x != 0)
  证明: LinearMap.isCompl_span_singleton_orthogonal hx

Depends on / 依赖: LinearMap, LinearMap.isCompl_span_singleton_orthogonal, isCompl_span_singleton_orthogonal
-/
theorem isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : B x x != 0) :
    IsCompl (K ∙ x) (B.orthogonal <| K ∙ x) :=
  LinearMap.isCompl_span_singleton_orthogonal hx

end Orthogonal

variable {M₂' : Type*}
variable [AddCommMonoid M₂'] [Module R M₂']

/--
theorem `nondegenerate_restrict_of_disjoint_orthogonal` / 定理 `nondegenerate_restrict_of_disjoint_orthogonal`

English:
theorem nondegenerate_restrict_of_disjoint_orthogonal
  statement: (B : BilinForm R₁ M₁) (b : B.IsRefl)
  proof: LinearMap.nondegenerate_restrict_of_disjoint_orthogonal b hW

中文:
定理 nondegenerate_restrict_of_disjoint_orthogonal
  结论: (B : BilinForm R₁ M₁) (b : B.IsRefl)
  证明: LinearMap.nondegenerate_restrict_of_disjoint_orthogonal b hW

Depends on / 依赖: LinearMap, LinearMap.nondegenerate_restrict_of_disjoint_orthogonal, nondegenerate_restrict_of_disjoint_orthogonal
-/
theorem nondegenerate_restrict_of_disjoint_orthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl)
    {W : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) : (B.restrict W).Nondegenerate :=
  LinearMap.nondegenerate_restrict_of_disjoint_orthogonal b hW

/--
theorem `iIsOrtho.not_isOrtho_basis_self_of_nondegenerate` / 定理 `iIsOrtho.not_isOrtho_basis_self_of_nondegenerate`

English:
theorem iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
  statement: {n : Type w} [Nontrivial R]
  proof: h.not_isOrtho_basis_self_of_separatingLeft hB.1 i

中文:
定理 iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
  结论: {n : 类型 w} [非平凡 R]
  证明: h.not_isOrtho_basis_self_of_separatingLeft hB.1 i

Depends on / 依赖: h.not_isOrtho_basis_self_of_separatingLeft, not_isOrtho_basis_self_of_separatingLeft
-/
theorem iIsOrtho.not_isOrtho_basis_self_of_nondegenerate {n : Type w} [Nontrivial R]
    {B : BilinForm R M} {v : Basis n R M} (h : B.iIsOrtho v) (hB : B.Nondegenerate) (i : n) :
    B (v i) (v i) != 0 :=
  h.not_isOrtho_basis_self_of_separatingLeft hB.1 i

/--
theorem `iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self` / 定理 `iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self`

English:
theorem iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self
  statement: {n : Type w} [IsDomain R]
  proof: ⟨hO.not_isOrtho_basis_self_of_nondegenerate, hO.nondegenerate_of_not_isOrtho_basis_self _⟩

中文:
定理 iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self
  结论: {n : 类型 w} [是整环 R]
  证明: ⟨hO.not_isOrtho_basis_self_of_nondegenerate, hO.nondegenerate_of_not_isOrtho_basis_self _⟩

Depends on / 依赖: hO.nondegenerate_of_not_isOrtho_basis_self, hO.not_isOrtho_basis_self_of_nondegenerate, nondegenerate_of_not_isOrtho_basis_self, not_isOrtho_basis_self_of_nondegenerate
-/
theorem iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self {n : Type w} [IsDomain R]
    (B : BilinForm R M) (v : Basis n R M) (hO : B.iIsOrtho v) :
    B.Nondegenerate ↔ forall i, B (v i) (v i) != 0 :=
  ⟨hO.not_isOrtho_basis_self_of_nondegenerate, hO.nondegenerate_of_not_isOrtho_basis_self _⟩

section

/--
theorem `toLin_restrict_ker_eq_inf_ker` / 定理 `toLin_restrict_ker_eq_inf_ker`

English:
theorem toLin_restrict_ker_eq_inf_ker
  given: (B : BilinForm K V) (W : Subspace K V)
  proof: by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    constructor
    · simp [hx]
    · simpa
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    exact ⟨⟨x, hx.1⟩, hx.right, rfl⟩

中文:
定理 toLin_restrict_ker_eq_inf_ker
  条件: (B : BilinForm K V) (W : 子空间 K V)
  证明: by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    constructor
    · simp [hx]
    · simpa
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    exact ⟨⟨x, hx.1⟩, hx.right, rfl⟩

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Submodule, Submodule.mem_map, hx.right, mem_ker, mem_map, simp_rw
-/
theorem toLin_restrict_ker_eq_inf_ker (B : BilinForm K V) (W : Subspace K V) :
    (LinearMap.ker <| B.domRestrict W).map W.subtype = W ⊓ B.ker := by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    constructor
    · simp [hx]
    · simpa
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    exact ⟨⟨x, hx.1⟩, hx.right, rfl⟩

/--
theorem `toLin_restrict_ker_eq_inf_orthogonal` / 定理 `toLin_restrict_ker_eq_inf_orthogonal`

English:
theorem toLin_restrict_ker_eq_inf_orthogonal
  given: (B : BilinForm K V) (W : Subspace K V) (b : B.IsRefl)
  proof: by
  rw [orthogonal_top_eq_ker b]
  exact toLin_restrict_ker_eq_inf_ker ..

中文:
定理 toLin_restrict_ker_eq_inf_orthogonal
  条件: (B : BilinForm K V) (W : 子空间 K V) (b : B.IsRefl)
  证明: by
  rw [orthogonal_top_eq_ker b]
  exact toLin_restrict_ker_eq_inf_ker ..

Depends on / 依赖: orthogonal_top_eq_ker, toLin_restrict_ker_eq_inf_ker
-/
theorem toLin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V) (W : Subspace K V) (b : B.IsRefl) :
    (LinearMap.ker <| B.domRestrict W).map W.subtype = W ⊓ B.orthogonal ⊤ := by
  rw [orthogonal_top_eq_ker b]
  exact toLin_restrict_ker_eq_inf_ker ..

/--
theorem `toLin_restrict_range_dualCoannihilator_eq_orthogonal` / 定理 `toLin_restrict_range_dualCoannihilator_eq_orthogonal`

English:
theorem toLin_restrict_range_dualCoannihilator_eq_orthogonal
  statement: (B : BilinForm K V)
  proof: by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hx (B.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw

中文:
定理 toLin_restrict_range_dualCoannihilator_eq_orthogonal
  结论: (B : BilinForm K V)
  证明: by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hx (B.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw

Depends on / 依赖: B.domRestrict, Submodule, Submodule.mem_dualCoannihilator, domRestrict, mem_dualCoannihilator, mem_orthogonal_iff
-/
theorem toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V)
    (W : Subspace K V) :
    (LinearMap.range (B.domRestrict W)).dualCoannihilator = B.orthogonal W := by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hx (B.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw

/--
lemma `ker_restrict_eq_of_codisjoint` / 引理 `ker_restrict_eq_of_codisjoint`

English:
lemma ker_restrict_eq_of_codisjoint
  statement: {p q : Submodule R M} (hpq : Codisjoint p q)
  proof: by
  ext ⟨z, hz⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext w
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hpq w
    simpa [hB z hz y hy] using LinearMap.congr_fun h ⟨x, hx⟩
  · ext ⟨x, hx⟩
  

中文:
引理 ker_restrict_eq_of_codisjoint
  结论: {p q : 子模 R M} (hpq : Codisjoint p q)
  证明: by
  ext ⟨z, hz⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext w
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hpq w
    simpa [hB z hz y hy] using LinearMap.congr_fun h ⟨x, hx⟩
  · ext ⟨x, hx⟩
  

Depends on / 依赖: LinearMap, LinearMap.congr_fun, LinearMap.mem_ker, Submodule, Submodule.codisjoint_iff_exists_add_eq.mp, Submodule.coe_subtype, Submodule.mem_comap, codisjoint_iff_exists_add_eq, coe_subtype, congr_fun, mem_comap, mem_ker
-/
lemma ker_restrict_eq_of_codisjoint {p q : Submodule R M} (hpq : Codisjoint p q)
    {B : LinearMap.BilinForm R M} (hB : forall x in p, forall y in q, B x y = 0) :
    LinearMap.ker (B.restrict p) = (LinearMap.ker B).comap p.subtype := by
  ext ⟨z, hz⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext w
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hpq w
    simpa [hB z hz y hy] using LinearMap.congr_fun h ⟨x, hx⟩
  · ext ⟨x, hx⟩
    simpa using LinearMap.congr_fun h x

/--
lemma `inf_orthogonal_self_le_ker_restrict` / 引理 `inf_orthogonal_self_le_ker_restrict`

English:
lemma inf_orthogonal_self_le_ker_restrict
  given: {W : Submodule R M} (b₁ : B.IsRefl)
  proof: by
  rintro v ⟨hv : v in W, hv' : v in B.orthogonal W⟩
  simp only [Submodule.mem_map, mem_ker, restrict_apply, Submodule.coe_subtype, Subtype.exists,
    exists_and_left, exists_prop, exists_eq_right_right]
  refine ⟨?_, hv⟩
  ext ⟨w, hw⟩
exact b₁ w v hv' w hw

中文:
引理 inf_orthogonal_self_le_ker_restrict
  条件: {W : 子模 R M} (b₁ : B.IsRefl)
  证明: by
  rintro v ⟨hv : v in W, hv' : v in B.orthogonal W⟩
  simp only [Submodule.mem_map, mem_ker, restrict_apply, Submodule.coe_subtype, Subtype.exists,
    exists_and_left, exists_prop, exists_eq_right_right]
  refine ⟨?_, hv⟩
  ext ⟨w, hw⟩
exact b₁ w v hv' w hw

Depends on / 依赖: B.orthogonal, Submodule, Submodule.coe_subtype, Submodule.mem_map, Subtype, Subtype.exists, coe_subtype, exists_and_left, exists_eq_right_right, exists_prop, mem_ker, mem_map, orthogonal, restrict_apply
-/
lemma inf_orthogonal_self_le_ker_restrict {W : Submodule R M} (b₁ : B.IsRefl) :
    W ⊓ B.orthogonal W <= (LinearMap.ker <| B.restrict W).map W.subtype := by
  rintro v ⟨hv : v in W, hv' : v in B.orthogonal W⟩
  simp only [Submodule.mem_map, mem_ker, restrict_apply, Submodule.coe_subtype, Subtype.exists,
    exists_and_left, exists_prop, exists_eq_right_right]
  refine ⟨?_, hv⟩
  ext ⟨w, hw⟩
exact b₁ w v hv' w hw

variable [FiniteDimensional K V]

open Module Submodule

variable {B : BilinForm K V}

/--
theorem `finrank_add_finrank_orthogonal'` / 定理 `finrank_add_finrank_orthogonal'`

English:
theorem finrank_add_finrank_orthogonal'
  given: (W : Submodule K V)
  proof: by
  rw [← toLin_restrict_ker_eq_inf_ker _ _]; rw [←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _]; rw [finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W))]; rw [add_comm]; rw [← ad

中文:
定理 finrank_add_finrank_orthogonal'
  条件: (W : 子模 K V)
  证明: by
  rw [← toLin_restrict_ker_eq_inf_ker _ _]; rw [←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _]; rw [finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W))]; rw [add_comm]; rw [← ad

Depends on / 依赖: B.domRestrict, LinearMap, LinearMap.finrank_range_add_finrank_ker, LinearMap.ker, LinearMap.range, Subspace, Subspace.finrank_add_finrank_dualCoannihilator_eq, add_assoc, add_comm, conv_rhs, domRestrict, finrank, finrank_add_finrank_dualCoannihilator_eq, finrank_map_subtype_eq, finrank_range_add_finrank_ker, toLin_restrict_ker_eq_inf_ker, toLin_restrict_range_dualCoannihilator_eq_orthogonal
-/
theorem finrank_add_finrank_orthogonal' (W : Submodule K V) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.ker : Subspace K V) := by
  rw [← toLin_restrict_ker_eq_inf_ker _ _]; rw [←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _]; rw [finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W))]; rw [add_comm]; rw [← add_assoc]; rw [add_comm (finrank K (LinearMap.ker (B.domRestrict W)))]; rw [LinearMap.finrank_range_add_finrank_ker]

/--
theorem `finrank_add_finrank_orthogonal` / 定理 `finrank_add_finrank_orthogonal`

English:
theorem finrank_add_finrank_orthogonal
  given: (b₁ : B.IsRefl) (W : Submodule K V)
  proof: by
  rw [orthogonal_top_eq_ker b₁]
  exact finrank_add_finrank_orthogonal' _

中文:
定理 finrank_add_finrank_orthogonal
  条件: (b₁ : B.IsRefl) (W : 子模 K V)
  证明: by
  rw [orthogonal_top_eq_ker b₁]
  exact finrank_add_finrank_orthogonal' _

Depends on / 依赖: finrank_add_finrank_orthogonal, orthogonal_top_eq_ker
-/
theorem finrank_add_finrank_orthogonal (b₁ : B.IsRefl) (W : Submodule K V) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  rw [orthogonal_top_eq_ker b₁]
  exact finrank_add_finrank_orthogonal' _

/--
lemma `finrank_orthogonal` / 引理 `finrank_orthogonal`

English:
lemma finrank_orthogonal
  given: (hB : B.Nondegenerate) (W : Submodule K V)
  proof: by
  have := finrank_add_finrank_orthogonal' (B := B) W
  rw [hB.ker_eq_bot]; rw [inf_bot_eq]; rw [finrank_bot]; rw [add_zero] at this
  lia

中文:
引理 finrank_orthogonal
  条件: (hB : B.非退化) (W : 子模 K V)
  证明: by
  have := finrank_add_finrank_orthogonal' (B := B) W
  rw [hB.ker_eq_bot]; rw [inf_bot_eq]; rw [finrank_bot]; rw [add_zero] at this
  lia

Depends on / 依赖: add_zero, finrank_add_finrank_orthogonal, finrank_bot, hB.ker_eq_bot, inf_bot_eq, ker_eq_bot
-/
lemma finrank_orthogonal (hB : B.Nondegenerate) (W : Submodule K V) :
    finrank K (B.orthogonal W) = finrank K V - finrank K W := by
  have := finrank_add_finrank_orthogonal' (B := B) W
  rw [hB.ker_eq_bot]; rw [inf_bot_eq]; rw [finrank_bot]; rw [add_zero] at this
  lia

/--
lemma `orthogonal_orthogonal` / 引理 `orthogonal_orthogonal`

English:
lemma orthogonal_orthogonal
  given: (hB : B.Nondegenerate) (hB₀ : B.IsRefl) (W : Submodule K V)
  proof: by
  apply (eq_of_le_of_finrank_le (LinearMap.BilinForm.le_orthogonal_orthogonal hB₀) _).symm
  simp only [finrank_orthogonal hB]
  lia

中文:
引理 orthogonal_orthogonal
  条件: (hB : B.非退化) (hB₀ : B.IsRefl) (W : 子模 K V)
  证明: by
  apply (eq_of_le_of_finrank_le (LinearMap.BilinForm.le_orthogonal_orthogonal hB₀) _).symm
  simp only [finrank_orthogonal hB]
  lia

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.le_orthogonal_orthogonal, eq_of_le_of_finrank_le, finrank_orthogonal, le_orthogonal_orthogonal
-/
lemma orthogonal_orthogonal (hB : B.Nondegenerate) (hB₀ : B.IsRefl) (W : Submodule K V) :
    B.orthogonal (B.orthogonal W) = W := by
  apply (eq_of_le_of_finrank_le (LinearMap.BilinForm.le_orthogonal_orthogonal hB₀) _).symm
  simp only [finrank_orthogonal hB]
  lia

variable {W : Submodule K V}

/--
lemma `isCompl_orthogonal_iff_disjoint` / 引理 `isCompl_orthogonal_iff_disjoint`

English:
lemma isCompl_orthogonal_iff_disjoint
  given: (hB₀ : B.IsRefl)
  proof: by
  refine ⟨IsCompl.disjoint, fun h => ⟨h, ?_⟩⟩
  rw [codisjoint_iff]
  apply (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  calc
    finrank K V <= finrank K V + finrank K ↥(W ⊓ B.orthogonal ⊤) := le_self_add
    _ <= finrank K ↥(W ⊔ B.orthogonal W) + finrank K ↥(W ⊓ B.orthogonal W) := ?_
 

中文:
引理 isCompl_orthogonal_iff_disjoint
  条件: (hB₀ : B.IsRefl)
  证明: by
  refine ⟨IsCompl.disjoint, fun h => ⟨h, ?_⟩⟩
  rw [codisjoint_iff]
  apply (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  calc
    finrank K V <= finrank K V + finrank K ↥(W ⊓ B.orthogonal ⊤) := le_self_add
    _ <= finrank K ↥(W ⊔ B.orthogonal W) + finrank K ↥(W ⊓ B.orthogonal W) := ?_
 

Depends on / 依赖: B.orthogonal, IsCompl, IsCompl.disjoint, antisymm, codisjoint_iff, disjoint, eq_bot, eq_top_of_finrank_eq, finrank, finrank_add_finrank_orthogonal, finrank_le, finrank_sup_add_finrank_inf_eq, h.eq_bot, le_self_add, orthogonal
-/
lemma isCompl_orthogonal_iff_disjoint (hB₀ : B.IsRefl) :
    IsCompl W (B.orthogonal W) ↔ Disjoint W (B.orthogonal W) := by
  refine ⟨IsCompl.disjoint, fun h => ⟨h, ?_⟩⟩
  rw [codisjoint_iff]
  apply (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  calc
    finrank K V <= finrank K V + finrank K ↥(W ⊓ B.orthogonal ⊤) := le_self_add
    _ <= finrank K ↥(W ⊔ B.orthogonal W) + finrank K ↥(W ⊓ B.orthogonal W) := ?_
    _ <= finrank K ↥(W ⊔ B.orthogonal W) := by simp [h.eq_bot]
  rw [finrank_sup_add_finrank_inf_eq]; rw [finrank_add_finrank_orthogonal hB₀ W]

/--
theorem `isCompl_orthogonal_of_restrict_nondegenerate` / 定理 `isCompl_orthogonal_of_restrict_nondegenerate`

English:
theorem isCompl_orthogonal_of_restrict_nondegenerate
  proof: by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    refine Subtype.mk_eq_mk.1 (b₂.1 ⟨x, hx₁⟩ ?_)
    rintro ⟨n, hn⟩
    simp only [restrict_apply, domRestrict_apply]
    exact b₁ n x (b₁ x n (b₁ n x (hx₂ n hn)))
  refine IsCompl.of_eq

中文:
定理 isCompl_orthogonal_of_restrict_nondegenerate
  证明: by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    refine Subtype.mk_eq_mk.1 (b₂.1 ⟨x, hx₁⟩ ?_)
    rintro ⟨n, hn⟩
    simp only [restrict_apply, domRestrict_apply]
    exact b₁ n x (b₁ x n (b₁ n x (hx₂ n hn)))
  refine IsCompl.of_eq

Depends on / 依赖: B.orthogonal, IsCompl, IsCompl.of_eq, Subtype, Subtype.mk_eq_mk, add_zero, antisymm, conv_rhs, domRestrict_apply, eq_bot_iff, eq_top_of_finrank_eq, finrank, finrank_add_finrank_orthogonal, finrank_bot, finrank_le, finrank_sup_add_finrank_inf_eq, le_self_add, mem_inf, mk_eq_mk, of_eq
-/
theorem isCompl_orthogonal_of_restrict_nondegenerate
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    refine Subtype.mk_eq_mk.1 (b₂.1 ⟨x, hx₁⟩ ?_)
    rintro ⟨n, hn⟩
    simp only [restrict_apply, domRestrict_apply]
    exact b₁ n x (b₁ x n (b₁ n x (hx₂ n hn)))
  refine IsCompl.of_eq this (eq_top_of_finrank_eq <| (finrank_le _).antisymm ?_)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K V]; rw [← this]; rw [finrank_sup_add_finrank_inf_eq]; rw [finrank_add_finrank_orthogonal b₁]
  exact le_self_add

/--
theorem `restrict_nondegenerate_iff_isCompl_orthogonal` / 定理 `restrict_nondegenerate_iff_isCompl_orthogonal`

English:
theorem restrict_nondegenerate_iff_isCompl_orthogonal
  proof: ⟨fun b₂ => isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂, fun h =>
    B.nondegenerate_restrict_of_disjoint_orthogonal b₁ h.1⟩

中文:
定理 restrict_nondegenerate_iff_isCompl_orthogonal
  证明: ⟨fun b₂ => isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂, fun h =>
    B.nondegenerate_restrict_of_disjoint_orthogonal b₁ h.1⟩

Depends on / 依赖: B.nondegenerate_restrict_of_disjoint_orthogonal, isCompl_orthogonal_of_restrict_nondegenerate, nondegenerate_restrict_of_disjoint_orthogonal
-/
theorem restrict_nondegenerate_iff_isCompl_orthogonal
    (b₁ : B.IsRefl) : (B.restrict W).Nondegenerate ↔ IsCompl W (B.orthogonal W) :=
  ⟨fun b₂ => isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂, fun h =>
    B.nondegenerate_restrict_of_disjoint_orthogonal b₁ h.1⟩

/--
lemma `orthogonal_eq_top_iff` / 引理 `orthogonal_eq_top_iff`

English:
lemma orthogonal_eq_top_iff
  given: (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate)
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).inf_eq_bot
  rwa [h, inf_top_eq] at this

中文:
引理 orthogonal_eq_top_iff
  条件: (b₁ : B.IsRefl) (b₂ : (B.restrict W).非退化)
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).inf_eq_bot
  rwa [h, inf_top_eq] at this

Depends on / 依赖: B.isCompl_orthogonal_of_restrict_nondegenerate, inf_eq_bot, inf_top_eq, isCompl_orthogonal_of_restrict_nondegenerate
-/
lemma orthogonal_eq_top_iff (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) :
    B.orthogonal W = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).inf_eq_bot
  rwa [h, inf_top_eq] at this

/--
lemma `eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot` / 引理 `eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot`

English:
lemma eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
  proof: by
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).sup_eq_top
  rwa [b₃, sup_bot_eq] at this

中文:
引理 eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
  证明: by
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).sup_eq_top
  rwa [b₃, sup_bot_eq] at this

Depends on / 依赖: B.isCompl_orthogonal_of_restrict_nondegenerate, isCompl_orthogonal_of_restrict_nondegenerate, sup_bot_eq, sup_eq_top
-/
lemma eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) (b₃ : B.orthogonal W = ⊥) :
    W = ⊤ := by
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).sup_eq_top
  rwa [b₃, sup_bot_eq] at this

/--
lemma `orthogonal_eq_bot_iff` / 引理 `orthogonal_eq_bot_iff`

English:
lemma orthogonal_eq_bot_iff
  proof: by
  refine ⟨eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot b₁ b₂, fun h => ?_⟩
  rw [h]; rw [eq_bot_iff]
exact fun x hx => b₃.1 x fun y => b₁ y x by simpa using! hx y

中文:
引理 orthogonal_eq_bot_iff
  证明: by
  refine ⟨eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot b₁ b₂, fun h => ?_⟩
  rw [h]; rw [eq_bot_iff]
exact fun x hx => b₃.1 x fun y => b₁ y x by simpa using! hx y

Depends on / 依赖: eq_bot_iff, eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
-/
lemma orthogonal_eq_bot_iff
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) (b₃ : B.Nondegenerate) :
    B.orthogonal W = ⊥ ↔ W = ⊤ := by
  refine ⟨eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot b₁ b₂, fun h => ?_⟩
  rw [h]; rw [eq_bot_iff]
exact fun x hx => b₃.1 x fun y => b₁ y x by simpa using! hx y

end

/-! We note that we cannot use `BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` for the
lemma below since the below lemma does not require `V` to be finite dimensional. However,
`BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` does not require `B` to be nondegenerate
on the whole space. -/


/--
theorem `restrict_nondegenerate_orthogonal_spanSingleton` / 定理 `restrict_nondegenerate_orthogonal_spanSingleton`

English:
theorem restrict_nondegenerate_orthogonal_spanSingleton
  statement: (B : BilinForm K V) (b₁ : B.Nondegenerate)
  proof: by
  have (n : V) : n in K ∙ x ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  refine ⟨fun m hm => Submodule.coe_eq_zero.1 (b₁.1 m fun n => ?_),
    fun m hm => Submodule.coe_eq_zero.1 (b₁.2 m fun n => ?_)⟩ <;>
obtain ⟨y, hy, z, hz, rfl⟩ := Submodul

中文:
定理 restrict_nondegenerate_orthogonal_spanSingleton
  结论: (B : BilinForm K V) (b₁ : B.非退化)
  证明: by
  have (n : V) : n in K ∙ x ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  refine ⟨fun m hm => Submodule.coe_eq_zero.1 (b₁.1 m fun n => ?_),
    fun m hm => Submodule.coe_eq_zero.1 (b₁.2 m fun n => ?_)⟩ <;>
obtain ⟨y, hy, z, hz, rfl⟩ := Submodul

Depends on / 依赖: B.orthogonal, Submodule, Submodule.coe_eq_zero, Submodule.mem_sup, Submodule.mem_top, add_left, add_right, add_zero, coe_eq_zero, mem_sup, mem_top, orthogonal, span_singleton_sup_orthogonal_eq_top
-/
theorem restrict_nondegenerate_orthogonal_spanSingleton (B : BilinForm K V) (b₁ : B.Nondegenerate)
    (b₂ : B.IsRefl) {x : V} (hx : B x x != 0) :
Nondegenerate B.restrict B.orthogonal (K ∙ x) := by
  have (n : V) : n in K ∙ x ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  refine ⟨fun m hm => Submodule.coe_eq_zero.1 (b₁.1 m fun n => ?_),
    fun m hm => Submodule.coe_eq_zero.1 (b₁.2 m fun n => ?_)⟩ <;>
obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this n
  · rw [add_right, b₂ y m <| m.2 y hy, show B m z = 0 from hm ⟨z, hz⟩, add_zero]
  · rw [add_left, m.2 y hy, show B z m = 0 from hm ⟨z, hz⟩, add_zero]

end BilinForm

end LinearMap
