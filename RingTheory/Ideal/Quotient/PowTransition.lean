/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jiedong Jiang
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The quotient map from `R ⧸ I ^ m` to `R ⧸ I ^ n` where `m ≥ n`

In this file we define the canonical quotient linear map from
`M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` and canonical quotient ring map from
`R ⧸ I ^ m` to `R ⧸ I ^ n`. These definitions will be used in theorems
related to `IsAdicComplete` to find a lift element from compatible sequences in the quotients.
We also include results about the relation between quotients of submodules and quotients of
ideals here.

## Main definitions
- `Submodule.factorPow`: the linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
  the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.
- `Ideal.Quotient.factorPow`: the ring homomorphism from `R ⧸ I ^ m`
  to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.

## Main results
-/

@[expose] public section

/- Since `Mathlib/LinearAlgebra/Quotient/Basic.lean` and
`Mathlib/RingTheory/Ideal/Quotient/Defs.lean` do not import each other, and the first file that
imports both of them is `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, which has already
established the first isomorphism theorem and Chinese remainder theorem, we put these pure technical
lemmas that involves both `Submodule.mapQ` and `Ideal.Quotient.factor` in this file. -/

open Ideal Quotient

variable {R : Type*} [Ring R] {I J K : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]

/--
lemma `Ideal.Quotient.factor_ker` / 引理 `Ideal.Quotient.factor_ker`

English:
lemma Ideal.Quotient.factor_ker
  given: (H : I <= J) [I.IsTwoSided] [J.IsTwoSided]
  proof: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [factor, RingHom.mem_ker, lift_mk, eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases mem_image_of_mem_map_of_surjective _ Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa [← eq, Ideal.Quotient.eq_zero_iff_mem] using hr

中文:
引理 理想.商.factor_ker
  条件: (H : I <= J) [I.是TwoSided] [J.是TwoSided]
  证明: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [factor, RingHom.mem_ker, lift_mk, eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases mem_image_of_mem_map_of_surjective _ Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa [← eq, Ideal.Quotient.eq_zero_iff_mem] using hr

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_surjective, Ideal.mem_map_of_mem, Quotient, RingHom, RingHom.mem_ker, eq_zero_iff_mem, factor, lift_mk, mem_image_of_mem_map_of_surjective, mem_ker, mem_map_of_mem, mk_surjective
-/
lemma Ideal.Quotient.factor_ker (H : I <= J) [I.IsTwoSided] [J.IsTwoSided] :
    RingHom.ker (factor H) = J.map (Ideal.Quotient.mk I) := by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [factor, RingHom.mem_ker, lift_mk, eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases mem_image_of_mem_map_of_surjective _ Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa [← eq, Ideal.Quotient.eq_zero_iff_mem] using hr

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Submodule.eq_factor_of_eq_factor_succ` / 引理 `Submodule.eq_factor_of_eq_factor_succ`

English:
lemma Submodule.eq_factor_of_eq_factor_succ
  statement: {p : Nat -> Submodule R M}
  proof: by
  have : n = m + (n - m) := (Nat.add_sub_of_le g).symm
  induction hmn : n - m generalizing m n with
  | zero =>
    rw [hmn]; rw [Nat.add_zero] at this
    subst this
    simp
  | succ k ih =>
    rw [hmn]; rw [← add_assoc] at this
    subst this
    rw [ih (m.le_add_right k) (by simp)]; rw [h]
    · simp
    · lia

中文:
引理 子模.eq_factor_of_eq_factor_succ
  结论: {p : 自然数 -> 子模 R M}
  证明: by
  have : n = m + (n - m) := (Nat.add_sub_of_le g).symm
  induction hmn : n - m generalizing m n with
  | zero =>
    rw [hmn]; rw [Nat.add_zero] at this
    subst this
    simp
  | succ k ih =>
    rw [hmn]; rw [← add_assoc] at this
    subst this
    rw [ih (m.le_add_right k) (by simp)]; rw [h]
    · simp
    · lia

Depends on / 依赖: Nat.add_sub_of_le, Nat.add_zero, add_assoc, add_sub_of_le, add_zero, generalizing, le_add_right, m.le_add_right
-/
lemma Submodule.eq_factor_of_eq_factor_succ {p : Nat -> Submodule R M}
    (hp : Antitone p) (x : (n : Nat) -> M ⧸ (p n)) (h : forall m, x m = factor (hp m.le_succ) (x (m + 1)))
    {m n : Nat} (g : m <= n) : x m = factor (hp g) (x n) := by
  have : n = m + (n - m) := (Nat.add_sub_of_le g).symm
  induction hmn : n - m generalizing m n with
  | zero =>
    rw [hmn]; rw [Nat.add_zero] at this
    subst this
    simp
  | succ k ih =>
    rw [hmn]; rw [← add_assoc] at this
    subst this
    rw [ih (m.le_add_right k) (by simp)]; rw [h]
    · simp
    · lia

/--
lemma `Ideal.Quotient.eq_factor_of_eq_factor_succ` / 引理 `Ideal.Quotient.eq_factor_of_eq_factor_succ`

English:
lemma Ideal.Quotient.eq_factor_of_eq_factor_succ
  statement: {I : Nat -> Ideal R} [forall n, (I n).IsTwoSided]
  proof: Submodule.eq_factor_of_eq_factor_succ hI x h g

中文:
引理 理想.商.eq_factor_of_eq_factor_succ
  结论: {I : 自然数 -> 理想 R} [对任意 n, (I n).是TwoSided]
  证明: Submodule.eq_factor_of_eq_factor_succ hI x h g

Depends on / 依赖: Submodule, Submodule.eq_factor_of_eq_factor_succ, eq_factor_of_eq_factor_succ
-/
lemma Ideal.Quotient.eq_factor_of_eq_factor_succ {I : Nat -> Ideal R} [forall n, (I n).IsTwoSided]
    (hI : Antitone I) (x : (n : Nat) -> R ⧸ (I n)) (h : forall m, x m = factor (hI m.le_succ) (x (m + 1)))
    {m n : Nat} (g : m <= n) : x m = factor (hI g) (x n) :=
  Submodule.eq_factor_of_eq_factor_succ hI x h g

/--
lemma `Ideal.map_mk_comap_factor` / 引理 `Ideal.map_mk_comap_factor`

English:
lemma Ideal.map_mk_comap_factor
  given: [J.IsTwoSided] [K.IsTwoSided] (hIJ : J <= I) (hJK : K <= J)
  proof: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases mem_image_of_mem_map_of_surjective (mk J) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    have : x - ((mk K) r) in J.map (mk K) := by
      simp [← factor_ker hJK, ← eq]
    rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((mk K) r) x]; rw [← eq']; rw [← map_add]
    exact mem_map_of_mem (mk K) (Submodule.add_mem _ hr (hIJ hs))
  · rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [← eq] using! mem_map_of_mem (mk J) hr

中文:
引理 理想.map_mk_comap_factor
  条件: [J.是TwoSided] [K.是TwoSided] (hIJ : J <= I) (hJK : K <= J)
  证明: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases mem_image_of_mem_map_of_surjective (mk J) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    have : x - ((mk K) r) in J.map (mk K) := by
      simp [← factor_ker hJK, ← eq]
    rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((mk K) r) x]; rw [← eq']; rw [← map_add]
    exact mem_map_of_mem (mk K) (Submodule.add_mem _ hr (hIJ hs))
  · rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [← eq] using! mem_map_of_mem (mk J) hr

Depends on / 依赖: J.map, Quotient, Quotient.mk_surject, Quotient.mk_surjective, Submodule, Submodule.add_mem, add_mem, add_sub_cancel, factor_ker, map_add, mem_image_of_mem_map_of_surjective, mem_map_of_mem, mk_surject, mk_surjective
-/
lemma Ideal.map_mk_comap_factor [J.IsTwoSided] [K.IsTwoSided] (hIJ : J <= I) (hJK : K <= J) :
    (I.map (mk J)).comap (factor hJK) = I.map (mk K) := by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases mem_image_of_mem_map_of_surjective (mk J) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    have : x - ((mk K) r) in J.map (mk K) := by
      simp [← factor_ker hJK, ← eq]
    rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((mk K) r) x]; rw [← eq']; rw [← map_add]
    exact mem_map_of_mem (mk K) (Submodule.add_mem _ hr (hIJ hs))
  · rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [← eq] using! mem_map_of_mem (mk J) hr

namespace Submodule

open Submodule

section

@[simp]
/--
theorem `mapQ_eq_factor` / 定理 `mapQ_eq_factor`

English:
theorem mapQ_eq_factor
  given: (h : I <= J) (x : R ⧸ I)
  proof: rfl

@[simp]

中文:
定理 mapQ_eq_factor
  条件: (h : I <= J) (x : R ⧸ I)
  证明: rfl

@[simp]
-/
theorem mapQ_eq_factor (h : I <= J) (x : R ⧸ I) :
    mapQ I J LinearMap.id h x = factor h x := rfl

@[simp]
/--
theorem `factor_eq_factor` / 定理 `factor_eq_factor`

English:
theorem factor_eq_factor
  given: [I.IsTwoSided] [J.IsTwoSided] (h : I <= J) (x : R ⧸ I)
  proof: rfl

中文:
定理 factor_eq_factor
  条件: [I.是TwoSided] [J.是TwoSided] (h : I <= J) (x : R ⧸ I)
  证明: rfl
-/
theorem factor_eq_factor [I.IsTwoSided] [J.IsTwoSided] (h : I <= J) (x : R ⧸ I) :
    Submodule.factor h x = Ideal.Quotient.factor h x := rfl

end

variable (I M)

/--
lemma `pow_smul_top_le` / 引理 `pow_smul_top_le`

English:
lemma pow_smul_top_le
  given: {m n : Nat} (h : m <= n)
  statement: (I ^ n • ⊤ : Submodule R M) <= I ^ m • ⊤
  proof: smul_mono_left (Ideal.pow_le_pow_right h)

中文:
引理 pow_smul_top_le
  条件: {m n : 自然数} (h : m <= n)
  结论: (I ^ n • ⊤ : 子模 R M) <= I ^ m • ⊤
  证明: smul_mono_left (Ideal.pow_le_pow_right h)

Depends on / 依赖: Ideal.pow_le_pow_right, pow_le_pow_right, smul_mono_left
-/
lemma pow_smul_top_le {m n : Nat} (h : m <= n) : (I ^ n • ⊤ : Submodule R M) <= I ^ m • ⊤ :=
  smul_mono_left (Ideal.pow_le_pow_right h)

/--
Definition of `factorPow` / `factorPow` 的定义

English:
abbreviation factorPow
  signature: {m n : Nat} (le : m <= n)
  body: factor (smul_mono_left (Ideal.pow_le_pow_right le))

中文:
缩写 factorPow
  签名: {m n : 自然数} (le : m <= n)
  定义体: factor (smul_mono_left (Ideal.pow_le_pow_right le))

Depends on / 依赖: Ideal.pow_le_pow_right, factor, pow_le_pow_right, smul_mono_left
-/
abbrev factorPow {m n : Nat} (le : m <= n) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) ->ₗ[R] M ⧸ (I ^ m • ⊤ : Submodule R M) :=
  factor (smul_mono_left (Ideal.pow_le_pow_right le))

/--
Definition of `factorPowSucc` / `factorPowSucc` 的定义

English:
abbreviation factorPowSucc
  signature: (m : Nat)
  body: factorPow I M (Nat.le_succ m)

中文:
缩写 factorPowSucc
  签名: (m : 自然数)
  定义体: factorPow I M (Nat.le_succ m)

Depends on / 依赖: Nat.le_succ, factorPow, le_succ
-/
abbrev factorPowSucc (m : Nat) : M ⧸ (I ^ (m + 1) • ⊤ : Submodule R M) ->ₗ[R]
    M ⧸ (I ^ m • ⊤ : Submodule R M) := factorPow I M (Nat.le_succ m)

end Submodule

namespace Ideal

namespace Quotient

variable [I.IsTwoSided]

variable (I)

/--
Definition of `factorPow` / `factorPow` 的定义

English:
abbreviation factorPow
  signature: {m n : Nat} (le : n <= m)
  body: factor (pow_le_pow_right le)

中文:
缩写 factorPow
  签名: {m n : 自然数} (le : n <= m)
  定义体: factor (pow_le_pow_right le)

Depends on / 依赖: factor, pow_le_pow_right
-/
abbrev factorPow {m n : Nat} (le : n <= m) : R ⧸ I ^ m ->+* R ⧸ I ^ n :=
  factor (pow_le_pow_right le)

/--
Definition of `factorPowSucc` / `factorPowSucc` 的定义

English:
abbreviation factorPowSucc
  signature: (n : Nat)
  body: factorPow I (Nat.le_succ n)

中文:
缩写 factorPowSucc
  签名: (n : 自然数)
  定义体: factorPow I (Nat.le_succ n)

Depends on / 依赖: Nat.le_succ, factorPow, le_succ
-/
abbrev factorPowSucc (n : Nat) : R ⧸ I ^ (n + 1) ->+* R ⧸ I ^ n :=
  factorPow I (Nat.le_succ n)

end Quotient

end Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)

/--
lemma `Ideal.map_mk_comap_factorPow` / 引理 `Ideal.map_mk_comap_factorPow`

English:
lemma Ideal.map_mk_comap_factorPow
  given: {a b : Nat} (apos : 0 < a) (le : a <= b)
  proof: by
  apply Ideal.map_mk_comap_factor
  exact pow_le_self (Nat.ne_zero_of_lt apos)

中文:
引理 理想.map_mk_comap_factorPow
  条件: {a b : 自然数} (apos : 0 < a) (le : a <= b)
  证明: by
  apply Ideal.map_mk_comap_factor
  exact pow_le_self (Nat.ne_zero_of_lt apos)

Depends on / 依赖: Ideal.map_mk_comap_factor, Nat.ne_zero_of_lt, map_mk_comap_factor, ne_zero_of_lt, pow_le_self
-/
lemma Ideal.map_mk_comap_factorPow {a b : Nat} (apos : 0 < a) (le : a <= b) :
    (I.map (mk (I ^ a))).comap (factorPow I le) = I.map (mk (I ^ b)) := by
  apply Ideal.map_mk_comap_factor
  exact pow_le_self (Nat.ne_zero_of_lt apos)

variable {I} in
/--
lemma `factorPowSucc.isUnit_of_isUnit_image` / 引理 `factorPowSucc.isUnit_of_isUnit_image`

English:
lemma factorPowSucc.isUnit_of_isUnit_image
  statement: {n : Nat} (npos : n > 0) {a : R ⧸ I ^ (n + 1)}
  proof: by
  rcases isUnit_iff_exists.mp h with ⟨b, hb, _⟩
  rcases factor_surjective (pow_le_pow_right n.le_succ) b with ⟨b', hb'⟩
  rw [← hb']; rw [← map_one (factorPow I n.le_succ)]; rw [← map_mul] at hb
  apply (RingHom.sub_mem_ker_iff (factorPow I n.le_succ)).mpr at hb
  rw [factor_ker (pow_le_pow_right n.le_succ)] at hb
  rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (I ^ (n + 1)))
    Ideal.Quotient.mk_surjective hb with ⟨c, hc, eq⟩
  refine .of_mul_eq_one (b' * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c)) ?_
  calc
    _ = (a * b' - 1) * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) +
        (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) := by ring
    _ = 1 := by
      rw [← eq]; rw [mul_sub]; rw [mul_one]; rw [sub_add_sub_cancel']; rw [sub_eq_self]; rw [← map_mul]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [pow_add]
      apply Ideal.mul_mem_mul hc (Ideal.mul_le_right (I := I ^ (n - 1)) _)
      simpa only [← pow_add, Nat.sub_add_cancel npos] using! hc

中文:
引理 factorPowSucc.isUnit_of_isUnit_image
  结论: {n : 自然数} (npos : n > 0) {a : R ⧸ I ^ (n + 1)}
  证明: by
  rcases isUnit_iff_exists.mp h with ⟨b, hb, _⟩
  rcases factor_surjective (pow_le_pow_right n.le_succ) b with ⟨b', hb'⟩
  rw [← hb']; rw [← map_one (factorPow I n.le_succ)]; rw [← map_mul] at hb
  apply (RingHom.sub_mem_ker_iff (factorPow I n.le_succ)).mpr at hb
  rw [factor_ker (pow_le_pow_right n.le_succ)] at hb
  rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (I ^ (n + 1)))
    Ideal.Quotient.mk_surjective hb with ⟨c, hc, eq⟩
  refine .of_mul_eq_one (b' * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c)) ?_
  calc
    _ = (a * b' - 1) * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) +
        (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) := by ring
    _ = 1 := by
      rw [← eq]; rw [mul_sub]; rw [mul_one]; rw [sub_add_sub_cancel']; rw [sub_eq_self]; rw [← map_mul]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [pow_add]
      apply Ideal.mul_mem_mul hc (Ideal.mul_le_right (I := I ^ (n - 1)) _)
      simpa only [← pow_add, Nat.sub_add_cancel npos] using! hc

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.mem_image_of_mem_map_of_surjective, Quotient, RingHom, RingHom.sub_mem_ker_iff, factorPow, factor_ker, factor_surjective, isUnit_iff_exists, isUnit_iff_exists.mp, le_succ, map_mul, map_one, mem_image_of_mem_map_of_surjective, mk_surjective, n.le_succ, of_mul_eq_one, pow_le_pow_right, sub_mem_ker_iff
-/
lemma factorPowSucc.isUnit_of_isUnit_image {n : Nat} (npos : n > 0) {a : R ⧸ I ^ (n + 1)}
    (h : IsUnit (factorPow I n.le_succ a)) : IsUnit a := by
  rcases isUnit_iff_exists.mp h with ⟨b, hb, _⟩
  rcases factor_surjective (pow_le_pow_right n.le_succ) b with ⟨b', hb'⟩
  rw [← hb']; rw [← map_one (factorPow I n.le_succ)]; rw [← map_mul] at hb
  apply (RingHom.sub_mem_ker_iff (factorPow I n.le_succ)).mpr at hb
  rw [factor_ker (pow_le_pow_right n.le_succ)] at hb
  rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (I ^ (n + 1)))
    Ideal.Quotient.mk_surjective hb with ⟨c, hc, eq⟩
  refine .of_mul_eq_one (b' * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c)) ?_
  calc
    _ = (a * b' - 1) * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) +
        (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) := by ring
    _ = 1 := by
      rw [← eq]; rw [mul_sub]; rw [mul_one]; rw [sub_add_sub_cancel']; rw [sub_eq_self]; rw [← map_mul]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [pow_add]
      apply Ideal.mul_mem_mul hc (Ideal.mul_le_right (I := I ^ (n - 1)) _)
      simpa only [← pow_add, Nat.sub_add_cancel npos] using! hc

section powSMulQuotInclusion

variable {M : Type*} [AddCommGroup M] [Module R M] {a b c : Nat}

namespace Submodule

variable (M) in
/--
Definition of `powSMulQuotInclusion` / `powSMulQuotInclusion` 的定义

English:
definition powSMulQuotInclusion
  signature: (h : c = b + a) (N : Submodule R M)
  body: mapQ _ _ (I ^ a • N).subtype by simp [← map_le_iff_le_comap, h, pow_add, mul_smul]

@[simp]

中文:
定义 powSMulQuotInclusion
  签名: (h : c = b + a) (N : 子模 R M)
  定义体: mapQ _ _ (I ^ a • N).subtype by simp [← map_le_iff_le_comap, h, pow_add, mul_smul]

@[simp]

Depends on / 依赖: map_le_iff_le_comap, mul_smul, pow_add, subtype
-/
def powSMulQuotInclusion (h : c = b + a) (N : Submodule R M) :
    ↑(I ^ a • N) ⧸ (I ^ b • ⊤ : Submodule R ↑(I ^ a • N)) ->ₗ[R] M ⧸ (I ^ c • N) :=
mapQ _ _ (I ^ a • N).subtype by simp [← map_le_iff_le_comap, h, pow_add, mul_smul]

@[simp]
/--
theorem `powSMulQuotInclusion_mk` / 定理 `powSMulQuotInclusion_mk`

English:
theorem powSMulQuotInclusion_mk
  statement: (h : c = b + a) (N : Submodule R M)
  proof: rfl

中文:
定理 powSMulQuotInclusion_mk
  结论: (h : c = b + a) (N : 子模 R M)
  证明: rfl
-/
theorem powSMulQuotInclusion_mk (h : c = b + a) (N : Submodule R M)
    (x : ↑(I ^ a • N)) : powSMulQuotInclusion I M h N (Quotient.mk x) = Quotient.mk (x : M) := rfl

/--
theorem `powSMulQuotInclusion_injective` / 定理 `powSMulQuotInclusion_injective`

English:
theorem powSMulQuotInclusion_injective
  given: {a b c : Nat} (h : c = b + a) (N : Submodule R M)
  proof: by
  rw [← LinearMap.ker_eq_bot]
  simp [powSMulQuotInclusion, mapQ, ← le_bot_iff, ker_liftQ, LinearMap.ker_comp, pow_add, mul_smul,
    map_le_iff_le_comap, ← Submodule.map_le_map_iff_of_injective (I ^ a • N).subtype_injective, h]

中文:
定理 powSMulQuotInclusion_injective
  条件: {a b c : 自然数} (h : c = b + a) (N : 子模 R M)
  证明: by
  rw [← LinearMap.ker_eq_bot]
  simp [powSMulQuotInclusion, mapQ, ← le_bot_iff, ker_liftQ, LinearMap.ker_comp, pow_add, mul_smul,
    map_le_iff_le_comap, ← Submodule.map_le_map_iff_of_injective (I ^ a • N).subtype_injective, h]

Depends on / 依赖: LinearMap, LinearMap.ker_comp, LinearMap.ker_eq_bot, Submodule, Submodule.map_le_map_iff_of_injective, ker_comp, ker_eq_bot, ker_liftQ, le_bot_iff, map_le_iff_le_comap, map_le_map_iff_of_injective, mul_smul, powSMulQuotInclusion, pow_add, subtype_injective
-/
theorem powSMulQuotInclusion_injective {a b c : Nat} (h : c = b + a) (N : Submodule R M) :
    Function.Injective (powSMulQuotInclusion I M h N) := by
  rw [← LinearMap.ker_eq_bot]
  simp [powSMulQuotInclusion, mapQ, ← le_bot_iff, ker_liftQ, LinearMap.ker_comp, pow_add, mul_smul,
    map_le_iff_le_comap, ← Submodule.map_le_map_iff_of_injective (I ^ a • N).subtype_injective, h]

/--
theorem `factorPow_comp_powSMulQuotInclusion` / 定理 `factorPow_comp_powSMulQuotInclusion`

English:
theorem factorPow_comp_powSMulQuotInclusion
  given: {d e : Nat} (h : c = b + a) (h' : e = d + c)
  proof: by
  ext; rfl

中文:
定理 factorPow_comp_powSMulQuotInclusion
  条件: {d e : 自然数} (h : c = b + a) (h' : e = d + c)
  证明: by
  ext; rfl
-/
theorem factorPow_comp_powSMulQuotInclusion {d e : Nat} (h : c = b + a) (h' : e = d + c) :
    factorPow I M (show c <= e by lia) ∘ₗ
      powSMulQuotInclusion I M (show e = (b + d) + a by lia) ⊤ =
    powSMulQuotInclusion I M h ⊤ ∘ₗ
      factorPow I ↥(I ^ a • ⊤ : Submodule R M) (b.le_add_right d) := by
  ext; rfl

/--
theorem `range_powSMulQuotInclusion` / 定理 `range_powSMulQuotInclusion`

English:
theorem range_powSMulQuotInclusion
  given: (h : c = b + a) (N : Submodule R M)
  proof: by
  simp [powSMulQuotInclusion, mapQ, range_liftQ, LinearMap.range_comp]

中文:
定理 range_powSMulQuotInclusion
  条件: (h : c = b + a) (N : 子模 R M)
  证明: by
  simp [powSMulQuotInclusion, mapQ, range_liftQ, LinearMap.range_comp]

Depends on / 依赖: LinearMap, LinearMap.range_comp, powSMulQuotInclusion, range_comp, range_liftQ
-/
theorem range_powSMulQuotInclusion (h : c = b + a) (N : Submodule R M) :
    (powSMulQuotInclusion I M h N).range = (I ^ a • N).map (mkQ (I ^ c • N)) := by
  simp [powSMulQuotInclusion, mapQ, range_liftQ, LinearMap.range_comp]

end Submodule

end powSMulQuotInclusion
