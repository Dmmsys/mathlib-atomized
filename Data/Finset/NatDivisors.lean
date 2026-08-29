/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yury Kudryashov, Lawrence Wu
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# `Nat.divisors` as a multiplicative homomorphism

The main definition of this file is `Nat.divisorsHom : ℕ →* Finset ℕ`,
exhibiting `Nat.divisors` as a multiplicative homomorphism from `ℕ` to `Finset ℕ`.
-/

@[expose] public section

open Nat Finset
open scoped Pointwise

/--
lemma `Nat.divisors_mul` / 引理 `Nat.divisors_mul`

English:
lemma Nat.divisors_mul
  given: (m n : Nat)
  statement: divisors (m * n) = divisors m * divisors n
  proof: by
  ext k
  simp_rw [mem_mul, mem_divisors, Nat.dvd_mul, mul_ne_zero_iff, ← exists_and_left,
    ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

中文:
引理 自然数.divisors_mul
  条件: (m n : 自然数)
  结论: divisors (m * n) = divisors m * divisors n
  证明: by
  ext k
  simp_rw [mem_mul, mem_divisors, Nat.dvd_mul, mul_ne_zero_iff, ← exists_and_left,
    ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

Depends on / 依赖: Nat.dvd_mul, and_assoc, and_comm, and_left_comm, dvd_mul, exists_and_left, exists_and_right, mem_divisors, mem_mul, mul_ne_zero_iff, simp_rw
-/
lemma Nat.divisors_mul (m n : Nat) : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, Nat.dvd_mul, mul_ne_zero_iff, ← exists_and_left,
    ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

/-- `Nat.divisors` as a `MonoidHom`. -/
@[simps]
/--
Definition of `Nat.divisorsHom` / `Nat.divisorsHom` 的定义

English:
definition Nat.divisorsHom
  signature: : Nat ->* Finset Nat where
  body: Nat.divisors
  map_mul' := divisors_mul
  map_one' := divisors_one

中文:
定义 自然数.divisorsHom
  签名: : 自然数 ->* 有限集 自然数 where
  定义体: Nat.divisors
  map_mul' := divisors_mul
  map_one' := divisors_one

Depends on / 依赖: Nat.divisors, divisors
-/
def Nat.divisorsHom : Nat ->* Finset Nat where
  toFun := Nat.divisors
  map_mul' := divisors_mul
  map_one' := divisors_one

/--
lemma `Nat.Prime.divisors_sq` / 引理 `Nat.Prime.divisors_sq`

English:
lemma Nat.Prime.divisors_sq
  given: {p : Nat} (hp : p.Prime)
  statement: (p ^ 2).divisors = {p ^ 2, p, 1}
  proof: by
  simp [divisors_prime_pow hp, range_add_one]

中文:
引理 自然数.素.divisors_sq
  条件: {p : 自然数} (hp : p.素)
  结论: (p ^ 2).divisors = {p ^ 2, p, 1}
  证明: by
  simp [divisors_prime_pow hp, range_add_one]

Depends on / 依赖: divisors_prime_pow, range_add_one
-/
lemma Nat.Prime.divisors_sq {p : Nat} (hp : p.Prime) : (p ^ 2).divisors = {p ^ 2, p, 1} := by
  simp [divisors_prime_pow hp, range_add_one]

/--
lemma `List.nat_divisors_prod` / 引理 `List.nat_divisors_prod`

English:
lemma List.nat_divisors_prod
  given: (l : List Nat)
  statement: divisors l.prod = (l.map divisors).prod
  proof: map_list_prod Nat.divisorsHom l

中文:
引理 列表.nat_divisors_prod
  条件: (l : 列表 自然数)
  结论: divisors l.乘积 = (l.map divisors).乘积
  证明: map_list_prod Nat.divisorsHom l

Depends on / 依赖: Nat.divisorsHom, divisorsHom, map_list_prod
-/
lemma List.nat_divisors_prod (l : List Nat) : divisors l.prod = (l.map divisors).prod :=
  map_list_prod Nat.divisorsHom l

/--
lemma `Multiset.nat_divisors_prod` / 引理 `Multiset.nat_divisors_prod`

English:
lemma Multiset.nat_divisors_prod
  given: (s : Multiset Nat)
  statement: divisors s.prod = (s.map divisors).prod
  proof: map_multiset_prod Nat.divisorsHom s

中文:
引理 Multiset.nat_divisors_prod
  条件: (s : Multiset 自然数)
  结论: divisors s.乘积 = (s.map divisors).乘积
  证明: map_multiset_prod Nat.divisorsHom s

Depends on / 依赖: Nat.divisorsHom, divisorsHom, map_multiset_prod
-/
lemma Multiset.nat_divisors_prod (s : Multiset Nat) : divisors s.prod = (s.map divisors).prod :=
  map_multiset_prod Nat.divisorsHom s

/--
lemma `Finset.nat_divisors_prod` / 引理 `Finset.nat_divisors_prod`

English:
lemma Finset.nat_divisors_prod
  given: {ι : Type*} (s : Finset ι) (f : ι -> Nat)
  proof: map_prod Nat.divisorsHom f s

中文:
引理 有限集.nat_divisors_prod
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 自然数)
  证明: map_prod Nat.divisorsHom f s

Depends on / 依赖: Nat.divisorsHom, divisorsHom, map_prod
-/
lemma Finset.nat_divisors_prod {ι : Type*} (s : Finset ι) (f : ι -> Nat) :
    divisors (∏ i in s, f i) = ∏ i in s, divisors (f i) :=
  map_prod Nat.divisorsHom f s

/--
theorem `Nat.Coprime.mul_injOn_divisors` / 定理 `Nat.Coprime.mul_injOn_divisors`

English:
theorem Nat.Coprime.mul_injOn_divisors
  given: {m n : Nat} (hmn : m.Coprime n)
  proof: by
  rintro ⟨dm₁, dn₁⟩ h₁ ⟨dm₂, dn₂⟩ h₂ hd
  simp only [Finset.mem_coe, Finset.mem_product, mem_divisors] at *
suffices dm₁ = dm₂ from Prod.ext this by
    rwa [this, Nat.mul_right_inj (by simp [·] at h₂)] at hd
  exact dvd_antisymm
    (hmn.coprime_dvd_left h₁.1.1 |>.coprime_dvd_right h₂.2.1
.dvd_o

中文:
定理 自然数.Coprime.mul_injOn_divisors
  条件: {m n : 自然数} (hmn : m.Coprime n)
  证明: by
  rintro ⟨dm₁, dn₁⟩ h₁ ⟨dm₂, dn₂⟩ h₂ hd
  simp only [Finset.mem_coe, Finset.mem_product, mem_divisors] at *
suffices dm₁ = dm₂ from Prod.ext this by
    rwa [this, Nat.mul_right_inj (by simp [·] at h₂)] at hd
  exact dvd_antisymm
    (hmn.coprime_dvd_left h₁.1.1 |>.coprime_dvd_right h₂.2.1
.dvd_o

Depends on / 依赖: Finset, Finset.mem_coe, Finset.mem_product, Nat.mul_right_inj, Prod.ext, coprime_dvd_left, coprime_dvd_right, dvd_antisymm, dvd_mul_right, dvd_of_dvd_mul_right, hmn.coprime_dvd_left, mem_coe, mem_divisors, mem_product, mul_right_inj
-/
theorem Nat.Coprime.mul_injOn_divisors {m n : Nat} (hmn : m.Coprime n) :
    Set.InjOn (fun p : Nat × Nat => p.1 * p.2) ↑(divisors m ×ˢ divisors n) := by
  rintro ⟨dm₁, dn₁⟩ h₁ ⟨dm₂, dn₂⟩ h₂ hd
  simp only [Finset.mem_coe, Finset.mem_product, mem_divisors] at *
suffices dm₁ = dm₂ from Prod.ext this by
    rwa [this, Nat.mul_right_inj (by simp [·] at h₂)] at hd
  exact dvd_antisymm
    (hmn.coprime_dvd_left h₁.1.1 |>.coprime_dvd_right h₂.2.1
.dvd_of_dvd_mul_right (hd ▸ dm₁.dvd_mul_right dn₁))
    (hmn.coprime_dvd_left h₂.1.1 |>.coprime_dvd_right h₁.2.1
.dvd_of_dvd_mul_right (hd ▸ dm₂.dvd_mul_right dn₂))

/--
theorem `Nat.Coprime.divisors_mul` / 定理 `Nat.Coprime.divisors_mul`

English:
theorem Nat.Coprime.divisors_mul
  given: {m n : Nat} (hmn : m.Coprime n)
  proof: calc
  _ = ((divisors m ×ˢ divisors n).attach.image Subtype.val).image fun p => p.1 * p.2 := by
    rw [Finset.attach_image_val]; rw [← Finset.mul_def]; rw [Nat.divisors_mul]
  _ = _ := by rw [Finset.map_eq_image, Finset.image_image]; rfl

中文:
定理 自然数.Coprime.divisors_mul
  条件: {m n : 自然数} (hmn : m.Coprime n)
  证明: calc
  _ = ((divisors m ×ˢ divisors n).attach.image Subtype.val).image fun p => p.1 * p.2 := by
    rw [Finset.attach_image_val]; rw [← Finset.mul_def]; rw [Nat.divisors_mul]
  _ = _ := by rw [Finset.map_eq_image, Finset.image_image]; rfl
-/
theorem Nat.Coprime.divisors_mul {m n : Nat} (hmn : m.Coprime n) :
    divisors (m * n) = (divisors m ×ˢ divisors n).attach.map
      ⟨fun p => p.val.1 * p.val.2,
fun i j hxy => Subtype.ext hmn.mul_injOn_divisors i.prop j.prop hxy⟩ := calc
  _ = ((divisors m ×ˢ divisors n).attach.image Subtype.val).image fun p => p.1 * p.2 := by
    rw [Finset.attach_image_val]; rw [← Finset.mul_def]; rw [Nat.divisors_mul]
  _ = _ := by rw [Finset.map_eq_image, Finset.image_image]; rfl
