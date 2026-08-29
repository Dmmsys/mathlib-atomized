/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# Properties of `Nat.gcd`, `Nat.lcm`, and `Nat.Coprime`

Definitions are provided in batteries.

Generalizations of these are provided in a later file as `GCDMonoid.gcd` and
`GCDMonoid.lcm`.

Note that the global `IsCoprime` is not a straightforward generalization of `Nat.Coprime`, see
`Nat.isCoprime_iff_coprime` for the connection between the two.

Most of this file could be moved to batteries as well.
-/

public section

assert_not_exists IsOrderedMonoid

namespace Nat
variable {a a₁ a₂ b b₁ b₂ c : Nat}


/--
theorem `gcd_greatest` / 定理 `gcd_greatest`

English:
theorem gcd_greatest
  given: {a b d : Nat} (hda : d ∣ a) (hdb : d ∣ b) (hd : forall e : Nat, e ∣ a -> e ∣ b -> e ∣ d)
  proof: (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm

中文:
定理 gcd_greatest
  条件: {a b d : 自然数} (hda : d ∣ a) (hdb : d ∣ b) (hd : 对任意 e : 自然数, e ∣ a -> e ∣ b -> e ∣ d)
  证明: (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm

Depends on / 依赖: dvd_antisymm, dvd_gcd, gcd_dvd_left, gcd_dvd_right
-/
theorem gcd_greatest {a b d : Nat} (hda : d ∣ a) (hdb : d ∣ b) (hd : forall e : Nat, e ∣ a -> e ∣ b -> e ∣ d) :
    d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm

/--
theorem `gcd_right_comm` / 定理 `gcd_right_comm`

English:
theorem gcd_right_comm
  given: (a b c : Nat)
  statement: gcd (gcd a b) c = gcd (gcd a c) b
  proof: by
  rw [gcd_assoc]; rw [gcd_assoc]; rw [gcd_comm b c]

中文:
定理 gcd_right_comm
  条件: (a b c : 自然数)
  结论: 最大公约数 (最大公约数 a b) c = 最大公约数 (最大公约数 a c) b
  证明: by
  rw [gcd_assoc]; rw [gcd_assoc]; rw [gcd_comm b c]

Depends on / 依赖: gcd_assoc, gcd_comm
-/
theorem gcd_right_comm (a b c : Nat) : gcd (gcd a b) c = gcd (gcd a c) b := by
  rw [gcd_assoc]; rw [gcd_assoc]; rw [gcd_comm b c]

/-! Lemmas where one argument consists of addition of a multiple of the other -/

@[simp]
/--
theorem `pow_sub_one_mod_pow_sub_one` / 定理 `pow_sub_one_mod_pow_sub_one`

English:
theorem pow_sub_one_mod_pow_sub_one
  given: (a b c : Nat)
  statement: (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1
  proof: by
  rcases eq_zero_or_pos a with rfl | ha0
  · simp [zero_pow_eq]; split_ifs <;> simp
  rcases Nat.eq_or_lt_of_le ha0 with rfl | ha1
  · simp
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  rcases lt_or_ge c b with h | h
  · rw [mod_eq_of_lt, mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (o

中文:
定理 pow_sub_one_mod_pow_sub_one
  条件: (a b c : 自然数)
  结论: (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1
  证明: by
  rcases eq_zero_or_pos a with rfl | ha0
  · simp [zero_pow_eq]; split_ifs <;> simp
  rcases Nat.eq_or_lt_of_le ha0 with rfl | ha1
  · simp
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  rcases lt_or_ge c b with h | h
  · rw [mod_eq_of_lt, mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (o

Depends on / 依赖: Nat.eq_or_lt_of_le, Nat.pow_lt_pow_iff_right, Nat.sub_add_cancel, Nat.sub_lt_sub_iff_right, add_mod, add_mod_right, eq_or_lt_of_le, eq_zero_or_pos, lt_or_ge, mod_eq_of_lt, mul_mod, one_le_pow, pow_lt_pow_iff_right, split_ifs, sub_add_cancel, sub_lt_sub_iff_right, zero_pow_eq
-/
theorem pow_sub_one_mod_pow_sub_one (a b c : Nat) : (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1 := by
  rcases eq_zero_or_pos a with rfl | ha0
  · simp [zero_pow_eq]; split_ifs <;> simp
  rcases Nat.eq_or_lt_of_le ha0 with rfl | ha1
  · simp
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  rcases lt_or_ge c b with h | h
  · rw [mod_eq_of_lt, mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (one_le_pow c a ha0), Nat.pow_lt_pow_iff_right ha1]
  · suffices a ^ (c - b + b) - 1 = a ^ (c - b) * (a ^ b - 1) + (a ^ (c - b) - 1) by
      rw [← Nat.sub_add_cancel h]; rw [add_mod_right]; rw [this]; rw [add_mod]; rw [mul_mod]; rw [mod_self]; rw [mul_zero]; rw [zero_mod]; rw [zero_add]; rw [mod_mod]; rw [pow_sub_one_mod_pow_sub_one]
    rw [← Nat.add_sub_assoc (one_le_pow (c - b) a ha0)]; rw [← mul_add_one]; rw [pow_add]; rw [Nat.sub_add_cancel (one_le_pow b a ha0)]

@[simp]
/--
theorem `pow_sub_one_gcd_pow_sub_one` / 定理 `pow_sub_one_gcd_pow_sub_one`

English:
theorem pow_sub_one_gcd_pow_sub_one
  given: (a b c : Nat)
  proof: by
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  replace hb : c % b < b := mod_lt c hb
  rw [gcd_rec]; rw [pow_sub_one_mod_pow_sub_one]; rw [pow_sub_one_gcd_pow_sub_one]; rw [← gcd_rec]

中文:
定理 pow_sub_one_gcd_pow_sub_one
  条件: (a b c : 自然数)
  证明: by
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  replace hb : c % b < b := mod_lt c hb
  rw [gcd_rec]; rw [pow_sub_one_mod_pow_sub_one]; rw [pow_sub_one_gcd_pow_sub_one]; rw [← gcd_rec]

Depends on / 依赖: eq_zero_or_pos, gcd_rec, mod_lt, pow_sub_one_gcd_pow_sub_one, pow_sub_one_mod_pow_sub_one, replace
-/
theorem pow_sub_one_gcd_pow_sub_one (a b c : Nat) :
    gcd (a ^ b - 1) (a ^ c - 1) = a ^ gcd b c - 1 := by
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  replace hb : c % b < b := mod_lt c hb
  rw [gcd_rec]; rw [pow_sub_one_mod_pow_sub_one]; rw [pow_sub_one_gcd_pow_sub_one]; rw [← gcd_rec]


/--
theorem `dvd_lcm_of_dvd_left` / 定理 `dvd_lcm_of_dvd_left`

English:
theorem dvd_lcm_of_dvd_left
  given: (h : a ∣ b) (c : Nat)
  statement: a ∣ lcm b c
  proof: h.trans (dvd_lcm_left b c)

alias Dvd.dvd.nat_lcm_right := dvd_lcm_of_dvd_left

中文:
定理 dvd_lcm_of_dvd_left
  条件: (h : a ∣ b) (c : 自然数)
  结论: a ∣ 最小公倍数 b c
  证明: h.trans (dvd_lcm_left b c)

alias Dvd.dvd.nat_lcm_right := dvd_lcm_of_dvd_left

Depends on / 依赖: dvd_lcm_left, h.trans
-/
theorem dvd_lcm_of_dvd_left (h : a ∣ b) (c : Nat) : a ∣ lcm b c :=
  h.trans (dvd_lcm_left b c)

alias Dvd.dvd.nat_lcm_right := dvd_lcm_of_dvd_left

/--
theorem `dvd_of_lcm_right_dvd` / 定理 `dvd_of_lcm_right_dvd`

English:
theorem dvd_of_lcm_right_dvd
  given: {a b c : Nat} (h : lcm a b ∣ c)
  statement: a ∣ c
  proof: (dvd_lcm_left a b).trans h

中文:
定理 dvd_of_lcm_right_dvd
  条件: {a b c : 自然数} (h : 最小公倍数 a b ∣ c)
  结论: a ∣ c
  证明: (dvd_lcm_left a b).trans h

Depends on / 依赖: dvd_lcm_left
-/
theorem dvd_of_lcm_right_dvd {a b c : Nat} (h : lcm a b ∣ c) : a ∣ c :=
  (dvd_lcm_left a b).trans h

/--
theorem `dvd_lcm_of_dvd_right` / 定理 `dvd_lcm_of_dvd_right`

English:
theorem dvd_lcm_of_dvd_right
  given: {a b : Nat} (h : a ∣ b) (c : Nat)
  statement: a ∣ lcm c b
  proof: h.trans (dvd_lcm_right c b)

alias Dvd.dvd.nat_lcm_left := dvd_lcm_of_dvd_right

中文:
定理 dvd_lcm_of_dvd_right
  条件: {a b : 自然数} (h : a ∣ b) (c : 自然数)
  结论: a ∣ 最小公倍数 c b
  证明: h.trans (dvd_lcm_right c b)

alias Dvd.dvd.nat_lcm_left := dvd_lcm_of_dvd_right

Depends on / 依赖: dvd_lcm_right, h.trans
-/
theorem dvd_lcm_of_dvd_right {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ lcm c b :=
  h.trans (dvd_lcm_right c b)

alias Dvd.dvd.nat_lcm_left := dvd_lcm_of_dvd_right

/--
theorem `dvd_of_lcm_left_dvd` / 定理 `dvd_of_lcm_left_dvd`

English:
theorem dvd_of_lcm_left_dvd
  given: {a b c : Nat} (h : lcm a b ∣ c)
  statement: b ∣ c
  proof: (dvd_lcm_right a b).trans h

中文:
定理 dvd_of_lcm_left_dvd
  条件: {a b c : 自然数} (h : 最小公倍数 a b ∣ c)
  结论: b ∣ c
  证明: (dvd_lcm_right a b).trans h

Depends on / 依赖: dvd_lcm_right
-/
theorem dvd_of_lcm_left_dvd {a b c : Nat} (h : lcm a b ∣ c) : b ∣ c :=
  (dvd_lcm_right a b).trans h


/--
theorem `Coprime.lcm_eq_mul` / 定理 `Coprime.lcm_eq_mul`

English:
theorem Coprime.lcm_eq_mul
  given: {m n : Nat} (h : Coprime m n)
  statement: lcm m n = m * n
  proof: by
  rw [← one_mul (lcm m n)]; rw [← h.gcd_eq_one]; rw [gcd_mul_lcm]

中文:
定理 Coprime.lcm_eq_mul
  条件: {m n : 自然数} (h : Coprime m n)
  结论: 最小公倍数 m n = m * n
  证明: by
  rw [← one_mul (lcm m n)]; rw [← h.gcd_eq_one]; rw [gcd_mul_lcm]

Depends on / 依赖: gcd_eq_one, gcd_mul_lcm, h.gcd_eq_one, one_mul
-/
theorem Coprime.lcm_eq_mul {m n : Nat} (h : Coprime m n) : lcm m n = m * n := by
  rw [← one_mul (lcm m n)]; rw [← h.gcd_eq_one]; rw [gcd_mul_lcm]

/--
Instance `Coprime.stdSymm` / 实例 `Coprime.stdSymm`

English:
instance Coprime.stdSymm
  signature: : Std.Symm Coprime where
  body: Coprime.symm

@[deprecated (since := "2026-06-10")] alias Coprime.symmetric := Coprime.stdSymm

中文:
实例 Coprime.stdSymm
  签名: : Std.Symm Coprime where
  定义体: Coprime.symm

@[deprecated (since := "2026-06-10")] alias Coprime.symmetric := Coprime.stdSymm

Depends on / 依赖: Coprime, Coprime.symm
-/
instance Coprime.stdSymm : Std.Symm Coprime where
  symm _ _ := Coprime.symm

@[deprecated (since := "2026-06-10")] alias Coprime.symmetric := Coprime.stdSymm

/--
theorem `Coprime.dvd_mul_right` / 定理 `Coprime.dvd_mul_right`

English:
theorem Coprime.dvd_mul_right
  given: {m n k : Nat} (H : Coprime k n)
  statement: k ∣ m * n ↔ k ∣ m
  proof: ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩

中文:
定理 Coprime.dvd_mul_right
  条件: {m n k : 自然数} (H : Coprime k n)
  结论: k ∣ m * n ↔ k ∣ m
  证明: ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩

Depends on / 依赖: H.dvd_of_dvd_mul_right, dvd_mul_of_dvd_left, dvd_of_dvd_mul_right
-/
theorem Coprime.dvd_mul_right {m n k : Nat} (H : Coprime k n) : k ∣ m * n ↔ k ∣ m :=
  ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩

/--
theorem `Coprime.dvd_mul_left` / 定理 `Coprime.dvd_mul_left`

English:
theorem Coprime.dvd_mul_left
  given: {m n k : Nat} (H : Coprime k m)
  statement: k ∣ m * n ↔ k ∣ n
  proof: ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩

@[simp]

中文:
定理 Coprime.dvd_mul_left
  条件: {m n k : 自然数} (H : Coprime k m)
  结论: k ∣ m * n ↔ k ∣ n
  证明: ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩

@[simp]

Depends on / 依赖: GroupFilterBasis, GroupFilterBasis.isTopologicalGroup, H.dvd_of_dvd_mul_left, dvd_mul_of_dvd_right, dvd_of_dvd_mul_left, galGroupBasis, isTopologicalGroup
-/
theorem Coprime.dvd_mul_left {m n k : Nat} (H : Coprime k m) : k ∣ m * n ↔ k ∣ n :=
  ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩

@[simp]
/--
theorem `coprime_add_self_right` / 定理 `coprime_add_self_right`

English:
theorem coprime_add_self_right
  given: {m n : Nat}
  statement: Coprime m (n + m) ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_self_right]

@[simp]

中文:
定理 coprime_add_self_right
  条件: {m n : 自然数}
  结论: Coprime m (n + m) ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_self_right]

@[simp]

Depends on / 依赖: Coprime, gcd_add_self_right
-/
theorem coprime_add_self_right {m n : Nat} : Coprime m (n + m) ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_self_right]

@[simp]
/--
theorem `coprime_self_add_right` / 定理 `coprime_self_add_right`

English:
theorem coprime_self_add_right
  given: {m n : Nat}
  statement: Coprime m (m + n) ↔ Coprime m n
  proof: by
  rw [add_comm]; rw [coprime_add_self_right]

@[simp]

中文:
定理 coprime_self_add_right
  条件: {m n : 自然数}
  结论: Coprime m (m + n) ↔ Coprime m n
  证明: by
  rw [add_comm]; rw [coprime_add_self_right]

@[simp]

Depends on / 依赖: add_comm, coprime_add_self_right
-/
theorem coprime_self_add_right {m n : Nat} : Coprime m (m + n) ↔ Coprime m n := by
  rw [add_comm]; rw [coprime_add_self_right]

@[simp]
/--
theorem `coprime_add_self_left` / 定理 `coprime_add_self_left`

English:
theorem coprime_add_self_left
  given: {m n : Nat}
  statement: Coprime (m + n) n ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_self_left]

@[simp]

中文:
定理 coprime_add_self_left
  条件: {m n : 自然数}
  结论: Coprime (m + n) n ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_self_left]

@[simp]

Depends on / 依赖: Coprime, gcd_add_self_left
-/
theorem coprime_add_self_left {m n : Nat} : Coprime (m + n) n ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_self_left]

@[simp]
/--
theorem `coprime_self_add_left` / 定理 `coprime_self_add_left`

English:
theorem coprime_self_add_left
  given: {m n : Nat}
  statement: Coprime (m + n) m ↔ Coprime n m
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_add_left]

@[simp]

中文:
定理 coprime_self_add_left
  条件: {m n : 自然数}
  结论: Coprime (m + n) m ↔ Coprime n m
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_add_left]

@[simp]

Depends on / 依赖: Coprime, gcd_self_add_left
-/
theorem coprime_self_add_left {m n : Nat} : Coprime (m + n) m ↔ Coprime n m := by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_add_left]

@[simp]
/--
theorem `coprime_add_mul_right_right` / 定理 `coprime_add_mul_right_right`

English:
theorem coprime_add_mul_right_right
  given: (m n k : Nat)
  statement: Coprime m (n + k * m) ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_right_right]

@[simp]

中文:
定理 coprime_add_mul_right_right
  条件: (m n k : 自然数)
  结论: Coprime m (n + k * m) ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_right_right]

@[simp]

Depends on / 依赖: Coprime, gcd_add_mul_right_right
-/
theorem coprime_add_mul_right_right (m n k : Nat) : Coprime m (n + k * m) ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_right_right]

@[simp]
/--
theorem `coprime_add_mul_left_right` / 定理 `coprime_add_mul_left_right`

English:
theorem coprime_add_mul_left_right
  given: (m n k : Nat)
  statement: Coprime m (n + m * k) ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_left_right]

@[simp]

中文:
定理 coprime_add_mul_left_right
  条件: (m n k : 自然数)
  结论: Coprime m (n + m * k) ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_left_right]

@[simp]

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, Coprime, DFunLike, DFunLike.exists_ne, E.fixingSubgroup, E.fixingSubgroup.one_mem, E.fixingSubgroup_isClosed.leftCoset, E.fixingSubgroup_isOpen.leftCoset, IntermediateField, IntermediateField.adjoin, IntermediateField.adjoin.finiteDimensional, IsIntegral, Set.me, adjoin, exists_ne, finiteDimensional, fixingSubgroup, fixingSubgroup_isClosed, fixingSubgroup_isOpen
-/
theorem coprime_add_mul_left_right (m n k : Nat) : Coprime m (n + m * k) ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_left_right]

@[simp]
/--
theorem `coprime_mul_right_add_right` / 定理 `coprime_mul_right_add_right`

English:
theorem coprime_mul_right_add_right
  given: (m n k : Nat)
  statement: Coprime m (k * m + n) ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_right_add_right]

@[simp]

中文:
定理 coprime_mul_right_add_right
  条件: (m n k : 自然数)
  结论: Coprime m (k * m + n) ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_right_add_right]

@[simp]

Depends on / 依赖: Coprime, gcd_mul_right_add_right
-/
theorem coprime_mul_right_add_right (m n k : Nat) : Coprime m (k * m + n) ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_right_add_right]

@[simp]
/--
theorem `coprime_mul_left_add_right` / 定理 `coprime_mul_left_add_right`

English:
theorem coprime_mul_left_add_right
  given: (m n k : Nat)
  statement: Coprime m (m * k + n) ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_left_add_right]

@[simp]

中文:
定理 coprime_mul_left_add_right
  条件: (m n k : 自然数)
  结论: Coprime m (m * k + n) ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_left_add_right]

@[simp]

Depends on / 依赖: Coprime, gcd_mul_left_add_right
-/
theorem coprime_mul_left_add_right (m n k : Nat) : Coprime m (m * k + n) ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_left_add_right]

@[simp]
/--
theorem `coprime_add_mul_right_left` / 定理 `coprime_add_mul_right_left`

English:
theorem coprime_add_mul_right_left
  given: (m n k : Nat)
  statement: Coprime (m + k * n) n ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_right_left]

@[simp]

中文:
定理 coprime_add_mul_right_left
  条件: (m n k : 自然数)
  结论: Coprime (m + k * n) n ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_right_left]

@[simp]

Depends on / 依赖: Coprime, gcd_add_mul_right_left
-/
theorem coprime_add_mul_right_left (m n k : Nat) : Coprime (m + k * n) n ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_right_left]

@[simp]
/--
theorem `coprime_add_mul_left_left` / 定理 `coprime_add_mul_left_left`

English:
theorem coprime_add_mul_left_left
  given: (m n k : Nat)
  statement: Coprime (m + n * k) n ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_left_left]

@[simp]

中文:
定理 coprime_add_mul_left_left
  条件: (m n k : 自然数)
  结论: Coprime (m + n * k) n ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_left_left]

@[simp]

Depends on / 依赖: Coprime, gcd_add_mul_left_left
-/
theorem coprime_add_mul_left_left (m n k : Nat) : Coprime (m + n * k) n ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_add_mul_left_left]

@[simp]
/--
theorem `coprime_mul_right_add_left` / 定理 `coprime_mul_right_add_left`

English:
theorem coprime_mul_right_add_left
  given: (m n k : Nat)
  statement: Coprime (k * n + m) n ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_right_add_left]

@[simp]

中文:
定理 coprime_mul_right_add_left
  条件: (m n k : 自然数)
  结论: Coprime (k * n + m) n ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_right_add_left]

@[simp]

Depends on / 依赖: Coprime, gcd_mul_right_add_left
-/
theorem coprime_mul_right_add_left (m n k : Nat) : Coprime (k * n + m) n ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_right_add_left]

@[simp]
/--
theorem `coprime_mul_left_add_left` / 定理 `coprime_mul_left_add_left`

English:
theorem coprime_mul_left_add_left
  given: (m n k : Nat)
  statement: Coprime (n * k + m) n ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_left_add_left]

中文:
定理 coprime_mul_left_add_left
  条件: (m n k : 自然数)
  结论: Coprime (n * k + m) n ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_left_add_left]

Depends on / 依赖: Coprime, gcd_mul_left_add_left
-/
theorem coprime_mul_left_add_left (m n k : Nat) : Coprime (n * k + m) n ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_mul_left_add_left]

/--
lemma `add_coprime_iff_left` / 引理 `add_coprime_iff_left`

English:
lemma add_coprime_iff_left
  given: (h : c ∣ b)
  statement: Coprime (a + b) c ↔ Coprime a c
  proof: by
  obtain ⟨n, rfl⟩ := h; simp

中文:
引理 add_coprime_iff_left
  条件: (h : c ∣ b)
  结论: Coprime (a + b) c ↔ Coprime a c
  证明: by
  obtain ⟨n, rfl⟩ := h; simp
-/
lemma add_coprime_iff_left (h : c ∣ b) : Coprime (a + b) c ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp

/--
lemma `add_coprime_iff_right` / 引理 `add_coprime_iff_right`

English:
lemma add_coprime_iff_right
  given: (h : c ∣ a)
  statement: Coprime (a + b) c ↔ Coprime b c
  proof: by
  obtain ⟨n, rfl⟩ := h; simp

中文:
引理 add_coprime_iff_right
  条件: (h : c ∣ a)
  结论: Coprime (a + b) c ↔ Coprime b c
  证明: by
  obtain ⟨n, rfl⟩ := h; simp
-/
lemma add_coprime_iff_right (h : c ∣ a) : Coprime (a + b) c ↔ Coprime b c := by
  obtain ⟨n, rfl⟩ := h; simp

/--
lemma `coprime_add_iff_left` / 引理 `coprime_add_iff_left`

English:
lemma coprime_add_iff_left
  given: (h : a ∣ c)
  statement: Coprime a (b + c) ↔ Coprime a b
  proof: by
  obtain ⟨n, rfl⟩ := h; simp

中文:
引理 coprime_add_iff_left
  条件: (h : a ∣ c)
  结论: Coprime a (b + c) ↔ Coprime a b
  证明: by
  obtain ⟨n, rfl⟩ := h; simp
-/
lemma coprime_add_iff_left (h : a ∣ c) : Coprime a (b + c) ↔ Coprime a b := by
  obtain ⟨n, rfl⟩ := h; simp

/--
lemma `coprime_add_iff_right` / 引理 `coprime_add_iff_right`

English:
lemma coprime_add_iff_right
  given: (h : a ∣ b)
  statement: Coprime a (b + c) ↔ Coprime a c
  proof: by
  obtain ⟨n, rfl⟩ := h; simp

中文:
引理 coprime_add_iff_right
  条件: (h : a ∣ b)
  结论: Coprime a (b + c) ↔ Coprime a c
  证明: by
  obtain ⟨n, rfl⟩ := h; simp
-/
lemma coprime_add_iff_right (h : a ∣ b) : Coprime a (b + c) ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp

-- TODO: Replace `Nat.Coprime.coprime_dvd_left`
/--
lemma `Coprime.of_dvd_left` / 引理 `Coprime.of_dvd_left`

English:
lemma Coprime.of_dvd_left
  given: (ha : a₁ ∣ a₂) (h : Coprime a₂ b)
  statement: Coprime a₁ b
  proof: h.coprime_dvd_left ha

中文:
引理 Coprime.of_dvd_left
  条件: (ha : a₁ ∣ a₂) (h : Coprime a₂ b)
  结论: Coprime a₁ b
  证明: h.coprime_dvd_left ha

Depends on / 依赖: coprime_dvd_left, h.coprime_dvd_left
-/
lemma Coprime.of_dvd_left (ha : a₁ ∣ a₂) (h : Coprime a₂ b) : Coprime a₁ b := h.coprime_dvd_left ha

-- TODO: Replace `Nat.Coprime.coprime_dvd_right`
/--
lemma `Coprime.of_dvd_right` / 引理 `Coprime.of_dvd_right`

English:
lemma Coprime.of_dvd_right
  given: (hb : b₁ ∣ b₂) (h : Coprime a b₂)
  statement: Coprime a b₁
  proof: h.coprime_dvd_right hb

中文:
引理 Coprime.of_dvd_right
  条件: (hb : b₁ ∣ b₂) (h : Coprime a b₂)
  结论: Coprime a b₁
  证明: h.coprime_dvd_right hb

Depends on / 依赖: coprime_dvd_right, h.coprime_dvd_right
-/
lemma Coprime.of_dvd_right (hb : b₁ ∣ b₂) (h : Coprime a b₂) : Coprime a b₁ :=
  h.coprime_dvd_right hb

/--
lemma `Coprime.of_dvd` / 引理 `Coprime.of_dvd`

English:
lemma Coprime.of_dvd
  given: (ha : a₁ ∣ a₂) (hb : b₁ ∣ b₂) (h : Coprime a₂ b₂)
  statement: Coprime a₁ b₁
  proof: (h.of_dvd_left ha).of_dvd_right hb

@[simp]

中文:
引理 Coprime.of_dvd
  条件: (ha : a₁ ∣ a₂) (hb : b₁ ∣ b₂) (h : Coprime a₂ b₂)
  结论: Coprime a₁ b₁
  证明: (h.of_dvd_left ha).of_dvd_right hb

@[simp]

Depends on / 依赖: h.of_dvd_left, of_dvd_left, of_dvd_right
-/
lemma Coprime.of_dvd (ha : a₁ ∣ a₂) (hb : b₁ ∣ b₂) (h : Coprime a₂ b₂) : Coprime a₁ b₁ :=
  (h.of_dvd_left ha).of_dvd_right hb

@[simp]
/--
theorem `coprime_sub_self_left` / 定理 `coprime_sub_self_left`

English:
theorem coprime_sub_self_left
  given: {m n : Nat} (h : m <= n)
  statement: Coprime (n - m) m ↔ Coprime n m
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_sub_self_left h]

@[simp]

中文:
定理 coprime_sub_self_left
  条件: {m n : 自然数} (h : m <= n)
  结论: Coprime (n - m) m ↔ Coprime n m
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_sub_self_left h]

@[simp]

Depends on / 依赖: Coprime, gcd_sub_self_left
-/
theorem coprime_sub_self_left {m n : Nat} (h : m <= n) : Coprime (n - m) m ↔ Coprime n m := by
  rw [Coprime]; rw [Coprime]; rw [gcd_sub_self_left h]

@[simp]
/--
theorem `coprime_sub_self_right` / 定理 `coprime_sub_self_right`

English:
theorem coprime_sub_self_right
  given: {m n : Nat} (h : m <= n)
  statement: Coprime m (n - m) ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_sub_self_right h]

@[simp]

中文:
定理 coprime_sub_self_right
  条件: {m n : 自然数} (h : m <= n)
  结论: Coprime m (n - m) ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_sub_self_right h]

@[simp]

Depends on / 依赖: Coprime, gcd_sub_self_right
-/
theorem coprime_sub_self_right {m n : Nat} (h : m <= n) : Coprime m (n - m) ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_sub_self_right h]

@[simp]
/--
theorem `coprime_self_sub_left` / 定理 `coprime_self_sub_left`

English:
theorem coprime_self_sub_left
  given: {m n : Nat} (h : m <= n)
  statement: Coprime (n - m) n ↔ Coprime m n
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_sub_left h]

@[simp]

中文:
定理 coprime_self_sub_left
  条件: {m n : 自然数} (h : m <= n)
  结论: Coprime (n - m) n ↔ Coprime m n
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_sub_left h]

@[simp]

Depends on / 依赖: Coprime, gcd_self_sub_left
-/
theorem coprime_self_sub_left {m n : Nat} (h : m <= n) : Coprime (n - m) n ↔ Coprime m n := by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_sub_left h]

@[simp]
/--
theorem `coprime_self_sub_right` / 定理 `coprime_self_sub_right`

English:
theorem coprime_self_sub_right
  given: {m n : Nat} (h : m <= n)
  statement: Coprime n (n - m) ↔ Coprime n m
  proof: by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_sub_right h]

@[simp]

中文:
定理 coprime_self_sub_right
  条件: {m n : 自然数} (h : m <= n)
  结论: Coprime n (n - m) ↔ Coprime n m
  证明: by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_sub_right h]

@[simp]

Depends on / 依赖: Coprime, gcd_self_sub_right
-/
theorem coprime_self_sub_right {m n : Nat} (h : m <= n) : Coprime n (n - m) ↔ Coprime n m := by
  rw [Coprime]; rw [Coprime]; rw [gcd_self_sub_right h]

@[simp]
/--
theorem `coprime_pow_left_iff` / 定理 `coprime_pow_left_iff`

English:
theorem coprime_pow_left_iff
  given: {n : Nat} (hn : 0 < n) (a b : Nat)
  proof: by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.pow_succ]; rw [Nat.coprime_mul_iff_left]
  exact ⟨And.right, fun hab => ⟨hab.pow_left _, hab⟩⟩

@[simp]

中文:
定理 coprime_pow_left_iff
  条件: {n : 自然数} (hn : 0 < n) (a b : 自然数)
  证明: by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.pow_succ]; rw [Nat.coprime_mul_iff_left]
  exact ⟨And.right, fun hab => ⟨hab.pow_left _, hab⟩⟩

@[simp]

Depends on / 依赖: And.right, Nat.coprime_mul_iff_left, Nat.ne_of_gt, Nat.pow_succ, coprime_mul_iff_left, exists_eq_succ_of_ne_zero, hab.pow_left, ne_of_gt, pow_left, pow_succ
-/
theorem coprime_pow_left_iff {n : Nat} (hn : 0 < n) (a b : Nat) :
    Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.pow_succ]; rw [Nat.coprime_mul_iff_left]
  exact ⟨And.right, fun hab => ⟨hab.pow_left _, hab⟩⟩

@[simp]
/--
theorem `coprime_pow_right_iff` / 定理 `coprime_pow_right_iff`

English:
theorem coprime_pow_right_iff
  given: {n : Nat} (hn : 0 < n) (a b : Nat)
  proof: by
  rw [Nat.coprime_comm]; rw [coprime_pow_left_iff hn]; rw [Nat.coprime_comm]

中文:
定理 coprime_pow_right_iff
  条件: {n : 自然数} (hn : 0 < n) (a b : 自然数)
  证明: by
  rw [Nat.coprime_comm]; rw [coprime_pow_left_iff hn]; rw [Nat.coprime_comm]

Depends on / 依赖: Nat.coprime_comm, coprime_comm, coprime_pow_left_iff
-/
theorem coprime_pow_right_iff {n : Nat} (hn : 0 < n) (a b : Nat) :
    Nat.Coprime a (b ^ n) ↔ Nat.Coprime a b := by
  rw [Nat.coprime_comm]; rw [coprime_pow_left_iff hn]; rw [Nat.coprime_comm]

/--
theorem `not_coprime_zero_zero` / 定理 `not_coprime_zero_zero`

English:
theorem not_coprime_zero_zero
  statement: ¬Coprime 0 0
  proof: by simp

中文:
定理 not_coprime_zero_zero
  结论: ¬Coprime 0 0
  证明: by simp
-/
theorem not_coprime_zero_zero : ¬Coprime 0 0 := by simp

/--
theorem `coprime_one_left_iff` / 定理 `coprime_one_left_iff`

English:
theorem coprime_one_left_iff
  given: (n : Nat)
  statement: Coprime 1 n ↔ True
  proof: by simp [Coprime]

中文:
定理 coprime_one_left_iff
  条件: (n : 自然数)
  结论: Coprime 1 n ↔ 真
  证明: by simp [Coprime]

Depends on / 依赖: Coprime
-/
theorem coprime_one_left_iff (n : Nat) : Coprime 1 n ↔ True := by simp [Coprime]

/--
theorem `coprime_one_right_iff` / 定理 `coprime_one_right_iff`

English:
theorem coprime_one_right_iff
  given: (n : Nat)
  statement: Coprime n 1 ↔ True
  proof: by simp [Coprime]

中文:
定理 coprime_one_right_iff
  条件: (n : 自然数)
  结论: Coprime n 1 ↔ 真
  证明: by simp [Coprime]

Depends on / 依赖: Coprime
-/
theorem coprime_one_right_iff (n : Nat) : Coprime n 1 ↔ True := by simp [Coprime]

/--
theorem `gcd_mul_of_coprime_of_dvd` / 定理 `gcd_mul_of_coprime_of_dvd`

English:
theorem gcd_mul_of_coprime_of_dvd
  given: {a b c : Nat} (hac : Coprime a c) (b_dvd_c : b ∣ c)
  proof: by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  rw [gcd_mul_right]
  convert! one_mul b
  exact Coprime.coprime_mul_right_right hac

中文:
定理 gcd_mul_of_coprime_of_dvd
  条件: {a b c : 自然数} (hac : Coprime a c) (b_dvd_c : b ∣ c)
  证明: by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  rw [gcd_mul_right]
  convert! one_mul b
  exact Coprime.coprime_mul_right_right hac

Depends on / 依赖: Coprime, Coprime.coprime_mul_right_right, b_dvd_c, convert, coprime_mul_right_right, exists_eq_mul_left_of_dvd, gcd_mul_right, one_mul
-/
theorem gcd_mul_of_coprime_of_dvd {a b c : Nat} (hac : Coprime a c) (b_dvd_c : b ∣ c) :
    gcd (a * b) c = b := by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  rw [gcd_mul_right]
  convert! one_mul b
  exact Coprime.coprime_mul_right_right hac

/--
theorem `Coprime.eq_of_mul_eq_zero` / 定理 `Coprime.eq_of_mul_eq_zero`

English:
theorem Coprime.eq_of_mul_eq_zero
  given: {m n : Nat} (h : m.Coprime n) (hmn : m * n = 0)
  proof: (Nat.mul_eq_zero.mp hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    let eq := hn ▸ h.symm
⟨m.coprime_zero_left.mp eq, hn⟩

中文:
定理 Coprime.eq_of_mul_eq_zero
  条件: {m n : 自然数} (h : m.Coprime n) (hmn : m * n = 0)
  证明: (Nat.mul_eq_zero.mp hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    let eq := hn ▸ h.symm
⟨m.coprime_zero_left.mp eq, hn⟩

Depends on / 依赖: Nat.mul_eq_zero.mp, coprime_zero_left, h.symm, m.coprime_zero_left.mp, mul_eq_zero, n.coprime_zero_left.mp
-/
theorem Coprime.eq_of_mul_eq_zero {m n : Nat} (h : m.Coprime n) (hmn : m * n = 0) :
    m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
  (Nat.mul_eq_zero.mp hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    let eq := hn ▸ h.symm
⟨m.coprime_zero_left.mp eq, hn⟩

/--
theorem `coprime_iff_isRelPrime` / 定理 `coprime_iff_isRelPrime`

English:
theorem coprime_iff_isRelPrime
  given: {m n : Nat}
  statement: m.Coprime n ↔ IsRelPrime m n
  proof: by
  simp_rw [coprime_iff_gcd_eq_one, IsRelPrime, ← and_imp, ← dvd_gcd_iff, isUnit_iff_dvd_one]
  exact ⟨fun h _ => (h ▸ ·), (dvd_one.mp <| · dvd_rfl)⟩

中文:
定理 coprime_iff_isRelPrime
  条件: {m n : 自然数}
  结论: m.Coprime n ↔ IsRelPrime m n
  证明: by
  simp_rw [coprime_iff_gcd_eq_one, IsRelPrime, ← and_imp, ← dvd_gcd_iff, isUnit_iff_dvd_one]
  exact ⟨fun h _ => (h ▸ ·), (dvd_one.mp <| · dvd_rfl)⟩

Depends on / 依赖: IsRelPrime, and_imp, coprime_iff_gcd_eq_one, dvd_gcd_iff, dvd_one, dvd_one.mp, dvd_rfl, isUnit_iff_dvd_one, simp_rw
-/
theorem coprime_iff_isRelPrime {m n : Nat} : m.Coprime n ↔ IsRelPrime m n := by
  simp_rw [coprime_iff_gcd_eq_one, IsRelPrime, ← and_imp, ← dvd_gcd_iff, isUnit_iff_dvd_one]
  exact ⟨fun h _ => (h ▸ ·), (dvd_one.mp <| · dvd_rfl)⟩

/--
theorem `eq_one_of_dvd_coprimes` / 定理 `eq_one_of_dvd_coprimes`

English:
theorem eq_one_of_dvd_coprimes
  statement: {a b k : Nat} (h_ab_coprime : Coprime a b) (hka : k ∣ a)
  proof: dvd_one.mp (isUnit_iff_dvd_one.mp <| coprime_iff_isRelPrime.mp h_ab_coprime hka hkb)

中文:
定理 eq_one_of_dvd_coprimes
  结论: {a b k : 自然数} (h_ab_coprime : Coprime a b) (hka : k ∣ a)
  证明: dvd_one.mp (isUnit_iff_dvd_one.mp <| coprime_iff_isRelPrime.mp h_ab_coprime hka hkb)

Depends on / 依赖: coprime_iff_isRelPrime, coprime_iff_isRelPrime.mp, dvd_one, dvd_one.mp, h_ab_coprime, isUnit_iff_dvd_one, isUnit_iff_dvd_one.mp
-/
theorem eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_coprime : Coprime a b) (hka : k ∣ a)
    (hkb : k ∣ b) : k = 1 :=
  dvd_one.mp (isUnit_iff_dvd_one.mp <| coprime_iff_isRelPrime.mp h_ab_coprime hka hkb)

/--
theorem `Coprime.mul_add_mul_ne_mul` / 定理 `Coprime.mul_add_mul_ne_mul`

English:
theorem Coprime.mul_add_mul_ne_mul
  given: {m n a b : Nat} (cop : Coprime m n) (ha : a != 0) (hb : b != 0)
  proof: by
  intro h
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (Nat.dvd_mul_left n b)).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (Nat.dvd_mul_left m (n * 

中文:
定理 Coprime.mul_add_mul_ne_mul
  条件: {m n a b : 自然数} (cop : Coprime m n) (ha : a != 0) (hb : b != 0)
  证明: by
  intro h
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (Nat.dvd_mul_left n b)).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (Nat.dvd_mul_left m (n * 

Depends on / 依赖: Nat.dvd_add_iff_left, Nat.dvd_add_iff_right, Nat.dvd_mul_left, Nat.dvd_mul_right, add_le_add, congr_arg, cop.dvd_of_dvd_mul_right, cop.symm.dvd_of_dvd_mul_right, dvd_add_iff_left, dvd_add_iff_right, dvd_mul_left, dvd_mul_right, dvd_of_dvd_mul_right, eq_zero_of_mul_eq_self_left, mul_, mul_comm, mul_ne_zero, mul_ne_zero_iff, ne_of_gt, one_le_iff_ne_zero
-/
theorem Coprime.mul_add_mul_ne_mul {m n a b : Nat} (cop : Coprime m n) (ha : a != 0) (hb : b != 0) :
    a * m + b * n != m * n := by
  intro h
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (Nat.dvd_mul_left n b)).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (Nat.dvd_mul_left m (n * x))).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_right m n)))
  rw [mul_comm]; rw [mul_ne_zero_iff]; rw [← one_le_iff_ne_zero] at ha hb
  refine mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gt (add_le_add ha.1 hb.1)) ?_)
  rw [← mul_assoc]; rw [← h]; rw [Nat.add_mul]; rw [Nat.add_mul]; rw [mul_comm _ n]; rw [← mul_assoc]; rw [mul_comm y]

variable {x n m k : Nat}

/--
theorem `gcd_mul_gcd_eq_iff_dvd_mul_of_coprime` / 定理 `gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`

English:
theorem gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
  given: (hcop : Coprime n m)
  proof: by
  refine ⟨fun h => ?_, (dvd_antisymm ?_ <| dvd_gcd_mul_gcd_iff_dvd_mul.mpr ·)⟩
  refine h ▸ Nat.mul_dvd_mul ?_ ?_ <;> exact x.gcd_dvd_right _
  refine (hcop.gcd_both x x).mul_dvd_of_dvd_of_dvd ?_ ?_ <;> exact x.gcd_dvd_left _

中文:
定理 gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
  条件: (hcop : Coprime n m)
  证明: by
  refine ⟨fun h => ?_, (dvd_antisymm ?_ <| dvd_gcd_mul_gcd_iff_dvd_mul.mpr ·)⟩
  refine h ▸ Nat.mul_dvd_mul ?_ ?_ <;> exact x.gcd_dvd_right _
  refine (hcop.gcd_both x x).mul_dvd_of_dvd_of_dvd ?_ ?_ <;> exact x.gcd_dvd_left _

Depends on / 依赖: Nat.mul_dvd_mul, dvd_antisymm, dvd_gcd_mul_gcd_iff_dvd_mul, dvd_gcd_mul_gcd_iff_dvd_mul.mpr, gcd_both, gcd_dvd_left, gcd_dvd_right, hcop.gcd_both, mul_dvd_mul, mul_dvd_of_dvd_of_dvd, x.gcd_dvd_left, x.gcd_dvd_right
-/
theorem gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (hcop : Coprime n m) :
    gcd x n * gcd x m = x ↔ x ∣ n * m := by
  refine ⟨fun h => ?_, (dvd_antisymm ?_ <| dvd_gcd_mul_gcd_iff_dvd_mul.mpr ·)⟩
  refine h ▸ Nat.mul_dvd_mul ?_ ?_ <;> exact x.gcd_dvd_right _
  refine (hcop.gcd_both x x).mul_dvd_of_dvd_of_dvd ?_ ?_ <;> exact x.gcd_dvd_left _

/--
lemma `div_mul_div` / 引理 `div_mul_div`

English:
lemma div_mul_div
  given: (hkm : m ∣ k) (hkn : n ∣ m)
  statement: (k / m) * (m / n) = k / n
  proof: by
  rcases n.eq_zero_or_pos with hn | hn
  · simp [hn]
  refine (Nat.div_eq_of_eq_mul_left hn ?_).symm
  rw [mul_assoc]; rw [Nat.div_mul_cancel hkn]; rw [Nat.div_mul_cancel hkm]

中文:
引理 div_mul_div
  条件: (hkm : m ∣ k) (hkn : n ∣ m)
  结论: (k / m) * (m / n) = k / n
  证明: by
  rcases n.eq_zero_or_pos with hn | hn
  · simp [hn]
  refine (Nat.div_eq_of_eq_mul_left hn ?_).symm
  rw [mul_assoc]; rw [Nat.div_mul_cancel hkn]; rw [Nat.div_mul_cancel hkm]

Depends on / 依赖: Nat.div_eq_of_eq_mul_left, Nat.div_mul_cancel, div_eq_of_eq_mul_left, div_mul_cancel, eq_zero_or_pos, mul_assoc, n.eq_zero_or_pos
-/
lemma div_mul_div (hkm : m ∣ k) (hkn : n ∣ m) : (k / m) * (m / n) = k / n := by
  rcases n.eq_zero_or_pos with hn | hn
  · simp [hn]
  refine (Nat.div_eq_of_eq_mul_left hn ?_).symm
  rw [mul_assoc]; rw [Nat.div_mul_cancel hkn]; rw [Nat.div_mul_cancel hkm]

/--
lemma `div_dvd_div_left` / 引理 `div_dvd_div_left`

English:
lemma div_dvd_div_left
  given: (hkm : m ∣ k) (hkn : n ∣ m)
  statement: k / m ∣ k / n
  proof: ⟨_, (div_mul_div hkm hkn).symm⟩

中文:
引理 div_dvd_div_left
  条件: (hkm : m ∣ k) (hkn : n ∣ m)
  结论: k / m ∣ k / n
  证明: ⟨_, (div_mul_div hkm hkn).symm⟩

Depends on / 依赖: div_mul_div
-/
lemma div_dvd_div_left (hkm : m ∣ k) (hkn : n ∣ m) : k / m ∣ k / n :=
  ⟨_, (div_mul_div hkm hkn).symm⟩

/--
lemma `div_lcm_eq_div_gcd` / 引理 `div_lcm_eq_div_gcd`

English:
lemma div_lcm_eq_div_gcd
  given: (hkm : m ∣ k) (hkn : n ∣ k)
  statement: (k / m).lcm (k / n) = k / (m.gcd n)
  proof: by
  rw [Nat.lcm_eq_iff]
  refine ⟨div_dvd_div_left hkm (Nat.gcd_dvd_left m n),
        div_dvd_div_left hkn (Nat.gcd_dvd_right m n), fun c hmc hnc => ?_⟩
  rcases m.eq_zero_or_pos with hm | hm
  · simp_all
  rcases n.eq_zero_or_pos with hn | hn
  · simp_all
  rw [Nat.div_dvd_iff_dvd_mul hkm hm] at 

中文:
引理 div_lcm_eq_div_gcd
  条件: (hkm : m ∣ k) (hkn : n ∣ k)
  结论: (k / m).最小公倍数 (k / n) = k / (m.最大公约数 n)
  证明: by
  rw [Nat.lcm_eq_iff]
  refine ⟨div_dvd_div_left hkm (Nat.gcd_dvd_left m n),
        div_dvd_div_left hkn (Nat.gcd_dvd_right m n), fun c hmc hnc => ?_⟩
  rcases m.eq_zero_or_pos with hm | hm
  · simp_all
  rcases n.eq_zero_or_pos with hn | hn
  · simp_all
  rw [Nat.div_dvd_iff_dvd_mul hkm hm] at 

Depends on / 依赖: Nat.div_dvd_iff_dvd_mul, Nat.dvd_gcd, Nat.dvd_trans, Nat.gcd_dvd_left, Nat.gcd_dvd_right, Nat.gcd_mul_right, Nat.lcm_eq_iff, div_dvd_div_left, div_dvd_iff_dvd_mul, dvd_gcd, dvd_trans, eq_zero_or_pos, gcd_dvd_left, gcd_dvd_right, gcd_mul_right, gcd_pos_of_pos_left, lcm_eq_iff, m.eq_zero_or_pos, n.eq_zero_or_pos
-/
lemma div_lcm_eq_div_gcd (hkm : m ∣ k) (hkn : n ∣ k) : (k / m).lcm (k / n) = k / (m.gcd n) := by
  rw [Nat.lcm_eq_iff]
  refine ⟨div_dvd_div_left hkm (Nat.gcd_dvd_left m n),
        div_dvd_div_left hkn (Nat.gcd_dvd_right m n), fun c hmc hnc => ?_⟩
  rcases m.eq_zero_or_pos with hm | hm
  · simp_all
  rcases n.eq_zero_or_pos with hn | hn
  · simp_all
  rw [Nat.div_dvd_iff_dvd_mul hkm hm] at hmc
  rw [Nat.div_dvd_iff_dvd_mul hkn hn] at hnc
  simpa [Nat.div_dvd_iff_dvd_mul (Nat.dvd_trans (Nat.gcd_dvd_left m n) hkm)
    (gcd_pos_of_pos_left n hm), Nat.gcd_mul_right m c n] using (Nat.dvd_gcd hmc hnc)

end Nat
