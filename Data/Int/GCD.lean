/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcdA x y` and `gcdB x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcdA x y + y * gcdB x y`.

## Tags

Bézout's lemma, Bezout's lemma
-/

@[expose] public section

/-! ### Extended Euclidean algorithm -/


namespace Nat

/--
Definition of `xgcdAux` / `xgcdAux` 的定义

English:
definition xgcdAux
  signature: : Nat -> Int -> Int -> Nat -> Int -> Int -> Nat × Int × Int
  body: Nat.strongRec fun n ih s t r' s' t' => match n with
  | 0 => (r', s', t')
  | succ k =>
    let q := r' / succ k
    ih (r' % succ k) (mod_lt _ <| (succ_pos _).gt) (s' - q * s) (t' - q * t) (succ k) s t

@[simp]

中文:
定义 xgcdAux
  签名: : 自然数 -> 整数 -> 整数 -> 自然数 -> 整数 -> 整数 -> 自然数 × 整数 × 整数
  定义体: Nat.strongRec fun n ih s t r' s' t' => match n with
  | 0 => (r', s', t')
  | succ k =>
    let q := r' / succ k
    ih (r' % succ k) (mod_lt _ <| (succ_pos _).gt) (s' - q * s) (t' - q * t) (succ k) s t

@[simp]

Depends on / 依赖: Nat.strongRec, mod_lt, strongRec, succ_pos
-/
def xgcdAux : Nat -> Int -> Int -> Nat -> Int -> Int -> Nat × Int × Int :=
  Nat.strongRec fun n ih s t r' s' t' => match n with
  | 0 => (r', s', t')
  | succ k =>
    let q := r' / succ k
    ih (r' % succ k) (mod_lt _ <| (succ_pos _).gt) (s' - q * s) (t' - q * t) (succ k) s t

@[simp]
/--
theorem `xgcd_zero_left` / 定理 `xgcd_zero_left`

English:
theorem xgcd_zero_left
  given: {s t r' s' t'}
  statement: xgcdAux 0 s t r' s' t' = (r', s', t')
  proof: by
  rw [xgcdAux]; rw [Nat.strongRec_eq]

中文:
定理 xgcd_zero_left
  条件: {s t r' s' t'}
  结论: xgcdAux 0 s t r' s' t' = (r', s', t')
  证明: by
  rw [xgcdAux]; rw [Nat.strongRec_eq]

Depends on / 依赖: Nat.strongRec_eq, strongRec_eq, xgcdAux
-/
theorem xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  rw [xgcdAux]; rw [Nat.strongRec_eq]

/--
theorem `xgcdAux_rec` / 定理 `xgcdAux_rec`

English:
theorem xgcdAux_rec
  given: {r s t r' s' t'} (h : 0 < r)
  proof: by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rw [xgcdAux]; rw [Nat.strongRec_eq]
  rfl

中文:
定理 xgcdAux_rec
  条件: {r s t r' s' t'} (h : 0 < r)
  证明: by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rw [xgcdAux]; rw [Nat.strongRec_eq]
  rfl

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, Nat.strongRec_eq, exists_eq_succ_of_ne_zero, h.ne, strongRec_eq, xgcdAux
-/
theorem xgcdAux_rec {r s t r' s' t'} (h : 0 < r) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rw [xgcdAux]; rw [Nat.strongRec_eq]
  rfl

/--
Definition of `xgcd` / `xgcd` 的定义

English:
definition xgcd
  signature: (x y : Nat)
  body: (xgcdAux x 1 0 y 0 1).2

中文:
定义 xgcd
  签名: (x y : 自然数)
  定义体: (xgcdAux x 1 0 y 0 1).2

Depends on / 依赖: xgcdAux
-/
def xgcd (x y : Nat) : Int × Int :=
  (xgcdAux x 1 0 y 0 1).2

/--
Definition of `gcdA` / `gcdA` 的定义

English:
definition gcdA
  signature: (x y : Nat)
  body: (xgcd x y).1

中文:
定义 gcdA
  签名: (x y : 自然数)
  定义体: (xgcd x y).1
-/
def gcdA (x y : Nat) : Int :=
  (xgcd x y).1

/--
Definition of `gcdB` / `gcdB` 的定义

English:
definition gcdB
  signature: (x y : Nat)
  body: (xgcd x y).2

@[simp]

中文:
定义 gcdB
  签名: (x y : 自然数)
  定义体: (xgcd x y).2

@[simp]
-/
def gcdB (x y : Nat) : Int :=
  (xgcd x y).2

@[simp]
/--
theorem `gcdA_zero_left` / 定理 `gcdA_zero_left`

English:
theorem gcdA_zero_left
  given: {s : Nat}
  statement: gcdA 0 s = 0
  proof: by
  rw [gcdA]; rw [xgcd]; rw [xgcdAux]; rw [Nat.strongRec_eq]

@[simp]

中文:
定理 gcdA_zero_left
  条件: {s : 自然数}
  结论: gcdA 0 s = 0
  证明: by
  rw [gcdA]; rw [xgcd]; rw [xgcdAux]; rw [Nat.strongRec_eq]

@[simp]

Depends on / 依赖: Nat.strongRec_eq, strongRec_eq, xgcdAux
-/
theorem gcdA_zero_left {s : Nat} : gcdA 0 s = 0 := by
  rw [gcdA]; rw [xgcd]; rw [xgcdAux]; rw [Nat.strongRec_eq]

@[simp]
/--
theorem `gcdB_zero_left` / 定理 `gcdB_zero_left`

English:
theorem gcdB_zero_left
  given: {s : Nat}
  statement: gcdB 0 s = 1
  proof: by
  rw [gcdB]; rw [xgcd]; rw [xgcdAux]; rw [Nat.strongRec_eq]

@[simp]

中文:
定理 gcdB_zero_left
  条件: {s : 自然数}
  结论: gcdB 0 s = 1
  证明: by
  rw [gcdB]; rw [xgcd]; rw [xgcdAux]; rw [Nat.strongRec_eq]

@[simp]

Depends on / 依赖: Nat.strongRec_eq, strongRec_eq, xgcdAux
-/
theorem gcdB_zero_left {s : Nat} : gcdB 0 s = 1 := by
  rw [gcdB]; rw [xgcd]; rw [xgcdAux]; rw [Nat.strongRec_eq]

@[simp]
/--
theorem `gcdA_zero_right` / 定理 `gcdA_zero_right`

English:
theorem gcdA_zero_right
  given: {s : Nat} (h : s != 0)
  statement: gcdA s 0 = 1
  proof: by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdA, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]

中文:
定理 gcdA_zero_right
  条件: {s : 自然数} (h : s != 0)
  结论: gcdA s 0 = 1
  证明: by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdA, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, Nat.strongRec_eq, exists_eq_succ_of_ne_zero, strongRec_eq, xgcdAux
-/
theorem gcdA_zero_right {s : Nat} (h : s != 0) : gcdA s 0 = 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdA, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]
/--
theorem `gcdB_zero_right` / 定理 `gcdB_zero_right`

English:
theorem gcdB_zero_right
  given: {s : Nat} (h : s != 0)
  statement: gcdB s 0 = 0
  proof: by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdB, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]

中文:
定理 gcdB_zero_right
  条件: {s : 自然数} (h : s != 0)
  结论: gcdB s 0 = 0
  证明: by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdB, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, Nat.strongRec_eq, exists_eq_succ_of_ne_zero, strongRec_eq, xgcdAux
-/
theorem gcdB_zero_right {s : Nat} (h : s != 0) : gcdB s 0 = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdB, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]
/--
theorem `xgcdAux_fst` / 定理 `xgcdAux_fst`

English:
theorem xgcdAux_fst
  given: (x y)
  statement: forall s t s' t', (xgcdAux x s t y s' t').1 = gcd x y
  proof: gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp only [h, xgcdAux_rec, IH]
    rw [← gcd_rec]

中文:
定理 xgcdAux_fst
  条件: (x y)
  结论: 对任意 s t s' t', (xgcdAux x s t y s' t').1 = 最大公约数 x y
  证明: gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp only [h, xgcdAux_rec, IH]
    rw [← gcd_rec]

Depends on / 依赖: gcd.induction, gcd_rec, xgcdAux_rec
-/
theorem xgcdAux_fst (x y) : forall s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp only [h, xgcdAux_rec, IH]
    rw [← gcd_rec]

/--
theorem `xgcdAux_val` / 定理 `xgcdAux_val`

English:
theorem xgcdAux_val
  given: (x y)
  statement: xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y)
  proof: by
  rw [xgcd]; rw [← xgcdAux_fst x y 1 0 0 1]

中文:
定理 xgcdAux_val
  条件: (x y)
  结论: xgcdAux x 1 0 y 0 1 = (最大公约数 x y, xgcd x y)
  证明: by
  rw [xgcd]; rw [← xgcdAux_fst x y 1 0 0 1]

Depends on / 依赖: xgcdAux_fst
-/
theorem xgcdAux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd]; rw [← xgcdAux_fst x y 1 0 0 1]

/--
theorem `xgcd_val` / 定理 `xgcd_val`

English:
theorem xgcd_val
  given: (x y)
  statement: xgcd x y = (gcdA x y, gcdB x y)
  proof: by
  unfold gcdA gcdB; constructor

中文:
定理 xgcd_val
  条件: (x y)
  结论: xgcd x y = (gcdA x y, gcdB x y)
  证明: by
  unfold gcdA gcdB; constructor
-/
theorem xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y) := by
  unfold gcdA gcdB; constructor

section

variable (x y : Nat)

/--
Definition of `P` / `P` 的定义

English:
definition P
  signature: : Nat × Int × Int -> Prop

中文:
定义 P
  签名: : 自然数 × 整数 × 整数 -> 命题
-/
private def P : Nat × Int × Int -> Prop
  | (r, s, t) => (r : Int) = x * s + y * t

/--
theorem `xgcdAux_P` / 定理 `xgcdAux_P`

English:
theorem xgcdAux_P
  given: {r r'}
  proof: by
  induction r, r' using gcd.induction with
  | H0 => simp
  | H1 a b h IH =>
    intro s t s' t' p p'
    rw [xgcdAux_rec h]; refine IH ?_ p; dsimp [P] at *
    rw [Int.emod_def]; generalize (b / a : Int) = k
    rw [p]; rw [p']; rw [Int.mul_sub]; rw [sub_add_eq_add_sub]; rw [Int.mul_sub]; rw [In

中文:
定理 xgcdAux_P
  条件: {r r'}
  证明: by
  induction r, r' using gcd.induction with
  | H0 => simp
  | H1 a b h IH =>
    intro s t s' t' p p'
    rw [xgcdAux_rec h]; refine IH ?_ p; dsimp [P] at *
    rw [Int.emod_def]; generalize (b / a : Int) = k
    rw [p]; rw [p']; rw [Int.mul_sub]; rw [sub_add_eq_add_sub]; rw [Int.mul_sub]; rw [In
-/
private theorem xgcdAux_P {r r'} :
    forall {s t s' t'}, P x y (r, s, t) -> P x y (r', s', t') -> P x y (xgcdAux r s t r' s' t') := by
  induction r, r' using gcd.induction with
  | H0 => simp
  | H1 a b h IH =>
    intro s t s' t' p p'
    rw [xgcdAux_rec h]; refine IH ?_ p; dsimp [P] at *
    rw [Int.emod_def]; generalize (b / a : Int) = k
    rw [p]; rw [p']; rw [Int.mul_sub]; rw [sub_add_eq_add_sub]; rw [Int.mul_sub]; rw [Int.add_mul]; rw [mul_comm k t]; rw [mul_comm k s]; rw [← mul_assoc]; rw [← mul_assoc]; rw [add_comm (x * s * k)]; rw [← add_sub_assoc]; rw [sub_sub]

/--
theorem `gcd_eq_gcd_ab` / 定理 `gcd_eq_gcd_ab`

English:
theorem gcd_eq_gcd_ab
  statement: (gcd x y : Int) = x * gcdA x y + y * gcdB x y
  proof: by
  have := @xgcdAux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P])
  rwa [xgcdAux_val, xgcd_val] at this

中文:
定理 gcd_eq_gcd_ab
  结论: (最大公约数 x y : 整数) = x * gcdA x y + y * gcdB x y
  证明: by
  have := @xgcdAux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P])
  rwa [xgcdAux_val, xgcd_val] at this

Depends on / 依赖: xgcdAux_P, xgcdAux_val, xgcd_val
-/
theorem gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * gcdB x y := by
  have := @xgcdAux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P])
  rwa [xgcdAux_val, xgcd_val] at this

end

/--
theorem `exists_mul_mod_eq_gcd` / 定理 `exists_mul_mod_eq_gcd`

English:
theorem exists_mul_mod_eq_gcd
  given: {k n : Nat} (hk : gcd n k < k)
  statement: exists m < k, n * m % k = gcd n k
  proof: by
  have hk' := Int.ofNat_ne_zero.2 (Nat.zero_lt_of_lt hk).ne'
  have key := congr(($(gcd_eq_gcd_ab n k) % k).toNat)
  rw [Int.add_mul_emod_self_left]; rw [← Int.natCast_mod]; rw [Int.toNat_natCast]; rw [mod_eq_of_lt hk] at key
  refine ⟨(n.gcdA k % k).toNat, ?_, (Int.ofNat_inj.1 ?_).trans key.symm

中文:
定理 存在_mul_mod_eq_gcd
  条件: {k n : 自然数} (hk : 最大公约数 n k < k)
  结论: 存在 m < k, n * m % k = 最大公约数 n k
  证明: by
  have hk' := Int.ofNat_ne_zero.2 (Nat.zero_lt_of_lt hk).ne'
  have key := congr(($(gcd_eq_gcd_ab n k) % k).toNat)
  rw [Int.add_mul_emod_self_left]; rw [← Int.natCast_mod]; rw [Int.toNat_natCast]; rw [mod_eq_of_lt hk] at key
  refine ⟨(n.gcdA k % k).toNat, ?_, (Int.ofNat_inj.1 ?_).trans key.symm

Depends on / 依赖: Int.add_mul_emod_self_left, Int.emod_lt, Int.emod_nonneg, Int.natCast_mod, Int.natCast_mul, Int.ofNat_inj, Int.ofNat_ne_zero, Int.toNat_lt, Int.toNat_natCast, Int.toNat_of_nonneg, Nat.zero_lt_of_lt, add_mul_emod_self_left, emod_lt, emod_nonneg, gcd_eq_gcd_ab, key.symm, mod_eq_of_lt, n.gcdA, natCast_mod, natCast_mul
-/
theorem exists_mul_mod_eq_gcd {k n : Nat} (hk : gcd n k < k) : exists m < k, n * m % k = gcd n k := by
  have hk' := Int.ofNat_ne_zero.2 (Nat.zero_lt_of_lt hk).ne'
  have key := congr(($(gcd_eq_gcd_ab n k) % k).toNat)
  rw [Int.add_mul_emod_self_left]; rw [← Int.natCast_mod]; rw [Int.toNat_natCast]; rw [mod_eq_of_lt hk] at key
  refine ⟨(n.gcdA k % k).toNat, ?_, (Int.ofNat_inj.1 ?_).trans key.symm⟩
  · rw [Int.toNat_lt (Int.emod_nonneg _ hk')]
    exact Int.emod_lt _ hk'
  rw [Int.natCast_mod]; rw [Int.natCast_mul]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk')]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk')]; rw [Int.mul_emod]; rw [Int.emod_emod]; rw [← Int.mul_emod]

/--
theorem `exists_mul_mod_eq_one_of_coprime` / 定理 `exists_mul_mod_eq_one_of_coprime`

English:
theorem exists_mul_mod_eq_one_of_coprime
  given: {k n : Nat} (hkn : Coprime n k) (hk : 1 < k)
  proof: by
  simpa [hkn, hk] using exists_mul_mod_eq_gcd (k := k) (n := n)

中文:
定理 存在_mul_mod_eq_one_of_coprime
  条件: {k n : 自然数} (hkn : Coprime n k) (hk : 1 < k)
  证明: by
  simpa [hkn, hk] using exists_mul_mod_eq_gcd (k := k) (n := n)

Depends on / 依赖: exists_mul_mod_eq_gcd
-/
theorem exists_mul_mod_eq_one_of_coprime {k n : Nat} (hkn : Coprime n k) (hk : 1 < k) :
    exists m < k, n * m % k = 1 := by
  simpa [hkn, hk] using exists_mul_mod_eq_gcd (k := k) (n := n)

/--
theorem `exists_mul_mod_eq_of_coprime` / 定理 `exists_mul_mod_eq_of_coprime`

English:
theorem exists_mul_mod_eq_of_coprime
  given: {k n : Nat} (r : Nat) (hkn : Coprime n k) (hk : k != 0)
  proof: by
  obtain rfl | hk : k = 1 ∨ 1 < k := by lia
  · simp [mod_one]
  obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hkn hk
  use (m * r) % k, mod_lt _ (by lia)
  rw [mul_mod]; rw [mod_mod]; rw [← mul_mod]; rw [← mul_assoc]; rw [mul_mod]; rw [hm]; rw [one_mul]; rw [mod_mod]

中文:
定理 存在_mul_mod_eq_of_coprime
  条件: {k n : 自然数} (r : 自然数) (hkn : Coprime n k) (hk : k != 0)
  证明: by
  obtain rfl | hk : k = 1 ∨ 1 < k := by lia
  · simp [mod_one]
  obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hkn hk
  use (m * r) % k, mod_lt _ (by lia)
  rw [mul_mod]; rw [mod_mod]; rw [← mul_mod]; rw [← mul_assoc]; rw [mul_mod]; rw [hm]; rw [one_mul]; rw [mod_mod]

Depends on / 依赖: exists_mul_mod_eq_one_of_coprime, mod_lt, mod_mod, mod_one, mul_assoc, mul_mod, one_mul
-/
theorem exists_mul_mod_eq_of_coprime {k n : Nat} (r : Nat) (hkn : Coprime n k) (hk : k != 0) :
    exists m < k, n * m % k = r % k := by
  obtain rfl | hk : k = 1 ∨ 1 < k := by lia
  · simp [mod_one]
  obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hkn hk
  use (m * r) % k, mod_lt _ (by lia)
  rw [mul_mod]; rw [mod_mod]; rw [← mul_mod]; rw [← mul_assoc]; rw [mul_mod]; rw [hm]; rw [one_mul]; rw [mod_mod]

end Nat

/-! ### Divisibility over ℤ -/


namespace Int

/--
theorem `gcd_def` / 定理 `gcd_def`

English:
theorem gcd_def
  given: (i j : Int)
  statement: gcd i j = Nat.gcd i.natAbs j.natAbs
  proof: rfl

中文:
定理 gcd_def
  条件: (i j : 整数)
  结论: 最大公约数 i j = 自然数.最大公约数 i.natAbs j.natAbs
  证明: rfl
-/
theorem gcd_def (i j : Int) : gcd i j = Nat.gcd i.natAbs j.natAbs := rfl

/--
Definition of `gcdA` / `gcdA` 的定义

English:
definition gcdA
  signature: : Int -> Int -> Int

中文:
定义 gcdA
  签名: : 整数 -> 整数 -> 整数
-/
def gcdA : Int -> Int -> Int
  | ofNat m, n => m.gcdA n.natAbs
  | -[m+1], n => -m.succ.gcdA n.natAbs

/--
Definition of `gcdB` / `gcdB` 的定义

English:
definition gcdB
  signature: : Int -> Int -> Int

中文:
定义 gcdB
  签名: : 整数 -> 整数 -> 整数
-/
def gcdB : Int -> Int -> Int
  | m, ofNat n => m.natAbs.gcdB n
  | m, -[n+1] => -m.natAbs.gcdB n.succ

/--
theorem `gcd_eq_gcd_ab` / 定理 `gcd_eq_gcd_ab`

English:
theorem gcd_eq_gcd_ab
  statement: forall x y : Int, (gcd x y : Int) = x * gcdA x y + y * gcdB x y

中文:
定理 gcd_eq_gcd_ab
  结论: 对任意 x y : 整数, (最大公约数 x y : 整数) = x * gcdA x y + y * gcdB x y
-/
theorem gcd_eq_gcd_ab : forall x y : Int, (gcd x y : Int) = x * gcdA x y + y * gcdB x y
  | (m : Nat), (n : Nat) => Nat.gcd_eq_gcd_ab _ _
  | (m : Nat), -[n+1] =>
    show (_ : Int) = _ + -(n + 1) * -_ by rw [Int.neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], (n : Nat) =>
    show (_ : Int) = -(m + 1) * -_ + _ by rw [Int.neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], -[n+1] =>
    show (_ : Int) = -(m + 1) * -_ + -(n + 1) * -_ by
      rw [Int.neg_mul_neg]; rw [Int.neg_mul_neg]
      apply Nat.gcd_eq_gcd_ab

/--
theorem `lcm_def` / 定理 `lcm_def`

English:
theorem lcm_def
  given: (i j : Int)
  statement: lcm i j = Nat.lcm (natAbs i) (natAbs j)
  proof: rfl

alias gcd_div := gcd_ediv
alias gcd_div_gcd_div_gcd := gcd_ediv_gcd_ediv_gcd

中文:
定理 lcm_def
  条件: (i j : 整数)
  结论: 最小公倍数 i j = 自然数.最小公倍数 (natAbs i) (natAbs j)
  证明: rfl

alias gcd_div := gcd_ediv
alias gcd_div_gcd_div_gcd := gcd_ediv_gcd_ediv_gcd
-/
theorem lcm_def (i j : Int) : lcm i j = Nat.lcm (natAbs i) (natAbs j) :=
  rfl

alias gcd_div := gcd_ediv
alias gcd_div_gcd_div_gcd := gcd_ediv_gcd_ediv_gcd

/--
theorem `gcd_eq_one_of_gcd_mul_right_eq_one_left` / 定理 `gcd_eq_one_of_gcd_mul_right_eq_one_left`

English:
theorem gcd_eq_one_of_gcd_mul_right_eq_one_left
  given: {a : Int} {m n : Nat} (h : a.gcd (m * n) = 1)
  proof: Nat.dvd_one.mp h ▸ gcd_dvd_gcd_mul_right_right a m n

中文:
定理 gcd_eq_one_of_gcd_mul_right_eq_one_left
  条件: {a : 整数} {m n : 自然数} (h : a.最大公约数 (m * n) = 1)
  证明: Nat.dvd_one.mp h ▸ gcd_dvd_gcd_mul_right_right a m n

Depends on / 依赖: Nat.dvd_one.mp, dvd_one, gcd_dvd_gcd_mul_right_right
-/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_left {a : Int} {m n : Nat} (h : a.gcd (m * n) = 1) :
    a.gcd m = 1 :=
Nat.dvd_one.mp h ▸ gcd_dvd_gcd_mul_right_right a m n

/--
theorem `gcd_eq_one_of_gcd_mul_right_eq_one_right` / 定理 `gcd_eq_one_of_gcd_mul_right_eq_one_right`

English:
theorem gcd_eq_one_of_gcd_mul_right_eq_one_right
  given: {a : Int} {m n : Nat} (h : a.gcd (m * n) = 1)
  proof: Nat.dvd_one.mp h ▸ gcd_dvd_gcd_mul_left_right a n m

中文:
定理 gcd_eq_one_of_gcd_mul_right_eq_one_right
  条件: {a : 整数} {m n : 自然数} (h : a.最大公约数 (m * n) = 1)
  证明: Nat.dvd_one.mp h ▸ gcd_dvd_gcd_mul_left_right a n m

Depends on / 依赖: Nat.dvd_one.mp, dvd_one, gcd_dvd_gcd_mul_left_right
-/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_right {a : Int} {m n : Nat} (h : a.gcd (m * n) = 1) :
    a.gcd n = 1 :=
Nat.dvd_one.mp h ▸ gcd_dvd_gcd_mul_left_right a n m

/--
theorem `ne_zero_of_gcd` / 定理 `ne_zero_of_gcd`

English:
theorem ne_zero_of_gcd
  given: {x y : Int} (hc : gcd x y != 0)
  statement: x != 0 ∨ y != 0
  proof: by
  contrapose! hc
  rw [hc.left]; rw [hc.right]; rw [gcd_zero_right]; rw [natAbs_zero]

中文:
定理 ne_zero_of_gcd
  条件: {x y : 整数} (hc : 最大公约数 x y != 0)
  结论: x != 0 ∨ y != 0
  证明: by
  contrapose! hc
  rw [hc.left]; rw [hc.right]; rw [gcd_zero_right]; rw [natAbs_zero]

Depends on / 依赖: contrapose, gcd_zero_right, hc.left, hc.right, natAbs_zero
-/
theorem ne_zero_of_gcd {x y : Int} (hc : gcd x y != 0) : x != 0 ∨ y != 0 := by
  contrapose! hc
  rw [hc.left]; rw [hc.right]; rw [gcd_zero_right]; rw [natAbs_zero]

/--
theorem `exists_gcd_one` / 定理 `exists_gcd_one`

English:
theorem exists_gcd_one
  given: {m n : Int} (H : 0 < gcd m n)
  proof: ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel (gcd_dvd_left ..)).symm,
    (Int.ediv_mul_cancel (gcd_dvd_right ..)).symm⟩

中文:
定理 存在_gcd_one
  条件: {m n : 整数} (H : 0 < 最大公约数 m n)
  证明: ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel (gcd_dvd_left ..)).symm,
    (Int.ediv_mul_cancel (gcd_dvd_right ..)).symm⟩

Depends on / 依赖: Int.ediv_mul_cancel, ediv_mul_cancel, gcd_div_gcd_div_gcd, gcd_dvd_left, gcd_dvd_right
-/
theorem exists_gcd_one {m n : Int} (H : 0 < gcd m n) :
    exists m' n' : Int, gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel (gcd_dvd_left ..)).symm,
    (Int.ediv_mul_cancel (gcd_dvd_right ..)).symm⟩

/--
theorem `exists_gcd_one'` / 定理 `exists_gcd_one'`

English:
theorem exists_gcd_one'
  given: {m n : Int} (H : 0 < gcd m n)
  proof: let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩

中文:
定理 存在_gcd_one'
  条件: {m n : 整数} (H : 0 < 最大公约数 m n)
  证明: let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩

Depends on / 依赖: exists_gcd_one
-/
theorem exists_gcd_one' {m n : Int} (H : 0 < gcd m n) :
    exists (g : Nat) (m' n' : Int), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩

/--
theorem `gcd_dvd_iff` / 定理 `gcd_dvd_iff`

English:
theorem gcd_dvd_iff
  given: {a b : Int} {n : Nat}
  statement: gcd a b ∣ n ↔ exists x y : Int, ↑n = a * x + b * y
  proof: by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel' h]; rw [Int.natCast_mul]; rw [gcd_eq_gcd_ab]; rw [Int.add_mul]; rw [mul_assoc]; rw [mul_assoc]
    exact ⟨_, _, rfl⟩
  · rintro ⟨x, y, h⟩
    rw [← Int.natCast_dvd_natCast]; rw [h]
    exact Int.dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left ..)

中文:
定理 gcd_dvd_iff
  条件: {a b : 整数} {n : 自然数}
  结论: 最大公约数 a b ∣ n ↔ 存在 x y : 整数, ↑n = a * x + b * y
  证明: by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel' h]; rw [Int.natCast_mul]; rw [gcd_eq_gcd_ab]; rw [Int.add_mul]; rw [mul_assoc]; rw [mul_assoc]
    exact ⟨_, _, rfl⟩
  · rintro ⟨x, y, h⟩
    rw [← Int.natCast_dvd_natCast]; rw [h]
    exact Int.dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left ..)

Depends on / 依赖: Int.add_mul, Int.dvd_add, Int.natCast_dvd_natCast, Int.natCast_mul, Nat.mul_div_cancel, add_mul, dvd_add, dvd_mul_of_dvd_left, gcd_dvd_left, gcd_dvd_right, gcd_eq_gcd_ab, mul_assoc, mul_div_cancel, natCast_dvd_natCast, natCast_mul
-/
theorem gcd_dvd_iff {a b : Int} {n : Nat} : gcd a b ∣ n ↔ exists x y : Int, ↑n = a * x + b * y := by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel' h]; rw [Int.natCast_mul]; rw [gcd_eq_gcd_ab]; rw [Int.add_mul]; rw [mul_assoc]; rw [mul_assoc]
    exact ⟨_, _, rfl⟩
  · rintro ⟨x, y, h⟩
    rw [← Int.natCast_dvd_natCast]; rw [h]
    exact Int.dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left ..))
      (dvd_mul_of_dvd_left (gcd_dvd_right ..))

/--
theorem `gcd_greatest` / 定理 `gcd_greatest`

English:
theorem gcd_greatest
  statement: {a b d : Int} (hd_pos : 0 <= d) (hda : d ∣ a) (hdb : d ∣ b)
  proof: dvd_antisymm hd_pos (natCast_nonneg (gcd a b)) (dvd_coe_gcd hda hdb)
    (hd _ (gcd_dvd_left ..) (gcd_dvd_right ..))

中文:
定理 gcd_greatest
  结论: {a b d : 整数} (hd_pos : 0 <= d) (hda : d ∣ a) (hdb : d ∣ b)
  证明: dvd_antisymm hd_pos (natCast_nonneg (gcd a b)) (dvd_coe_gcd hda hdb)
    (hd _ (gcd_dvd_left ..) (gcd_dvd_right ..))

Depends on / 依赖: dvd_antisymm, dvd_coe_gcd, gcd_dvd_left, gcd_dvd_right, hd_pos, natCast_nonneg
-/
theorem gcd_greatest {a b d : Int} (hd_pos : 0 <= d) (hda : d ∣ a) (hdb : d ∣ b)
    (hd : forall e : Int, e ∣ a -> e ∣ b -> e ∣ d) : d = gcd a b :=
  dvd_antisymm hd_pos (natCast_nonneg (gcd a b)) (dvd_coe_gcd hda hdb)
    (hd _ (gcd_dvd_left ..) (gcd_dvd_right ..))

/--
theorem `dvd_of_dvd_mul_left_of_gcd_one` / 定理 `dvd_of_dvd_mul_left_of_gcd_one`

English:
theorem dvd_of_dvd_mul_left_of_gcd_one
  given: {a b c : Int} (habc : a ∣ b * c) (hab : gcd a c = 1)
  proof: by
  have := gcd_eq_gcd_ab a c
  simp only [hab, Int.ofNat_zero, Int.natCast_succ, zero_add] at this
  have : b * a * gcdA a c + b * c * gcdB a c = b := by simp [mul_assoc, ← Int.mul_add, ← this]
  rw [← this]
  exact Int.dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a b)) (dvd_mul_of_dvd_left habc)

中文:
定理 dvd_of_dvd_mul_left_of_gcd_one
  条件: {a b c : 整数} (habc : a ∣ b * c) (hab : 最大公约数 a c = 1)
  证明: by
  have := gcd_eq_gcd_ab a c
  simp only [hab, Int.ofNat_zero, Int.natCast_succ, zero_add] at this
  have : b * a * gcdA a c + b * c * gcdB a c = b := by simp [mul_assoc, ← Int.mul_add, ← this]
  rw [← this]
  exact Int.dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a b)) (dvd_mul_of_dvd_left habc)

Depends on / 依赖: Int.dvd_add, Int.mul_add, Int.natCast_succ, Int.ofNat_zero, dvd_add, dvd_mul_left, dvd_mul_of_dvd_left, gcd_eq_gcd_ab, mul_add, mul_assoc, natCast_succ, ofNat_zero, zero_add
-/
theorem dvd_of_dvd_mul_left_of_gcd_one {a b c : Int} (habc : a ∣ b * c) (hab : gcd a c = 1) :
    a ∣ b := by
  have := gcd_eq_gcd_ab a c
  simp only [hab, Int.ofNat_zero, Int.natCast_succ, zero_add] at this
  have : b * a * gcdA a c + b * c * gcdB a c = b := by simp [mul_assoc, ← Int.mul_add, ← this]
  rw [← this]
  exact Int.dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a b)) (dvd_mul_of_dvd_left habc)

/--
theorem `dvd_of_dvd_mul_right_of_gcd_one` / 定理 `dvd_of_dvd_mul_right_of_gcd_one`

English:
theorem dvd_of_dvd_mul_right_of_gcd_one
  given: {a b c : Int} (habc : a ∣ b * c) (hab : gcd a b = 1)
  proof: by
  rw [mul_comm] at habc
  exact dvd_of_dvd_mul_left_of_gcd_one habc hab

中文:
定理 dvd_of_dvd_mul_right_of_gcd_one
  条件: {a b c : 整数} (habc : a ∣ b * c) (hab : 最大公约数 a b = 1)
  证明: by
  rw [mul_comm] at habc
  exact dvd_of_dvd_mul_left_of_gcd_one habc hab

Depends on / 依赖: dvd_of_dvd_mul_left_of_gcd_one, mul_comm
-/
theorem dvd_of_dvd_mul_right_of_gcd_one {a b c : Int} (habc : a ∣ b * c) (hab : gcd a b = 1) :
    a ∣ c := by
  rw [mul_comm] at habc
  exact dvd_of_dvd_mul_left_of_gcd_one habc hab

/--
theorem `gcd_least_linear` / 定理 `gcd_least_linear`

English:
theorem gcd_least_linear
  given: {a b : Int} (ha : a != 0)
  proof: by
  simp_rw [← gcd_dvd_iff]
  constructor
  · simpa [and_true, dvd_refl, Set.mem_ofPred_eq] using gcd_pos_of_ne_zero_left b ha
  · simp only [lowerBounds, and_imp, Set.mem_ofPred_eq]
    exact fun n hn_pos hn => Nat.le_of_dvd hn_pos hn

中文:
定理 gcd_least_linear
  条件: {a b : 整数} (ha : a != 0)
  证明: by
  simp_rw [← gcd_dvd_iff]
  constructor
  · simpa [and_true, dvd_refl, Set.mem_ofPred_eq] using gcd_pos_of_ne_zero_left b ha
  · simp only [lowerBounds, and_imp, Set.mem_ofPred_eq]
    exact fun n hn_pos hn => Nat.le_of_dvd hn_pos hn

Depends on / 依赖: Nat.le_of_dvd, Set.mem_ofPred_eq, and_imp, and_true, dvd_refl, gcd_dvd_iff, gcd_pos_of_ne_zero_left, hn_pos, le_of_dvd, lowerBounds, mem_ofPred_eq, simp_rw
-/
theorem gcd_least_linear {a b : Int} (ha : a != 0) :
    IsLeast { n : Nat | 0 < n ∧ exists x y : Int, ↑n = a * x + b * y } (a.gcd b) := by
  simp_rw [← gcd_dvd_iff]
  constructor
  · simpa [and_true, dvd_refl, Set.mem_ofPred_eq] using gcd_pos_of_ne_zero_left b ha
  · simp only [lowerBounds, and_imp, Set.mem_ofPred_eq]
    exact fun n hn_pos hn => Nat.le_of_dvd hn_pos hn

end Int

section Monoid
variable {M : Type*} [Monoid M] {a : M} {m n : Nat}

@[to_additive (attr := simp) gcd_nsmul_eq_zero]
/--
lemma `pow_gcd_eq_one` / 引理 `pow_gcd_eq_one`

English:
lemma pow_gcd_eq_one
  statement: a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 where
  proof: by
    constructor
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_left n), pow_mul, hmn, one_pow]
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_right n), pow_mul, hmn, one_pow]
  mpr
  | ⟨hm, hn⟩ => by
    obtain _ | m := m
    · simpa
    obtain ⟨y, rfl⟩ := IsUnit.of_pow_eq_one hm m.succ_ne_zero
    rw [←

中文:
引理 pow_gcd_eq_one
  结论: a ^ m.最大公约数 n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 where
  证明: by
    constructor
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_left n), pow_mul, hmn, one_pow]
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_right n), pow_mul, hmn, one_pow]
  mpr
  | ⟨hm, hn⟩ => by
    obtain _ | m := m
    · simpa
    obtain ⟨y, rfl⟩ := IsUnit.of_pow_eq_one hm m.succ_ne_zero
    rw [←

Depends on / 依赖: IsUnit, IsUnit.of_pow_eq_one, Nat.gcd_eq_gcd_ab, Nat.mul_div_cancel, Units.ext_iff, Units.val_one, Units.val_pow_eq_pow_val, ext_iff, gcd_dvd_left, gcd_dvd_right, gcd_eq_gcd_ab, m.gcd_dvd_left, m.gcd_dvd_right, m.succ_ne_zero, mul_div_cancel, of_pow_eq_one, one_m, one_pow, one_zpow, pow_mul
-/
lemma pow_gcd_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 where
  mp hmn := by
    constructor
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_left n), pow_mul, hmn, one_pow]
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_right n), pow_mul, hmn, one_pow]
  mpr
  | ⟨hm, hn⟩ => by
    obtain _ | m := m
    · simpa
    obtain ⟨y, rfl⟩ := IsUnit.of_pow_eq_one hm m.succ_ne_zero
    rw [← Units.val_pow_eq_pow_val]; rw [← Units.val_one (α := M)]; rw [← zpow_natCast]; rw [← Units.ext_iff] at *
    rw [Nat.gcd_eq_gcd_ab]; rw [zpow_add]; rw [zpow_mul]; rw [zpow_mul]; rw [hn]; rw [hm]; rw [one_zpow]; rw [one_zpow]; rw [one_mul]

@[to_additive]
/--
lemma `pow_eq_one_iff_of_coprime` / 引理 `pow_eq_one_iff_of_coprime`

English:
lemma pow_eq_one_iff_of_coprime
  given: (hmn : m.Coprime n)
  statement: a ^ m = 1 ∧ a ^ n = 1 ↔ a = 1
  proof: by
  simp [← pow_gcd_eq_one, hmn]

中文:
引理 pow_eq_one_iff_of_coprime
  条件: (hmn : m.Coprime n)
  结论: a ^ m = 1 ∧ a ^ n = 1 ↔ a = 1
  证明: by
  simp [← pow_gcd_eq_one, hmn]

Depends on / 依赖: pow_gcd_eq_one
-/
lemma pow_eq_one_iff_of_coprime (hmn : m.Coprime n) : a ^ m = 1 ∧ a ^ n = 1 ↔ a = 1 := by
  simp [← pow_gcd_eq_one, hmn]

end Monoid

section Group
variable {M : Type*} [Group M] {a : M} {m n : Int}

@[to_additive (attr := simp) intGCD_nsmul_eq_zero]
/--
lemma `pow_intGCD_eq_one` / 引理 `pow_intGCD_eq_one`

English:
lemma pow_intGCD_eq_one
  statement: a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1
  proof: by
  obtain m | m := m <;> obtain n | n := n <;> simp

中文:
引理 pow_intGCD_eq_one
  结论: a ^ m.最大公约数 n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1
  证明: by
  obtain m | m := m <;> obtain n | n := n <;> simp
-/
lemma pow_intGCD_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 := by
  obtain m | m := m <;> obtain n | n := n <;> simp

end Group

variable {α : Type*}

section GroupWithZero
variable [GroupWithZero α] {a b : α} {m n : Nat}

/--
lemma `Commute.pow_eq_pow_iff_of_coprime` / 引理 `Commute.pow_eq_pow_iff_of_coprime`

English:
lemma Commute.pow_eq_pow_iff_of_coprime
  given: (hab : Commute a b) (hmn : m.Coprime n)
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨c, rfl, rfl⟩; rw [← pow_mul, ← pow_mul']⟩
  by_cases m = 0; · simp_all
  by_cases n = 0; · simp_all
  by_cases hb : b = 0; · exact ⟨0, by simp_all⟩
  by_cases ha : a = 0; · exact ⟨0, by have := h.symm; simp_all⟩
  refine ⟨a ^ Nat.gcdB m n * b ^ Nat.gcdA m n, ?_, 

中文:
引理 Commute.pow_eq_pow_iff_of_coprime
  条件: (hab : Commute a b) (hmn : m.Coprime n)
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨c, rfl, rfl⟩; rw [← pow_mul, ← pow_mul']⟩
  by_cases m = 0; · simp_all
  by_cases n = 0; · simp_all
  by_cases hb : b = 0; · exact ⟨0, by simp_all⟩
  by_cases ha : a = 0; · exact ⟨0, by have := h.symm; simp_all⟩
  refine ⟨a ^ Nat.gcdB m n * b ^ Nat.gcdA m n, ?_, 
-/
protected lemma Commute.pow_eq_pow_iff_of_coprime (hab : Commute a b) (hmn : m.Coprime n) :
    a ^ m = b ^ n ↔ exists c, a = c ^ n ∧ b = c ^ m := by
  refine ⟨fun h => ?_, by rintro ⟨c, rfl, rfl⟩; rw [← pow_mul, ← pow_mul']⟩
  by_cases m = 0; · simp_all
  by_cases n = 0; · simp_all
  by_cases hb : b = 0; · exact ⟨0, by simp_all⟩
  by_cases ha : a = 0; · exact ⟨0, by have := h.symm; simp_all⟩
  refine ⟨a ^ Nat.gcdB m n * b ^ Nat.gcdA m n, ?_, ?_⟩ <;>
  · refine (pow_one _).symm.trans ?_
    conv_lhs => rw [← zpow_natCast, ← hmn, Nat.gcd_eq_gcd_ab]
    simp only [zpow_add₀ ha, zpow_add₀ hb, ← zpow_natCast, (hab.zpow_zpow₀ _ _).mul_zpow,
      ← zpow_mul, mul_comm (Nat.gcdB m n), mul_comm (Nat.gcdA m n)]
    simp only [zpow_mul, zpow_natCast, h]
    exact ((Commute.pow_pow (by aesop) _ _).zpow_zpow₀ _ _).symm

end GroupWithZero

section CommGroupWithZero
variable [CommGroupWithZero α] {a b : α} {m n : Nat}

/--
lemma `pow_eq_pow_iff_of_coprime` / 引理 `pow_eq_pow_iff_of_coprime`

English:
lemma pow_eq_pow_iff_of_coprime
  given: (hmn : m.Coprime n)
  statement: a ^ m = b ^ n ↔ exists c, a = c ^ n ∧ b = c ^ m
  proof: (Commute.all _ _).pow_eq_pow_iff_of_coprime hmn

中文:
引理 pow_eq_pow_iff_of_coprime
  条件: (hmn : m.Coprime n)
  结论: a ^ m = b ^ n ↔ 存在 c, a = c ^ n ∧ b = c ^ m
  证明: (Commute.all _ _).pow_eq_pow_iff_of_coprime hmn

Depends on / 依赖: Commute, Commute.all, pow_eq_pow_iff_of_coprime
-/
lemma pow_eq_pow_iff_of_coprime (hmn : m.Coprime n) : a ^ m = b ^ n ↔ exists c, a = c ^ n ∧ b = c ^ m :=
  (Commute.all _ _).pow_eq_pow_iff_of_coprime hmn

/--
lemma `pow_mem_range_pow_of_coprime` / 引理 `pow_mem_range_pow_of_coprime`

English:
lemma pow_mem_range_pow_of_coprime
  given: (hmn : m.Coprime n) (a : α)
  proof: by
  simp [pow_eq_pow_iff_of_coprime hmn.symm]; aesop

中文:
引理 pow_mem_range_pow_of_coprime
  条件: (hmn : m.Coprime n) (a : α)
  证明: by
  simp [pow_eq_pow_iff_of_coprime hmn.symm]; aesop

Depends on / 依赖: hmn.symm, pow_eq_pow_iff_of_coprime
-/
lemma pow_mem_range_pow_of_coprime (hmn : m.Coprime n) (a : α) :
    a ^ m in Set.range (· ^ n : α -> α) ↔ a in Set.range (· ^ n : α -> α) := by
  simp [pow_eq_pow_iff_of_coprime hmn.symm]; aesop

end CommGroupWithZero
