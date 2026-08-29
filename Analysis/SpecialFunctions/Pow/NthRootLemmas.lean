/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Zify
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# Lemmas about `Nat.nthRoot`

In this file we prove that `Nat.nthRoot n a` is indeed the floor of `ⁿ√a`.
-/

public section

namespace Nat

variable {m n a b guess fuel : Nat}

/--
theorem `nthRoot_zero_left` / 定理 `nthRoot_zero_left`

English:
theorem nthRoot_zero_left
  given: (a : Nat)
  statement: nthRoot 0 a = 1
  proof: rfl

中文:
定理 nthRoot_zero_left
  条件: (a : 自然数)
  结论: nthRoot 0 a = 1
  证明: rfl
-/
@[simp] theorem nthRoot_zero_left (a : Nat) : nthRoot 0 a = 1 := rfl

/--
theorem `nthRoot_one_left` / 定理 `nthRoot_one_left`

English:
theorem nthRoot_one_left
  statement: nthRoot 1 = id
  proof: rfl

@[simp]

中文:
定理 nthRoot_one_left
  结论: nthRoot 1 = id
  证明: rfl

@[simp]
-/
@[simp] theorem nthRoot_one_left : nthRoot 1 = id := rfl

@[simp]
/--
theorem `nthRoot_zero_right` / 定理 `nthRoot_zero_right`

English:
theorem nthRoot_zero_right
  given: (h : n != 0)
  statement: nthRoot n 0 = 0
  proof: by
  rcases n with _ | _ | _ <;> grind [nthRoot, nthRoot.go]

@[simp]

中文:
定理 nthRoot_zero_right
  条件: (h : n != 0)
  结论: nthRoot n 0 = 0
  证明: by
  rcases n with _ | _ | _ <;> grind [nthRoot, nthRoot.go]

@[simp]

Depends on / 依赖: nthRoot, nthRoot.go
-/
theorem nthRoot_zero_right (h : n != 0) : nthRoot n 0 = 0 := by
  rcases n with _ | _ | _ <;> grind [nthRoot, nthRoot.go]

@[simp]
/--
theorem `nthRoot_one_right` / 定理 `nthRoot_one_right`

English:
theorem nthRoot_one_right
  statement: nthRoot n 1 = 1
  proof: by
  rcases n with _ | _ | _ <;> simp [nthRoot, nthRoot.go, Nat.add_comm 1]

中文:
定理 nthRoot_one_right
  结论: nthRoot n 1 = 1
  证明: by
  rcases n with _ | _ | _ <;> simp [nthRoot, nthRoot.go, Nat.add_comm 1]

Depends on / 依赖: Nat.add_comm, add_comm, nthRoot, nthRoot.go
-/
theorem nthRoot_one_right : nthRoot n 1 = 1 := by
  rcases n with _ | _ | _ <;> simp [nthRoot, nthRoot.go, Nat.add_comm 1]

/--
theorem `nthRoot.pow_go_le` / 定理 `nthRoot.pow_go_le`

English:
theorem nthRoot.pow_go_le
  given: (hle : guess <= fuel) (n a : Nat)
  proof: by
  induction fuel generalizing guess with
  | zero =>
    obtain rfl : guess = 0 := by grind
    simp [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      grind
    case neg =>
      have : guess <= a / guess ^ (n + 1) := by
        linarith only [Nat.mul_le_of_le_div _ _ _ (not_lt.1 h)]
      replace := Nat.mul_le_of_le_div _ _ _ this
      grind

中文:
定理 nthRoot.pow_go_le
  条件: (hle : guess <= fuel) (n a : 自然数)
  证明: by
  induction fuel generalizing guess with
  | zero =>
    obtain rfl : guess = 0 := by grind
    simp [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      grind
    case neg =>
      have : guess <= a / guess ^ (n + 1) := by
        linarith only [Nat.mul_le_of_le_div _ _ _ (not_lt.1 h)]
      replace := Nat.mul_le_of_le_div _ _ _ this
      grind
-/
private theorem nthRoot.pow_go_le (hle : guess <= fuel) (n a : Nat) :
    go n a fuel guess ^ (n + 2) <= a := by
  induction fuel generalizing guess with
  | zero =>
    obtain rfl : guess = 0 := by grind
    simp [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      grind
    case neg =>
      have : guess <= a / guess ^ (n + 1) := by
        linarith only [Nat.mul_le_of_le_div _ _ _ (not_lt.1 h)]
      replace := Nat.mul_le_of_le_div _ _ _ this
      grind

/-- `nthRoot n a ^ n ≤ a` unless both `n` and `a` are zeros. -/
@[simp]
/--
theorem `pow_nthRoot_le_iff` / 定理 `pow_nthRoot_le_iff`

English:
theorem pow_nthRoot_le_iff
  statement: nthRoot n a ^ n <= a ↔ n != 0 ∨ a != 0
  proof: by
  rcases n with _ | _ | _ <;> first | grind | simp [nthRoot, nthRoot.pow_go_le]

alias ⟨_, pow_nthRoot_le⟩ := pow_nthRoot_le_iff

中文:
定理 pow_nthRoot_le_iff
  结论: nthRoot n a ^ n <= a ↔ n != 0 ∨ a != 0
  证明: by
  rcases n with _ | _ | _ <;> first | grind | simp [nthRoot, nthRoot.pow_go_le]

alias ⟨_, pow_nthRoot_le⟩ := pow_nthRoot_le_iff

Depends on / 依赖: nthRoot, nthRoot.pow_go_le, pow_go_le
-/
theorem pow_nthRoot_le_iff : nthRoot n a ^ n <= a ↔ n != 0 ∨ a != 0 := by
  rcases n with _ | _ | _ <;> first | grind | simp [nthRoot, nthRoot.pow_go_le]

alias ⟨_, pow_nthRoot_le⟩ := pow_nthRoot_le_iff

/--
theorem `nthRoot.lt_pow_go_succ_aux0` / 定理 `nthRoot.lt_pow_go_succ_aux0`

English:
theorem nthRoot.lt_pow_go_succ_aux0
  given: (hb : b != 0)
  proof: by
  rw [Nat.le_div_iff_mul_le (by positivity)]; rw [Nat.mul_comm]; rw [← Nat.add_mul_div_right _ _ (by positivity)]; rw [Nat.le_div_iff_mul_le (by positivity)]
  #adaptation_note /-- Prior to nightly-2026-04-06, this was
  ```
  have := (Commute.all (b : ℤ) (a - b)).pow_add_mul_le_add_pow_of_sq_nonneg
    (by positivity) (sq_nonneg _) (sq_nonneg _) (by grind) (n + 1)
  grind
  ```
  -/
  zify
  have h := pow_add_mul_le_add_pow_of_sq_nonneg (a := (b : Int)) (b := (a : Int) - b)
    (ha := by positivity) (Hsq := by positivity) (Hsq' := by positivity) (H := by omega)
    (n := n + 1)
  rw [← sub_nonneg] at h ⊢
  convert! h using 1
  rw [pow_succ]; push_cast; ring1

中文:
定理 nthRoot.lt_pow_go_succ_aux0
  条件: (hb : b != 0)
  证明: by
  rw [Nat.le_div_iff_mul_le (by positivity)]; rw [Nat.mul_comm]; rw [← Nat.add_mul_div_right _ _ (by positivity)]; rw [Nat.le_div_iff_mul_le (by positivity)]
  #adaptation_note /-- Prior to nightly-2026-04-06, this was
  ```
  have := (Commute.all (b : ℤ) (a - b)).pow_add_mul_le_add_pow_of_sq_nonneg
    (by positivity) (sq_nonneg _) (sq_nonneg _) (by grind) (n + 1)
  grind
  ```
  -/
  zify
  have h := pow_add_mul_le_add_pow_of_sq_nonneg (a := (b : Int)) (b := (a : Int) - b)
    (ha := by positivity) (Hsq := by positivity) (Hsq' := by positivity) (H := by omega)
    (n := n + 1)
  rw [← sub_nonneg] at h ⊢
  convert! h using 1
  rw [pow_succ]; push_cast; ring1
-/
private theorem nthRoot.lt_pow_go_succ_aux0 (hb : b != 0) :
    a <= ((a ^ (n + 1) / b ^ n) + n * b) / (n + 1) := by
  rw [Nat.le_div_iff_mul_le (by positivity)]; rw [Nat.mul_comm]; rw [← Nat.add_mul_div_right _ _ (by positivity)]; rw [Nat.le_div_iff_mul_le (by positivity)]
  #adaptation_note /-- Prior to nightly-2026-04-06, this was
  ```
  have := (Commute.all (b : ℤ) (a - b)).pow_add_mul_le_add_pow_of_sq_nonneg
    (by positivity) (sq_nonneg _) (sq_nonneg _) (by grind) (n + 1)
  grind
  ```
  -/
  zify
  have h := pow_add_mul_le_add_pow_of_sq_nonneg (a := (b : Int)) (b := (a : Int) - b)
    (ha := by positivity) (Hsq := by positivity) (Hsq' := by positivity) (H := by omega)
    (n := n + 1)
  rw [← sub_nonneg] at h ⊢
  convert! h using 1
  rw [pow_succ]; push_cast; ring1

/--
theorem `nthRoot.always_exists` / 定理 `nthRoot.always_exists`

English:
theorem nthRoot.always_exists
  given: (n a : Nat)
  proof: by
  have H : exists c, a < (c + 1) ^ (n + 1) := ⟨a, Nat.le_self_pow (by positivity) (a + 1)⟩
  let +nondep (eq := hc) c := Nat.find H
  refine ⟨c, ?_, hc ▸ Nat.find_spec H⟩
  cases c with
  | zero => simp
  | succ k => simpa using Nat.find_min H hc.le

中文:
定理 nthRoot.always_存在
  条件: (n a : 自然数)
  证明: by
  have H : exists c, a < (c + 1) ^ (n + 1) := ⟨a, Nat.le_self_pow (by positivity) (a + 1)⟩
  let +nondep (eq := hc) c := Nat.find H
  refine ⟨c, ?_, hc ▸ Nat.find_spec H⟩
  cases c with
  | zero => simp
  | succ k => simpa using Nat.find_min H hc.le
-/
private theorem nthRoot.always_exists (n a : Nat) :
    exists c, c ^ (n + 1) <= a ∧ a < (c + 1) ^ (n + 1) := by
  have H : exists c, a < (c + 1) ^ (n + 1) := ⟨a, Nat.le_self_pow (by positivity) (a + 1)⟩
  let +nondep (eq := hc) c := Nat.find H
  refine ⟨c, ?_, hc ▸ Nat.find_spec H⟩
  cases c with
  | zero => simp
  | succ k => simpa using Nat.find_min H hc.le

/--
theorem `nthRoot.lt_pow_go_succ_aux` / 定理 `nthRoot.lt_pow_go_succ_aux`

English:
theorem nthRoot.lt_pow_go_succ_aux
  given: (hb : b != 0)
  proof: by
  have ⟨c, hc1, hc2⟩ := nthRoot.always_exists n a
  calc a < (c + 1) ^ (n + 1) := hc2
    _ <= ((c ^ (n + 1) / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr
      exact nthRoot.lt_pow_go_succ_aux0 hb
    _ <= ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr

中文:
定理 nthRoot.lt_pow_go_succ_aux
  条件: (hb : b != 0)
  证明: by
  have ⟨c, hc1, hc2⟩ := nthRoot.always_exists n a
  calc a < (c + 1) ^ (n + 1) := hc2
    _ <= ((c ^ (n + 1) / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr
      exact nthRoot.lt_pow_go_succ_aux0 hb
    _ <= ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr

Depends on / 依赖: always_exists, lt_pow_go_succ_aux0, nthRoot, nthRoot.always_exists, nthRoot.lt_pow_go_succ_aux0
-/
theorem nthRoot.lt_pow_go_succ_aux (hb : b != 0) :
     a < ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
  have ⟨c, hc1, hc2⟩ := nthRoot.always_exists n a
  calc a < (c + 1) ^ (n + 1) := hc2
    _ <= ((c ^ (n + 1) / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr
      exact nthRoot.lt_pow_go_succ_aux0 hb
    _ <= ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr

/--
theorem `nthRoot.lt_pow_go_succ` / 定理 `nthRoot.lt_pow_go_succ`

English:
theorem nthRoot.lt_pow_go_succ
  given: (hlt : a < (guess + 1) ^ (n + 2))
  proof: by
  induction fuel generalizing guess with
  | zero => simpa [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      rcases eq_or_ne guess 0 with rfl | hguess
      · grind
· exact ih Nat.nthRoot.lt_pow_go_succ_aux hguess
    case neg =>
      assumption

中文:
定理 nthRoot.lt_pow_go_succ
  条件: (hlt : a < (guess + 1) ^ (n + 2))
  证明: by
  induction fuel generalizing guess with
  | zero => simpa [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      rcases eq_or_ne guess 0 with rfl | hguess
      · grind
· exact ih Nat.nthRoot.lt_pow_go_succ_aux hguess
    case neg =>
      assumption
-/
private theorem nthRoot.lt_pow_go_succ (hlt : a < (guess + 1) ^ (n + 2)) :
    a < (go n a fuel guess + 1) ^ (n + 2) := by
  induction fuel generalizing guess with
  | zero => simpa [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      rcases eq_or_ne guess 0 with rfl | hguess
      · grind
· exact ih Nat.nthRoot.lt_pow_go_succ_aux hguess
    case neg =>
      assumption

/--
theorem `lt_pow_nthRoot_add_one` / 定理 `lt_pow_nthRoot_add_one`

English:
theorem lt_pow_nthRoot_add_one
  given: (hn : n != 0) (a : Nat)
  statement: a < (nthRoot n a + 1) ^ n
  proof: by
  match n, hn with
  | 1, _ => simp
  | n + 2, hn =>
    simp only [nthRoot]
    apply nthRoot.lt_pow_go_succ
    exact a.lt_succ_self.trans_le (Nat.le_self_pow hn _)

@[simp]

中文:
定理 lt_pow_nthRoot_add_one
  条件: (hn : n != 0) (a : 自然数)
  结论: a < (nthRoot n a + 1) ^ n
  证明: by
  match n, hn with
  | 1, _ => simp
  | n + 2, hn =>
    simp only [nthRoot]
    apply nthRoot.lt_pow_go_succ
    exact a.lt_succ_self.trans_le (Nat.le_self_pow hn _)

@[simp]

Depends on / 依赖: Nat.le_self_pow, a.lt_succ_self.trans_le, le_self_pow, lt_pow_go_succ, lt_succ_self, nthRoot, nthRoot.lt_pow_go_succ, trans_le
-/
theorem lt_pow_nthRoot_add_one (hn : n != 0) (a : Nat) : a < (nthRoot n a + 1) ^ n := by
  match n, hn with
  | 1, _ => simp
  | n + 2, hn =>
    simp only [nthRoot]
    apply nthRoot.lt_pow_go_succ
    exact a.lt_succ_self.trans_le (Nat.le_self_pow hn _)

@[simp]
/--
theorem `le_nthRoot_iff` / 定理 `le_nthRoot_iff`

English:
theorem le_nthRoot_iff
  given: (hn : n != 0)
  statement: a <= nthRoot n b ↔ a ^ n <= b
  proof: by
  cases le_or_gt a (nthRoot n b) with
  | inl hle =>
    simp only [hle, true_iff]
    refine le_trans ?_ (pow_nthRoot_le (.inl hn))
    gcongr
  | inr hlt =>
    simp only [hlt.not_ge, false_iff, not_le]
    refine (lt_pow_nthRoot_add_one hn b).trans_le ?_
    gcongr
    assumption

@[simp]

中文:
定理 le_nthRoot_iff
  条件: (hn : n != 0)
  结论: a <= nthRoot n b ↔ a ^ n <= b
  证明: by
  cases le_or_gt a (nthRoot n b) with
  | inl hle =>
    simp only [hle, true_iff]
    refine le_trans ?_ (pow_nthRoot_le (.inl hn))
    gcongr
  | inr hlt =>
    simp only [hlt.not_ge, false_iff, not_le]
    refine (lt_pow_nthRoot_add_one hn b).trans_le ?_
    gcongr
    assumption

@[simp]

Depends on / 依赖: false_iff, hlt.not_ge, le_or_gt, le_trans, lt_pow_nthRoot_add_one, not_ge, not_le, nthRoot, pow_nthRoot_le, trans_le, true_iff
-/
theorem le_nthRoot_iff (hn : n != 0) : a <= nthRoot n b ↔ a ^ n <= b := by
  cases le_or_gt a (nthRoot n b) with
  | inl hle =>
    simp only [hle, true_iff]
    refine le_trans ?_ (pow_nthRoot_le (.inl hn))
    gcongr
  | inr hlt =>
    simp only [hlt.not_ge, false_iff, not_le]
    refine (lt_pow_nthRoot_add_one hn b).trans_le ?_
    gcongr
    assumption

@[simp]
/--
theorem `nthRoot_lt_iff` / 定理 `nthRoot_lt_iff`

English:
theorem nthRoot_lt_iff
  given: (hn : n != 0)
  statement: nthRoot n a < b ↔ a < b ^ n
  proof: by
  simp only [← not_le, le_nthRoot_iff hn]

@[simp]

中文:
定理 nthRoot_lt_iff
  条件: (hn : n != 0)
  结论: nthRoot n a < b ↔ a < b ^ n
  证明: by
  simp only [← not_le, le_nthRoot_iff hn]

@[simp]

Depends on / 依赖: le_nthRoot_iff, not_le
-/
theorem nthRoot_lt_iff (hn : n != 0) : nthRoot n a < b ↔ a < b ^ n := by
  simp only [← not_le, le_nthRoot_iff hn]

@[simp]
/--
theorem `nthRoot_pow` / 定理 `nthRoot_pow`

English:
theorem nthRoot_pow
  given: (hn : n != 0) (a : Nat)
  statement: nthRoot n (a ^ n) = a
  proof: by
  refine eq_of_forall_le_iff fun b => ?_
  rw [le_nthRoot_iff hn]
  exact (Nat.pow_left_strictMono hn).le_iff_le

中文:
定理 nthRoot_pow
  条件: (hn : n != 0) (a : 自然数)
  结论: nthRoot n (a ^ n) = a
  证明: by
  refine eq_of_forall_le_iff fun b => ?_
  rw [le_nthRoot_iff hn]
  exact (Nat.pow_left_strictMono hn).le_iff_le

Depends on / 依赖: Nat.pow_left_strictMono, eq_of_forall_le_iff, le_iff_le, le_nthRoot_iff, pow_left_strictMono
-/
theorem nthRoot_pow (hn : n != 0) (a : Nat) : nthRoot n (a ^ n) = a := by
  refine eq_of_forall_le_iff fun b => ?_
  rw [le_nthRoot_iff hn]
  exact (Nat.pow_left_strictMono hn).le_iff_le

/--
theorem `nthRoot_eq_of_le_of_lt` / 定理 `nthRoot_eq_of_le_of_lt`

English:
theorem nthRoot_eq_of_le_of_lt
  given: (h₁ : a ^ n <= b) (h₂ : b < (a + 1) ^ n)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · grind
  simp only [← le_nthRoot_iff hn, ← nthRoot_lt_iff hn] at h₁ h₂
  grind

中文:
定理 nthRoot_eq_of_le_of_lt
  条件: (h₁ : a ^ n <= b) (h₂ : b < (a + 1) ^ n)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · grind
  simp only [← le_nthRoot_iff hn, ← nthRoot_lt_iff hn] at h₁ h₂
  grind

Depends on / 依赖: eq_or_ne, le_nthRoot_iff, nthRoot_lt_iff
-/
theorem nthRoot_eq_of_le_of_lt (h₁ : a ^ n <= b) (h₂ : b < (a + 1) ^ n) :
    nthRoot n b = a := by
  rcases eq_or_ne n 0 with rfl | hn
  · grind
  simp only [← le_nthRoot_iff hn, ← nthRoot_lt_iff hn] at h₁ h₂
  grind

/--
theorem `exists_pow_eq_iff'` / 定理 `exists_pow_eq_iff'`

English:
theorem exists_pow_eq_iff'
  given: (hn : n != 0)
  statement: (exists x, x ^ n = a) ↔ (nthRoot n a) ^ n = a
  proof: by
  constructor
  · rintro ⟨x, rfl⟩
    rw [nthRoot_pow hn]
  · grind

中文:
定理 存在_pow_eq_iff'
  条件: (hn : n != 0)
  结论: (存在 x, x ^ n = a) ↔ (nthRoot n a) ^ n = a
  证明: by
  constructor
  · rintro ⟨x, rfl⟩
    rw [nthRoot_pow hn]
  · grind

Depends on / 依赖: nthRoot_pow
-/
theorem exists_pow_eq_iff' (hn : n != 0) : (exists x, x ^ n = a) ↔ (nthRoot n a) ^ n = a := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [nthRoot_pow hn]
  · grind

/--
theorem `exists_pow_eq_iff` / 定理 `exists_pow_eq_iff`

English:
theorem exists_pow_eq_iff
  proof: by
  rcases eq_or_ne n 0 with rfl | _ <;> grind [exists_pow_eq_iff']

中文:
定理 存在_pow_eq_iff
  证明: by
  rcases eq_or_ne n 0 with rfl | _ <;> grind [exists_pow_eq_iff']

Depends on / 依赖: eq_or_ne, exists_pow_eq_iff
-/
theorem exists_pow_eq_iff :
    (exists x, x ^ n = a) ↔ ((n = 0 ∧ a = 1) ∨ (n != 0 ∧ (nthRoot n a) ^ n = a)) := by
  rcases eq_or_ne n 0 with rfl | _ <;> grind [exists_pow_eq_iff']

/--
Instance `instDecidableExistsPowEq` / 实例 `instDecidableExistsPowEq`

English:
instance instDecidableExistsPowEq
  signature: : Decidable (exists x, x ^ n = a)
  body: decidable_of_iff' _ exists_pow_eq_iff

中文:
实例 instDecidableExistsPowEq
  签名: : 可判定 (存在 x, x ^ n = a)
  定义体: decidable_of_iff' _ exists_pow_eq_iff

Depends on / 依赖: decidable_of_iff, exists_pow_eq_iff
-/
instance instDecidableExistsPowEq : Decidable (exists x, x ^ n = a) :=
  decidable_of_iff' _ exists_pow_eq_iff

end Nat
