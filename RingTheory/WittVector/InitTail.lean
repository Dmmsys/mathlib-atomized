/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.IsPoly

/-!

# `init` and `tail`

Given a Witt vector `x`, we are sometimes interested
in its components before and after an index `n`.
This file defines those operations, proves that `init` is polynomial,
and shows how that polynomial interacts with `MvPolynomial.bind₁`.

## Main declarations

* `WittVector.init n x`: the first `n` coefficients of `x`, as a Witt vector. All coefficients at
  indices ≥ `n` are 0.
* `WittVector.tail n x`: the complementary part to `init`. All coefficients at indices < `n` are 0,
  otherwise they are the same as in `x`.
* `WittVector.coeff_add_of_disjoint`: if `x` and `y` are Witt vectors such that for every `n`
  the `n`-th coefficient of `x` or of `y` is `0`, then the coefficients of `x + y`
  are just `x.coeff n + y.coeff n`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/

@[expose] public section


variable {p : Nat} (n : Nat) {R : Type*} [CommRing R]

-- type as `\bbW`
local notation "𝕎" => WittVector p


namespace WittVector

open MvPolynomial

noncomputable section

section

open scoped Classical in
/--
Definition of `select` / `select` 的定义

English:
definition select
  signature: (P : Nat -> Prop) (x : 𝕎 R)
  body: mk p fun n => if P n then x.coeff n else 0

中文:
定义 select
  签名: (P : 自然数 -> 命题) (x : 𝕎 R)
  定义体: mk p fun n => if P n then x.coeff n else 0

Depends on / 依赖: x.coeff
-/
def select (P : Nat -> Prop) (x : 𝕎 R) : 𝕎 R :=
  mk p fun n => if P n then x.coeff n else 0

section Select

variable (P : Nat -> Prop)

open scoped Classical in
/--
Definition of `selectPoly` / `selectPoly` 的定义

English:
definition selectPoly
  signature: (n : Nat)
  body: if P n then X n else 0

中文:
定义 selectPoly
  签名: (n : 自然数)
  定义体: if P n then X n else 0
-/
def selectPoly (n : Nat) : MvPolynomial Nat Int :=
  if P n then X n else 0

/--
theorem `coeff_select` / 定理 `coeff_select`

English:
theorem coeff_select
  given: (x : 𝕎 R) (n : Nat)
  proof: by
  dsimp [select, selectPoly]
  split_ifs with hi <;> simp

中文:
定理 coeff_select
  条件: (x : 𝕎 R) (n : 自然数)
  证明: by
  dsimp [select, selectPoly]
  split_ifs with hi <;> simp

Depends on / 依赖: select, selectPoly, split_ifs
-/
theorem coeff_select (x : 𝕎 R) (n : Nat) :
    (select P x).coeff n = aeval x.coeff (selectPoly P n) := by
  dsimp [select, selectPoly]
  split_ifs with hi <;> simp

/--
Instance `select_isPoly` / 实例 `select_isPoly`

English:
instance select_isPoly
  signature: {P : Nat -> Prop}
  body: by
  use selectPoly P
  rintro R _Rcr x
  funext i
  apply coeff_select

中文:
实例 select_isPoly
  签名: {P : 自然数 -> 命题}
  定义体: by
  use selectPoly P
  rintro R _Rcr x
  funext i
  apply coeff_select

Depends on / 依赖: _Rcr, coeff_select, selectPoly
-/
instance select_isPoly {P : Nat -> Prop} : IsPoly p fun _ _ x => select P x := by
  use selectPoly P
  rintro R _Rcr x
  funext i
  apply coeff_select

variable [hp : Fact p.Prime]

/--
theorem `select_add_select_not` / 定理 `select_add_select_not`

English:
theorem select_add_select_not
  statement: forall x : 𝕎 R, select P x + select (fun i => ¬P i) x = x
  proof: by
  -- Porting note: TC search was insufficient to find this instance, even though all required
  -- instances exist. See zulip: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/WittVector.20saga/near/370073526]
  have : IsPoly p fun {R} [CommRing R] x => select P x + select (

中文:
定理 select_add_select_not
  结论: 对任意 x : 𝕎 R, select P x + select (fun i => ¬P i) x = x
  证明: by
  -- Porting note: TC search was insufficient to find this instance, even though all required
  -- instances exist. See zulip: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/WittVector.20saga/near/370073526]
  have : IsPoly p fun {R} [CommRing R] x => select P x + select (
-/
theorem select_add_select_not : forall x : 𝕎 R, select P x + select (fun i => ¬P i) x = x := by
  -- Porting note: TC search was insufficient to find this instance, even though all required
  -- instances exist. See zulip: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/WittVector.20saga/near/370073526]
  have : IsPoly p fun {R} [CommRing R] x => select P x + select (fun i => ¬P i) x :=
    IsPoly₂.diag (hf := IsPoly₂.comp)
  ghost_calc x
  intro n
  simp only [map_add]
  suffices
    (bind₁ (selectPoly P)) (wittPolynomial p Int n) +
        (bind₁ (selectPoly fun i => ¬P i)) (wittPolynomial p Int n) =
      wittPolynomial p Int n by
    apply_fun aeval x.coeff at this
    simpa only [map_add, aeval_bind₁, ← coeff_select]
  simp only [wittPolynomial_eq_sum_C_mul_X_pow, selectPoly, map_sum, map_pow, map_mul,
    bind₁_X_right, bind₁_C_right, ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  refine fun m _ => mul_eq_mul_left_iff.mpr (Or.inl ?_)
  rw [ite_pow]; rw [zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  by_cases Pm : P m
  · rw [if_pos Pm, if_neg <| not_not_intro Pm, zero_pow Fin.pos'.ne', add_zero]
  · rwa [if_neg Pm, if_pos, zero_add]

/--
theorem `coeff_add_of_disjoint` / 定理 `coeff_add_of_disjoint`

English:
theorem coeff_add_of_disjoint
  given: (x y : 𝕎 R) (h : forall n, x.coeff n = 0 ∨ y.coeff n = 0)
  proof: by
  let P : Nat -> Prop := fun n => y.coeff n = 0
  have : DecidablePred P := Classical.decPred P
  set z := mk p fun n => if P n then x.coeff n else y.coeff n
  have hx : select P z = x := by
    ext1 n; rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · rfl
    · rw [(h n).resolve_right 

中文:
定理 coeff_add_of_disjoint
  条件: (x y : 𝕎 R) (h : 对任意 n, x.coeff n = 0 ∨ y.coeff n = 0)
  证明: by
  let P : Nat -> Prop := fun n => y.coeff n = 0
  have : DecidablePred P := Classical.decPred P
  set z := mk p fun n => if P n then x.coeff n else y.coeff n
  have hx : select P z = x := by
    ext1 n; rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · rfl
    · rw [(h n).resolve_right 

Depends on / 依赖: Classical, Classical.decPred, DecidablePred, coeff_mk, decPred, hn.symm, resolve_right, select, select_add_select_not, split_ifs, x.coeff, y.coeff, z.coeff
-/
theorem coeff_add_of_disjoint (x y : 𝕎 R) (h : forall n, x.coeff n = 0 ∨ y.coeff n = 0) :
    (x + y).coeff n = x.coeff n + y.coeff n := by
  let P : Nat -> Prop := fun n => y.coeff n = 0
  have : DecidablePred P := Classical.decPred P
  set z := mk p fun n => if P n then x.coeff n else y.coeff n
  have hx : select P z = x := by
    ext1 n; rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · rfl
    · rw [(h n).resolve_right hn]
  have hy : select (fun i => ¬P i) z = y := by
    ext1 n; rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · exact hn.symm
    · rfl
  calc
    (x + y).coeff n = z.coeff n := by rw [← hx, ← hy, select_add_select_not P z]
    _ = x.coeff n + y.coeff n := by
      simp only [z, mk.eq_1]
      split_ifs with y0
      · rw [y0, add_zero]
      · rw [h n |>.resolve_right y0, zero_add]

end Select

variable [Fact p.Prime]

/--
Definition of `init` / `init` 的定义

English:
definition init
  signature: (n : Nat)
  body: select fun i => i < n

中文:
定义 init
  签名: (n : 自然数)
  定义体: select fun i => i < n

Depends on / 依赖: select
-/
def init (n : Nat) : 𝕎 R -> 𝕎 R :=
  select fun i => i < n

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (n : Nat)
  body: select fun i => n <= i

@[simp]

中文:
定义 tail
  签名: (n : 自然数)
  定义体: select fun i => n <= i

@[simp]

Depends on / 依赖: select
-/
def tail (n : Nat) : 𝕎 R -> 𝕎 R :=
  select fun i => n <= i

@[simp]
/--
theorem `init_add_tail` / 定理 `init_add_tail`

English:
theorem init_add_tail
  given: (x : 𝕎 R) (n : Nat)
  statement: init n x + tail n x = x
  proof: by
  simp only [init, tail, ← not_lt, select_add_select_not]

中文:
定理 init_add_tail
  条件: (x : 𝕎 R) (n : 自然数)
  结论: init n x + tail n x = x
  证明: by
  simp only [init, tail, ← not_lt, select_add_select_not]

Depends on / 依赖: not_lt, select_add_select_not
-/
theorem init_add_tail (x : 𝕎 R) (n : Nat) : init n x + tail n x = x := by
  simp only [init, tail, ← not_lt, select_add_select_not]

end

/--
`init_ring` is an auxiliary tactic that discharges goals factoring `init` over ring operations.
-/
syntax (name := initRing) "init_ring" (" using " term)? : tactic

-- Porting note: this tactic requires that we turn hygiene off (note the free `n`).
-- TODO: make this tactic hygienic.
open Lean Elab Elab.Tactic in
elab_rules : tactic
| `(tactic| init_ring $[ using $a:term]?) => withMainContext set_option hygiene false in do
evalTactic ← `(tactic|(
    rw [WittVector.ext_iff]
    intro i
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    split_ifs with hi <;> try {rfl}
    ))
  if let some e := a then
evalTactic ← `(tactic|(
      simp only [WittVector.add_coeff, WittVector.mul_coeff, WittVector.neg_coeff,
        WittVector.sub_coeff, WittVector.nsmul_coeff, WittVector.zsmul_coeff, WittVector.pow_coeff]
      apply MvPolynomial.eval₂Hom_congr' (RingHom.ext_int _ _) _ rfl
      rintro ⟨b, k⟩ h -
replace h := e:term p _ h
      simp only [Finset.mem_range, Finset.mem_product, true_and, Finset.mem_univ] at h
      have hk : k < n := by lia
      fin_cases b <;> simp only [Function.uncurry, Matrix.cons_val_zero, Matrix.head_cons,
        WittVector.coeff_mk, Matrix.cons_val_one, WittVector.mk, Fin.mk_zero, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        hk, if_true]
    ))

@[simp]
/--
theorem `init_init` / 定理 `init_init`

English:
theorem init_init
  given: (x : 𝕎 R) (n : Nat)
  statement: init n (init n x) = init n x
  proof: by
  init_ring

中文:
定理 init_init
  条件: (x : 𝕎 R) (n : 自然数)
  结论: init n (init n x) = init n x
  证明: by
  init_ring

Depends on / 依赖: init_ring
-/
theorem init_init (x : 𝕎 R) (n : Nat) : init n (init n x) = init n x := by
  init_ring

section
variable [Fact p.Prime]

/--
theorem `init_add` / 定理 `init_add`

English:
theorem init_add
  given: (x y : 𝕎 R) (n : Nat)
  statement: init n (x + y) = init n (init n x + init n y)
  proof: by
  init_ring using wittAdd_vars

中文:
定理 init_add
  条件: (x y : 𝕎 R) (n : 自然数)
  结论: init n (x + y) = init n (init n x + init n y)
  证明: by
  init_ring using wittAdd_vars

Depends on / 依赖: init_ring, wittAdd_vars
-/
theorem init_add (x y : 𝕎 R) (n : Nat) : init n (x + y) = init n (init n x + init n y) := by
  init_ring using wittAdd_vars

/--
theorem `init_mul` / 定理 `init_mul`

English:
theorem init_mul
  given: (x y : 𝕎 R) (n : Nat)
  statement: init n (x * y) = init n (init n x * init n y)
  proof: by
  init_ring using wittMul_vars

中文:
定理 init_mul
  条件: (x y : 𝕎 R) (n : 自然数)
  结论: init n (x * y) = init n (init n x * init n y)
  证明: by
  init_ring using wittMul_vars

Depends on / 依赖: init_ring, wittMul_vars
-/
theorem init_mul (x y : 𝕎 R) (n : Nat) : init n (x * y) = init n (init n x * init n y) := by
  init_ring using wittMul_vars

/--
theorem `init_neg` / 定理 `init_neg`

English:
theorem init_neg
  given: (x : 𝕎 R) (n : Nat)
  statement: init n (-x) = init n (-init n x)
  proof: by
  init_ring using wittNeg_vars

中文:
定理 init_neg
  条件: (x : 𝕎 R) (n : 自然数)
  结论: init n (-x) = init n (-init n x)
  证明: by
  init_ring using wittNeg_vars

Depends on / 依赖: init_ring, wittNeg_vars
-/
theorem init_neg (x : 𝕎 R) (n : Nat) : init n (-x) = init n (-init n x) := by
  init_ring using wittNeg_vars

/--
theorem `init_sub` / 定理 `init_sub`

English:
theorem init_sub
  given: (x y : 𝕎 R) (n : Nat)
  statement: init n (x - y) = init n (init n x - init n y)
  proof: by
  init_ring using wittSub_vars

中文:
定理 init_sub
  条件: (x y : 𝕎 R) (n : 自然数)
  结论: init n (x - y) = init n (init n x - init n y)
  证明: by
  init_ring using wittSub_vars

Depends on / 依赖: init_ring, wittSub_vars
-/
theorem init_sub (x y : 𝕎 R) (n : Nat) : init n (x - y) = init n (init n x - init n y) := by
  init_ring using wittSub_vars

/--
theorem `init_nsmul` / 定理 `init_nsmul`

English:
theorem init_nsmul
  given: (m : Nat) (x : 𝕎 R) (n : Nat)
  statement: init n (m • x) = init n (m • init n x)
  proof: by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittNSMul_vars p m n

中文:
定理 init_nsmul
  条件: (m : 自然数) (x : 𝕎 R) (n : 自然数)
  结论: init n (m • x) = init n (m • init n x)
  证明: by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittNSMul_vars p m n

Depends on / 依赖: Nat.Prime, init_ring, wittNSMul_vars
-/
theorem init_nsmul (m : Nat) (x : 𝕎 R) (n : Nat) : init n (m • x) = init n (m • init n x) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittNSMul_vars p m n

/--
theorem `init_zsmul` / 定理 `init_zsmul`

English:
theorem init_zsmul
  given: (m : Int) (x : 𝕎 R) (n : Nat)
  statement: init n (m • x) = init n (m • init n x)
  proof: by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittZSMul_vars p m n

中文:
定理 init_zsmul
  条件: (m : 整数) (x : 𝕎 R) (n : 自然数)
  结论: init n (m • x) = init n (m • init n x)
  证明: by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittZSMul_vars p m n

Depends on / 依赖: Nat.Prime, init_ring, wittZSMul_vars
-/
theorem init_zsmul (m : Int) (x : 𝕎 R) (n : Nat) : init n (m • x) = init n (m • init n x) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittZSMul_vars p m n

/--
theorem `init_pow` / 定理 `init_pow`

English:
theorem init_pow
  given: (m : Nat) (x : 𝕎 R) (n : Nat)
  statement: init n (x ^ m) = init n (init n x ^ m)
  proof: by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittPow_vars p m n

中文:
定理 init_pow
  条件: (m : 自然数) (x : 𝕎 R) (n : 自然数)
  结论: init n (x ^ m) = init n (init n x ^ m)
  证明: by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittPow_vars p m n

Depends on / 依赖: Nat.Prime, init_ring, wittPow_vars
-/
theorem init_pow (m : Nat) (x : 𝕎 R) (n : Nat) : init n (x ^ m) = init n (init n x ^ m) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => wittPow_vars p m n

end
section

variable (p)

/--
theorem `init_isPoly` / 定理 `init_isPoly`

English:
theorem init_isPoly
  given: (n : Nat)
  statement: IsPoly p fun _ _ => init n
  proof: select_isPoly (P := fun i => i < n)

中文:
定理 init_isPoly
  条件: (n : 自然数)
  结论: 是Poly p fun _ _ => init n
  证明: select_isPoly (P := fun i => i < n)

Depends on / 依赖: select_isPoly
-/
theorem init_isPoly (n : Nat) : IsPoly p fun _ _ => init n :=
  select_isPoly (P := fun i => i < n)

end

end

end WittVector
