/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Monomial.Predicates

/-!

# Computing limits of monomials

In this file we define the `Monomial` structure, representing monomials in a basis, i.e.
`coef * b₁ ^ e₁ * ... * bₙ ^ eₙ` where `[b₁, ..., bₙ]` is a well-formed basis.

In the tactic implementation, we use `Monomial` to connect multiseries with real functions.
In this file we show how to find a limit of `Monomial` and how to asymptotically compare two
`Monomial`s.

## Main definitions

* `Monomial`: type to represent monomials.
* `UnitMonomial.toFun`/`Monomial.toFun`: converts structures to real functions.
* `UnitMonomial.toLogFun_isEquivalent_of_nonzero_head`: `log m.toFun` is asymptotically equivalent
  to its first summand - `m[0] • log basis[0]` if `m[0] ≠ 0`. Using this theorem we can prove that
  the asymptotic behaviour of the monomials is determined by its first non-zero exponent.
* `toFun_tendsto_top_of_FirstNonzeroIsPos` and its variants are used to infer the limit of
  `t.toFun` from `FirstNonzeroIsPos`/`FirstNonzeroIsNeg`/`AllZero`.
* `IsLittleO_of_lt_exps` and its variants are used to asymptotically compare two monomials.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Asymptotics Filter Topology Real

/--
Definition of `Monomial` / `Monomial` 的定义

English:
structure Monomial
  parameters: where
  axioms and operations (2):
    - coef : Real
    - unit : UnitMonomial

中文:
结构 单项式
  参数: where
  公理与运算 (2 个):
    - coef : 实数
    - unit : UnitMonomial
-/
structure Monomial where
  /-- Real coefficient of the monomial. -/
  coef : Real
  /-- Unit part of the monomial. -/
  unit : UnitMonomial

namespace UnitMonomial

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: (m : UnitMonomial) (basis : Basis)
  body: fun x => (m.zipWith (fun exp b => (b x)^exp) basis).prod

中文:
定义 toFun
  签名: (m : UnitMonomial) (basis : 基)
  定义体: fun x => (m.zipWith (fun exp b => (b x)^exp) basis).prod

Depends on / 依赖: m.zipWith, zipWith
-/
noncomputable def toFun (m : UnitMonomial) (basis : Basis) : Real -> Real :=
  fun x => (m.zipWith (fun exp b => (b x)^exp) basis).prod

/--
Definition of `toLogFun` / `toLogFun` 的定义

English:
definition toLogFun
  signature: (m : UnitMonomial) (basis : Basis)
  body: fun x => (m.zipWith (fun exp b => exp * log (b x)) basis).sum

@[simp]

中文:
定义 toLogFun
  签名: (m : UnitMonomial) (basis : 基)
  定义体: fun x => (m.zipWith (fun exp b => exp * log (b x)) basis).sum

@[simp]

Depends on / 依赖: T1Space, m.zipWith, toT1Space, zipWith
-/
noncomputable def toLogFun (m : UnitMonomial) (basis : Basis) : Real -> Real :=
  fun x => (m.zipWith (fun exp b => exp * log (b x)) basis).sum

@[simp]
/--
theorem `toFun_nil` / 定理 `toFun_nil`

English:
theorem toFun_nil
  given: (basis : Basis)
  statement: (UnitMonomial.toFun [] basis) = 1
  proof: by
  ext x
  simp [toFun]

@[simp]

中文:
定理 toFun_nil
  条件: (basis : 基)
  结论: (UnitMonomial.toFun [] basis) = 1
  证明: by
  ext x
  simp [toFun]

@[simp]
-/
theorem toFun_nil (basis : Basis) : (UnitMonomial.toFun [] basis) = 1 := by
  ext x
  simp [toFun]

@[simp]
/--
theorem `toFun_nil_basis` / 定理 `toFun_nil_basis`

English:
theorem toFun_nil_basis
  given: (m : UnitMonomial)
  statement: (UnitMonomial.toFun m []) = 1
  proof: by
  ext x
  simp [toFun]

@[simp]

中文:
定理 toFun_nil_basis
  条件: (m : UnitMonomial)
  结论: (UnitMonomial.toFun m []) = 1
  证明: by
  ext x
  simp [toFun]

@[simp]
-/
theorem toFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toFun m []) = 1 := by
  ext x
  simp [toFun]

@[simp]
/--
theorem `toFun_cons` / 定理 `toFun_cons`

English:
theorem toFun_cons
  given: (exp : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis)
  proof: by
  ext x
  simp [toFun]

@[simp]

中文:
定理 toFun_cons
  条件: (exp : 实数) (tl : UnitMonomial) (basis_hd : 实数 -> 实数) (basis_tl : 基)
  证明: by
  ext x
  simp [toFun]

@[simp]
-/
theorem toFun_cons (exp : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) :
    (UnitMonomial.toFun (exp :: tl) (basis_hd :: basis_tl)) =
    basis_hd ^ exp * tl.toFun basis_tl := by
  ext x
  simp [toFun]

@[simp]
/--
theorem `toLogFun_nil` / 定理 `toLogFun_nil`

English:
theorem toLogFun_nil
  given: (basis : Basis)
  statement: (UnitMonomial.toLogFun [] basis) = 0
  proof: by
  ext x
  simp [toLogFun]

@[simp]

中文:
定理 toLogFun_nil
  条件: (basis : 基)
  结论: (UnitMonomial.toLogFun [] basis) = 0
  证明: by
  ext x
  simp [toLogFun]

@[simp]

Depends on / 依赖: toLogFun
-/
theorem toLogFun_nil (basis : Basis) : (UnitMonomial.toLogFun [] basis) = 0 := by
  ext x
  simp [toLogFun]

@[simp]
/--
theorem `toLogFun_nil_basis` / 定理 `toLogFun_nil_basis`

English:
theorem toLogFun_nil_basis
  given: (m : UnitMonomial)
  statement: (UnitMonomial.toLogFun m []) = 0
  proof: by
  ext x
  simp [toLogFun]

@[simp]

中文:
定理 toLogFun_nil_basis
  条件: (m : UnitMonomial)
  结论: (UnitMonomial.toLogFun m []) = 0
  证明: by
  ext x
  simp [toLogFun]

@[simp]

Depends on / 依赖: toLogFun
-/
theorem toLogFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toLogFun m []) = 0 := by
  ext x
  simp [toLogFun]

@[simp]
/--
theorem `toLogFun_cons` / 定理 `toLogFun_cons`

English:
theorem toLogFun_cons
  given: (exp : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis)
  proof: by
  ext x
  simp [toLogFun]

中文:
定理 toLogFun_cons
  条件: (exp : 实数) (tl : UnitMonomial) (basis_hd : 实数 -> 实数) (basis_tl : 基)
  证明: by
  ext x
  simp [toLogFun]

Depends on / 依赖: toLogFun
-/
theorem toLogFun_cons (exp : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) :
    (UnitMonomial.toLogFun (exp :: tl) (basis_hd :: basis_tl)) =
    exp • Real.log ∘ basis_hd + UnitMonomial.toLogFun tl basis_tl := by
  ext x
  simp [toLogFun]

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: (m1 m2 : UnitMonomial)
  body: m1.zipWith (· + ·) m2

中文:
定义 mul
  签名: (m1 m2 : UnitMonomial)
  定义体: m1.zipWith (· + ·) m2

Depends on / 依赖: m1.zipWith, zipWith
-/
noncomputable def mul (m1 m2 : UnitMonomial) : UnitMonomial :=
  m1.zipWith (· + ·) m2

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (m : UnitMonomial)
  body: m.map (-·)

中文:
定义 inv
  签名: (m : UnitMonomial)
  定义体: m.map (-·)

Depends on / 依赖: m.map
-/
noncomputable def inv (m : UnitMonomial) : UnitMonomial :=
  m.map (-·)

/--
theorem `mul_length` / 定理 `mul_length`

English:
theorem mul_length
  given: {m1 m2 : UnitMonomial} (h : m1.length = m2.length)
  proof: by
  simp [mul, h]

@[simp]

中文:
定理 mul_length
  条件: {m1 m2 : UnitMonomial} (h : m1.length = m2.length)
  证明: by
  simp [mul, h]

@[simp]
-/
theorem mul_length {m1 m2 : UnitMonomial} (h : m1.length = m2.length) :
    (mul m1 m2).length = m1.length := by
  simp [mul, h]

@[simp]
/--
theorem `inv_length` / 定理 `inv_length`

English:
theorem inv_length
  given: (m : UnitMonomial)
  proof: by
  simp [inv]

中文:
定理 inv_length
  条件: (m : UnitMonomial)
  证明: by
  simp [inv]
-/
theorem inv_length (m : UnitMonomial) :
    (inv m).length = m.length := by
  simp [inv]

/--
theorem `mul_toFun` / 定理 `mul_toFun`

English:
theorem mul_toFun
  statement: {m1 m2 : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: by
  apply h_basis.eventually_pos.mono
  intro x h_pos
  simp only [toFun, mul, Pi.mul_apply]
  induction m1 generalizing m2 basis with
  | nil =>
    symm at h_length
    simp_all
  | cons exp1 exps1 ih =>
    cases m2 with
    | nil => simp at h_length
    | cons exp2 exps2 =>
    cases basis with

中文:
定理 mul_toFun
  结论: {m1 m2 : UnitMonomial} {basis : 基} (h_basis : WellFormedBasis basis)
  证明: by
  apply h_basis.eventually_pos.mono
  intro x h_pos
  simp only [toFun, mul, Pi.mul_apply]
  induction m1 generalizing m2 basis with
  | nil =>
    symm at h_length
    simp_all
  | cons exp1 exps1 ih =>
    cases m2 with
    | nil => simp at h_length
    | cons exp2 exps2 =>
    cases basis with

Depends on / 依赖: List.prod_cons, List.zipWith_cons_cons, Pi.mul_apply, basis_hd, basis_tl, eventually_pos, exps1.length, exps2.length, generalizing, h_basis, h_basis.eventually_pos.mono, h_length, h_po, h_pos, length, mul_apply, prod_cons, zipWith_cons_cons
-/
theorem mul_toFun {m1 m2 : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : m1.length = m2.length) :
    (m1.mul m2).toFun basis =ᶠ[atTop] m1.toFun basis * m2.toFun basis := by
  apply h_basis.eventually_pos.mono
  intro x h_pos
  simp only [toFun, mul, Pi.mul_apply]
  induction m1 generalizing m2 basis with
  | nil =>
    symm at h_length
    simp_all
  | cons exp1 exps1 ih =>
    cases m2 with
    | nil => simp at h_length
    | cons exp2 exps2 =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [List.zipWith_cons_cons, List.prod_cons] at ih ⊢
      have h1 : exps1.length = exps2.length := by grind
      have h2 : forall f in basis_tl, 0 < f x := by grind
      have h3 : 0 < basis_hd x := h_pos _ (by simp)
      rw [ih h_basis.tail h1 h2]; rw [Real.rpow_add h3]
      grind

/--
theorem `inv_toFun` / 定理 `inv_toFun`

English:
theorem inv_toFun
  given: {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: by
  eta_expand
  simp only [toFun, inv, Pi.inv_apply]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      apply ((h_basis.head_eventually_pos).and (ih (h_basis.tail))).mono
      intro x ⟨h_pos, i

中文:
定理 inv_toFun
  条件: {m : UnitMonomial} {basis : 基} (h_basis : WellFormedBasis basis)
  证明: by
  eta_expand
  simp only [toFun, inv, Pi.inv_apply]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      apply ((h_basis.head_eventually_pos).and (ih (h_basis.tail))).mono
      intro x ⟨h_pos, i

Depends on / 依赖: List.map_cons, List.prod_cons, List.zipWith_cons_cons, Pi.inv_apply, Real.rpow_neg, basis_hd, basis_tl, eta_expand, generalizing, h_basis, h_basis.head_eventually_pos, h_basis.tail, h_pos, h_pos.le, head_eventually_pos, inv_apply, map_cons, mul_inv_rev, prod_cons, rpow_neg
-/
theorem inv_toFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    m.inv.toFun basis =ᶠ[atTop] (m.toFun basis)⁻¹ := by
  eta_expand
  simp only [toFun, inv, Pi.inv_apply]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      apply ((h_basis.head_eventually_pos).and (ih (h_basis.tail))).mono
      intro x ⟨h_pos, ih⟩
      simp only [List.map_cons, List.zipWith_cons_cons, List.prod_cons, mul_inv_rev]
      grind [Real.rpow_neg h_pos.le]

/--
theorem `majorized_tail_toFun_head` / 定理 `majorized_tail_toFun_head`

English:
theorem majorized_tail_toFun_head
  statement: {m : UnitMonomial} {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  induction m generalizing basis_hd basis_tl with
  | nil =>
    simp only [toFun_nil]
    exact Majorized.const (h_basis.tendsto_atTop (by simp))
  | cons hd tl ih =>
    cases basis_tl with
    | nil => simp at h_length
    | cons basis_tl_hd basis_tl_tl =>
      simp only [List.length_cons, Na

中文:
定理 majorized_tail_toFun_head
  结论: {m : UnitMonomial} {basis_hd : 实数 -> 实数} {basis_tl : 基}
  证明: by
  induction m generalizing basis_hd basis_tl with
  | nil =>
    simp only [toFun_nil]
    exact Majorized.const (h_basis.tendsto_atTop (by simp))
  | cons hd tl ih =>
    cases basis_tl with
    | nil => simp at h_length
    | cons basis_tl_hd basis_tl_tl =>
      simp only [List.length_cons, Na

Depends on / 依赖: List.length_cons, Majorized, Majorized.const, Majorized.mul, Nat.add_right_cancel_iff, add_right_cancel_iff, add_zero, basis_hd, basis_tl, basis_tl_hd, basis_tl_tl, generalizing, h_basis, h_basis.head_eventually_pos, h_basis.tail, h_basis.tail_pow_majorized_head, h_basis.tendsto_atTop, h_exp, h_length, head_eventually_pos
-/
theorem majorized_tail_toFun_head {m : UnitMonomial} {basis_hd : Real -> Real} {basis_tl : Basis}
    (h_length : m.length = basis_tl.length)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    Majorized (m.toFun basis_tl) basis_hd 0 := by
  induction m generalizing basis_hd basis_tl with
  | nil =>
    simp only [toFun_nil]
    exact Majorized.const (h_basis.tendsto_atTop (by simp))
  | cons hd tl ih =>
    cases basis_tl with
    | nil => simp at h_length
    | cons basis_tl_hd basis_tl_tl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff, toFun_cons] at h_length ⊢
      rw [← add_zero 0]
      apply Majorized.mul (h_basis.tail_pow_majorized_head (by simp) _) _
        h_basis.head_eventually_pos
      exact fun exp h_exp =>
(ih h_length h_basis.tail 1 (by simp)).trans
        h_basis.tail_pow_majorized_head (by simp) 1 exp h_exp

/--
theorem `toFun_pos` / 定理 `toFun_pos`

English:
theorem toFun_pos
  statement: {m : UnitMonomial} {basis : Basis}
  proof: by
  apply h_basis.eventually_pos.mono
  intro x hx
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [toFun, List.zipWith_cons_cons, List.prod_cons]
      apply mul_pos (Real.rpow_pos_

中文:
定理 toFun_pos
  结论: {m : UnitMonomial} {basis : 基}
  证明: by
  apply h_basis.eventually_pos.mono
  intro x hx
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [toFun, List.zipWith_cons_cons, List.prod_cons]
      apply mul_pos (Real.rpow_pos_

Depends on / 依赖: List.prod_cons, List.zipWith_cons_cons, Real.rpow_pos_of_pos, basis_hd, basis_tl, eventually_pos, generalizing, h_basis, h_basis.eventually_pos.mono, h_basis.tail, mul_pos, prod_cons, rpow_pos_of_pos, zipWith_cons_cons
-/
theorem toFun_pos {m : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) :
    forallᶠ x in atTop, 0 < m.toFun basis x := by
  apply h_basis.eventually_pos.mono
  intro x hx
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [toFun, List.zipWith_cons_cons, List.prod_cons]
      apply mul_pos (Real.rpow_pos_of_pos (hx basis_hd (by simp)) _)
      exact ih h_basis.tail (hx · <| by simp [·])

/--
theorem `toFun_ne_zero` / 定理 `toFun_ne_zero`

English:
theorem toFun_ne_zero
  given: {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: (toFun_pos h_basis).mono fun _ hx => hx.ne'

中文:
定理 toFun_ne_zero
  条件: {m : UnitMonomial} {basis : 基} (h_basis : WellFormedBasis basis)
  证明: (toFun_pos h_basis).mono fun _ hx => hx.ne'

Depends on / 依赖: h_basis, hx.ne, toFun_pos
-/
theorem toFun_ne_zero {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    forallᶠ x in atTop, m.toFun basis x != 0 :=
  (toFun_pos h_basis).mono fun _ hx => hx.ne'

/--
theorem `zeros_append_toFun` / 定理 `zeros_append_toFun`

English:
theorem zeros_append_toFun
  given: {m : UnitMonomial} {left right : Basis}
  proof: by
  induction left with
  | nil => rfl
  | cons left_hd left_tl ih => simp [List.replicate_succ, ih]

中文:
定理 zeros_append_toFun
  条件: {m : UnitMonomial} {left right : 基}
  证明: by
  induction left with
  | nil => rfl
  | cons left_hd left_tl ih => simp [List.replicate_succ, ih]

Depends on / 依赖: List.replicate_succ, left_hd, left_tl, replicate_succ
-/
theorem zeros_append_toFun {m : UnitMonomial} {left right : Basis} :
    (List.replicate left.length 0 ++ m : UnitMonomial).toFun (left ++ right) = m.toFun right := by
  induction left with
  | nil => rfl
  | cons left_hd left_tl ih => simp [List.replicate_succ, ih]

/--
theorem `log_toFun_eq_toLogFun` / 定理 `log_toFun_eq_toLogFun`

English:
theorem log_toFun_eq_toLogFun
  given: {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: by
  apply h_basis.eventually_pos.mono
  intro x hx
  suffices h : (0 < m.toFun basis x ∧ (log ∘ m.toFun basis) x = m.toLogFun basis x) from h.2
  induction m generalizing basis with
  | nil => simp
  | cons e es ih =>
    cases basis with
    | nil => simp
    | cons b bs =>
      simp only [toFun_

中文:
定理 log_toFun_eq_toLogFun
  条件: {m : UnitMonomial} {basis : 基} (h_basis : WellFormedBasis basis)
  证明: by
  apply h_basis.eventually_pos.mono
  intro x hx
  suffices h : (0 < m.toFun basis x ∧ (log ∘ m.toFun basis) x = m.toLogFun basis x) from h.2
  induction m generalizing basis with
  | nil => simp
  | cons e es ih =>
    cases basis with
    | nil => simp
    | cons b bs =>
      simp only [toFun_

Depends on / 依赖: Function, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, Real.rpow_pos_of_pos, add_apply, comp_apply, eventually_pos, generalizing, h_basis, h_basis.eventually_pos.mono, h_basis.tail, m.toFun, m.toLogFun, mul_apply, mul_pos, pow_apply, rpow_pos_of_pos
-/
theorem log_toFun_eq_toLogFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    Real.log ∘ m.toFun basis =ᶠ[atTop] m.toLogFun basis := by
  apply h_basis.eventually_pos.mono
  intro x hx
  suffices h : (0 < m.toFun basis x ∧ (log ∘ m.toFun basis) x = m.toLogFun basis x) from h.2
  induction m generalizing basis with
  | nil => simp
  | cons e es ih =>
    cases basis with
    | nil => simp
    | cons b bs =>
      simp only [toFun_cons, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, toLogFun_cons,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      obtain ⟨hpos, heq⟩ := ih h_basis.tail (hx · <| by simp [·])
      refine ⟨mul_pos (Real.rpow_pos_of_pos (hx b (by simp)) _) hpos, ?_⟩
      rw [Real.log_mul (Real.rpow_pos_of_pos (hx b (by simp)) _).ne' hpos.ne']; rw [Real.log_rpow (hx b (by simp))]; rw [← heq]
      rfl

/--
theorem `toLogFun_isEquivalent_of_nonzero_head` / 定理 `toLogFun_isEquivalent_of_nonzero_head`

English:
theorem toLogFun_isEquivalent_of_nonzero_head
  statement: {exps_hd : Real} {exps_tl : UnitMonomial}
  proof: by
  simp only [toLogFun_cons]
  apply IsEquivalent.refl.add_isLittleO
  apply IsLittleO.const_mul_right' (isUnit_iff_ne_zero.mpr h_nonzero)
  have hlo : forall b in basis_tl, (Real.log ∘ b) =o[atTop] (Real.log ∘ basis_hd) :=
    fun b hb => h_basis.tail_isLittleO_head hb
  clear h_basis
  induction

中文:
定理 toLogFun_isEquivalent_of_nonzero_head
  结论: {exps_hd : 实数} {exps_tl : UnitMonomial}
  证明: by
  simp only [toLogFun_cons]
  apply IsEquivalent.refl.add_isLittleO
  apply IsLittleO.const_mul_right' (isUnit_iff_ne_zero.mpr h_nonzero)
  have hlo : forall b in basis_tl, (Real.log ∘ b) =o[atTop] (Real.log ∘ basis_hd) :=
    fun b hb => h_basis.tail_isLittleO_head hb
  clear h_basis
  induction

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_zer, Asymptotics.isLittleO_zero, IsEquivalent, IsEquivalent.refl.add_isLittleO, IsLittleO, IsLittleO.const_mul_right, Real.log, add_isLittleO, basis_hd, basis_tl, const_mul_right, exps_tl, generalizing, h_basis, h_basis.tail_isLittleO_head, h_nonzero, isLittleO_zer, isLittleO_zero, isUnit_iff_ne_zero
-/
theorem toLogFun_isEquivalent_of_nonzero_head {exps_hd : Real} {exps_tl : UnitMonomial}
    {basis_hd : Real -> Real} {basis_tl : Basis} (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : exps_hd != 0) :
    UnitMonomial.toLogFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • log ∘ basis_hd := by
  simp only [toLogFun_cons]
  apply IsEquivalent.refl.add_isLittleO
  apply IsLittleO.const_mul_right' (isUnit_iff_ne_zero.mpr h_nonzero)
  have hlo : forall b in basis_tl, (Real.log ∘ b) =o[atTop] (Real.log ∘ basis_hd) :=
    fun b hb => h_basis.tail_isLittleO_head hb
  clear h_basis
  induction exps_tl generalizing basis_tl with
  | nil =>
    simp only [toLogFun_nil]
    exact Asymptotics.isLittleO_zero _ _
  | cons e es ih =>
    cases basis_tl with
    | nil =>
      simp only [toLogFun_nil_basis]
      exact Asymptotics.isLittleO_zero _ _
    | cons b bs =>
      exact (IsLittleO.const_mul_left (hlo b (by simp)) e).add (ih (by grind))

/--
theorem `toFun_tendsto_top_of_head_pos` / 定理 `toFun_tendsto_top_of_head_pos`

English:
theorem toFun_tendsto_top_of_head_pos
  statement: {exps_hd : Real} {exps_tl : UnitMonomial} {basis_hd : Real -> Real}
  proof: by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne').congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_

中文:
定理 toFun_tendsto_top_of_head_pos
  结论: {exps_hd : 实数} {exps_tl : UnitMonomial} {basis_hd : 实数 -> 实数}
  证明: by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne').congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_

Depends on / 依赖: Filter, Filter.Tendsto.congr, Function, Function.comp_apply, Real.log, Real.tendsto_exp_atTop.comp, Tendsto, basis_hd, basis_tl, comp_apply, congr_left, exps_hd, exps_tl, h_basis, h_equiv, h_log, h_nonzero, h_nonzero.ne, log_toFun_eq_toLogFun, tendsto_exp_atTop
-/
theorem toFun_tendsto_top_of_head_pos {exps_hd : Real} {exps_tl : UnitMonomial} {basis_hd : Real -> Real}
    {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : 0 < exps_hd) :
    Tendsto (UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl)) atTop atTop := by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne').congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl))
      atTop atTop by
    apply Filter.Tendsto.congr' _ (Real.tendsto_exp_atTop.comp h_log)
    apply (toFun_pos (m := (exps_hd :: exps_tl)) h_basis).mono
    intro x hx
    simp only [Function.comp_apply]
    exact Real.exp_log hx
  apply IsEquivalent.tendsto_atTop h_equiv.symm
  apply Filter.Tendsto.const_mul_atTop h_nonzero
  apply Tendsto.comp Real.tendsto_log_atTop
  exact h_basis.tendsto_atTop (by simp)

/--
theorem `toFun_tendsto_zero_of_head_neg` / 定理 `toFun_tendsto_zero_of_head_neg`

English:
theorem toFun_tendsto_zero_of_head_neg
  statement: {exps_hd : Real} {exps_tl : UnitMonomial} {basis_hd : Real -> Real}
  proof: by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne).congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_h

中文:
定理 toFun_tendsto_zero_of_head_neg
  结论: {exps_hd : 实数} {exps_tl : UnitMonomial} {basis_hd : 实数 -> 实数}
  证明: by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne).congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_h

Depends on / 依赖: Filter, Filter.Tendsto.congr, Real.log, Real.tendsto_exp_atBot.comp, Tendsto, basis_hd, basis_tl, congr_left, exps_hd, exps_tl, h_basis, h_equiv, h_log, h_nonzero, h_nonzero.ne, log_toFun_eq_toLogFun, tendsto_exp_atBot, toFun_pos, toLogFun_isEquivalent_of_nonzero_head
-/
theorem toFun_tendsto_zero_of_head_neg {exps_hd : Real} {exps_tl : UnitMonomial} {basis_hd : Real -> Real}
    {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : exps_hd < 0) :
    Tendsto (UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl)) atTop (𝓝 0) := by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne).congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl))
      atTop atBot by
    have hmono := Real.tendsto_exp_atBot.comp h_log
    apply Filter.Tendsto.congr' _ hmono
    apply (toFun_pos (m := (exps_hd :: exps_tl)) h_basis).mono
    intro x hx
    simp only [Function.comp_apply]
    exact Real.exp_log hx
  apply IsEquivalent.tendsto_atBot h_equiv.symm
  have h_log_atTop : Tendsto (Real.log ∘ basis_hd) atTop atTop :=
    Tendsto.comp Real.tendsto_log_atTop (h_basis.tendsto_atTop (by simp))
  exact Filter.Tendsto.const_mul_atTop_of_neg h_nonzero h_log_atTop

/--
theorem `toFun_tendsto_top_of_firstNonzeroIsPos` / 定理 `toFun_tendsto_top_of_firstNonzeroIsPos`

English:
theorem toFun_tendsto_top_of_firstNonzeroIsPos
  statement: {m : UnitMonomial} {basis : Basis}
  proof: by
  cases m with
  | nil => simp at h_firstIsPos
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsPos.cons_iff] at h_firstIsPos
      obtain h | h := h_firstIsPos
      · exact toFun_tendsto_top_of_head_pos

中文:
定理 toFun_tendsto_top_of_firstNonzeroIsPos
  结论: {m : UnitMonomial} {basis : 基}
  证明: by
  cases m with
  | nil => simp at h_firstIsPos
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsPos.cons_iff] at h_firstIsPos
      obtain h | h := h_firstIsPos
      · exact toFun_tendsto_top_of_head_pos

Depends on / 依赖: FirstNonzeroIsPos, FirstNonzeroIsPos.cons_iff, UnitMonomial, UnitMonomial.toFun, basis_hd, basis_tl, cons_iff, exps_hd, exps_tl, h.left, h_basis, h_eq, h_firstIsPos, h_length, toFun_tendsto_top_of_firstNonzeroIsPos, toFun_tendsto_top_of_head_pos
-/
theorem toFun_tendsto_top_of_firstNonzeroIsPos {m : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_length : m.length = basis.length)
    (h_firstIsPos : FirstNonzeroIsPos m) :
    Tendsto (UnitMonomial.toFun m basis) atTop atTop := by
  cases m with
  | nil => simp at h_firstIsPos
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsPos.cons_iff] at h_firstIsPos
      obtain h | h := h_firstIsPos
      · exact toFun_tendsto_top_of_head_pos h_basis h
      · have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                    UnitMonomial.toFun exps_tl basis_tl := by
          ext x; simp [UnitMonomial.toFun, h.left]
        rw [h_eq]
        exact toFun_tendsto_top_of_firstNonzeroIsPos h_basis.tail (by simpa using h_length) h.right

/--
theorem `toFun_tendsto_zero_of_firstNonzeroIsNeg` / 定理 `toFun_tendsto_zero_of_firstNonzeroIsNeg`

English:
theorem toFun_tendsto_zero_of_firstNonzeroIsNeg
  statement: {m : UnitMonomial} {basis : Basis}
  proof: by
  cases m with
  | nil => simp at h_firstIsNeg
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsNeg.cons_iff] at h_firstIsNeg
      obtain h | h := h_firstIsNeg
      · exact toFun_tendsto_zero_of_head_ne

中文:
定理 toFun_tendsto_zero_of_firstNonzeroIsNeg
  结论: {m : UnitMonomial} {basis : 基}
  证明: by
  cases m with
  | nil => simp at h_firstIsNeg
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsNeg.cons_iff] at h_firstIsNeg
      obtain h | h := h_firstIsNeg
      · exact toFun_tendsto_zero_of_head_ne

Depends on / 依赖: FirstNonzeroIsNeg, FirstNonzeroIsNeg.cons_iff, UnitMonomial, UnitMonomial.toFun, basis_hd, basis_tl, cons_iff, exps_hd, exps_tl, h.left, h_basi, h_basis, h_eq, h_firstIsNeg, h_length, toFun_tendsto_zero_of_firstNonzeroIsNeg, toFun_tendsto_zero_of_head_neg
-/
theorem toFun_tendsto_zero_of_firstNonzeroIsNeg {m : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_length : m.length = basis.length)
    (h_firstIsNeg : FirstNonzeroIsNeg m) :
    Tendsto (UnitMonomial.toFun m basis) atTop (𝓝 0) := by
  cases m with
  | nil => simp at h_firstIsNeg
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsNeg.cons_iff] at h_firstIsNeg
      obtain h | h := h_firstIsNeg
      · exact toFun_tendsto_zero_of_head_neg h_basis h
      · have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                    UnitMonomial.toFun exps_tl basis_tl := by
          ext x; simp [UnitMonomial.toFun, h.left]
        rw [h_eq]
        exact toFun_tendsto_zero_of_firstNonzeroIsNeg h_basis.tail (by simpa using h_length) h.right

/--
theorem `toFun_tendsto_one_of_allZero` / 定理 `toFun_tendsto_one_of_allZero`

English:
theorem toFun_tendsto_one_of_allZero
  statement: {m : UnitMonomial} {basis : Basis}
  proof: by
  cases m with
  | nil =>
    exact tendsto_const_nhds
  | cons exps_hd exps_tl =>
    cases basis with
    | nil =>
      eta_expand
      simp [toFun]
    | cons basis_hd basis_tl =>
      simp at h_allZero
      have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
     

中文:
定理 toFun_tendsto_one_of_allZero
  结论: {m : UnitMonomial} {basis : 基}
  证明: by
  cases m with
  | nil =>
    exact tendsto_const_nhds
  | cons exps_hd exps_tl =>
    cases basis with
    | nil =>
      eta_expand
      simp [toFun]
    | cons basis_hd basis_tl =>
      simp at h_allZero
      have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
     

Depends on / 依赖: UnitMonomial, UnitMonomial.toFun, basis_hd, basis_tl, eta_expand, exps_hd, exps_tl, h_allZero, h_allZero.left, h_allZero.right, h_eq, tendsto_const_nhds, toFun_tendsto_one_of_allZero
-/
theorem toFun_tendsto_one_of_allZero {m : UnitMonomial} {basis : Basis}
    (h_allZero : AllZero m) :
    Tendsto (UnitMonomial.toFun m basis) atTop (𝓝 1) := by
  cases m with
  | nil =>
    exact tendsto_const_nhds
  | cons exps_hd exps_tl =>
    cases basis with
    | nil =>
      eta_expand
      simp [toFun]
    | cons basis_hd basis_tl =>
      simp at h_allZero
      have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                  UnitMonomial.toFun exps_tl basis_tl := by
        ext x; simp [UnitMonomial.toFun, h_allZero.left]
      rw [h_eq]
      apply toFun_tendsto_one_of_allZero h_allZero.right

/--
lemma `isLittleO_of_lt` / 引理 `isLittleO_of_lt`

English:
lemma isLittleO_of_lt
  statement: {basis : Basis} {m1 m2 : UnitMonomial}
  proof: by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [List.length_nil, List.length_eq_zero_iff] at h1 h2
    simp [h1, h2] at h_lt
  obtain _ | ⟨exp1, m1⟩ := m1
  · simp at h1
  obtain _ | ⟨exp2, m2⟩ := m2
  · simp at h2
  cases h_lt with
  | cons h =>
    simp only [toFun_cons]
    apply IsB

中文:
引理 isLittleO_of_lt
  结论: {basis : 基} {m1 m2 : UnitMonomial}
  证明: by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [List.length_nil, List.length_eq_zero_iff] at h1 h2
    simp [h1, h2] at h_lt
  obtain _ | ⟨exp1, m1⟩ := m1
  · simp at h1
  obtain _ | ⟨exp2, m2⟩ := m2
  · simp at h2
  cases h_lt with
  | cons h =>
    simp only [toFun_cons]
    apply IsB

Depends on / 依赖: IsBigO, IsBigO.mul_isLittleO, IsLittleO, IsLittleO.of_tendsto, List.length_cons, List.length_eq_zero_iff, List.length_nil, Nat.add_right_cancel_iff, add_right_cancel_iff, basis_hd, basis_tl, h_basis, h_basis.tail, h_lt, isBigO_refl, isLittleO_of_lt, length_cons, length_eq_zero_iff, length_nil, mul_isLittleO
-/
lemma isLittleO_of_lt {basis : Basis} {m1 m2 : UnitMonomial}
    (h_basis : WellFormedBasis basis)
    (h1 : m1.length = basis.length)
    (h2 : m2.length = basis.length)
    (h_lt : m1 < m2) :
    m1.toFun basis =o[atTop] m2.toFun basis := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [List.length_nil, List.length_eq_zero_iff] at h1 h2
    simp [h1, h2] at h_lt
  obtain _ | ⟨exp1, m1⟩ := m1
  · simp at h1
  obtain _ | ⟨exp2, m2⟩ := m2
  · simp at h2
  cases h_lt with
  | cons h =>
    simp only [toFun_cons]
    apply IsBigO.mul_isLittleO (isBigO_refl _ _)
    exact isLittleO_of_lt h_basis.tail (by simpa using h1) (by simpa using h2) h
  | rel h =>
    simp only [List.length_cons, Nat.add_right_cancel_iff, toFun_cons] at h1 h2 ⊢
    apply IsLittleO.of_tendsto_div_atTop
    apply Filter.Tendsto.congr' (f₁ := UnitMonomial.toFun ((exp2 - exp1) ::
      UnitMonomial.mul m2 (UnitMonomial.inv m1)) (basis_hd :: basis_tl))
    · simp only [toFun_cons, Pi.mul_apply, Pi.pow_apply]
      grw [mul_toFun h_basis.tail (by grind [inv_length]), inv_toFun h_basis.tail]
      apply h_basis.head_eventually_pos.mono
      intro x hx
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, Real.rpow_sub hx]
      field
    · apply toFun_tendsto_top_of_firstNonzeroIsPos h_basis
      · grind [inv_length, mul_length]
      · apply FirstNonzeroIsPos.of_head
        grind

end UnitMonomial

namespace Monomial

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: (t : Monomial) (basis : Basis)
  body: t.coef • t.unit.toFun basis

@[simp]

中文:
定义 toFun
  签名: (t : 单项式) (basis : 基)
  定义体: t.coef • t.unit.toFun basis

@[simp]

Depends on / 依赖: t.coef, t.unit.toFun
-/
noncomputable def toFun (t : Monomial) (basis : Basis) : Real -> Real :=
  t.coef • t.unit.toFun basis

@[simp]
/--
theorem `nil_toFun` / 定理 `nil_toFun`

English:
theorem nil_toFun
  given: {coef : Real} {basis : Basis}
  proof: by
  ext x
  simp [toFun]

@[simp]

中文:
定理 nil_toFun
  条件: {coef : 实数} {basis : 基}
  证明: by
  ext x
  simp [toFun]

@[simp]
-/
theorem nil_toFun {coef : Real} {basis : Basis} :
    Monomial.toFun ⟨coef, []⟩ basis = fun _ => coef := by
  ext x
  simp [toFun]

@[simp]
/--
theorem `cons_toFun` / 定理 `cons_toFun`

English:
theorem cons_toFun
  given: {coef exp : Real} {m : UnitMonomial} {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  ext x
  simp [toFun]
  ring

中文:
定理 cons_toFun
  条件: {coef exp : 实数} {m : UnitMonomial} {basis_hd : 实数 -> 实数} {basis_tl : 基}
  证明: by
  ext x
  simp [toFun]
  ring
-/
theorem cons_toFun {coef exp : Real} {m : UnitMonomial} {basis_hd : Real -> Real} {basis_tl : Basis} :
    Monomial.toFun ⟨coef, exp :: m⟩ (basis_hd :: basis_tl) =
    basis_hd ^ exp * Monomial.toFun ⟨coef, m⟩ basis_tl := by
  ext x
  simp [toFun]
  ring

/--
theorem `zero_coef_toFun` / 定理 `zero_coef_toFun`

English:
theorem zero_coef_toFun
  given: {t : Monomial} (basis : Basis) (h_coef : t.coef = 0)
  proof: by
  simp [toFun, h_coef]

中文:
定理 zero_coef_toFun
  条件: {t : 单项式} (basis : 基) (h_coef : t.coef = 0)
  证明: by
  simp [toFun, h_coef]

Depends on / 依赖: h_coef
-/
theorem zero_coef_toFun {t : Monomial} (basis : Basis) (h_coef : t.coef = 0) :
    t.toFun basis = 0 := by
  simp [toFun, h_coef]

/--
theorem `zero_coef_toFun'` / 定理 `zero_coef_toFun'`

English:
theorem zero_coef_toFun'
  given: (basis : Basis) (exps : UnitMonomial)
  proof: zero_coef_toFun _ rfl

中文:
定理 zero_coef_toFun'
  条件: (basis : 基) (exps : UnitMonomial)
  证明: zero_coef_toFun _ rfl

Depends on / 依赖: zero_coef_toFun
-/
theorem zero_coef_toFun' (basis : Basis) (exps : UnitMonomial) :
    Monomial.toFun ⟨0, exps⟩ basis = 0 := zero_coef_toFun _ rfl

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: (t : Monomial)
  body: ⟨-t.coef, t.unit⟩

中文:
定义 neg
  签名: (t : 单项式)
  定义体: ⟨-t.coef, t.unit⟩

Depends on / 依赖: t.coef, t.unit
-/
noncomputable def neg (t : Monomial) : Monomial :=
  ⟨-t.coef, t.unit⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: (t1 t2 : Monomial)
  body: ⟨t1.coef * t2.coef, t1.unit.mul t2.unit⟩

中文:
定义 mul
  签名: (t1 t2 : 单项式)
  定义体: ⟨t1.coef * t2.coef, t1.unit.mul t2.unit⟩

Depends on / 依赖: t1.coef, t1.unit.mul, t2.coef, t2.unit
-/
noncomputable def mul (t1 t2 : Monomial) : Monomial :=
  ⟨t1.coef * t2.coef, t1.unit.mul t2.unit⟩

/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (t : Monomial) (c : Real)
  body: ⟨c * t.coef, t.unit⟩

中文:
定义 smul
  签名: (t : 单项式) (c : 实数)
  定义体: ⟨c * t.coef, t.unit⟩

Depends on / 依赖: t.coef, t.unit
-/
noncomputable def smul (t : Monomial) (c : Real) : Monomial :=
  ⟨c * t.coef, t.unit⟩

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (t : Monomial)
  body: ⟨t.coef⁻¹, t.unit.inv⟩

中文:
定义 inv
  签名: (t : 单项式)
  定义体: ⟨t.coef⁻¹, t.unit.inv⟩

Depends on / 依赖: t.coef, t.unit.inv
-/
noncomputable def inv (t : Monomial) : Monomial :=
  ⟨t.coef⁻¹, t.unit.inv⟩

/--
theorem `neg_toFun` / 定理 `neg_toFun`

English:
theorem neg_toFun
  given: {t : Monomial} {basis : Basis}
  proof: by
  ext x
  simp [neg, toFun]

中文:
定理 neg_toFun
  条件: {t : 单项式} {basis : 基}
  证明: by
  ext x
  simp [neg, toFun]
-/
theorem neg_toFun {t : Monomial} {basis : Basis} :
    t.toFun basis = -t.neg.toFun basis := by
  ext x
  simp [neg, toFun]

/--
theorem `mul_toFun` / 定理 `mul_toFun`

English:
theorem mul_toFun
  statement: {t1 t2 : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: by
  simp only [toFun, mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  grw [UnitMonomial.mul_toFun h_basis h_length]
  filter_upwards [] with t
  simp [Pi.smul_apply, Pi.mul_apply]
  ring

中文:
定理 mul_toFun
  结论: {t1 t2 : 单项式} {basis : 基} (h_basis : WellFormedBasis basis)
  证明: by
  simp only [toFun, mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  grw [UnitMonomial.mul_toFun h_basis h_length]
  filter_upwards [] with t
  simp [Pi.smul_apply, Pi.mul_apply]
  ring

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Pi.mul_apply, Pi.smul_apply, UnitMonomial, UnitMonomial.mul_toFun, filter_upwards, h_basis, h_length, mul_apply, mul_smul_comm, mul_toFun, smul_apply, smul_mul_assoc
-/
theorem mul_toFun {t1 t2 : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : t1.unit.length = t2.unit.length) :
    (mul t1 t2).toFun basis =ᶠ[atTop] t1.toFun basis * t2.toFun basis := by
  simp only [toFun, mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  grw [UnitMonomial.mul_toFun h_basis h_length]
  filter_upwards [] with t
  simp [Pi.smul_apply, Pi.mul_apply]
  ring

/--
theorem `smul_toFun` / 定理 `smul_toFun`

English:
theorem smul_toFun
  given: {t : Monomial} {basis : Basis} (c : Real)
  proof: by
  ext x
  simp [smul, toFun]
  ring

中文:
定理 smul_toFun
  条件: {t : 单项式} {basis : 基} (c : 实数)
  证明: by
  ext x
  simp [smul, toFun]
  ring
-/
theorem smul_toFun {t : Monomial} {basis : Basis} (c : Real) :
    (smul t c).toFun basis = c • t.toFun basis := by
  ext x
  simp [smul, toFun]
  ring

/--
theorem `inv_toFun` / 定理 `inv_toFun`

English:
theorem inv_toFun
  given: {t : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: by
  simp only [toFun, inv]
  grw [UnitMonomial.inv_toFun h_basis]
  filter_upwards [] with x
  simp [Pi.smul_apply, Pi.inv_apply]
  ring

@[simp]

中文:
定理 inv_toFun
  条件: {t : 单项式} {basis : 基} (h_basis : WellFormedBasis basis)
  证明: by
  simp only [toFun, inv]
  grw [UnitMonomial.inv_toFun h_basis]
  filter_upwards [] with x
  simp [Pi.smul_apply, Pi.inv_apply]
  ring

@[simp]

Depends on / 依赖: Pi.inv_apply, Pi.smul_apply, UnitMonomial, UnitMonomial.inv_toFun, filter_upwards, h_basis, inv_apply, inv_toFun, smul_apply
-/
theorem inv_toFun {t : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    t.inv.toFun basis =ᶠ[atTop] (t.toFun basis)⁻¹ := by
  simp only [toFun, inv]
  grw [UnitMonomial.inv_toFun h_basis]
  filter_upwards [] with x
  simp [Pi.smul_apply, Pi.inv_apply]
  ring

@[simp]
/--
theorem `inv_length` / 定理 `inv_length`

English:
theorem inv_length
  given: (t : Monomial)
  proof: by
  simp [inv]

中文:
定理 inv_length
  条件: (t : 单项式)
  证明: by
  simp [inv]
-/
theorem inv_length (t : Monomial) :
    t.inv.unit.length = t.unit.length := by
  simp [inv]

/--
theorem `toFun_pos` / 定理 `toFun_pos`

English:
theorem toFun_pos
  statement: {t : Monomial} {basis : Basis}
  proof: by
  simp only [Monomial.toFun]
  apply (t.unit.toFun_pos h_basis).mono
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  positivity

中文:
定理 toFun_pos
  结论: {t : 单项式} {basis : 基}
  证明: by
  simp only [Monomial.toFun]
  apply (t.unit.toFun_pos h_basis).mono
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  positivity

Depends on / 依赖: Monomial, Monomial.toFun, Pi.smul_apply, h_basis, smul_apply, smul_eq_mul, t.unit.toFun_pos, toFun_pos
-/
theorem toFun_pos {t : Monomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_coef : 0 < t.coef) :
    forallᶠ x in atTop, 0 < t.toFun basis x := by
  simp only [Monomial.toFun]
  apply (t.unit.toFun_pos h_basis).mono
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  positivity

/--
theorem `zeros_append_toFun` / 定理 `zeros_append_toFun`

English:
theorem zeros_append_toFun
  given: (coef : Real) {exps : UnitMonomial} {left right : Basis}
  proof: ⟨coef, List.replicate left.length 0 ++ exps⟩;
    t.toFun (left ++ right) = (mk coef exps).toFun right := by
  exact congrArg (coef • ·) UnitMonomial.zeros_append_toFun

中文:
定理 zeros_append_toFun
  条件: (coef : 实数) {exps : UnitMonomial} {left right : 基}
  证明: ⟨coef, List.replicate left.length 0 ++ exps⟩;
    t.toFun (left ++ right) = (mk coef exps).toFun right := by
  exact congrArg (coef • ·) UnitMonomial.zeros_append_toFun

Depends on / 依赖: List.replicate, left.length, length, replicate
-/
theorem zeros_append_toFun (coef : Real) {exps : UnitMonomial} {left right : Basis} :
    let t : Monomial := ⟨coef, List.replicate left.length 0 ++ exps⟩;
    t.toFun (left ++ right) = (mk coef exps).toFun right := by
  exact congrArg (coef • ·) UnitMonomial.zeros_append_toFun

/--
theorem `tendsto_zero_of_coef_zero` / 定理 `tendsto_zero_of_coef_zero`

English:
theorem tendsto_zero_of_coef_zero
  statement: {coef : Real} {exps : UnitMonomial} (basis : Basis)
  proof: ⟨coef, exps⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  rw [zero_coef_toFun _ (by simpa [t])]
  exact tendsto_const_nhds

中文:
定理 tendsto_zero_of_coef_zero
  结论: {coef : 实数} {exps : UnitMonomial} (basis : 基)
  证明: ⟨coef, exps⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  rw [zero_coef_toFun _ (by simpa [t])]
  exact tendsto_const_nhds
-/
theorem tendsto_zero_of_coef_zero {coef : Real} {exps : UnitMonomial} (basis : Basis)
    (h_coef : coef = 0) :
    let t : Monomial := ⟨coef, exps⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  rw [zero_coef_toFun _ (by simpa [t])]
  exact tendsto_const_nhds

/--
theorem `toFun_tendsto_zero_of_firstNonzeroIsNeg` / 定理 `toFun_tendsto_zero_of_firstNonzeroIsNeg`

English:
theorem toFun_tendsto_zero_of_firstNonzeroIsNeg
  statement: {coef : Real} {exps : UnitMonomial} {basis : Basis}
  proof: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _
    (UnitMonomial.toFun_tendsto_zero_of_firstNonzeroIsNeg h_basis h_length h_exps)
  simp

中文:
定理 toFun_tendsto_zero_of_firstNonzeroIsNeg
  结论: {coef : 实数} {exps : UnitMonomial} {basis : 基}
  证明: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _
    (UnitMonomial.toFun_tendsto_zero_of_firstNonzeroIsNeg h_basis h_length h_exps)
  simp
-/
theorem toFun_tendsto_zero_of_firstNonzeroIsNeg {coef : Real} {exps : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_exps : exps.FirstNonzeroIsNeg) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _
    (UnitMonomial.toFun_tendsto_zero_of_firstNonzeroIsNeg h_basis h_length h_exps)
  simp

/--
theorem `toFun_tendsto_top_of_firstNonzeroIsPos` / 定理 `toFun_tendsto_top_of_firstNonzeroIsPos`

English:
theorem toFun_tendsto_top_of_firstNonzeroIsPos
  statement: {coef : Real} {exps : UnitMonomial} {basis : Basis}
  proof: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atTop := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)

中文:
定理 toFun_tendsto_top_of_firstNonzeroIsPos
  结论: {coef : 实数} {exps : UnitMonomial} {basis : 基}
  证明: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atTop := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)
-/
theorem toFun_tendsto_top_of_firstNonzeroIsPos {coef : Real} {exps : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : 0 < coef)
    (h_exps : exps.FirstNonzeroIsPos) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atTop := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)

/--
theorem `toFun_tendsto_bot_of_firstNonzeroIsPos` / 定理 `toFun_tendsto_bot_of_firstNonzeroIsPos`

English:
theorem toFun_tendsto_bot_of_firstNonzeroIsPos
  statement: {coef : Real} {exps : UnitMonomial} {basis : Basis}
  proof: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atBot := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop_of_neg h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)

中文:
定理 toFun_tendsto_bot_of_firstNonzeroIsPos
  结论: {coef : 实数} {exps : UnitMonomial} {basis : 基}
  证明: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atBot := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop_of_neg h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)
-/
theorem toFun_tendsto_bot_of_firstNonzeroIsPos {coef : Real} {exps : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : coef < 0)
    (h_exps : exps.FirstNonzeroIsPos) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atBot := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop_of_neg h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)

/--
theorem `toFun_tendsto_const_of_allZero` / 定理 `toFun_tendsto_const_of_allZero`

English:
theorem toFun_tendsto_const_of_allZero
  statement: {coef : Real} {exps : UnitMonomial} {basis : Basis}
  proof: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 coef) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _ (UnitMonomial.toFun_tendsto_one_of_allZero h_exps)
  simp [t]

中文:
定理 toFun_tendsto_const_of_allZero
  结论: {coef : 实数} {exps : UnitMonomial} {basis : 基}
  证明: ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 coef) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _ (UnitMonomial.toFun_tendsto_one_of_allZero h_exps)
  simp [t]
-/
theorem toFun_tendsto_const_of_allZero {coef : Real} {exps : UnitMonomial} {basis : Basis}
    (h_exps : exps.AllZero) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 coef) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _ (UnitMonomial.toFun_tendsto_one_of_allZero h_exps)
  simp [t]

/--
theorem `majorized_tail_toFun_head` / 定理 `majorized_tail_toFun_head`

English:
theorem majorized_tail_toFun_head
  statement: {t : Monomial} {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  exact Majorized.smul (UnitMonomial.majorized_tail_toFun_head h_length h_basis)

中文:
定理 majorized_tail_toFun_head
  结论: {t : 单项式} {basis_hd : 实数 -> 实数} {basis_tl : 基}
  证明: by
  exact Majorized.smul (UnitMonomial.majorized_tail_toFun_head h_length h_basis)

Depends on / 依赖: Majorized, Majorized.smul, UnitMonomial, UnitMonomial.majorized_tail_toFun_head, h_basis, h_length, majorized_tail_toFun_head
-/
theorem majorized_tail_toFun_head {t : Monomial} {basis_hd : Real -> Real} {basis_tl : Basis}
    (h_length : t.unit.length = basis_tl.length)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    Majorized (t.toFun basis_tl) basis_hd 0 := by
  exact Majorized.smul (UnitMonomial.majorized_tail_toFun_head h_length h_basis)

/--
lemma `isLittleO_of_lt_exps` / 引理 `isLittleO_of_lt_exps`

English:
lemma isLittleO_of_lt_exps
  statement: {basis : Basis} {t1 t2 : Monomial}
  proof: by
  simp only [toFun]
  pull fun _ => _
  apply Asymptotics.IsBigO.smul_isLittleO
  · simp at h_coef2
    simp
    grind
  apply UnitMonomial.isLittleO_of_lt h_basis h1 h2 h_lt

中文:
引理 isLittleO_of_lt_exps
  结论: {basis : 基} {t1 t2 : 单项式}
  证明: by
  simp only [toFun]
  pull fun _ => _
  apply Asymptotics.IsBigO.smul_isLittleO
  · simp at h_coef2
    simp
    grind
  apply UnitMonomial.isLittleO_of_lt h_basis h1 h2 h_lt

Depends on / 依赖: Asymptotics, Asymptotics.IsBigO.smul_isLittleO, IsBigO, UnitMonomial, UnitMonomial.isLittleO_of_lt, h_basis, h_coef2, h_lt, isLittleO_of_lt, smul_isLittleO
-/
lemma isLittleO_of_lt_exps {basis : Basis} {t1 t2 : Monomial}
    (h_basis : WellFormedBasis basis)
    (h1 : t1.unit.length = basis.length)
    (h2 : t2.unit.length = basis.length)
    (h_coef2 : t2.coef != 0)
    (h_lt : t1.unit < t2.unit) :
    t1.toFun basis =o[atTop] t2.toFun basis := by
  simp only [toFun]
  pull fun _ => _
  apply Asymptotics.IsBigO.smul_isLittleO
  · simp at h_coef2
    simp
    grind
  apply UnitMonomial.isLittleO_of_lt h_basis h1 h2 h_lt

/--
theorem `isLittleO_of_lt_exps_left` / 定理 `isLittleO_of_lt_exps_left`

English:
theorem isLittleO_of_lt_exps_left
  statement: {left right : Basis} {t1 t2 : Monomial}
  proof: by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']

中文:
定理 isLittleO_of_lt_exps_left
  结论: {left right : 基} {t1 t2 : 单项式}
  证明: by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']

Depends on / 依赖: List.replicate, Monomial, Monomial.toFun, Monomial.zeros_append_toFun, h_basis, isLittleO_of_lt_exps, left.length, length, replicate, zeros_append_toFun
-/
theorem isLittleO_of_lt_exps_left {left right : Basis} {t1 t2 : Monomial}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.unit.length = left.length + right.length)
    (h2 : t2.unit.length = right.length)
    (h_coef2 : t2.coef != 0)
    (h_lt : t1.unit < List.replicate left.length 0 ++ t2.unit) :
    t1.toFun (left ++ right) =o[atTop] t2.toFun right := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']

/--
theorem `isLittleO_of_lt_exps_right` / 定理 `isLittleO_of_lt_exps_right`

English:
theorem isLittleO_of_lt_exps_right
  statement: {left right : Basis} {t1 t2 : Monomial}
  proof: by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']

中文:
定理 isLittleO_of_lt_exps_right
  结论: {left right : 基} {t1 t2 : 单项式}
  证明: by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']

Depends on / 依赖: List.replicate, Monomial, Monomial.toFun, Monomial.zeros_append_toFun, h_basis, isLittleO_of_lt_exps, left.length, length, replicate, zeros_append_toFun
-/
theorem isLittleO_of_lt_exps_right {left right : Basis} {t1 t2 : Monomial}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.unit.length = left.length + right.length)
    (h2 : t2.unit.length = right.length)
    (h_coef1 : t1.coef != 0)
    (h_lt : List.replicate left.length 0 ++ t2.unit < t1.unit) :
    t2.toFun right =o[atTop] t1.toFun (left ++ right) := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']

end Monomial

end Tactic.ComputeAsymptotics
