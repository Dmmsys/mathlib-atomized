/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Correctness of Terminating Continued Fraction Computations (`GenContFract.of`)

## Summary

We show the correctness of the algorithm computing continued fractions (`GenContFract.of`)
in case of termination in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(GenContFract.of v).convs' n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in `GenContFract.IntFractPair.stream v n`.

For an example, refer to
`GenContFract.compExactValue_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `Algebra.ContinuedFractions.Computation.Basic`.

## Main definitions

- `GenContFract.compExactValue` can be used to compute the exact value approximated by the
  continued fraction `GenContFract.of v` by adding a residual term as described in the summary.

## Main Theorems

- `GenContFract.compExactValue_correctness_of_stream_eq_some` shows that
  `GenContFract.compExactValue` indeed returns the value `v` when given the convergent and
  fractional part as described in the summary.
- `GenContFract.of_correctness_of_terminatedAt` shows the equality
  `v = (GenContFract.of v).convs n` if `GenContFract.of v` terminated at position `n`.
-/

@[expose] public section

assert_not_exists Finset

namespace GenContFract

open GenContFract (of)

-- `compExactValue_correctness_of_stream_eq_some` does not trivially generalize to `DivisionRing`
variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

/-- Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `exactConts.a / exactConts.b` where `exactConts = nextConts 1 fr⁻¹ pconts conts`
  otherwise.

This function can be used to compute the exact value approximated by a continued fraction
`GenContFract.of v` as described in lemma `compExactValue_correctness_of_stream_eq_some`.
-/
/-
**GenContFract.compExactValue** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract`。
形式化陈述：{K : Type u_1} → [Field K] → [LinearOrder K] → GenContFract.Pair K → GenCo
ntFract.Pair K → K → K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two continuants `pconts` and `conts` and a value `fr`, this function retur
ns
- `conts.a / conts.b` if `fr = 0`
- `exactConts.a / exactConts.b` where `exactConts = nextConts 1 fr⁻¹ pconts cont
s`
  otherwise.

This function can be used to compute the exact value approximated by a continued
 fraction
`GenContFract.of v` as described in lemma `compExactValue_correctness_of_stream_
eq_some`.
-/
protected def compExactValue (pconts conts : Pair K) (fr : K) : K :=
  -- if the fractional part is zero, we exactly approximated the value by the last continuants
  if fr = 0 then
    conts.a / conts.b
  else -- otherwise, we have to include the fractional part in a final continuants step.
    letI exactConts := nextConts 1 fr⁻¹ pconts conts
    exactConts.a / exactConts.b

variable [FloorRing K]

/-- Just a computational lemma we need for the next main proof. -/
/-
**GenContFract.compExactValue_correctness_of_stream_eq_some_aux_comp** 是 Mathlib
 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : LinearOrder K] [inst_2 : Floor
Ring K] {a : K} (b c : K),   Int.fract a ≠ 0 → (↑⌊a⌋ * b + c) / Int.fract a + b 
= (b * a + c) / Int.fract a
参数：b c : K；↑⌊a⌋ * b + c；b * a + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Int.fract.eq_1`：∀ {α : Type u_2} [inst : Ring α] [inst_1 : LinearOrder α
] [inst_2 : FloorRing α] (a : α), Int.fract a = a - ↑⌊a⌋
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Just a computational lemma we need for the next main proof.
-/
protected theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  field_simp
  rw [Int.fract]
  ring

open GenContFract
  (compExactValue compExactValue_correctness_of_stream_eq_some_aux_comp)

/-- Shows the correctness of `compExactValue` in case the continued fraction
`GenContFract.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n` and `n + 1` as well
as the fractional part at `IntFractPair.stream n` to `compExactValue`.

The correctness might be seen more readily if one uses `convs'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `GenContFract.IntFractPair.stream v 0 = some ⟨3, 0.4⟩`, and
- `GenContFract.IntFractPair.stream v 1 = some ⟨2, 0.5⟩`.

Now `(GenContFract.of v).convs' 1 = 3 + 1/2`, and our fractional term at position `2` is `0.5`.
We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`.
This computation corresponds exactly to the one using the recurrence equation in `compExactValue`.
-/
/-
**GenContFract.compExactValue_correctness_of_stream_eq_some** 是 Mathlib 中的一个定理，位
于命名空间 `GenContFract`。
形式化陈述：compExactValue_correctness_of_stream_eq_some : forall {ifp_n : IntFractPai
r K}, IntFractPair.stream v n = some ifp_n -> v = compExactValue ((of v).contsAu
x n) ((of v).contsAux <| n + 1) ifp_n.fr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fract_add_floor`：fract_add_floor (a : R) : fract a + ⌊a⌋ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
Shows the correctness of `compExactValue` in case the continued fraction
`GenContFract.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n`
 and `n + 1` as well
as the fractional part at `IntFractPair.stream n` to `compExactValue`.

The correctness might be seen more readily if one uses `convs'` to evaluate the 
continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `GenContFract.IntFractPair.stream v 0 = some ⟨3, 0.4⟩`, and
- `GenContFract.IntFractPair.stream v 1 = some ⟨2, 0.5⟩`.

Now `(GenContFract.of v).convs' 1 = 3 + 1/2`, and our fractional term at positio
n `2` is `0.5`.
We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`.
This computation corresponds exactly to the one using the recurrence equation in
 `compExactValue`.
-/
theorem compExactValue_correctness_of_stream_eq_some :
    ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v n = some ifp_n →
      v = compExactValue ((of v).contsAux n) ((of v).contsAux <| n + 1) ifp_n.fr := by
  let g := of v
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    obtain rfl : IntFractPair.of v = ifp_zero := by
      simpa only [IntFractPair.stream, Option.some.injEq] using stream_zero_eq
    cases eq_or_ne (Int.fract v) 0 with
    | inl fract_eq_zero =>
      -- Int.fract v = 0; we must then have `v = ⌊v⌋`
      suffices v = ⌊v⌋ by
        simpa [compExactValue, IntFractPair.of, fract_eq_zero]
      calc
        v = Int.fract v + ⌊v⌋ := by rw [Int.fract_add_floor]
        _ = ⌊v⌋ := by simp [fract_eq_zero]
    | inr fract_ne_zero =>
      -- Int.fract v ≠ 0; the claim then easily follows by unfolding a single computation step
      simp [field, contsAux, nextConts, nextNum, nextDen, of_h_eq_floor, compExactValue,
        IntFractPair.of, fract_ne_zero]
  | succ n IH =>
    intro ifp_succ_n succ_nth_stream_eq
    obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, -⟩ :
      ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
        ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
      IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
    -- introduce some notation
    let conts := g.contsAux (n + 2)
    set pconts := g.contsAux (n + 1) with pconts_eq
    set ppconts := g.contsAux n with ppconts_eq
    cases eq_or_ne ifp_succ_n.fr 0 with
    | inl ifp_succ_n_fr_eq_zero =>
      -- ifp_succ_n.fr = 0
      suffices v = conts.a / conts.b by simpa [compExactValue, ifp_succ_n_fr_eq_zero]
      -- use the IH and the fact that ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ to prove this case
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_inv_eq_floor⟩ :
          ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
        IntFractPair.exists_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero
      obtain rfl : ifp_n = ifp_n' := by injection Eq.trans nth_stream_eq.symm nth_stream_eq'
      have s_nth_eq : g.s.get? n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero
      rw [← ifp_n_fract_inv_eq_floor] at s_nth_eq
      suffices v = compExactValue ppconts pconts ifp_n.fr by
        simpa [conts, contsAux, s_nth_eq, compExactValue, nth_fract_ne_zero] using this
      exact IH nth_stream_eq
    | inr ifp_succ_n_fr_ne_zero =>
      -- ifp_succ_n.fr ≠ 0
      -- use the IH to show that the following equality suffices
      suffices
        compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts ifp_succ_n.fr by grind
      -- get the correspondence between ifp_n and ifp_succ_n
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_ne_zero, ⟨rfl⟩⟩ :
        ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
        IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
      obtain rfl : ifp_n = ifp_n' := by injection Eq.trans nth_stream_eq.symm nth_stream_eq'
      -- get the correspondence between ifp_n and g.s.nth n
      have s_nth_eq : g.s.get? n = some ⟨1, (⌊ifp_n.fr⁻¹⌋ : K)⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero
      -- the claim now follows by unfolding the definitions and tedious calculations
      -- some shorthand notation
      let ppA := ppconts.a
      let ppB := ppconts.b
      let pA := pconts.a
      let pB := pconts.b
      have : compExactValue ppconts pconts ifp_n.fr =
          (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) := by
        -- unfold compExactValue and the convergent computation once
        grind [compExactValue, nextConts, nextNum, nextDen]
      rw [this]
      -- two calculations needed to show the claim
      have tmp_calc :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pA ppA ifp_succ_n_fr_ne_zero
      have tmp_calc' :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pB ppB ifp_succ_n_fr_ne_zero
      let f := Int.fract (1 / ifp_n.fr)
      -- now unfold the recurrence one step and simplify both sides to arrive at the conclusion
      dsimp only [conts, pconts, ppconts]
      have hfr : (IntFractPair.of (1 / ifp_n.fr)).fr = f := rfl
      simp [compExactValue, contsAux_recurrence s_nth_eq ppconts_eq pconts_eq,
        nextConts, nextNum, nextDen]
      grind

open GenContFract (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none)

/-- The convergent of `GenContFract.of v` at step `n - 1` is exactly `v` if the
`IntFractPair.stream` of the corresponding continued fraction terminated at step `n`. -/
/-
**GenContFract.of_correctness_of_nth_stream_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `G
enContFract`。
形式化陈述：of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.st
ream v n = none) : v = (of v).convs (n - 1)
参数：nth_stream_eq_none : IntFractPair.stream v n = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_none_iff`：succ_nth_stream_e
q_none_iff : IntFractPair.stream v (n + 1) = none ↔ IntFractPair.stream v n = no
ne ∨ exists ifp, IntFractPair.stream v n = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none`
：of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none : (of v).TerminatedA
t n ↔ IntFractPair.stream v (n + 1) = none
· 使用定理 `GenContFract.convs_stable_of_terminated`：convs_stable_of_terminated (n_l
e_m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.convs m = g.convs n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GenContFract.compExactValue_correctness_of_stream_eq_some`：compExactValu
e_correctness_of_stream_eq_some : forall {ifp_n : IntFractPair K}, IntFractPair.
stream v n = some ifp_n -> v = compExactValue (…

--- 原说明 ---
The convergent of `GenContFract.of v` at step `n - 1` is exactly `v` if the
`IntFractPair.stream` of the corresponding continued fraction terminated at step
 `n`.
-/
theorem of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) :
    v = (of v).convs (n - 1) := by
  induction n with
  | zero => contradiction
  -- IntFractPair.stream v 0 ≠ none
  | succ n IH =>
    let g := of v
    change v = g.convs n
    obtain ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩ :
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
      IntFractPair.succ_nth_stream_eq_none_iff.1 nth_stream_eq_none
    · cases n with
      | zero => contradiction
      | succ n' =>
        -- IntFractPair.stream v 0 ≠ none
        have : g.TerminatedAt n' :=
          of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
            nth_stream_eq_none
        have : g.convs (n' + 1) = g.convs n' :=
          convs_stable_of_terminated n'.le_succ this
        rw [this]
        exact IH nth_stream_eq_none
    · simpa [nth_stream_fr_eq_zero, compExactValue] using!
        compExactValue_correctness_of_stream_eq_some nth_stream_eq

/-- If `GenContFract.of v` terminated at step `n`, then the `n`th convergent is exactly `v`. -/
/-
**GenContFract.of_correctness_of_terminatedAt** 是 Mathlib 中的一个定理，位于命名空间 `GenCont
Fract`。
形式化陈述：of_correctness_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) : 
v = (of v).convs n
参数：terminatedAt_n : (of v).TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none`
：of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none : (of v).TerminatedA
t n ↔ IntFractPair.stream v (n + 1) = none
· 使用定理 `GenContFract.of_correctness_of_nth_stream_eq_none`：of_correctness_of_nth
_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) : v = (of 
v).convs (n - 1)

--- 原说明 ---
If `GenContFract.of v` terminated at step `n`, then the `n`th convergent is exac
tly `v`.
-/
theorem of_correctness_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) :
    v = (of v).convs n :=
  have : IntFractPair.stream v (n + 1) = none :=
    of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminatedAt_n
  of_correctness_of_nth_stream_eq_none this

/-- If `GenContFract.of v` terminates, then there is `n : ℕ` such that the `n`th convergent is
exactly `v`.
-/
/-
**GenContFract.of_correctness_of_terminates** 是 Mathlib 中的一个定理，位于命名空间 `GenContFr
act`。
形式化陈述：of_correctness_of_terminates (terminates : (of v).Terminates) : exists n :
 Nat, v = (of v).convs n
参数：terminates : (of v).Terminates。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `GenContFract.of_correctness_of_terminatedAt`：of_correctness_of_terminate
dAt (terminatedAt_n : (of v).TerminatedAt n) : v = (of v).convs n

--- 原说明 ---
If `GenContFract.of v` terminates, then there is `n : ℕ` such that the `n`th con
vergent is
exactly `v`.
-/
theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ n : ℕ, v = (of v).convs n :=
  Exists.elim terminates fun n terminatedAt_n =>
    Exists.intro n (of_correctness_of_terminatedAt terminatedAt_n)

open Filter

/-- If `GenContFract.of v` terminates, then its convergents will eventually always be `v`. -/
/-
**GenContFract.of_correctness_atTop_of_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Gen
ContFract`。
形式化陈述：of_correctness_atTop_of_terminates (terminates : (of v).Terminates) : fora
llᶠ n in atTop, v = (of v).convs n
参数：terminates : (of v).Terminates。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `GenContFract.convs_stable_of_terminated`：convs_stable_of_terminated (n_l
e_m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.convs m = g.convs n
· 使用定理 `GenContFract.of_correctness_of_terminatedAt`：of_correctness_of_terminate
dAt (terminatedAt_n : (of v).TerminatedAt n) : v = (of v).convs n

--- 原说明 ---
If `GenContFract.of v` terminates, then its convergents will eventually always b
e `v`.
-/
theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, v = (of v).convs n := by
  rw [eventually_atTop]
  obtain ⟨n, terminatedAt_n⟩ : ∃ n, (of v).TerminatedAt n := terminates
  use n
  intro m m_geq_n
  rw [convs_stable_of_terminated m_geq_n terminatedAt_n]
  exact of_correctness_of_terminatedAt terminatedAt_n

end GenContFract

