/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Principal ordinals

If `op` is a binary operation on ordinals, we say that an ordinal `o` is `op`-principal (or
`op`-indecomposable) whenever `a < o` and `b < o` imply `op a b < o`. Most commonly, one talks of
additive and multiplicative principal ordinals.

Additive principal ordinals were originally called "gamma numbers" by Cantor, but this term now more
commonly refers to the values given by `Ordinal.gamma`. Likewise, multiplicative principal ordinals
are sometimes known as "delta numbers". Exponential principal ordinals are (barring edge cases)
equivalent to the epsilon numbers given by `Ordinal.epsilon`.

## Main definitions and results

* `IsPrincipal`: A principal (or indecomposable) ordinal under some binary operation. We include `0`
  and other typically excluded edge cases for simplicity.
* `not_bddAbove_setOfPred_isPrincipal`: Principal ordinals (under any operation) are unbounded.
* `isPrincipal_add_iff_zero_or_omega0_opow`: The additive principal ordinals are
  `0` and the ordinal powers of `ω`.
* `isPrincipal_mul_iff_le_two_or_omega0_opow_opow`: The multiplicative principal ordinals are
  `0`, `1`, `2`, and the ordinals `ω ^ ω ^ x`.

## TODO

* Prove that the exponential principal ordinals are `0`, `1`, `2`, `ω`, or `ε_ x`.

## Tags

additively indecomposable, multiplicatively indecomposable
-/

@[expose] public section

universe u

open Order

namespace Ordinal

variable {a b c o : Ordinal.{u}}

section Arbitrary

variable {op : Ordinal -> Ordinal -> Ordinal}

/-! ### Principal ordinals under an arbitrary operation -/

/--
Definition of `IsPrincipal` / `IsPrincipal` 的定义

English:
definition IsPrincipal
  signature: (op : Ordinal -> Ordinal -> Ordinal) (o : Ordinal)
  body: forall ⦃a b⦄, a < o -> b < o -> op a b < o

@[deprecated (since := "2026-03-17")]
alias Principal := IsPrincipal

中文:
定义 是Principal
  签名: (op : 序数 -> 序数 -> 序数) (o : 序数)
  定义体: forall ⦃a b⦄, a < o -> b < o -> op a b < o

@[deprecated (since := "2026-03-17")]
alias Principal := IsPrincipal
-/
def IsPrincipal (op : Ordinal -> Ordinal -> Ordinal) (o : Ordinal) : Prop :=
  forall ⦃a b⦄, a < o -> b < o -> op a b < o

@[deprecated (since := "2026-03-17")]
alias Principal := IsPrincipal

/--
theorem `isPrincipal_swap_iff` / 定理 `isPrincipal_swap_iff`

English:
theorem isPrincipal_swap_iff
  statement: IsPrincipal (Function.swap op) o ↔ IsPrincipal op o
  proof: by
  constructor <;> exact fun h a b ha hb => h hb ha

@[deprecated (since := "2026-03-17")]
alias principal_swap_iff := isPrincipal_swap_iff

中文:
定理 isPrincipal_swap_iff
  结论: 是Principal (函数.swap op) o ↔ 是Principal op o
  证明: by
  constructor <;> exact fun h a b ha hb => h hb ha

@[deprecated (since := "2026-03-17")]
alias principal_swap_iff := isPrincipal_swap_iff
-/
theorem isPrincipal_swap_iff : IsPrincipal (Function.swap op) o ↔ IsPrincipal op o := by
  constructor <;> exact fun h a b ha hb => h hb ha

@[deprecated (since := "2026-03-17")]
alias principal_swap_iff := isPrincipal_swap_iff

/--
theorem `not_isPrincipal_iff` / 定理 `not_isPrincipal_iff`

English:
theorem not_isPrincipal_iff
  statement: ¬ IsPrincipal op o ↔ exists a < o, exists b < o, o <= op a b
  proof: by
  simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff := not_isPrincipal_iff

中文:
定理 not_isPrincipal_iff
  结论: ¬ 是Principal op o ↔ 存在 a < o, 存在 b < o, o <= op a b
  证明: by
  simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff := not_isPrincipal_iff

Depends on / 依赖: IsPrincipal
-/
theorem not_isPrincipal_iff : ¬ IsPrincipal op o ↔ exists a < o, exists b < o, o <= op a b := by
  simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff := not_isPrincipal_iff

/--
theorem `isPrincipal_iff_of_monotone` / 定理 `isPrincipal_iff_of_monotone`

English:
theorem isPrincipal_iff_of_monotone
  proof: by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_gt a b
· exact (h₂ b hab).trans_lt H b hb
· exact (h₁ a hba.le).trans_lt H a ha

@[deprecated (since := "2026-03-17")]
alias principal_iff_of_monotone := isPrincipal_iff_of_monotone

中文:
定理 isPrincipal_iff_of_monotone
  证明: by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_gt a b
· exact (h₂ b hab).trans_lt H b hb
· exact (h₁ a hba.le).trans_lt H a ha

@[deprecated (since := "2026-03-17")]
alias principal_iff_of_monotone := isPrincipal_iff_of_monotone

Depends on / 依赖: hba.le, le_or_gt, trans_lt
-/
theorem isPrincipal_iff_of_monotone
    (h₁ : forall a, Monotone (op a)) (h₂ : forall a, Monotone (Function.swap op a)) :
    IsPrincipal op o ↔ forall a < o, op a a < o := by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_gt a b
· exact (h₂ b hab).trans_lt H b hb
· exact (h₁ a hba.le).trans_lt H a ha

@[deprecated (since := "2026-03-17")]
alias principal_iff_of_monotone := isPrincipal_iff_of_monotone

/--
theorem `not_isPrincipal_iff_of_monotone` / 定理 `not_isPrincipal_iff_of_monotone`

English:
theorem not_isPrincipal_iff_of_monotone
  proof: by
  simp [isPrincipal_iff_of_monotone h₁ h₂]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff_of_monotone := not_isPrincipal_iff_of_monotone

中文:
定理 not_isPrincipal_iff_of_monotone
  证明: by
  simp [isPrincipal_iff_of_monotone h₁ h₂]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff_of_monotone := not_isPrincipal_iff_of_monotone

Depends on / 依赖: isPrincipal_iff_of_monotone
-/
theorem not_isPrincipal_iff_of_monotone
    (h₁ : forall a, Monotone (op a)) (h₂ : forall a, Monotone (Function.swap op a)) :
    ¬ IsPrincipal op o ↔ exists a < o, o <= op a a := by
  simp [isPrincipal_iff_of_monotone h₁ h₂]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff_of_monotone := not_isPrincipal_iff_of_monotone

/--
lemma `isPrincipal_zero` / 引理 `isPrincipal_zero`

English:
lemma isPrincipal_zero
  statement: IsPrincipal op 0
  proof: by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_zero := isPrincipal_zero

中文:
引理 isPrincipal_zero
  结论: 是Principal op 0
  证明: by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_zero := isPrincipal_zero
-/
@[simp] lemma isPrincipal_zero : IsPrincipal op 0 := by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_zero := isPrincipal_zero

/--
theorem `isPrincipal_one_iff` / 定理 `isPrincipal_one_iff`

English:
theorem isPrincipal_one_iff
  statement: IsPrincipal op 1 ↔ op 0 0 = 0
  proof: by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_one_iff := isPrincipal_one_iff

中文:
定理 isPrincipal_one_iff
  结论: 是Principal op 1 ↔ op 0 0 = 0
  证明: by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_one_iff := isPrincipal_one_iff
-/
@[simp] theorem isPrincipal_one_iff : IsPrincipal op 1 ↔ op 0 0 = 0 := by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_one_iff := isPrincipal_one_iff

/--
theorem `IsPrincipal.iterate_lt` / 定理 `IsPrincipal.iterate_lt`

English:
theorem IsPrincipal.iterate_lt
  given: (hao : a < o) (ho : IsPrincipal op o) (n : Nat)
  proof: by
  induction n with
  | zero => rwa [Function.iterate_zero]
  | succ n hn =>
    rw [Function.iterate_succ']
    exact ho hao hn

@[deprecated (since := "2026-03-17")]
alias Principal.iterate_lt := IsPrincipal.iterate_lt

中文:
定理 是Principal.iterate_lt
  条件: (hao : a < o) (ho : 是Principal op o) (n : 自然数)
  证明: by
  induction n with
  | zero => rwa [Function.iterate_zero]
  | succ n hn =>
    rw [Function.iterate_succ']
    exact ho hao hn

@[deprecated (since := "2026-03-17")]
alias Principal.iterate_lt := IsPrincipal.iterate_lt

Depends on / 依赖: Function, Function.iterate_succ, Function.iterate_zero, iterate_succ, iterate_zero
-/
theorem IsPrincipal.iterate_lt (hao : a < o) (ho : IsPrincipal op o) (n : Nat) :
    (op a)^[n] a < o := by
  induction n with
  | zero => rwa [Function.iterate_zero]
  | succ n hn =>
    rw [Function.iterate_succ']
    exact ho hao hn

@[deprecated (since := "2026-03-17")]
alias Principal.iterate_lt := IsPrincipal.iterate_lt

/--
theorem `op_eq_self_of_isPrincipal` / 定理 `op_eq_self_of_isPrincipal`

English:
theorem op_eq_self_of_isPrincipal
  statement: (hao : a < o) (H : IsNormal (op a))
  proof: by
  apply H.strictMono.le_apply.antisymm'
  rw [H.apply_of_isSuccLimit ho']; rw [Ordinal.iSup_le_iff]
  exact fun ⟨b, hbo⟩ => (ho hao hbo).le

@[deprecated (since := "2026-03-17")]
alias op_eq_self_of_principal := op_eq_self_of_isPrincipal

中文:
定理 op_eq_self_of_isPrincipal
  结论: (hao : a < o) (H : 是正规 (op a))
  证明: by
  apply H.strictMono.le_apply.antisymm'
  rw [H.apply_of_isSuccLimit ho']; rw [Ordinal.iSup_le_iff]
  exact fun ⟨b, hbo⟩ => (ho hao hbo).le

@[deprecated (since := "2026-03-17")]
alias op_eq_self_of_principal := op_eq_self_of_isPrincipal

Depends on / 依赖: H.apply_of_isSuccLimit, H.strictMono.le_apply.antisymm, Ordinal, Ordinal.iSup_le_iff, antisymm, apply_of_isSuccLimit, iSup_le_iff, le_apply, strictMono
-/
theorem op_eq_self_of_isPrincipal (hao : a < o) (H : IsNormal (op a))
    (ho : IsPrincipal op o) (ho' : IsSuccLimit o) : op a o = o := by
  apply H.strictMono.le_apply.antisymm'
  rw [H.apply_of_isSuccLimit ho']; rw [Ordinal.iSup_le_iff]
  exact fun ⟨b, hbo⟩ => (ho hao hbo).le

@[deprecated (since := "2026-03-17")]
alias op_eq_self_of_principal := op_eq_self_of_isPrincipal

/--
theorem `nfp_le_of_isPrincipal` / 定理 `nfp_le_of_isPrincipal`

English:
theorem nfp_le_of_isPrincipal
  given: (hao : a < o) (ho : IsPrincipal op o)
  statement: nfp (op a) a <= o
  proof: nfp_le fun n => (ho.iterate_lt hao n).le

@[deprecated (since := "2026-03-17")]
alias nfp_le_of_principal := nfp_le_of_isPrincipal

中文:
定理 nfp_le_of_isPrincipal
  条件: (hao : a < o) (ho : 是Principal op o)
  结论: nfp (op a) a <= o
  证明: nfp_le fun n => (ho.iterate_lt hao n).le

@[deprecated (since := "2026-03-17")]
alias nfp_le_of_principal := nfp_le_of_isPrincipal

Depends on / 依赖: ho.iterate_lt, iterate_lt, nfp_le
-/
theorem nfp_le_of_isPrincipal (hao : a < o) (ho : IsPrincipal op o) : nfp (op a) a <= o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

@[deprecated (since := "2026-03-17")]
alias nfp_le_of_principal := nfp_le_of_isPrincipal

/--
theorem `IsPrincipal.sSup` / 定理 `IsPrincipal.sSup`

English:
theorem IsPrincipal.sSup
  given: {s : Set Ordinal} (H : forall x in s, IsPrincipal op x)
  proof: by
  have : IsPrincipal op (sSup ∅) := by simp
  by_cases hs : BddAbove s
  · obtain rfl | hs' := s.eq_empty_or_nonempty
    · assumption
    simp only [IsPrincipal, lt_csSup_iff hs hs', forall_exists_index, and_imp]
    intro x y a has ha b hbs hb
    have h : max a b in s := max_rec' _ has hbs
   

中文:
定理 是Principal.sSup
  条件: {s : 集合 序数} (H : 对任意 x in s, 是Principal op x)
  证明: by
  have : IsPrincipal op (sSup ∅) := by simp
  by_cases hs : BddAbove s
  · obtain rfl | hs' := s.eq_empty_or_nonempty
    · assumption
    simp only [IsPrincipal, lt_csSup_iff hs hs', forall_exists_index, and_imp]
    intro x y a has ha b hbs hb
    have h : max a b in s := max_rec' _ has hbs
   
-/
protected theorem IsPrincipal.sSup {s : Set Ordinal} (H : forall x in s, IsPrincipal op x) :
    IsPrincipal op (sSup s) := by
  have : IsPrincipal op (sSup ∅) := by simp
  by_cases hs : BddAbove s
  · obtain rfl | hs' := s.eq_empty_or_nonempty
    · assumption
    simp only [IsPrincipal, lt_csSup_iff hs hs', forall_exists_index, and_imp]
    intro x y a has ha b hbs hb
    have h : max a b in s := max_rec' _ has hbs
    exact ⟨_, h, H (max a b) h (lt_max_of_lt_left ha) (lt_max_of_lt_right hb)⟩
  · rwa [csSup_of_not_bddAbove hs]

@[deprecated (since := "2026-03-17")]
protected alias Principal.sSup := IsPrincipal.sSup

/--
theorem `IsPrincipal.iSup` / 定理 `IsPrincipal.iSup`

English:
theorem IsPrincipal.iSup
  given: {ι} {f : ι -> Ordinal} (H : forall i, IsPrincipal op (f i))
  proof: IsPrincipal.sSup (by simpa)

@[deprecated (since := "2026-03-17")]
protected alias Principal.iSup := IsPrincipal.iSup

中文:
定理 是Principal.iSup
  条件: {ι} {f : ι -> 序数} (H : 对任意 i, 是Principal op (f i))
  证明: IsPrincipal.sSup (by simpa)

@[deprecated (since := "2026-03-17")]
protected alias Principal.iSup := IsPrincipal.iSup
-/
protected theorem IsPrincipal.iSup {ι} {f : ι -> Ordinal} (H : forall i, IsPrincipal op (f i)) :
    IsPrincipal op (⨆ i, f i) := IsPrincipal.sSup (by simpa)

@[deprecated (since := "2026-03-17")]
protected alias Principal.iSup := IsPrincipal.iSup

end Arbitrary

/--
theorem `isPrincipal_nfp_iSup` / 定理 `isPrincipal_nfp_iSup`

English:
theorem isPrincipal_nfp_iSup
  given: (op : Ordinal -> Ordinal -> Ordinal) (o : Ordinal)
  proof: by
  intro a b ha hb
  rw [lt_nfp_iff] at *
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  obtain h | h := le_total
    ((fun x => ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[m] o)
    ((fun x => ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[n] o)
  · use n + 1
    rw [Function.it

中文:
定理 isPrincipal_nfp_iSup
  条件: (op : 序数 -> 序数 -> 序数) (o : 序数)
  证明: by
  intro a b ha hb
  rw [lt_nfp_iff] at *
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  obtain h | h := le_total
    ((fun x => ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[m] o)
    ((fun x => ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[n] o)
  · use n + 1
    rw [Function.it
-/
private theorem isPrincipal_nfp_iSup (op : Ordinal -> Ordinal -> Ordinal) (o : Ordinal) :
    IsPrincipal op (nfp (fun x => ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2)) o) := by
  intro a b ha hb
  rw [lt_nfp_iff] at *
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  obtain h | h := le_total
    ((fun x => ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[m] o)
    ((fun x => ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[n] o)
  · use n + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ => succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod (ha.trans_le h) hb⟩
  · use m + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ => succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod ha (hb.trans_le h)⟩

/--
theorem `not_bddAbove_setOfPred_isPrincipal` / 定理 `not_bddAbove_setOfPred_isPrincipal`

English:
theorem not_bddAbove_setOfPred_isPrincipal
  given: (op : Ordinal -> Ordinal -> Ordinal)
  proof: by
  rintro ⟨a, ha⟩
  exact ((le_nfp _ _).trans (ha (isPrincipal_nfp_iSup op (succ a)))).not_gt (lt_succ a)

@[deprecated (since := "2026-07-09")]
alias not_bddAbove_setOf_isPrincipal := not_bddAbove_setOfPred_isPrincipal

@[deprecated (since := "2026-03-17")]
alias not_bddAbove_principal := not_bdd

中文:
定理 not_bddAbove_setOfPred_isPrincipal
  条件: (op : 序数 -> 序数 -> 序数)
  证明: by
  rintro ⟨a, ha⟩
  exact ((le_nfp _ _).trans (ha (isPrincipal_nfp_iSup op (succ a)))).not_gt (lt_succ a)

@[deprecated (since := "2026-07-09")]
alias not_bddAbove_setOf_isPrincipal := not_bddAbove_setOfPred_isPrincipal

@[deprecated (since := "2026-03-17")]
alias not_bddAbove_principal := not_bdd

Depends on / 依赖: isPrincipal_nfp_iSup, le_nfp, lt_succ, not_gt
-/
theorem not_bddAbove_setOfPred_isPrincipal (op : Ordinal -> Ordinal -> Ordinal) :
    ¬ BddAbove { o | IsPrincipal op o } := by
  rintro ⟨a, ha⟩
  exact ((le_nfp _ _).trans (ha (isPrincipal_nfp_iSup op (succ a)))).not_gt (lt_succ a)

@[deprecated (since := "2026-07-09")]
alias not_bddAbove_setOf_isPrincipal := not_bddAbove_setOfPred_isPrincipal

@[deprecated (since := "2026-03-17")]
alias not_bddAbove_principal := not_bddAbove_setOfPred_isPrincipal


/--
theorem `isPrincipal_add_iff_add_self_lt` / 定理 `isPrincipal_add_iff_add_self_lt`

English:
theorem isPrincipal_add_iff_add_self_lt
  statement: IsPrincipal (· + ·) a ↔ forall b < a, b + b < a
  proof: isPrincipal_iff_of_monotone
    (fun x _ _ h => add_le_add_right h x) (fun x _ _ h => add_le_add_left h x)

中文:
定理 isPrincipal_add_iff_add_self_lt
  结论: 是Principal (· + ·) a ↔ 对任意 b < a, b + b < a
  证明: isPrincipal_iff_of_monotone
    (fun x _ _ h => add_le_add_right h x) (fun x _ _ h => add_le_add_left h x)

Depends on / 依赖: add_le_add_left, add_le_add_right, isPrincipal_iff_of_monotone
-/
theorem isPrincipal_add_iff_add_self_lt : IsPrincipal (· + ·) a ↔ forall b < a, b + b < a :=
  isPrincipal_iff_of_monotone
    (fun x _ _ h => add_le_add_right h x) (fun x _ _ h => add_le_add_left h x)

/--
theorem `IsPrincipal.mul_natCast_lt` / 定理 `IsPrincipal.mul_natCast_lt`

English:
theorem IsPrincipal.mul_natCast_lt
  given: (ho : IsPrincipal (· + ·) o) (ha : a < o) (n : Nat)
  proof: by
  induction n with
  | zero => simpa using ha.pos
  | succ n h =>
    rw [Nat.cast_add_one]; rw [mul_add_one]
    exact ho h ha

中文:
定理 是Principal.mul_natCast_lt
  条件: (ho : 是Principal (· + ·) o) (ha : a < o) (n : 自然数)
  证明: by
  induction n with
  | zero => simpa using ha.pos
  | succ n h =>
    rw [Nat.cast_add_one]; rw [mul_add_one]
    exact ho h ha

Depends on / 依赖: Nat.cast_add_one, cast_add_one, ha.pos, mul_add_one
-/
theorem IsPrincipal.mul_natCast_lt (ho : IsPrincipal (· + ·) o) (ha : a < o) (n : Nat) :
    a * n < o := by
  induction n with
  | zero => simpa using ha.pos
  | succ n h =>
    rw [Nat.cast_add_one]; rw [mul_add_one]
    exact ho h ha

/--
theorem `isPrincipal_add_one` / 定理 `isPrincipal_add_one`

English:
theorem isPrincipal_add_one
  statement: IsPrincipal (· + ·) 1
  proof: by simp

@[deprecated (since := "2026-03-17")]
alias principal_add_one := isPrincipal_add_one

中文:
定理 isPrincipal_add_one
  结论: 是Principal (· + ·) 1
  证明: by simp

@[deprecated (since := "2026-03-17")]
alias principal_add_one := isPrincipal_add_one
-/
theorem isPrincipal_add_one : IsPrincipal (· + ·) 1 := by simp

@[deprecated (since := "2026-03-17")]
alias principal_add_one := isPrincipal_add_one

/--
theorem `isPrincipal_add_of_le_one` / 定理 `isPrincipal_add_of_le_one`

English:
theorem isPrincipal_add_of_le_one
  given: (ho : o <= 1)
  statement: IsPrincipal (· + ·) o
  proof: by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact isPrincipal_zero
  · exact isPrincipal_add_one

@[deprecated (since := "2026-03-17")]
alias principal_add_of_le_one := isPrincipal_add_of_le_one

中文:
定理 isPrincipal_add_of_le_one
  条件: (ho : o <= 1)
  结论: 是Principal (· + ·) o
  证明: by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact isPrincipal_zero
  · exact isPrincipal_add_one

@[deprecated (since := "2026-03-17")]
alias principal_add_of_le_one := isPrincipal_add_of_le_one

Depends on / 依赖: isPrincipal_add_one, isPrincipal_zero, le_one_iff
-/
theorem isPrincipal_add_of_le_one (ho : o <= 1) : IsPrincipal (· + ·) o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact isPrincipal_zero
  · exact isPrincipal_add_one

@[deprecated (since := "2026-03-17")]
alias principal_add_of_le_one := isPrincipal_add_of_le_one

/--
theorem `isSuccLimit_of_isPrincipal_add` / 定理 `isSuccLimit_of_isPrincipal_add`

English:
theorem isSuccLimit_of_isPrincipal_add
  given: (ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o)
  proof: by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_lt]
  exact ⟨ho₁.ne_bot, fun _ ha => ho ha ho₁⟩

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_add := isSuccLimit_of_isPrincipal_add

中文:
定理 isSuccLimit_of_isPrincipal_add
  条件: (ho₁ : 1 < o) (ho : 是Principal (· + ·) o)
  证明: by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_lt]
  exact ⟨ho₁.ne_bot, fun _ ha => ho ha ho₁⟩

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_add := isSuccLimit_of_isPrincipal_add

Depends on / 依赖: isSuccLimit_iff, isSuccPrelimit_iff_succ_lt, ne_bot
-/
theorem isSuccLimit_of_isPrincipal_add (ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) :
    IsSuccLimit o := by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_lt]
  exact ⟨ho₁.ne_bot, fun _ ha => ho ha ho₁⟩

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_add := isSuccLimit_of_isPrincipal_add

/--
theorem `isPrincipal_add_iff_add_left_eq_self` / 定理 `isPrincipal_add_iff_add_left_eq_self`

English:
theorem isPrincipal_add_iff_add_left_eq_self
  statement: IsPrincipal (· + ·) o ↔ forall a < o, a + o = o
  proof: by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases lt_or_ge 1 o with ho₁ | ho₁
    · exact op_eq_self_of_isPrincipal hao (isNormal_add_right a) ho
        (isSuccLimit_of_isPrincipal_add ho₁ ho)
    · cases le_one_iff.1 ho₁ <;> simp_all
  · rw [← h a hao]
    exact (isNormal_add_ri

中文:
定理 isPrincipal_add_iff_add_left_eq_self
  结论: 是Principal (· + ·) o ↔ 对任意 a < o, a + o = o
  证明: by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases lt_or_ge 1 o with ho₁ | ho₁
    · exact op_eq_self_of_isPrincipal hao (isNormal_add_right a) ho
        (isSuccLimit_of_isPrincipal_add ho₁ ho)
    · cases le_one_iff.1 ho₁ <;> simp_all
  · rw [← h a hao]
    exact (isNormal_add_ri

Depends on / 依赖: isNormal_add_right, isSuccLimit_of_isPrincipal_add, le_one_iff, lt_or_ge, op_eq_self_of_isPrincipal, strictMono
-/
theorem isPrincipal_add_iff_add_left_eq_self : IsPrincipal (· + ·) o ↔ forall a < o, a + o = o := by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases lt_or_ge 1 o with ho₁ | ho₁
    · exact op_eq_self_of_isPrincipal hao (isNormal_add_right a) ho
        (isSuccLimit_of_isPrincipal_add ho₁ ho)
    · cases le_one_iff.1 ho₁ <;> simp_all
  · rw [← h a hao]
    exact (isNormal_add_right a).strictMono hbo

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_left_eq_self := isPrincipal_add_iff_add_left_eq_self

/--
theorem `IsPrincipal.add_eq_right` / 定理 `IsPrincipal.add_eq_right`

English:
theorem IsPrincipal.add_eq_right
  given: (ho : IsPrincipal (· + ·) o) (ha : a < o)
  statement: a + o = o
  proof: isPrincipal_add_iff_add_left_eq_self.1 ho a ha

中文:
定理 是Principal.add_eq_right
  条件: (ho : 是Principal (· + ·) o) (ha : a < o)
  结论: a + o = o
  证明: isPrincipal_add_iff_add_left_eq_self.1 ho a ha

Depends on / 依赖: isPrincipal_add_iff_add_left_eq_self
-/
theorem IsPrincipal.add_eq_right (ho : IsPrincipal (· + ·) o) (ha : a < o) : a + o = o :=
  isPrincipal_add_iff_add_left_eq_self.1 ho a ha

/--
theorem `IsPrincipal.add_eq_right_of_le` / 定理 `IsPrincipal.add_eq_right_of_le`

English:
theorem IsPrincipal.add_eq_right_of_le
  statement: (hb : IsPrincipal (· + ·) b)
  proof: by
  rw [← Ordinal.add_sub_cancel_of_le hbc]; rw [← add_assoc]; rw [hb.add_eq_right hab]; rw [Ordinal.add_sub_cancel_of_le hbc]

中文:
定理 是Principal.add_eq_right_of_le
  结论: (hb : 是Principal (· + ·) b)
  证明: by
  rw [← Ordinal.add_sub_cancel_of_le hbc]; rw [← add_assoc]; rw [hb.add_eq_right hab]; rw [Ordinal.add_sub_cancel_of_le hbc]

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_assoc, add_eq_right, add_sub_cancel_of_le, hb.add_eq_right
-/
theorem IsPrincipal.add_eq_right_of_le (hb : IsPrincipal (· + ·) b)
    (hab : a < b) (hbc : b <= c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le hbc]; rw [← add_assoc]; rw [hb.add_eq_right hab]; rw [Ordinal.add_sub_cancel_of_le hbc]

/--
theorem `exists_lt_add_of_not_isPrincipal_add` / 定理 `exists_lt_add_of_not_isPrincipal_add`

English:
theorem exists_lt_add_of_not_isPrincipal_add
  given: (ha : ¬ IsPrincipal (· + ·) a)
  proof: by
  rw [not_isPrincipal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le]; rw [hab] at H
  exact H.not_gt hc

@[deprecated (since := "2026-03-17")]
alias exists_lt_add_of_not_prin

中文:
定理 存在_lt_add_of_not_isPrincipal_add
  条件: (ha : ¬ 是Principal (· + ·) a)
  证明: by
  rw [not_isPrincipal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le]; rw [hab] at H
  exact H.not_gt hc

@[deprecated (since := "2026-03-17")]
alias exists_lt_add_of_not_prin

Depends on / 依赖: H.not_gt, Ordinal, Ordinal.add_sub_cancel_of_le, add_sub_cancel_of_le, hb.le, lt_of_le_of_ne, not_gt, not_isPrincipal_iff, sub_le, sub_le_self
-/
theorem exists_lt_add_of_not_isPrincipal_add (ha : ¬ IsPrincipal (· + ·) a) :
    exists b < a, exists c < a, b + c = a := by
  rw [not_isPrincipal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le]; rw [hab] at H
  exact H.not_gt hc

@[deprecated (since := "2026-03-17")]
alias exists_lt_add_of_not_principal_add := exists_lt_add_of_not_isPrincipal_add

/--
theorem `isPrincipal_add_iff_add_lt_ne_self` / 定理 `isPrincipal_add_iff_add_lt_ne_self`

English:
theorem isPrincipal_add_iff_add_lt_ne_self
  statement: IsPrincipal (· + ·) a ↔ forall b < a, forall c < a, b + c != a
  proof: ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra ha
    rcases exists_lt_add_of_not_isPrincipal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_lt_ne_self := isPrincipal_add_iff_add_lt_ne_self

中文:
定理 isPrincipal_add_iff_add_lt_ne_self
  结论: 是Principal (· + ·) a ↔ 对任意 b < a, 对任意 c < a, b + c != a
  证明: ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra ha
    rcases exists_lt_add_of_not_isPrincipal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_lt_ne_self := isPrincipal_add_iff_add_lt_ne_self

Depends on / 依赖: exists_lt_add_of_not_isPrincipal_add, irrefl
-/
theorem isPrincipal_add_iff_add_lt_ne_self : IsPrincipal (· + ·) a ↔ forall b < a, forall c < a, b + c != a :=
  ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra ha
    rcases exists_lt_add_of_not_isPrincipal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_lt_ne_self := isPrincipal_add_iff_add_lt_ne_self

/--
theorem `isPrincipal_add_omega0` / 定理 `isPrincipal_add_omega0`

English:
theorem isPrincipal_add_omega0
  statement: IsPrincipal (· + ·) ω
  proof: isPrincipal_add_iff_add_left_eq_self.2 fun _ => add_omega0

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0 := isPrincipal_add_omega0

中文:
定理 isPrincipal_add_omega0
  结论: 是Principal (· + ·) ω
  证明: isPrincipal_add_iff_add_left_eq_self.2 fun _ => add_omega0

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0 := isPrincipal_add_omega0

Depends on / 依赖: add_omega0, isPrincipal_add_iff_add_left_eq_self
-/
theorem isPrincipal_add_omega0 : IsPrincipal (· + ·) ω :=
  isPrincipal_add_iff_add_left_eq_self.2 fun _ => add_omega0

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0 := isPrincipal_add_omega0

-- `add_omega0` is proven in the Arithmetic file.

/--
theorem `add_of_omega0_le` / 定理 `add_of_omega0_le`

English:
theorem add_of_omega0_le
  statement: a < ω -> ω <= b -> a + b = b
  proof: isPrincipal_add_omega0.add_eq_right_of_le

中文:
定理 add_of_omega0_le
  结论: a < ω -> ω <= b -> a + b = b
  证明: isPrincipal_add_omega0.add_eq_right_of_le

Depends on / 依赖: add_eq_right_of_le, isPrincipal_add_omega0, isPrincipal_add_omega0.add_eq_right_of_le
-/
theorem add_of_omega0_le : a < ω -> ω <= b -> a + b = b :=
  isPrincipal_add_omega0.add_eq_right_of_le

/--
theorem `isPrincipal_add_omega0_opow` / 定理 `isPrincipal_add_omega0_opow`

English:
theorem isPrincipal_add_omega0_opow
  given: (o : Ordinal)
  statement: IsPrincipal (· + ·) (ω ^ o)
  proof: by
  obtain rfl | ha' := eq_or_ne o 0
  · rw [opow_zero, isPrincipal_one_iff, add_zero]
  · rw [isPrincipal_add_iff_add_self_lt]
    intro a ha
    obtain ⟨c, hc, m, hm⟩ := (lt_omega0_opow ha').1 ha
    apply (add_lt_add_of_le_of_lt hm.le hm).trans_le
    rw [← mul_add]; rw [← Nat.cast_add]
    exac

中文:
定理 isPrincipal_add_omega0_opow
  条件: (o : 序数)
  结论: 是Principal (· + ·) (ω ^ o)
  证明: by
  obtain rfl | ha' := eq_or_ne o 0
  · rw [opow_zero, isPrincipal_one_iff, add_zero]
  · rw [isPrincipal_add_iff_add_self_lt]
    intro a ha
    obtain ⟨c, hc, m, hm⟩ := (lt_omega0_opow ha').1 ha
    apply (add_lt_add_of_le_of_lt hm.le hm).trans_le
    rw [← mul_add]; rw [← Nat.cast_add]
    exac

Depends on / 依赖: Nat.cast_add, add_lt_add_of_le_of_lt, add_zero, cast_add, eq_or_ne, hm.le, isPrincipal_add_iff_add_self_lt, isPrincipal_one_iff, lt_omega0_opow, mul_add, natCast_lt_omega0, opow_mul_lt_opow, opow_zero, trans_le
-/
theorem isPrincipal_add_omega0_opow (o : Ordinal) : IsPrincipal (· + ·) (ω ^ o) := by
  obtain rfl | ha' := eq_or_ne o 0
  · rw [opow_zero, isPrincipal_one_iff, add_zero]
  · rw [isPrincipal_add_iff_add_self_lt]
    intro a ha
    obtain ⟨c, hc, m, hm⟩ := (lt_omega0_opow ha').1 ha
    apply (add_lt_add_of_le_of_lt hm.le hm).trans_le
    rw [← mul_add]; rw [← Nat.cast_add]
    exact (opow_mul_lt_opow (natCast_lt_omega0 _) hc).le

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0_opow := isPrincipal_add_omega0_opow

/--
theorem `add_omega0_opow` / 定理 `add_omega0_opow`

English:
theorem add_omega0_opow
  given: (h : a < ω ^ b)
  statement: a + ω ^ b = ω ^ b
  proof: (isPrincipal_add_omega0_opow b).add_eq_right h

中文:
定理 add_omega0_opow
  条件: (h : a < ω ^ b)
  结论: a + ω ^ b = ω ^ b
  证明: (isPrincipal_add_omega0_opow b).add_eq_right h

Depends on / 依赖: add_eq_right, isPrincipal_add_omega0_opow
-/
theorem add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b :=
  (isPrincipal_add_omega0_opow b).add_eq_right h

/--
theorem `add_of_omega0_opow_le` / 定理 `add_of_omega0_opow_le`

English:
theorem add_of_omega0_opow_le
  given: (h₁ : a < ω ^ b) (h₂ : ω ^ b <= c)
  statement: a + c = c
  proof: (isPrincipal_add_omega0_opow b).add_eq_right_of_le h₁ h₂

@[deprecated (since := "2026-03-18")]
alias add_absorp := add_of_omega0_opow_le

中文:
定理 add_of_omega0_opow_le
  条件: (h₁ : a < ω ^ b) (h₂ : ω ^ b <= c)
  结论: a + c = c
  证明: (isPrincipal_add_omega0_opow b).add_eq_right_of_le h₁ h₂

@[deprecated (since := "2026-03-18")]
alias add_absorp := add_of_omega0_opow_le

Depends on / 依赖: add_eq_right_of_le, isPrincipal_add_omega0_opow
-/
theorem add_of_omega0_opow_le (h₁ : a < ω ^ b) (h₂ : ω ^ b <= c) : a + c = c :=
  (isPrincipal_add_omega0_opow b).add_eq_right_of_le h₁ h₂

@[deprecated (since := "2026-03-18")]
alias add_absorp := add_of_omega0_opow_le

/--
theorem `isLeast_sub_lt_omega0_opow_log` / 定理 `isLeast_sub_lt_omega0_opow_log`

English:
theorem isLeast_sub_lt_omega0_opow_log
  given: (h : a != 0)
  statement: IsLeast {b | a - b < a} (ω ^ log ω a)
  proof: by
  refine ⟨sub_omega0_opow_log_lt h, fun c (hc : a - _ < _) => ?_⟩
  contrapose! hc
  exact le_sub_of_add_le (add_of_omega0_opow_le hc (opow_log_le_self ω h)).le

中文:
定理 isLeast_sub_lt_omega0_opow_log
  条件: (h : a != 0)
  结论: IsLeast {b | a - b < a} (ω ^ log ω a)
  证明: by
  refine ⟨sub_omega0_opow_log_lt h, fun c (hc : a - _ < _) => ?_⟩
  contrapose! hc
  exact le_sub_of_add_le (add_of_omega0_opow_le hc (opow_log_le_self ω h)).le

Depends on / 依赖: add_of_omega0_opow_le, contrapose, le_sub_of_add_le, opow_log_le_self, sub_omega0_opow_log_lt
-/
theorem isLeast_sub_lt_omega0_opow_log (h : a != 0) : IsLeast {b | a - b < a} (ω ^ log ω a) := by
  refine ⟨sub_omega0_opow_log_lt h, fun c (hc : a - _ < _) => ?_⟩
  contrapose! hc
  exact le_sub_of_add_le (add_of_omega0_opow_le hc (opow_log_le_self ω h)).le

/--
theorem `isPrincipal_add_iff_zero_or_omega0_opow` / 定理 `isPrincipal_add_iff_zero_or_omega0_opow`

English:
theorem isPrincipal_add_iff_zero_or_omega0_opow
  proof: by
  constructor
  · rw [or_iff_not_imp_left]
    refine fun H ho => ⟨log ω o, (opow_log_le_self ω ho).eq_of_not_lt ?_⟩
    obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 o)
exact fun h => hn.not_gt H.mul_natCast_lt h n
  · rintro (rfl | ⟨a, rfl⟩)
    exacts [isPrincipa

中文:
定理 isPrincipal_add_iff_zero_or_omega0_opow
  证明: by
  constructor
  · rw [or_iff_not_imp_left]
    refine fun H ho => ⟨log ω o, (opow_log_le_self ω ho).eq_of_not_lt ?_⟩
    obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 o)
exact fun h => hn.not_gt H.mul_natCast_lt h n
  · rintro (rfl | ⟨a, rfl⟩)
    exacts [isPrincipa

Depends on / 依赖: H.mul_natCast_lt, eq_of_not_lt, exacts, hn.not_gt, isPrincipal_add_omega0_opow, isPrincipal_zero, lt_omega0_opow_succ, lt_opow_succ_log_self, mul_natCast_lt, not_gt, one_lt_omega0, opow_log_le_self, or_iff_not_imp_left
-/
theorem isPrincipal_add_iff_zero_or_omega0_opow :
    IsPrincipal (· + ·) o ↔ o = 0 ∨ o in Set.range (ω ^ · : Ordinal -> Ordinal) := by
  constructor
  · rw [or_iff_not_imp_left]
    refine fun H ho => ⟨log ω o, (opow_log_le_self ω ho).eq_of_not_lt ?_⟩
    obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 o)
exact fun h => hn.not_gt H.mul_natCast_lt h n
  · rintro (rfl | ⟨a, rfl⟩)
    exacts [isPrincipal_zero, isPrincipal_add_omega0_opow a]

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_zero_or_omega0_opow := isPrincipal_add_iff_zero_or_omega0_opow

/--
theorem `isPrincipal_add_opow_of_isPrincipal_add` / 定理 `isPrincipal_add_opow_of_isPrincipal_add`

English:
theorem isPrincipal_add_opow_of_isPrincipal_add
  given: {a} (ha : IsPrincipal (· + ·) a) (b : Ordinal)
  proof: by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact isPrincipal_add_one
    · rwa [zero_opow hb]
  · rw [← opow_mul]
    exact isPrincipal_add_omega0_opow _

@[deprecated (since := "2026-03-17")]
alia

中文:
定理 isPrincipal_add_opow_of_isPrincipal_add
  条件: {a} (ha : 是Principal (· + ·) a) (b : 序数)
  证明: by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact isPrincipal_add_one
    · rwa [zero_opow hb]
  · rw [← opow_mul]
    exact isPrincipal_add_omega0_opow _

@[deprecated (since := "2026-03-17")]
alia

Depends on / 依赖: eq_or_ne, isPrincipal_add_iff_zero_or_omega0_opow, isPrincipal_add_omega0_opow, isPrincipal_add_one, opow_mul, opow_zero, zero_opow
-/
theorem isPrincipal_add_opow_of_isPrincipal_add {a} (ha : IsPrincipal (· + ·) a) (b : Ordinal) :
    IsPrincipal (· + ·) (a ^ b) := by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact isPrincipal_add_one
    · rwa [zero_opow hb]
  · rw [← opow_mul]
    exact isPrincipal_add_omega0_opow _

@[deprecated (since := "2026-03-17")]
alias principal_add_opow_of_principal_add := isPrincipal_add_opow_of_isPrincipal_add

/--
theorem `isPrincipal_add_mul_of_isPrincipal_add` / 定理 `isPrincipal_add_mul_of_isPrincipal_add`

English:
theorem isPrincipal_add_mul_of_isPrincipal_add
  statement: (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b != 1)
  proof: by
  rcases eq_zero_or_pos a with (rfl | _)
  · rw [zero_mul]
    exact isPrincipal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact isPrincipal_zero
    · rw [← one_le_iff_pos] at hb₁'
      intro c d hc hd
      rw [lt_mul_iff_of_isSuccLimit
        (isSuccLimit_o

中文:
定理 isPrincipal_add_mul_of_isPrincipal_add
  结论: (a : 序数.{u}) {b : 序数.{u}} (hb₁ : b != 1)
  证明: by
  rcases eq_zero_or_pos a with (rfl | _)
  · rw [zero_mul]
    exact isPrincipal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact isPrincipal_zero
    · rw [← one_le_iff_pos] at hb₁'
      intro c d hc hd
      rw [lt_mul_iff_of_isSuccLimit
        (isSuccLimit_o

Depends on / 依赖: Left.add_lt_add, add_lt_add, eq_zero_or_pos, isPrincipal_zero, isSuccLimit_of_isPrincipal_add, lt_mul_iff_of_isSuccLimit, lt_of_le_of_ne, mul_add, mul_zero, one_le_iff_pos, zero_mul
-/
theorem isPrincipal_add_mul_of_isPrincipal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b != 1)
    (hb : IsPrincipal (· + ·) b) : IsPrincipal (· + ·) (a * b) := by
  rcases eq_zero_or_pos a with (rfl | _)
  · rw [zero_mul]
    exact isPrincipal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact isPrincipal_zero
    · rw [← one_le_iff_pos] at hb₁'
      intro c d hc hd
      rw [lt_mul_iff_of_isSuccLimit
        (isSuccLimit_of_isPrincipal_add (lt_of_le_of_ne hb₁' hb₁.symm) hb)] at *
      rcases hc with ⟨x, hx, hx'⟩
      rcases hd with ⟨y, hy, hy'⟩
      use x + y, hb hx hy
      rw [mul_add]
      exact Left.add_lt_add hx' hy'

@[deprecated (since := "2026-03-17")]
alias principal_add_mul_of_principal_add := isPrincipal_add_mul_of_isPrincipal_add


/--
theorem `isPrincipal_mul_one` / 定理 `isPrincipal_mul_one`

English:
theorem isPrincipal_mul_one
  statement: IsPrincipal (· * ·) 1
  proof: by simp

@[deprecated (since := "2026-03-17")]
alias principal_mul_one := isPrincipal_mul_one

中文:
定理 isPrincipal_mul_one
  结论: 是Principal (· * ·) 1
  证明: by simp

@[deprecated (since := "2026-03-17")]
alias principal_mul_one := isPrincipal_mul_one
-/
theorem isPrincipal_mul_one : IsPrincipal (· * ·) 1 := by simp

@[deprecated (since := "2026-03-17")]
alias principal_mul_one := isPrincipal_mul_one

/--
theorem `isPrincipal_mul_two` / 定理 `isPrincipal_mul_two`

English:
theorem isPrincipal_mul_two
  statement: IsPrincipal (· * ·) 2
  proof: by
  intro a b ha hb
  rw [lt_two_iff] at *
  simpa using mul_le_mul' ha hb

@[deprecated (since := "2026-03-17")]
alias principal_mul_two := isPrincipal_mul_two

中文:
定理 isPrincipal_mul_two
  结论: 是Principal (· * ·) 2
  证明: by
  intro a b ha hb
  rw [lt_two_iff] at *
  simpa using mul_le_mul' ha hb

@[deprecated (since := "2026-03-17")]
alias principal_mul_two := isPrincipal_mul_two

Depends on / 依赖: lt_two_iff, mul_le_mul
-/
theorem isPrincipal_mul_two : IsPrincipal (· * ·) 2 := by
  intro a b ha hb
  rw [lt_two_iff] at *
  simpa using mul_le_mul' ha hb

@[deprecated (since := "2026-03-17")]
alias principal_mul_two := isPrincipal_mul_two

/--
theorem `isPrincipal_mul_of_le_two` / 定理 `isPrincipal_mul_of_le_two`

English:
theorem isPrincipal_mul_of_le_two
  given: (ho : o <= 2)
  statement: IsPrincipal (· * ·) o
  proof: by
  obtain rfl | rfl | rfl := le_two_iff.1 ho
  exacts [isPrincipal_zero, isPrincipal_mul_one, isPrincipal_mul_two]

@[deprecated (since := "2026-03-17")]
alias principal_mul_of_le_two := isPrincipal_mul_of_le_two

中文:
定理 isPrincipal_mul_of_le_two
  条件: (ho : o <= 2)
  结论: 是Principal (· * ·) o
  证明: by
  obtain rfl | rfl | rfl := le_two_iff.1 ho
  exacts [isPrincipal_zero, isPrincipal_mul_one, isPrincipal_mul_two]

@[deprecated (since := "2026-03-17")]
alias principal_mul_of_le_two := isPrincipal_mul_of_le_two

Depends on / 依赖: exacts, isPrincipal_mul_one, isPrincipal_mul_two, isPrincipal_zero, le_two_iff
-/
theorem isPrincipal_mul_of_le_two (ho : o <= 2) : IsPrincipal (· * ·) o := by
  obtain rfl | rfl | rfl := le_two_iff.1 ho
  exacts [isPrincipal_zero, isPrincipal_mul_one, isPrincipal_mul_two]

@[deprecated (since := "2026-03-17")]
alias principal_mul_of_le_two := isPrincipal_mul_of_le_two

/--
theorem `isPrincipal_add_of_isPrincipal_mul` / 定理 `isPrincipal_add_of_isPrincipal_mul`

English:
theorem isPrincipal_add_of_isPrincipal_mul
  given: (ho : IsPrincipal (· * ·) o) (ho₂ : o != 2)
  proof: by
  rcases lt_or_gt_of_ne ho₂ with ho₁ | ho₂
· exact isPrincipal_add_of_le_one lt_two_iff.mp ho₁
  · simp_rw [isPrincipal_add_iff_add_self_lt, ← Ordinal.mul_two]
    exact fun a ha => ho ha ho₂

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul := isPrincipal_add_of_isPrinc

中文:
定理 isPrincipal_add_of_isPrincipal_mul
  条件: (ho : 是Principal (· * ·) o) (ho₂ : o != 2)
  证明: by
  rcases lt_or_gt_of_ne ho₂ with ho₁ | ho₂
· exact isPrincipal_add_of_le_one lt_two_iff.mp ho₁
  · simp_rw [isPrincipal_add_iff_add_self_lt, ← Ordinal.mul_two]
    exact fun a ha => ho ha ho₂

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul := isPrincipal_add_of_isPrinc

Depends on / 依赖: Ordinal, Ordinal.mul_two, isPrincipal_add_iff_add_self_lt, isPrincipal_add_of_le_one, lt_or_gt_of_ne, lt_two_iff, lt_two_iff.mp, mul_two, simp_rw
-/
theorem isPrincipal_add_of_isPrincipal_mul (ho : IsPrincipal (· * ·) o) (ho₂ : o != 2) :
    IsPrincipal (· + ·) o := by
  rcases lt_or_gt_of_ne ho₂ with ho₁ | ho₂
· exact isPrincipal_add_of_le_one lt_two_iff.mp ho₁
  · simp_rw [isPrincipal_add_iff_add_self_lt, ← Ordinal.mul_two]
    exact fun a ha => ho ha ho₂

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul := isPrincipal_add_of_isPrincipal_mul

/--
theorem `isSuccLimit_of_isPrincipal_mul` / 定理 `isSuccLimit_of_isPrincipal_mul`

English:
theorem isSuccLimit_of_isPrincipal_mul
  given: (ho₂ : 2 < o) (ho : IsPrincipal (· * ·) o)
  statement: IsSuccLimit o
  proof: isSuccLimit_of_isPrincipal_add (one_lt_two.trans ho₂)
    (isPrincipal_add_of_isPrincipal_mul ho (ne_of_gt ho₂))

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_mul := isSuccLimit_of_isPrincipal_mul

中文:
定理 isSuccLimit_of_isPrincipal_mul
  条件: (ho₂ : 2 < o) (ho : 是Principal (· * ·) o)
  结论: 是SuccLimit o
  证明: isSuccLimit_of_isPrincipal_add (one_lt_two.trans ho₂)
    (isPrincipal_add_of_isPrincipal_mul ho (ne_of_gt ho₂))

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_mul := isSuccLimit_of_isPrincipal_mul

Depends on / 依赖: isPrincipal_add_of_isPrincipal_mul, isSuccLimit_of_isPrincipal_add, ne_of_gt, one_lt_two, one_lt_two.trans
-/
theorem isSuccLimit_of_isPrincipal_mul (ho₂ : 2 < o) (ho : IsPrincipal (· * ·) o) : IsSuccLimit o :=
  isSuccLimit_of_isPrincipal_add (one_lt_two.trans ho₂)
    (isPrincipal_add_of_isPrincipal_mul ho (ne_of_gt ho₂))

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_mul := isSuccLimit_of_isPrincipal_mul

/--
theorem `isPrincipal_mul_iff_mul_left_eq` / 定理 `isPrincipal_mul_iff_mul_left_eq`

English:
theorem isPrincipal_mul_iff_mul_left_eq
  proof: by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases le_or_gt o 2 with ho | ho
    · convert! one_mul o
      apply le_antisymm
      · rw [← lt_add_one_iff, one_add_one_eq_two]
        exact hao.trans_le ho
      · rwa [one_le_iff_pos]
    · exact op_eq_self_of_isPrincipal hao (i

中文:
定理 isPrincipal_mul_iff_mul_left_eq
  证明: by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases le_or_gt o 2 with ho | ho
    · convert! one_mul o
      apply le_antisymm
      · rw [← lt_add_one_iff, one_add_one_eq_two]
        exact hao.trans_le ho
      · rwa [one_le_iff_pos]
    · exact op_eq_self_of_isPrincipal hao (i

Depends on / 依赖: convert, eq_or_ne, hao.trans_le, isNormal_mul_right, isSuccLimit_of_isPrincipal_mul, le_antisymm, le_or_gt, lt_add_one_iff, one_add_one_eq_two, one_le_iff_pos, one_mul, op_eq_self_of_isPrincipal, pos_iff_ne_zero, strictMono, trans_le, zero_mul
-/
theorem isPrincipal_mul_iff_mul_left_eq :
    IsPrincipal (· * ·) o ↔ forall a, 0 < a -> a < o -> a * o = o := by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases le_or_gt o 2 with ho | ho
    · convert! one_mul o
      apply le_antisymm
      · rw [← lt_add_one_iff, one_add_one_eq_two]
        exact hao.trans_le ho
      · rwa [one_le_iff_pos]
    · exact op_eq_self_of_isPrincipal hao (isNormal_mul_right ha₀) h
        (isSuccLimit_of_isPrincipal_mul ho h)
  · rcases eq_or_ne a 0 with (rfl | ha)
    · dsimp only; rwa [zero_mul]
    rw [← pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (isNormal_mul_right ha).strictMono hbo

@[deprecated (since := "2026-03-17")]
alias principal_mul_iff_mul_left_eq := isPrincipal_mul_iff_mul_left_eq

/--
theorem `isPrincipal_mul_omega0` / 定理 `isPrincipal_mul_omega0`

English:
theorem isPrincipal_mul_omega0
  statement: IsPrincipal (· * ·) ω
  proof: fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply natCast_lt_omega0

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0 := isPrincipal_mul_omega0

中文:
定理 isPrincipal_mul_omega0
  结论: 是Principal (· * ·) ω
  证明: fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply natCast_lt_omega0

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0 := isPrincipal_mul_omega0
-/
theorem isPrincipal_mul_omega0 : IsPrincipal (· * ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply natCast_lt_omega0

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0 := isPrincipal_mul_omega0

/--
theorem `mul_omega0` / 定理 `mul_omega0`

English:
theorem mul_omega0
  given: (a0 : 0 < a) (ha : a < ω)
  statement: a * ω = ω
  proof: isPrincipal_mul_iff_mul_left_eq.1 isPrincipal_mul_omega0 a a0 ha

中文:
定理 mul_omega0
  条件: (a0 : 0 < a) (ha : a < ω)
  结论: a * ω = ω
  证明: isPrincipal_mul_iff_mul_left_eq.1 isPrincipal_mul_omega0 a a0 ha

Depends on / 依赖: isPrincipal_mul_iff_mul_left_eq, isPrincipal_mul_omega0
-/
theorem mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω :=
  isPrincipal_mul_iff_mul_left_eq.1 isPrincipal_mul_omega0 a a0 ha

/--
theorem `natCast_mul_omega0` / 定理 `natCast_mul_omega0`

English:
theorem natCast_mul_omega0
  given: {n : Nat} (hn : 0 < n)
  statement: n * ω = ω
  proof: mul_omega0 (mod_cast hn) (natCast_lt_omega0 n)

中文:
定理 natCast_mul_omega0
  条件: {n : 自然数} (hn : 0 < n)
  结论: n * ω = ω
  证明: mul_omega0 (mod_cast hn) (natCast_lt_omega0 n)

Depends on / 依赖: mod_cast, mul_omega0, natCast_lt_omega0
-/
theorem natCast_mul_omega0 {n : Nat} (hn : 0 < n) : n * ω = ω :=
  mul_omega0 (mod_cast hn) (natCast_lt_omega0 n)

/--
theorem `mul_lt_omega0_opow` / 定理 `mul_lt_omega0_opow`

English:
theorem mul_lt_omega0_opow
  given: (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω)
  statement: a * b < ω ^ c
  proof: by
  rcases zero_or_succ_or_isSuccLimit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irrefl _).elim c0
  · rw [opow_succ] at ha
    obtain ⟨n, hn, an⟩ :=
      ((isNormal_mul_right <| opow_pos _ omega0_pos).lt_iff_exists_lt isSuccLimit_omega0).1 ha
    grw [an, opow_succ, mul_assoc]
    gcongr
    exac

中文:
定理 mul_lt_omega0_opow
  条件: (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω)
  结论: a * b < ω ^ c
  证明: by
  rcases zero_or_succ_or_isSuccLimit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irrefl _).elim c0
  · rw [opow_succ] at ha
    obtain ⟨n, hn, an⟩ :=
      ((isNormal_mul_right <| opow_pos _ omega0_pos).lt_iff_exists_lt isSuccLimit_omega0).1 ha
    grw [an, opow_succ, mul_assoc]
    gcongr
    exac

Depends on / 依赖: exacts, isNormal_mul_right, isNormal_opow, isPrincipal_mul_omega0, isSuccLimit_omega0, le_of_lt, lt_iff_exists_lt, lt_irrefl, mul_assoc, mul_le_mul, omega0_pos, one_lt_omega0, opow_l, opow_pos, opow_succ, trans_lt, zero_or_succ_or_isSuccLimit
-/
theorem mul_lt_omega0_opow (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω) : a * b < ω ^ c := by
  rcases zero_or_succ_or_isSuccLimit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irrefl _).elim c0
  · rw [opow_succ] at ha
    obtain ⟨n, hn, an⟩ :=
      ((isNormal_mul_right <| opow_pos _ omega0_pos).lt_iff_exists_lt isSuccLimit_omega0).1 ha
    grw [an, opow_succ, mul_assoc]
    gcongr
    exacts [opow_pos _ omega0_pos, isPrincipal_mul_omega0 hn hb]
  · rcases ((isNormal_opow one_lt_omega0).lt_iff_exists_lt l).1 ha with ⟨x, hx, ax⟩
    refine (mul_le_mul' (le_of_lt ax) (le_of_lt hb)).trans_lt ?_
    rw [← opow_succ]; rw [opow_lt_opow_iff_right one_lt_omega0]
    exact l.succ_lt hx

/--
theorem `mul_omega0_opow_opow` / 定理 `mul_omega0_opow_opow`

English:
theorem mul_omega0_opow_opow
  given: (a0 : 0 < a) (h : a < ω ^ ω ^ b)
  statement: a * ω ^ ω ^ b = ω ^ ω ^ b
  proof: by
  obtain rfl | b0 := eq_or_ne b 0
  · rw [opow_zero, opow_one] at h ⊢
    exact mul_omega0 a0 h
  · apply le_antisymm
    · obtain ⟨x, xb, ax⟩ :=
        (lt_opow_of_isSuccLimit omega0_ne_zero (isSuccLimit_opow_left isSuccLimit_omega0 b0)).1 h
      grw [ax, ← opow_add, add_omega0_opow xb]
    · 

中文:
定理 mul_omega0_opow_opow
  条件: (a0 : 0 < a) (h : a < ω ^ ω ^ b)
  结论: a * ω ^ ω ^ b = ω ^ ω ^ b
  证明: by
  obtain rfl | b0 := eq_or_ne b 0
  · rw [opow_zero, opow_one] at h ⊢
    exact mul_omega0 a0 h
  · apply le_antisymm
    · obtain ⟨x, xb, ax⟩ :=
        (lt_opow_of_isSuccLimit omega0_ne_zero (isSuccLimit_opow_left isSuccLimit_omega0 b0)).1 h
      grw [ax, ← opow_add, add_omega0_opow xb]
    · 

Depends on / 依赖: add_omega0_opow, conv_lhs, eq_or_ne, isSuccLimit_omega0, isSuccLimit_opow_left, le_antisymm, lt_opow_of_isSuccLimit, mul_omega0, omega0_ne_zero, one_le_iff_pos, one_mul, opow_add, opow_one, opow_zero
-/
theorem mul_omega0_opow_opow (a0 : 0 < a) (h : a < ω ^ ω ^ b) : a * ω ^ ω ^ b = ω ^ ω ^ b := by
  obtain rfl | b0 := eq_or_ne b 0
  · rw [opow_zero, opow_one] at h ⊢
    exact mul_omega0 a0 h
  · apply le_antisymm
    · obtain ⟨x, xb, ax⟩ :=
        (lt_opow_of_isSuccLimit omega0_ne_zero (isSuccLimit_opow_left isSuccLimit_omega0 b0)).1 h
      grw [ax, ← opow_add, add_omega0_opow xb]
    · conv_lhs => rw [← one_mul (ω ^ _)]
      grw [one_le_iff_pos.2 a0]

/--
theorem `isPrincipal_mul_omega0_opow_opow` / 定理 `isPrincipal_mul_omega0_opow_opow`

English:
theorem isPrincipal_mul_omega0_opow_opow
  given: (o : Ordinal)
  statement: IsPrincipal (· * ·) (ω ^ ω ^ o)
  proof: isPrincipal_mul_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0_opow_opow := isPrincipal_mul_omega0_opow_opow

中文:
定理 isPrincipal_mul_omega0_opow_opow
  条件: (o : 序数)
  结论: 是Principal (· * ·) (ω ^ ω ^ o)
  证明: isPrincipal_mul_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0_opow_opow := isPrincipal_mul_omega0_opow_opow

Depends on / 依赖: isPrincipal_mul_iff_mul_left_eq, mul_omega0_opow_opow
-/
theorem isPrincipal_mul_omega0_opow_opow (o : Ordinal) : IsPrincipal (· * ·) (ω ^ ω ^ o) :=
  isPrincipal_mul_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0_opow_opow := isPrincipal_mul_omega0_opow_opow

/--
theorem `isPrincipal_add_of_isPrincipal_mul_opow` / 定理 `isPrincipal_add_of_isPrincipal_mul_opow`

English:
theorem isPrincipal_add_of_isPrincipal_mul_opow
  given: (hb : 1 < b) (ho : IsPrincipal (· * ·) (b ^ o))
  proof: by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul_opow := isPrincipal_add_of_isPrincipal_mul_opow

中文:
定理 isPrincipal_add_of_isPrincipal_mul_opow
  条件: (hb : 1 < b) (ho : 是Principal (· * ·) (b ^ o))
  证明: by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul_opow := isPrincipal_add_of_isPrincipal_mul_opow

Depends on / 依赖: opow_add, opow_lt_opow_iff_right
-/
theorem isPrincipal_add_of_isPrincipal_mul_opow (hb : 1 < b) (ho : IsPrincipal (· * ·) (b ^ o)) :
    IsPrincipal (· + ·) o := by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul_opow := isPrincipal_add_of_isPrincipal_mul_opow

/--
theorem `isPrincipal_mul_iff_le_two_or_omega0_opow_opow` / 定理 `isPrincipal_mul_iff_le_two_or_omega0_opow_opow`

English:
theorem isPrincipal_mul_iff_le_two_or_omega0_opow_opow
  proof: by
  refine ⟨fun ho => ?_, ?_⟩
  · rcases le_or_gt o 2 with ho₂ | ho₂
    · exact Or.inl ho₂
    · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
        (isPrincipal_add_of_isPrincipal_mul ho ho₂.ne') with (rfl | ⟨a, rfl⟩)
      · exact (not_lt_zero ho₂).elim
      · rcases isPrincipal_add_iff_ze

中文:
定理 isPrincipal_mul_iff_le_two_or_omega0_opow_opow
  证明: by
  refine ⟨fun ho => ?_, ?_⟩
  · rcases le_or_gt o 2 with ho₂ | ho₂
    · exact Or.inl ho₂
    · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
        (isPrincipal_add_of_isPrincipal_mul ho ho₂.ne') with (rfl | ⟨a, rfl⟩)
      · exact (not_lt_zero ho₂).elim
      · rcases isPrincipal_add_iff_ze

Depends on / 依赖: Or.inl, Or.inr, isPrincipal_add_iff_zero_or_omega0_opow, isPrincipal_add_of_isPrincipal_mul, isPrincipal_add_of_isPrincipal_mul_opow, isPrincipal_mul_of_le_two, isPrincipal_mul_omega0_opow_, le_or_gt, not_lt_zero, one_lt_omega0
-/
theorem isPrincipal_mul_iff_le_two_or_omega0_opow_opow :
    IsPrincipal (· * ·) o ↔ o <= 2 ∨ o in Set.range (ω ^ ω ^ · : Ordinal -> Ordinal) := by
  refine ⟨fun ho => ?_, ?_⟩
  · rcases le_or_gt o 2 with ho₂ | ho₂
    · exact Or.inl ho₂
    · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
        (isPrincipal_add_of_isPrincipal_mul ho ho₂.ne') with (rfl | ⟨a, rfl⟩)
      · exact (not_lt_zero ho₂).elim
      · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
          (isPrincipal_add_of_isPrincipal_mul_opow one_lt_omega0 ho) with (rfl | ⟨b, rfl⟩)
        · simp
        · exact Or.inr ⟨b, rfl⟩
  · rintro (ho₂ | ⟨a, rfl⟩)
    · exact isPrincipal_mul_of_le_two ho₂
    · exact isPrincipal_mul_omega0_opow_opow a

@[deprecated (since := "2026-03-17")]
alias principal_mul_iff_le_two_or_omega0_opow_opow := isPrincipal_mul_iff_le_two_or_omega0_opow_opow

/--
theorem `mul_omega0_dvd` / 定理 `mul_omega0_dvd`

English:
theorem mul_omega0_dvd
  given: (a0 : 0 < a) (ha : a < ω)
  statement: forall {b}, ω ∣ b -> a * b = b

中文:
定理 mul_omega0_dvd
  条件: (a0 : 0 < a) (ha : a < ω)
  结论: 对任意 {b}, ω ∣ b -> a * b = b
-/
theorem mul_omega0_dvd (a0 : 0 < a) (ha : a < ω) : forall {b}, ω ∣ b -> a * b = b
  | _, ⟨b, rfl⟩ => by rw [← mul_assoc, mul_omega0 a0 ha]

/--
theorem `mul_eq_opow_log_succ` / 定理 `mul_eq_opow_log_succ`

English:
theorem mul_eq_opow_log_succ
  given: (ha : a != 0) (hb : IsPrincipal (· * ·) b) (hb₂ : 2 < b)
  proof: by
  apply le_antisymm
  · have hbl := isSuccLimit_of_isPrincipal_mul hb₂ hb
    rw [(isNormal_mul_right (pos_iff_ne_zero.2 ha)).apply_of_isSuccLimit hbl]; rw [Ordinal.iSup_le_iff]
    intro ⟨c, hcb⟩
    have hb₁ : 1 < b := one_lt_two.trans hb₂
    have hbo₀ : b ^ log b a != 0 := pos_iff_ne_zero.1 (

中文:
定理 mul_eq_opow_log_succ
  条件: (ha : a != 0) (hb : 是Principal (· * ·) b) (hb₂ : 2 < b)
  证明: by
  apply le_antisymm
  · have hbl := isSuccLimit_of_isPrincipal_mul hb₂ hb
    rw [(isNormal_mul_right (pos_iff_ne_zero.2 ha)).apply_of_isSuccLimit hbl]; rw [Ordinal.iSup_le_iff]
    intro ⟨c, hcb⟩
    have hb₁ : 1 < b := one_lt_two.trans hb₂
    have hbo₀ : b ^ log b a != 0 := pos_iff_ne_zero.1 (

Depends on / 依赖: Ordinal, Ordinal.iSup_le_iff, apply_of_isSuccLimit, hbl.succ_lt, iSup_le_iff, isNormal_mul_right, isSuccLimit_of_isPrincipal_mul, le_antisymm, le_of_lt, lt_mul_iff_div_lt, lt_mul_succ_div, mul_assoc, mul_le_mul_left, one_lt_two, one_lt_two.trans, opow_, opow_pos, opow_succ, pos_iff_ne_zero, succ_lt
-/
theorem mul_eq_opow_log_succ (ha : a != 0) (hb : IsPrincipal (· * ·) b) (hb₂ : 2 < b) :
    a * b = b ^ succ (log b a) := by
  apply le_antisymm
  · have hbl := isSuccLimit_of_isPrincipal_mul hb₂ hb
    rw [(isNormal_mul_right (pos_iff_ne_zero.2 ha)).apply_of_isSuccLimit hbl]; rw [Ordinal.iSup_le_iff]
    intro ⟨c, hcb⟩
    have hb₁ : 1 < b := one_lt_two.trans hb₂
    have hbo₀ : b ^ log b a != 0 := pos_iff_ne_zero.1 (opow_pos _ (zero_lt_one.trans hb₁))
    apply (mul_le_mul_left (le_of_lt (lt_mul_succ_div a hbo₀)) c).trans
    rw [mul_assoc]; rw [opow_succ]
    gcongr
    refine (hb (hbl.succ_lt ?_) hcb).le
    rw [← lt_mul_iff_div_lt hbo₀]; rw [← opow_succ]
    exact lt_opow_succ_log_self hb₁ _
  · grw [opow_succ, opow_log_le_self b ha]


/--
theorem `isPrincipal_opow_omega0` / 定理 `isPrincipal_opow_omega0`

English:
theorem isPrincipal_opow_omega0
  statement: IsPrincipal (· ^ ·) ω
  proof: fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by simp [← natCast_pow]

@[deprecated (since := "2026-03-17")]
alias principal_opow_omega0 := isPrincipal_opow_omega0

中文:
定理 isPrincipal_opow_omega0
  结论: 是Principal (· ^ ·) ω
  证明: fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by simp [← natCast_pow]

@[deprecated (since := "2026-03-17")]
alias principal_opow_omega0 := isPrincipal_opow_omega0
-/
theorem isPrincipal_opow_omega0 : IsPrincipal (· ^ ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by simp [← natCast_pow]

@[deprecated (since := "2026-03-17")]
alias principal_opow_omega0 := isPrincipal_opow_omega0

/--
theorem `opow_omega0` / 定理 `opow_omega0`

English:
theorem opow_omega0
  given: (a1 : 1 < a) (h : a < ω)
  statement: a ^ ω = ω
  proof: ((opow_le_of_isSuccLimit (one_le_iff_ne_zero.1 <| le_of_lt a1) isSuccLimit_omega0).2 fun _ hb =>
      (isPrincipal_opow_omega0 h hb).le).antisymm
  (right_le_opow _ a1)

中文:
定理 opow_omega0
  条件: (a1 : 1 < a) (h : a < ω)
  结论: a ^ ω = ω
  证明: ((opow_le_of_isSuccLimit (one_le_iff_ne_zero.1 <| le_of_lt a1) isSuccLimit_omega0).2 fun _ hb =>
      (isPrincipal_opow_omega0 h hb).le).antisymm
  (right_le_opow _ a1)

Depends on / 依赖: antisymm, isPrincipal_opow_omega0, isSuccLimit_omega0, le_of_lt, one_le_iff_ne_zero, opow_le_of_isSuccLimit, right_le_opow
-/
theorem opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω :=
  ((opow_le_of_isSuccLimit (one_le_iff_ne_zero.1 <| le_of_lt a1) isSuccLimit_omega0).2 fun _ hb =>
      (isPrincipal_opow_omega0 h hb).le).antisymm
  (right_le_opow _ a1)

/--
theorem `natCast_opow_omega0` / 定理 `natCast_opow_omega0`

English:
theorem natCast_opow_omega0
  given: {n : Nat} (hn : 1 < n)
  statement: n ^ ω = ω
  proof: opow_omega0 (mod_cast hn) (natCast_lt_omega0 n)

中文:
定理 natCast_opow_omega0
  条件: {n : 自然数} (hn : 1 < n)
  结论: n ^ ω = ω
  证明: opow_omega0 (mod_cast hn) (natCast_lt_omega0 n)

Depends on / 依赖: mod_cast, natCast_lt_omega0, opow_omega0
-/
theorem natCast_opow_omega0 {n : Nat} (hn : 1 < n) : n ^ ω = ω :=
  opow_omega0 (mod_cast hn) (natCast_lt_omega0 n)

end Ordinal
