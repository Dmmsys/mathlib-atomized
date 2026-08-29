/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Mario Carneiro
-/
module

public import Mathlib.Tactic.NormNum.Ineq

/-!
# `norm_num` extension for integer div/mod and divides

This file adds support for the `%`, `/`, and `∣` (divisibility) operators on `ℤ`
to the `norm_num` tactic.
-/

public meta section

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

/--
lemma `isInt_ediv_zero` / 引理 `isInt_ediv_zero`

English:
lemma isInt_ediv_zero
  statement: forall {a b r : Int}, IsInt a r -> IsNat b (nat_lit 0) -> IsNat (a / b) (nat_lit 0)

中文:
引理 is整数_ediv_zero
  结论: 对任意 {a b r : 整数}, 是整数 a r -> 是自然数 b (nat_lit 0) -> 是自然数 (a / b) (nat_lit 0)

Depends on / 依赖: completelyRegularSpace_induced, completelyRegularSpace_inf
-/
lemma isInt_ediv_zero : forall {a b r : Int}, IsInt a r -> IsNat b (nat_lit 0) -> IsNat (a / b) (nat_lit 0)
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => ⟨by simp [Int.ediv_zero]⟩

/--
lemma `isInt_ediv` / 引理 `isInt_ediv`

English:
lemma isInt_ediv
  statement: {a b q m a' : Int} {b' r : Nat}
  proof: ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [Nat.blt_eq] at h₂; simp only [← h, ← hm, Int.cast_id]
  rw [Int.add_mul_ediv_right _ _ (Int.ofNat_ne_zero.2 ((Nat.zero_le ..).trans_lt h₂).ne')]
  rw [Int.ediv_eq_zero_of_lt]; rw [zero_add] <;> [simp; simpa using h₂]⟩

中文:
引理 is整数_ediv
  结论: {a b q m a' : 整数} {b' r : 自然数}
  证明: ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [Nat.blt_eq] at h₂; simp only [← h, ← hm, Int.cast_id]
  rw [Int.add_mul_ediv_right _ _ (Int.ofNat_ne_zero.2 ((Nat.zero_le ..).trans_lt h₂).ne')]
  rw [Int.ediv_eq_zero_of_lt]; rw [zero_add] <;> [simp; simpa using h₂]⟩

Depends on / 依赖: Int.add_mul_ediv_right, Int.cast_id, Int.ediv_eq_zero_of_lt, Int.ofNat_ne_zero, Nat.blt_eq, Nat.zero_le, add_mul_ediv_right, blt_eq, cast_id, ediv_eq_zero_of_lt, ofNat_ne_zero, trans_lt, zero_add, zero_le
-/
lemma isInt_ediv {a b q m a' : Int} {b' r : Nat}
    (ha : IsInt a a') (hb : IsNat b b')
    (hm : q * b' = m) (h : r + m = a') (h₂ : Nat.blt r b' = true) :
    IsInt (a / b) q := ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [Nat.blt_eq] at h₂; simp only [← h, ← hm, Int.cast_id]
  rw [Int.add_mul_ediv_right _ _ (Int.ofNat_ne_zero.2 ((Nat.zero_le ..).trans_lt h₂).ne')]
  rw [Int.ediv_eq_zero_of_lt]; rw [zero_add] <;> [simp; simpa using h₂]⟩

/--
lemma `isInt_ediv_neg` / 引理 `isInt_ediv_neg`

English:
lemma isInt_ediv_neg
  given: {a b q q' : Int} (h : IsInt (a / -b) q) (hq : -q = q')
  statement: IsInt (a / b) q'
  proof: ⟨by rw [Int.cast_id, ← hq, ← @Int.cast_id q, ← h.out, ← Int.ediv_neg, Int.neg_neg]⟩

中文:
引理 is整数_ediv_neg
  条件: {a b q q' : 整数} (h : 是整数 (a / -b) q) (hq : -q = q')
  结论: 是整数 (a / b) q'
  证明: ⟨by rw [Int.cast_id, ← hq, ← @Int.cast_id q, ← h.out, ← Int.ediv_neg, Int.neg_neg]⟩

Depends on / 依赖: Int.cast_id, Int.ediv_neg, Int.neg_neg, cast_id, ediv_neg, h.out, neg_neg
-/
lemma isInt_ediv_neg {a b q q' : Int} (h : IsInt (a / -b) q) (hq : -q = q') : IsInt (a / b) q' :=
  ⟨by rw [Int.cast_id, ← hq, ← @Int.cast_id q, ← h.out, ← Int.ediv_neg, Int.neg_neg]⟩

/--
lemma `isNat_neg_of_isNegNat` / 引理 `isNat_neg_of_isNegNat`

English:
lemma isNat_neg_of_isNegNat
  given: {a : Int} {b : Nat} (h : IsInt a (.negOfNat b))
  statement: IsNat (-a) b
  proof: ⟨by simp [h.out]⟩

中文:
引理 is自然数_neg_of_isNeg自然数
  条件: {a : 整数} {b : 自然数} (h : 是整数 a (.negOf自然数 b))
  结论: 是自然数 (-a) b
  证明: ⟨by simp [h.out]⟩

Depends on / 依赖: h.out
-/
lemma isNat_neg_of_isNegNat {a : Int} {b : Nat} (h : IsInt a (.negOfNat b)) : IsNat (-a) b :=
  ⟨by simp [h.out]⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `Int.ediv a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : Int) / _, Int.ediv _ _]
/--
Definition of `evalIntDiv` / `evalIntDiv` 的定义

English:
definition evalIntDiv
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
  -- We assert that the default instance for `HDiv` is `Int.div` when the first parameter is `ℤ`.
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := Int))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
haveI' : e =Q ($a / $b) := ⟨⟩
  let rInt : Q(Ring Int) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rInt
  match ← derive (u := .zero) b with
  | .isNat inst nb pb =>
    assumeInstancesCommute
    if nb.natLit! == 0 then
have _ : nb =Q nat_lit 0 := ⟨⟩
      return .isNat q(instAddMonoidWithOne) q(nat_lit 0) q(isInt_ediv_zero $pa $pb)
    else
      let ⟨zq, q, p⟩ := core a na za pa b nb pb
      return .isInt rInt q zq p
  | .isNegNat _ nb pb =>
    assumeInstancesCommute
    let ⟨zq, q, p⟩ := core a na za pa q(-$b) nb q(isNat_neg_of_isNegNat $pb)
    have q' := mkRawIntLit (-zq)
    have : Q(-$q = $q') := (q(Eq.refl $q') :)
    return .isInt rInt q' (-zq) q(isInt_ediv_neg $p $this)
  | _ => failure

中文:
定义 eval整数Div
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
  -- We assert that the default instance for `HDiv` is `Int.div` when the first parameter is `ℤ`.
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := Int))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
haveI' : e =Q ($a / $b) := ⟨⟩
  let rInt : Q(Ring Int) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rInt
  match ← derive (u := .zero) b with
  | .isNat inst nb pb =>
    assumeInstancesCommute
    if nb.natLit! == 0 then
have _ : nb =Q nat_lit 0 := ⟨⟩
      return .isNat q(instAddMonoidWithOne) q(nat_lit 0) q(isInt_ediv_zero $pa $pb)
    else
      let ⟨zq, q, p⟩ := core a na za pa b nb pb
      return .isInt rInt q zq p
  | .isNegNat _ nb pb =>
    assumeInstancesCommute
    let ⟨zq, q, p⟩ := core a na za pa q(-$b) nb q(isNat_neg_of_isNegNat $pb)
    have q' := mkRawIntLit (-zq)
    have : Q(-$q = $q') := (q(Eq.refl $q') :)
    return .isInt rInt q' (-zq) q(isInt_ediv_neg $p $this)
  | _ => failure
-/
partial def evalIntDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
  -- We assert that the default instance for `HDiv` is `Int.div` when the first parameter is `ℤ`.
guard ← withNewMCtxDepth isDefEq f q(HDiv.hDiv (α := Int))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
haveI' : e =Q ($a / $b) := ⟨⟩
  let rInt : Q(Ring Int) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rInt
  match ← derive (u := .zero) b with
  | .isNat inst nb pb =>
    assumeInstancesCommute
    if nb.natLit! == 0 then
have _ : nb =Q nat_lit 0 := ⟨⟩
      return .isNat q(instAddMonoidWithOne) q(nat_lit 0) q(isInt_ediv_zero $pa $pb)
    else
      let ⟨zq, q, p⟩ := core a na za pa b nb pb
      return .isInt rInt q zq p
  | .isNegNat _ nb pb =>
    assumeInstancesCommute
    let ⟨zq, q, p⟩ := core a na za pa q(-$b) nb q(isNat_neg_of_isNegNat $pb)
    have q' := mkRawIntLit (-zq)
    have : Q(-$q = $q') := (q(Eq.refl $q') :)
    return .isInt rInt q' (-zq) q(isInt_ediv_neg $p $this)
  | _ => failure
where
  /-- Given a result for evaluating `a b` in `ℤ` where `b > 0`, evaluate `a / b`. -/
  core (a na : Q(Int)) (za : Int) (pa : Q(IsInt $a $na))
      (b : Q(Int)) (nb : Q(Nat)) (pb : Q(IsNat $b $nb)) :
      Int × (q : Q(Int)) × Q(IsInt ($a / $b) $q) :=
    let b := nb.natLit!
    let q := za / b
    have nq := mkRawIntLit q
    let r := za.natMod b
    have nr : Q(Nat) := mkRawNatLit r
    let m := q * b
    have nm := mkRawIntLit m
    have pf₁ : Q($nq * $nb = $nm) := (q(Eq.refl $nm) :)
    have pf₂ : Q($nr + $nm = $na) := (q(Eq.refl $na) :)
    have pf₃ : Q(Nat.blt $nr $nb = true) := (q(Eq.refl true) :)
    ⟨q, nq, q(isInt_ediv $pa $pb $pf₁ $pf₂ $pf₃)⟩

/--
lemma `isInt_emod_zero` / 引理 `isInt_emod_zero`

English:
lemma isInt_emod_zero
  statement: forall {a b r : Int}, IsInt a r -> IsNat b (nat_lit 0) -> IsInt (a % b) r

中文:
引理 is整数_emod_zero
  结论: 对任意 {a b r : 整数}, 是整数 a r -> 是自然数 b (nat_lit 0) -> 是整数 (a % b) r
-/
lemma isInt_emod_zero : forall {a b r : Int}, IsInt a r -> IsNat b (nat_lit 0) -> IsInt (a % b) r
  | _, _, _, e, ⟨rfl⟩ => by simp [e]

/--
lemma `isInt_emod` / 引理 `isInt_emod`

English:
lemma isInt_emod
  statement: {a b q m a' : Int} {b' r : Nat}
  proof: ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [← h, ← hm, Int.add_mul_emod_self_right]
  rw [Int.emod_eq_of_lt] <;> [simp; simpa using h₂]⟩

中文:
引理 is整数_emod
  结论: {a b q m a' : 整数} {b' r : 自然数}
  证明: ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [← h, ← hm, Int.add_mul_emod_self_right]
  rw [Int.emod_eq_of_lt] <;> [simp; simpa using h₂]⟩

Depends on / 依赖: Int.add_mul_emod_self_right, Int.emod_eq_of_lt, add_mul_emod_self_right, emod_eq_of_lt
-/
lemma isInt_emod {a b q m a' : Int} {b' r : Nat}
    (ha : IsInt a a') (hb : IsNat b b')
    (hm : q * b' = m) (h : r + m = a') (h₂ : Nat.blt r b' = true) :
    IsNat (a % b) r := ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [← h, ← hm, Int.add_mul_emod_self_right]
  rw [Int.emod_eq_of_lt] <;> [simp; simpa using h₂]⟩

/--
lemma `isInt_emod_neg` / 引理 `isInt_emod_neg`

English:
lemma isInt_emod_neg
  given: {a b : Int} {r : Nat} (h : IsNat (a % -b) r)
  statement: IsNat (a % b) r
  proof: ⟨by rw [← Int.emod_neg, h.out]⟩

中文:
引理 is整数_emod_neg
  条件: {a b : 整数} {r : 自然数} (h : 是自然数 (a % -b) r)
  结论: 是自然数 (a % b) r
  证明: ⟨by rw [← Int.emod_neg, h.out]⟩

Depends on / 依赖: Int.emod_neg, emod_neg, h.out
-/
lemma isInt_emod_neg {a b : Int} {r : Nat} (h : IsNat (a % -b) r) : IsNat (a % b) r :=
  ⟨by rw [← Int.emod_neg, h.out]⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `Int.emod a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : Int) % _, Int.emod _ _]
/--
Definition of `evalIntMod` / `evalIntMod` 的定义

English:
definition evalIntMod
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
  -- We assert that the default instance for `HMod` is `Int.mod` when the first parameter is `ℤ`.
guard ← withNewMCtxDepth isDefEq f q(HMod.hMod (α := Int))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
haveI' : e =Q ($a % $b) := ⟨⟩
  let rInt : Q(Ring Int) := q(Int.instRing)
  let some ⟨za, na, pa⟩ := (← derive a).toInt rInt | failure
  go a na za pa b (← derive (u := .zero) b)

中文:
定义 eval整数Mod
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
  -- We assert that the default instance for `HMod` is `Int.mod` when the first parameter is `ℤ`.
guard ← withNewMCtxDepth isDefEq f q(HMod.hMod (α := Int))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
haveI' : e =Q ($a % $b) := ⟨⟩
  let rInt : Q(Ring Int) := q(Int.instRing)
  let some ⟨za, na, pa⟩ := (← derive a).toInt rInt | failure
  go a na za pa b (← derive (u := .zero) b)
-/
partial def evalIntMod : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
  -- We assert that the default instance for `HMod` is `Int.mod` when the first parameter is `ℤ`.
guard ← withNewMCtxDepth isDefEq f q(HMod.hMod (α := Int))
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Int := ⟨⟩
haveI' : e =Q ($a % $b) := ⟨⟩
  let rInt : Q(Ring Int) := q(Int.instRing)
  let some ⟨za, na, pa⟩ := (← derive a).toInt rInt | failure
  go a na za pa b (← derive (u := .zero) b)
where
  /-- Given a result for evaluating `a b` in `ℤ`, evaluate `a % b`. -/
  go (a na : Q(Int)) (za : Int) (pa : Q(IsInt $a $na))
      (b : Q(Int)) : Result b -> Option (Result q($a % $b))
    | .isNat inst nb pb => do
      assumeInstancesCommute
      if nb.natLit! == 0 then
have _ : nb =Q nat_lit 0 := ⟨⟩
        return .isInt q(Int.instRing) na za q(isInt_emod_zero $pa $pb)
      else
        let ⟨r, p⟩ := core a na za pa b nb pb
        return .isNat q(instAddMonoidWithOne) r p
    | .isNegNat _ nb pb => do
      assumeInstancesCommute
      let ⟨r, p⟩ := core a na za pa q(-$b) nb q(isNat_neg_of_isNegNat $pb)
      return .isNat q(instAddMonoidWithOne) r q(isInt_emod_neg $p)
    | _ => none

  /-- Given a result for evaluating `a b` in `ℤ` where `b > 0`, evaluate `a % b`. -/
  core (a na : Q(Int)) (za : Int) (pa : Q(IsInt $a $na))
      (b : Q(Int)) (nb : Q(Nat)) (pb : Q(IsNat $b $nb)) :
      (r : Q(Nat)) × Q(IsNat ($a % $b) $r) :=
    let b := nb.natLit!
    let q := za / b
    have nq := mkRawIntLit q
    let r := za.natMod b
    have nr : Q(Nat) := mkRawNatLit r
    let m := q * b
    have nm := mkRawIntLit m
    have pf₁ : Q($nq * $nb = $nm) := (q(Eq.refl $nm) :)
    have pf₂ : Q($nr + $nm = $na) := (q(Eq.refl $na) :)
    have pf₃ : Q(Nat.blt $nr $nb = true) := (q(Eq.refl true) :)
    ⟨nr, q(isInt_emod $pa $pb $pf₁ $pf₂ $pf₃)⟩

/--
theorem `isInt_dvd_true` / 定理 `isInt_dvd_true`

English:
theorem isInt_dvd_true
  statement: {a b : Int} -> {a' b' c : Int} ->

中文:
定理 is整数_dvd_true
  结论: {a b : 整数} -> {a' b' c : 整数} ->
-/
theorem isInt_dvd_true : {a b : Int} -> {a' b' c : Int} ->
    IsInt a a' -> IsInt b b' -> Int.mul a' c = b' -> a ∣ b
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨_, rfl⟩

/--
theorem `isInt_dvd_false` / 定理 `isInt_dvd_false`

English:
theorem isInt_dvd_false
  statement: {a b : Int} -> {a' b' : Int} ->

中文:
定理 is整数_dvd_false
  结论: {a b : 整数} -> {a' b' : 整数} ->
-/
theorem isInt_dvd_false : {a b : Int} -> {a' b' : Int} ->
    IsInt a a' -> IsInt b b' -> Int.emod b' a' != 0 -> ¬a ∣ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, e => mt Int.emod_eq_zero_of_dvd (by simpa using! e)

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalIntDvd` / `evalIntDvd` 的定义

English:
definition evalIntDvd
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Prop := ⟨⟩
haveI' : e =Q ($a ∣ $b) := ⟨⟩
  -- We assert that the default instance for `Dvd` is `Int.dvd` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(Dvd.dvd (α := Int))
  let rInt : Q(Ring Int) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rInt
  let ⟨zb, nb, pb⟩ ← (← derive b).toInt rInt
  if zb % za == 0 then
    let zc := zb / za
    have c := mkRawIntLit zc
haveI' : Int.mul na c =Q nb := ⟨⟩
    return .isTrue q(isInt_dvd_true $pa $pb (.refl $nb))
  else
    have : Q(Int.emod $nb $na != 0) := (q(Eq.refl true) : Expr)
    return .isFalse q(isInt_dvd_false $pa $pb $this)

中文:
定义 eval整数Dvd
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Prop := ⟨⟩
haveI' : e =Q ($a ∣ $b) := ⟨⟩
  -- We assert that the default instance for `Dvd` is `Int.dvd` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(Dvd.dvd (α := Int))
  let rInt : Q(Ring Int) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rInt
  let ⟨zb, nb, pb⟩ ← (← derive b).toInt rInt
  if zb % za == 0 then
    let zc := zb / za
    have c := mkRawIntLit zc
haveI' : Int.mul na c =Q nb := ⟨⟩
    return .isTrue q(isInt_dvd_true $pa $pb (.refl $nb))
  else
    have : Q(Int.emod $nb $na != 0) := (q(Eq.refl true) : Expr)
    return .isFalse q(isInt_dvd_false $pa $pb $this)
-/
@[norm_num (_ : Int) ∣ _] def evalIntDvd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(Int))) (b : Q(Int)) ← whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Prop := ⟨⟩
haveI' : e =Q ($a ∣ $b) := ⟨⟩
  -- We assert that the default instance for `Dvd` is `Int.dvd` when the first parameter is `ℕ`.
guard ← withNewMCtxDepth isDefEq f q(Dvd.dvd (α := Int))
  let rInt : Q(Ring Int) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rInt
  let ⟨zb, nb, pb⟩ ← (← derive b).toInt rInt
  if zb % za == 0 then
    let zc := zb / za
    have c := mkRawIntLit zc
haveI' : Int.mul na c =Q nb := ⟨⟩
    return .isTrue q(isInt_dvd_true $pa $pb (.refl $nb))
  else
    have : Q(Int.emod $nb $na != 0) := (q(Eq.refl true) : Expr)
    return .isFalse q(isInt_dvd_false $pa $pb $this)

end Mathlib.Meta.NormNum
