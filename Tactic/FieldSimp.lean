/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, David Renshaw, Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
module

public meta import Mathlib.Data.Ineq
public import Mathlib.Tactic.FieldSimp.Attr
public import Mathlib.Tactic.FieldSimp.Discharger
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Util.AtomM.Recurse
public import Mathlib.Util.SynthesizeUsing
public import Mathlib.Data.Ineq

/-!
# `field_simp` tactic

Tactic to clear denominators in algebraic expressions.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.FieldSimp

initialize registerTraceClass `Tactic.field_simp

variable {v : Level} {M : Q(Type v)}

/-! ### Lists of expressions representing exponents and atoms, and operations on such lists -/

/--
Definition of `qNF` / `qNF` 的定义

English:
abbreviation qNF
  signature: (M : Q(Type v))
  body: List ((Int × Q($M)) × Nat)

中文:
缩写 qNF
  签名: (M : Q(类型v))
  定义体: List ((Int × Q($M)) × Nat)
-/
abbrev qNF (M : Q(Type v)) := List ((Int × Q($M)) × Nat)

namespace qNF

/--
Definition of `toNF` / `toNF` 的定义

English:
definition toNF
  signature: (l : qNF q($M))
  body: l.foldr (fun ((a, x), _) l => q(($a, $x) ::ᵣ $l)) q([])

中文:
定义 toNF
  签名: (l : qNF q($M))
  定义体: l.foldr (fun ((a, x), _) l => q(($a, $x) ::ᵣ $l)) q([])

Depends on / 依赖: l.foldr
-/
def toNF (l : qNF q($M)) : Q(NF $M) := l.foldr (fun ((a, x), _) l => q(($a, $x) ::ᵣ $l)) q([])

/--
Definition of `onExponent` / `onExponent` 的定义

English:
definition onExponent
  signature: (l : qNF M) (f : Int -> Int)
  body: l.map fun ((a, x), k) => ((f a, x), k)

中文:
定义 onExponent
  签名: (l : qNF M) (f : 整数 -> 整数)
  定义体: l.map fun ((a, x), k) => ((f a, x), k)

Depends on / 依赖: l.map
-/
def onExponent (l : qNF M) (f : Int -> Int) : qNF M :=
  l.map fun ((a, x), k) => ((f a, x), k)

/--
Definition of `evalPrettyMonomial` / `evalPrettyMonomial` 的定义

English:
definition evalPrettyMonomial
  signature: (iM : Q(GroupWithZero $M)) (r : Int) (x : Q($M))
  body: match r with
  | 0 => /- If an exponent is zero then we must not have been able to prove that x is nonzero. -/
    return ⟨q($x / $x), q(zpow'_zero_eq_div ..)⟩
  | 1 => return ⟨x, q(zpow'_one $x)⟩
  | .ofNat r => do
    let pf ← mkDecideProofQ q($r != 0)
    return ⟨q($x ^ $r), q(zpow'_ofNat $x $pf)⟩
  | r => do
    let pf ← mkDecideProofQ q($r != 0)
    return ⟨q($x ^ $r), q(zpow'_of_ne_zero_right _ _ $pf)⟩

中文:
定义 evalPrettyMonomial
  签名: (iM : Q(带零群 $M)) (r : 整数) (x : Q($M))
  定义体: match r with
  | 0 => /- If an exponent is zero then we must not have been able to prove that x is nonzero. -/
    return ⟨q($x / $x), q(zpow'_zero_eq_div ..)⟩
  | 1 => return ⟨x, q(zpow'_one $x)⟩
  | .ofNat r => do
    let pf ← mkDecideProofQ q($r != 0)
    return ⟨q($x ^ $r), q(zpow'_ofNat $x $pf)⟩
  | r => do
    let pf ← mkDecideProofQ q($r != 0)
    return ⟨q($x ^ $r), q(zpow'_of_ne_zero_right _ _ $pf)⟩

Depends on / 依赖: _ofNat, _of_ne_zero_right, _one, _zero_eq_div, exponent, mkDecideProofQ, nonzero, return
-/
def evalPrettyMonomial (iM : Q(GroupWithZero $M)) (r : Int) (x : Q($M)) :
    MetaM (Σ e : Q($M), Q(zpow' $x $r = $e)) :=
  match r with
  | 0 => /- If an exponent is zero then we must not have been able to prove that x is nonzero. -/
    return ⟨q($x / $x), q(zpow'_zero_eq_div ..)⟩
  | 1 => return ⟨x, q(zpow'_one $x)⟩
  | .ofNat r => do
    let pf ← mkDecideProofQ q($r != 0)
    return ⟨q($x ^ $r), q(zpow'_ofNat $x $pf)⟩
  | r => do
    let pf ← mkDecideProofQ q($r != 0)
    return ⟨q($x ^ $r), q(zpow'_of_ne_zero_right _ _ $pf)⟩

/--
Definition of `tryClearZero` / `tryClearZero` 的定义

English:
definition tryClearZero
  body: do
  if r != 0 then
    return ⟨((r, x), i) :: l, q(rfl)⟩
  try
    let pf' : Q($x != 0) ← disch q($x != 0)
    have pf_r : Q($r = 0) := ← mkDecideProofQ q($r = 0)
    return ⟨l, (q(NF.eval_cons_of_pow_eq_zero $pf_r $pf' $(l.toNF)):)⟩
  catch _=>
    return ⟨((r, x), i) :: l, q(rfl)⟩

中文:
定义 tryClearZero
  定义体: do
  if r != 0 then
    return ⟨((r, x), i) :: l, q(rfl)⟩
  try
    let pf' : Q($x != 0) ← disch q($x != 0)
    have pf_r : Q($r = 0) := ← mkDecideProofQ q($r = 0)
    return ⟨l, (q(NF.eval_cons_of_pow_eq_zero $pf_r $pf' $(l.toNF)):)⟩
  catch _=>
    return ⟨((r, x), i) :: l, q(rfl)⟩
-/
def tryClearZero
    (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type)) (iM : Q(CommGroupWithZero $M))
    (r : Int) (x : Q($M)) (i : Nat) (l : qNF M) :
MetaM Σ l' : qNF M, Q(NF.eval $(qNF.toNF (((r, x), i) :: l)) = NF.eval $(l'.toNF)) := do
  if r != 0 then
    return ⟨((r, x), i) :: l, q(rfl)⟩
  try
    let pf' : Q($x != 0) ← disch q($x != 0)
    have pf_r : Q($r = 0) := ← mkDecideProofQ q($r = 0)
    return ⟨l, (q(NF.eval_cons_of_pow_eq_zero $pf_r $pf' $(l.toNF)):)⟩
  catch _=>
    return ⟨((r, x), i) :: l, q(rfl)⟩

/--
Definition of `removeZeros` / `removeZeros` 的定义

English:
definition removeZeros
  body: match l with
  | [] => return ⟨[], q(rfl)⟩
  | ((r, x), i) :: t => do
    let ⟨t', pf⟩ ← removeZeros disch iM t
    let ⟨l', pf'⟩ ← tryClearZero disch iM r x i t'
    let pf' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t')) = NF.eval $(qNF.toNF l')) := pf'
    let pf'' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t)) = NF.eval $(qNF.toNF l')) :=
      q(NF.eval_cons_eq_eval_of_eq_of_eq $r $x $pf $pf')
    return ⟨l', pf''⟩

中文:
定义 removeZeros
  定义体: match l with
  | [] => return ⟨[], q(rfl)⟩
  | ((r, x), i) :: t => do
    let ⟨t', pf⟩ ← removeZeros disch iM t
    let ⟨l', pf'⟩ ← tryClearZero disch iM r x i t'
    let pf' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t')) = NF.eval $(qNF.toNF l')) := pf'
    let pf'' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t)) = NF.eval $(qNF.toNF l')) :=
      q(NF.eval_cons_eq_eval_of_eq_of_eq $r $x $pf $pf')
    return ⟨l', pf''⟩

Depends on / 依赖: NF.eval, NF.eval_cons_eq_eval_of_eq_of_eq, eval_cons_eq_eval_of_eq_of_eq, qNF.toNF, removeZeros, return, tryClearZero
-/
def removeZeros
    (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type)) (iM : Q(CommGroupWithZero $M))
    (l : qNF M) :
MetaM Σ l' : qNF M, Q(NF.eval $(l.toNF) = NF.eval $(l'.toNF)) :=
  match l with
  | [] => return ⟨[], q(rfl)⟩
  | ((r, x), i) :: t => do
    let ⟨t', pf⟩ ← removeZeros disch iM t
    let ⟨l', pf'⟩ ← tryClearZero disch iM r x i t'
    let pf' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t')) = NF.eval $(qNF.toNF l')) := pf'
    let pf'' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t)) = NF.eval $(qNF.toNF l')) :=
      q(NF.eval_cons_eq_eval_of_eq_of_eq $r $x $pf $pf')
    return ⟨l', pf''⟩

/--
Definition of `split` / `split` 的定义

English:
definition split
  signature: (iM : Q(CommGroupWithZero $M)) (l : qNF M)
  body: match l with
  | [] => return ⟨[], [], q(Eq.symm (div_one (1:$M)))⟩
  | ((r, x), i) :: t => do
    let ⟨t_n, t_d, pf⟩ ← split iM t
    if r > 0 then
      return ⟨((r, x), i) :: t_n, t_d, (q(NF.cons_eq_div_of_eq_div $r $x $pf):)⟩
    else if r = 0 then
      return ⟨((1, x), i) :: t_n, ((1, x), i) :: t_d, (q(NF.cons_zero_eq_div_of_eq_div $x $pf):)⟩
    else
      let r' : Int := -r
      return ⟨t_n, ((r', x), i) :: t_d, (q(NF.cons_eq_div_of_eq_div' $r' $x $pf):)⟩

中文:
定义 split
  签名: (iM : Q(带零交换群 $M)) (l : qNF M)
  定义体: match l with
  | [] => return ⟨[], [], q(Eq.symm (div_one (1:$M)))⟩
  | ((r, x), i) :: t => do
    let ⟨t_n, t_d, pf⟩ ← split iM t
    if r > 0 then
      return ⟨((r, x), i) :: t_n, t_d, (q(NF.cons_eq_div_of_eq_div $r $x $pf):)⟩
    else if r = 0 then
      return ⟨((1, x), i) :: t_n, ((1, x), i) :: t_d, (q(NF.cons_zero_eq_div_of_eq_div $x $pf):)⟩
    else
      let r' : Int := -r
      return ⟨t_n, ((r', x), i) :: t_d, (q(NF.cons_eq_div_of_eq_div' $r' $x $pf):)⟩

Depends on / 依赖: Eq.symm, NF.cons_eq_div_of_eq_div, NF.cons_zero_eq_div_of_eq_div, cons_eq_div_of_eq_div, cons_zero_eq_div_of_eq_div, div_one, return
-/
def split (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ l_n l_d : qNF M, Q(NF.eval $(l.toNF)
= NF.eval (l_n.toNF) / NF.eval (l_d.toNF))) :=
  match l with
  | [] => return ⟨[], [], q(Eq.symm (div_one (1:$M)))⟩
  | ((r, x), i) :: t => do
    let ⟨t_n, t_d, pf⟩ ← split iM t
    if r > 0 then
      return ⟨((r, x), i) :: t_n, t_d, (q(NF.cons_eq_div_of_eq_div $r $x $pf):)⟩
    else if r = 0 then
      return ⟨((1, x), i) :: t_n, ((1, x), i) :: t_d, (q(NF.cons_zero_eq_div_of_eq_div $x $pf):)⟩
    else
      let r' : Int := -r
      return ⟨t_n, ((r', x), i) :: t_d, (q(NF.cons_eq_div_of_eq_div' $r' $x $pf):)⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evalPrettyAux` / `evalPrettyAux` 的定义

English:
definition evalPrettyAux
  signature: (iM : Q(CommGroupWithZero $M)) (l : qNF M)
  body: match l with
  | [] => return ⟨q(1), q(rfl)⟩
  | [((r, x), _)] => do
    let ⟨e, pf⟩ ← evalPrettyMonomial q(inferInstance) r x
    return ⟨e, q(by rw [NF.eval_cons]; exact Eq.trans (one_mul _) $pf)⟩
  | ((r, x), k) :: t => do
    let ⟨e, pf_e⟩ ← evalPrettyMonomial q(inferInstance) r x
    let ⟨t', pf⟩ ← evalPrettyAux iM t
    have pf'' : Q(NF.eval $(qNF.toNF (((r, x), k) :: t)) = (NF.eval $(qNF.toNF t)) * zpow' $x $r) :=
      (q(NF.eval_cons ($r, $x) $(qNF.toNF t)):)
    return ⟨q($t' * $e), q(Eq.trans $pf'' (congr_arg₂ HMul.hMul $pf $pf_e))⟩

中文:
定义 evalPrettyAux
  签名: (iM : Q(带零交换群 $M)) (l : qNF M)
  定义体: match l with
  | [] => return ⟨q(1), q(rfl)⟩
  | [((r, x), _)] => do
    let ⟨e, pf⟩ ← evalPrettyMonomial q(inferInstance) r x
    return ⟨e, q(by rw [NF.eval_cons]; exact Eq.trans (one_mul _) $pf)⟩
  | ((r, x), k) :: t => do
    let ⟨e, pf_e⟩ ← evalPrettyMonomial q(inferInstance) r x
    let ⟨t', pf⟩ ← evalPrettyAux iM t
    have pf'' : Q(NF.eval $(qNF.toNF (((r, x), k) :: t)) = (NF.eval $(qNF.toNF t)) * zpow' $x $r) :=
      (q(NF.eval_cons ($r, $x) $(qNF.toNF t)):)
    return ⟨q($t' * $e), q(Eq.trans $pf'' (congr_arg₂ HMul.hMul $pf $pf_e))⟩
-/
private def evalPrettyAux (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) :=
  match l with
  | [] => return ⟨q(1), q(rfl)⟩
  | [((r, x), _)] => do
    let ⟨e, pf⟩ ← evalPrettyMonomial q(inferInstance) r x
    return ⟨e, q(by rw [NF.eval_cons]; exact Eq.trans (one_mul _) $pf)⟩
  | ((r, x), k) :: t => do
    let ⟨e, pf_e⟩ ← evalPrettyMonomial q(inferInstance) r x
    let ⟨t', pf⟩ ← evalPrettyAux iM t
    have pf'' : Q(NF.eval $(qNF.toNF (((r, x), k) :: t)) = (NF.eval $(qNF.toNF t)) * zpow' $x $r) :=
      (q(NF.eval_cons ($r, $x) $(qNF.toNF t)):)
    return ⟨q($t' * $e), q(Eq.trans $pf'' (congr_arg₂ HMul.hMul $pf $pf_e))⟩

/--
Definition of `evalPretty` / `evalPretty` 的定义

English:
definition evalPretty
  signature: (iM : Q(CommGroupWithZero $M)) (l : qNF M)
  body: do
  let ⟨l_n, l_d, pf⟩ ← split iM l
  let ⟨num, pf_n⟩ ← evalPrettyAux q(inferInstance) l_n
  let ⟨den, pf_d⟩ ← evalPrettyAux q(inferInstance) l_d
  match (dependent := true) l_d with
  | [] => return ⟨num, q(eq_div_of_eq_one_of_subst $pf $pf_n)⟩
  | _ =>
    let pf_n : Q(NF.eval $(l_n.toNF) = $num) := pf_n
    let pf_d : Q(NF.eval $(l_d.toNF) = $den) := pf_d
    let pf : Q(NF.eval $(l.toNF) = NF.eval $(l_n.toNF) / NF.eval $(l_d.toNF)) := pf
    let pf_tot := q(eq_div_of_subst $pf $pf_n $pf_d)
    return ⟨q($num / $den), pf_tot⟩

中文:
定义 evalPretty
  签名: (iM : Q(带零交换群 $M)) (l : qNF M)
  定义体: do
  let ⟨l_n, l_d, pf⟩ ← split iM l
  let ⟨num, pf_n⟩ ← evalPrettyAux q(inferInstance) l_n
  let ⟨den, pf_d⟩ ← evalPrettyAux q(inferInstance) l_d
  match (dependent := true) l_d with
  | [] => return ⟨num, q(eq_div_of_eq_one_of_subst $pf $pf_n)⟩
  | _ =>
    let pf_n : Q(NF.eval $(l_n.toNF) = $num) := pf_n
    let pf_d : Q(NF.eval $(l_d.toNF) = $den) := pf_d
    let pf : Q(NF.eval $(l.toNF) = NF.eval $(l_n.toNF) / NF.eval $(l_d.toNF)) := pf
    let pf_tot := q(eq_div_of_subst $pf $pf_n $pf_d)
    return ⟨q($num / $den), pf_tot⟩
-/
def evalPretty (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) := do
  let ⟨l_n, l_d, pf⟩ ← split iM l
  let ⟨num, pf_n⟩ ← evalPrettyAux q(inferInstance) l_n
  let ⟨den, pf_d⟩ ← evalPrettyAux q(inferInstance) l_d
  match (dependent := true) l_d with
  | [] => return ⟨num, q(eq_div_of_eq_one_of_subst $pf $pf_n)⟩
  | _ =>
    let pf_n : Q(NF.eval $(l_n.toNF) = $num) := pf_n
    let pf_d : Q(NF.eval $(l_d.toNF) = $den) := pf_d
    let pf : Q(NF.eval $(l.toNF) = NF.eval $(l_n.toNF) / NF.eval $(l_d.toNF)) := pf
    let pf_tot := q(eq_div_of_subst $pf $pf_n $pf_d)
    return ⟨q($num / $den), pf_tot⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : qNF q($M) -> qNF q($M) -> qNF q($M)

中文:
定义 mul
  签名: : qNF q($M) -> qNF q($M) -> qNF q($M)
-/
def mul : qNF q($M) -> qNF q($M) -> qNF q($M)
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: mul t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      /- If we can prove that the atom is nonzero then we could remove it from this list,
      but this will be done at a later stage. -/
      ((a₁ + a₂, x₁), k₁) :: mul t₁ t₂
    else
      ((a₂, x₂), k₂) :: mul (((a₁, x₁), k₁) :: t₁) t₂

/--
Definition of `mkMulProof` / `mkMulProof` 的定义

English:
definition mkMulProof
  signature: (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M)
  body: match l₁, l₂ with
  | [], l => (q(one_mul (NF.eval $(l.toNF))):)
  | l, [] => (q(mul_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkMulProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.mul_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkMulProof iM t₁ t₂
      (q(NF.mul_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkMulProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.mul_eq_eval₃ ($a₂, $x₂) $pf):)

中文:
定义 mkMulProof
  签名: (iM : Q(带零交换群 $M)) (l₁ l₂ : qNF M)
  定义体: match l₁, l₂ with
  | [], l => (q(one_mul (NF.eval $(l.toNF))):)
  | l, [] => (q(mul_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkMulProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.mul_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkMulProof iM t₁ t₂
      (q(NF.mul_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkMulProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.mul_eq_eval₃ ($a₂, $x₂) $pf):)

Depends on / 依赖: NF.eval, NF.mul_eq_eval, l.toNF, mkMulProof, mul_one, one_mul
-/
def mkMulProof (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M) :
    Q((NF.eval $(l₁.toNF)) * NF.eval $(l₂.toNF) = NF.eval $((qNF.mul l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(one_mul (NF.eval $(l.toNF))):)
  | l, [] => (q(mul_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkMulProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.mul_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkMulProof iM t₁ t₂
      (q(NF.mul_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkMulProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.mul_eq_eval₃ ($a₂, $x₂) $pf):)

/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: : qNF M -> qNF M -> qNF M

中文:
定义 div
  签名: : qNF M -> qNF M -> qNF M
-/
def div : qNF M -> qNF M -> qNF M
  | [], l => l.onExponent Neg.neg
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: div t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((a₁ - a₂, x₁), k₁) :: div t₁ t₂
    else
      ((-a₂, x₂), k₂) :: div (((a₁, x₁), k₁) :: t₁) t₂

/--
Definition of `mkDivProof` / `mkDivProof` 的定义

English:
definition mkDivProof
  signature: (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M)
  body: match l₁, l₂ with
  | [], l => (q(NF.one_div_eq_eval $(l.toNF)):)
  | l, [] => (q(div_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkDivProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.div_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkDivProof iM t₁ t₂
      (q(NF.div_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.div_eq_eval₃ ($a₂, $x₂) $pf):)

中文:
定义 mkDivProof
  签名: (iM : Q(带零交换群 $M)) (l₁ l₂ : qNF M)
  定义体: match l₁, l₂ with
  | [], l => (q(NF.one_div_eq_eval $(l.toNF)):)
  | l, [] => (q(div_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkDivProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.div_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkDivProof iM t₁ t₂
      (q(NF.div_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.div_eq_eval₃ ($a₂, $x₂) $pf):)

Depends on / 依赖: NF.div_eq_eval, NF.eval, NF.one_div_eq_eval, div_one, l.toNF, mkDivProof, one_div_eq_eval
-/
def mkDivProof (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M) :
    Q(NF.eval $(l₁.toNF) / NF.eval $(l₂.toNF) = NF.eval $((qNF.div l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.one_div_eq_eval $(l.toNF)):)
  | l, [] => (q(div_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkDivProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.div_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkDivProof iM t₁ t₂
      (q(NF.div_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.div_eq_eval₃ ($a₂, $x₂) $pf):)

end qNF

/--
Inductive type `DenomCondition` / 归纳类型 `DenomCondition`

English:
inductive DenomCondition
  parameters: (iM : Q(GroupWithZero $M))
  constructors (3):
    - none: 
    - nonzero: 
    - positive: (iM' : Q(PartialOrder $M)) (iM'' : Q(PosMulStrictMono $M)) (iM''' : Q(PosMulReflectLT $M)) (iM'''' : Q(ZeroLEOneClass $M))

中文:
归纳类型 DenomCondition
  参数: (iM : Q(带零群 $M))
  构造子 (3 个):
    - none: 
    - nonzero: 
    - positive: (iM' : Q(偏序 $M)) (iM'' : Q(正乘严格递增 $M)) (iM''' : Q(正乘反映严格偏序 $M)) (iM'''' : Q(ZeroLEOne类 $M))
-/
inductive DenomCondition (iM : Q(GroupWithZero $M))
  | none
  | nonzero
  | positive (iM' : Q(PartialOrder $M)) (iM'' : Q(PosMulStrictMono $M))
      (iM''' : Q(PosMulReflectLT $M)) (iM'''' : Q(ZeroLEOneClass $M))

namespace DenomCondition

/--
Definition of `proof` / `proof` 的定义

English:
definition proof
  signature: {iM : Q(GroupWithZero $M)} (L : qNF M)

中文:
定义 proof
  签名: {iM : Q(带零群 $M)} (L : qNF M)
-/
@[expose] def proof {iM : Q(GroupWithZero $M)} (L : qNF M) : DenomCondition iM -> Type
  | .none => Unit
  | .nonzero => Q(NF.eval $(qNF.toNF L) != 0)
  | .positive _ _ _ _ => Q(0 < NF.eval $(qNF.toNF L))

/--
Definition of `proofZero` / `proofZero` 的定义

English:
definition proofZero
  signature: {iM : Q(CommGroupWithZero $M)}

中文:
定义 proofZero
  签名: {iM : Q(带零交换群 $M)}

Depends on / 依赖: cond.proof
-/
def proofZero {iM : Q(CommGroupWithZero $M)} :
    forall cond : DenomCondition (M := M) q(inferInstance), cond.proof []
  | .none => Unit.unit
  | .nonzero => q(one_ne_zero (α := $M))
  | .positive _ _ _ _ => q(zero_lt_one (α := $M))

end DenomCondition

/--
Definition of `mkDenomConditionProofSucc` / `mkDenomConditionProofSucc` 的定义

English:
definition mkDenomConditionProofSucc
  signature: {iM : Q(CommGroupWithZero $M)}
  body: match cond with
  | .none => return (← disch q($e != 0), Unit.unit)
  | .nonzero => do
    let pf ← disch q($e != 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := hL
    return (pf, q(NF.cons_ne_zero $r $pf $pf₀))
  | .positive _ _ _ _ => do
    let pf ← disch q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    let pf' := q(NF.cons_pos $r (x := $e) $pf $pf₀)
    return (q(LT.lt.ne' $pf), pf')

中文:
定义 mkDenomConditionProofSucc
  签名: {iM : Q(带零交换群 $M)}
  定义体: match cond with
  | .none => return (← disch q($e != 0), Unit.unit)
  | .nonzero => do
    let pf ← disch q($e != 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := hL
    return (pf, q(NF.cons_ne_zero $r $pf $pf₀))
  | .positive _ _ _ _ => do
    let pf ← disch q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    let pf' := q(NF.cons_pos $r (x := $e) $pf $pf₀)
    return (q(LT.lt.ne' $pf), pf')
-/
def mkDenomConditionProofSucc {iM : Q(CommGroupWithZero $M)}
    (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    {cond : DenomCondition (M := M) q(inferInstance)}
    {L : qNF M} (hL : cond.proof L) (e : Q($M)) (r : Int) (i : Nat) :
    MetaM (Q($e != 0) × cond.proof (((r, e), i) :: L)) :=
  match cond with
  | .none => return (← disch q($e != 0), Unit.unit)
  | .nonzero => do
    let pf ← disch q($e != 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := hL
    return (pf, q(NF.cons_ne_zero $r $pf $pf₀))
  | .positive _ _ _ _ => do
    let pf ← disch q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    let pf' := q(NF.cons_pos $r (x := $e) $pf $pf₀)
    return (q(LT.lt.ne' $pf), pf')

/--
Definition of `mkDenomConditionProofSucc'` / `mkDenomConditionProofSucc'` 的定义

English:
definition mkDenomConditionProofSucc'
  signature: {iM : Q(CommGroupWithZero $M)}
  body: match cond with
  | .none => return Unit.unit
  | .nonzero => do
    let pf ← disch q($e != 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := hL
    return q(NF.cons_ne_zero $r $pf $pf₀)
  | .positive _ _ _ _ => do
    let pf ← disch q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    return q(NF.cons_pos $r (x := $e) $pf $pf₀)

中文:
定义 mkDenomConditionProofSucc'
  签名: {iM : Q(带零交换群 $M)}
  定义体: match cond with
  | .none => return Unit.unit
  | .nonzero => do
    let pf ← disch q($e != 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := hL
    return q(NF.cons_ne_zero $r $pf $pf₀)
  | .positive _ _ _ _ => do
    let pf ← disch q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    return q(NF.cons_pos $r (x := $e) $pf $pf₀)
-/
def mkDenomConditionProofSucc' {iM : Q(CommGroupWithZero $M)}
    (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    {cond : DenomCondition (M := M) q(inferInstance)}
    {L : qNF M} (hL : cond.proof L) (e : Q($M)) (r : Int) (i : Nat) :
    MetaM (cond.proof (((r, e), i) :: L)) :=
  match cond with
  | .none => return Unit.unit
  | .nonzero => do
    let pf ← disch q($e != 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := hL
    return q(NF.cons_ne_zero $r $pf $pf₀)
  | .positive _ _ _ _ => do
    let pf ← disch q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    return q(NF.cons_pos $r (x := $e) $pf $pf₀)

namespace qNF

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M)
  body: /- Handle the case where atom `i` is present in the first list but not the second. -/
  let absent (l₁ l₂ : qNF M) (n : Int) (e : Q($M)) (i : Nat) :
MetaM Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n, e), i) :: l₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM l₁ l₂ disch cond
    if 0 < n then
      -- Don't pull anything out
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩
    else if n = 0 then
      -- Don't pull anything out, but eliminate the term if it is a cancellable zero
      let ⟨l₁'', pf''⟩ ← tryClearZero disch iM 0 e i l₁'
      let pf'' : Q(NF.eval ((0, $e) ::ᵣ $(l₁'.toNF)) = NF.eval $(l₁''.toNF)) := pf''
      return ⟨L, l₁'', l₂', (q(NF.eval_mul_eval_cons_zero $pf₁ $pf''):), q($pf₂), pf₀⟩
    try
      let (pf, b) ← mkDenomConditionProofSucc disch pf₀ e n i
      -- if nonzeroness proof succeeds
      return ⟨((n, e), i) :: L, l₁', ((-n, e), i) :: l₂', (q(NF.eval_cons_mul_eval $n $e $pf₁):),
        (q(NF.eval_cons_mul_eval_cons_neg $n $pf $pf₂):), b⟩
    catch _ =>
      -- if we can't prove nonzeroness, don't pull out e.
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩

  /- Handle the case where atom `i` is present in both lists. -/
  let bothPresent (t₁ t₂ : qNF M) (n₁ n₂ : Int) (e : Q($M)) (i : Nat) :
MetaM Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n₁, e), i) :: t₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(qNF.toNF (((n₂, e), i) :: t₂))) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch cond
    if n₁ < n₂ then
      let N : Int := n₂ - n₁
      return ⟨((n₁, e), i) :: L, l₁', ((n₂ - n₁, e), i) :: l₂',
        (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):), (q(NF.mul_eq_eval₂ $n₁ $N $e $pf₂):),
        ← mkDenomConditionProofSucc' disch pf₀ e n₁ i⟩
    else if n₁ = n₂ then
      return ⟨((n₁, e), i) :: L, l₁', l₂', (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):),
        (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):), ← mkDenomConditionProofSucc' disch pf₀ e n₁ i⟩
    else
      let N : Int := n₁ - n₂
      return ⟨((n₂, e), i) :: L, ((n₁ - n₂, e), i) :: l₁', l₂',
        (q(NF.mul_eq_eval₂ $n₂ $N $e $pf₁):), (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):),
        ← mkDenomConditionProofSucc' disch pf₀ e n₂ i⟩

  match l₁, l₂ with
  | [], [] => pure ⟨[], [], [],
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):),
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):), cond.proofZero⟩
  | ((n, e), i) :: t, [] => do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | [], ((n, e), i) :: t => do
    let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | ((n₁, e₁), i₁) :: t₁, ((n₂, e₂), i₂) :: t₂ => do
    if i₁ > i₂ then
      let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t₁ (((n₂, e₂), i₂) :: t₂) n₁ e₁ i₁
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
    else if i₁ == i₂ then
      try
        bothPresent t₁ t₂ n₁ n₂ e₁ i₁
      catch _ =>
        -- if `bothPresent` fails, don't pull out `e`
        -- the failure case of `bothPresent` should be:
        -- * `.none` case: never
        -- * `.nonzero` case: if `e` can't be proved nonzero
        -- * `.positive _` case: if `e` can't be proved positive
        let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch cond
        return ⟨L, ((n₁, e₁), i₁) :: l₁', ((n₂, e₂), i₂) :: l₂',
          (q(NF.eval_mul_eval_cons $n₁ $e₁ $pf₁):), (q(NF.eval_mul_eval_cons $n₂ $e₂ $pf₂):), pf₀⟩
    else
      let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t₂ (((n₁, e₁), i₁) :: t₁) n₂ e₂ i₂
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩

中文:
定义 最大公约数
  签名: (iM : Q(带零交换群 $M)) (l₁ l₂ : qNF M)
  定义体: /- Handle the case where atom `i` is present in the first list but not the second. -/
  let absent (l₁ l₂ : qNF M) (n : Int) (e : Q($M)) (i : Nat) :
MetaM Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n, e), i) :: l₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM l₁ l₂ disch cond
    if 0 < n then
      -- Don't pull anything out
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩
    else if n = 0 then
      -- Don't pull anything out, but eliminate the term if it is a cancellable zero
      let ⟨l₁'', pf''⟩ ← tryClearZero disch iM 0 e i l₁'
      let pf'' : Q(NF.eval ((0, $e) ::ᵣ $(l₁'.toNF)) = NF.eval $(l₁''.toNF)) := pf''
      return ⟨L, l₁'', l₂', (q(NF.eval_mul_eval_cons_zero $pf₁ $pf''):), q($pf₂), pf₀⟩
    try
      let (pf, b) ← mkDenomConditionProofSucc disch pf₀ e n i
      -- if nonzeroness proof succeeds
      return ⟨((n, e), i) :: L, l₁', ((-n, e), i) :: l₂', (q(NF.eval_cons_mul_eval $n $e $pf₁):),
        (q(NF.eval_cons_mul_eval_cons_neg $n $pf $pf₂):), b⟩
    catch _ =>
      -- if we can't prove nonzeroness, don't pull out e.
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩

  /- Handle the case where atom `i` is present in both lists. -/
  let bothPresent (t₁ t₂ : qNF M) (n₁ n₂ : Int) (e : Q($M)) (i : Nat) :
MetaM Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n₁, e), i) :: t₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(qNF.toNF (((n₂, e), i) :: t₂))) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch cond
    if n₁ < n₂ then
      let N : Int := n₂ - n₁
      return ⟨((n₁, e), i) :: L, l₁', ((n₂ - n₁, e), i) :: l₂',
        (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):), (q(NF.mul_eq_eval₂ $n₁ $N $e $pf₂):),
        ← mkDenomConditionProofSucc' disch pf₀ e n₁ i⟩
    else if n₁ = n₂ then
      return ⟨((n₁, e), i) :: L, l₁', l₂', (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):),
        (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):), ← mkDenomConditionProofSucc' disch pf₀ e n₁ i⟩
    else
      let N : Int := n₁ - n₂
      return ⟨((n₂, e), i) :: L, ((n₁ - n₂, e), i) :: l₁', l₂',
        (q(NF.mul_eq_eval₂ $n₂ $N $e $pf₁):), (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):),
        ← mkDenomConditionProofSucc' disch pf₀ e n₂ i⟩

  match l₁, l₂ with
  | [], [] => pure ⟨[], [], [],
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):),
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):), cond.proofZero⟩
  | ((n, e), i) :: t, [] => do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | [], ((n, e), i) :: t => do
    let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | ((n₁, e₁), i₁) :: t₁, ((n₂, e₂), i₂) :: t₂ => do
    if i₁ > i₂ then
      let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t₁ (((n₂, e₂), i₂) :: t₂) n₁ e₁ i₁
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
    else if i₁ == i₂ then
      try
        bothPresent t₁ t₂ n₁ n₂ e₁ i₁
      catch _ =>
        -- if `bothPresent` fails, don't pull out `e`
        -- the failure case of `bothPresent` should be:
        -- * `.none` case: never
        -- * `.nonzero` case: if `e` can't be proved nonzero
        -- * `.positive _` case: if `e` can't be proved positive
        let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch cond
        return ⟨L, ((n₁, e₁), i₁) :: l₁', ((n₂, e₂), i₂) :: l₂',
          (q(NF.eval_mul_eval_cons $n₁ $e₁ $pf₁):), (q(NF.eval_mul_eval_cons $n₂ $e₂ $pf₂):), pf₀⟩
    else
      let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t₂ (((n₁, e₁), i₁) :: t₁) n₂ e₂ i₂
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
-/
partial def gcd (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M)
    (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (cond : DenomCondition (M := M) q(inferInstance)) :
MetaM Σ (L l₁' l₂' : qNF M),
    Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)) ×
    Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
    cond.proof L :=

  /- Handle the case where atom `i` is present in the first list but not the second. -/
  let absent (l₁ l₂ : qNF M) (n : Int) (e : Q($M)) (i : Nat) :
MetaM Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n, e), i) :: l₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM l₁ l₂ disch cond
    if 0 < n then
      -- Don't pull anything out
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩
    else if n = 0 then
      -- Don't pull anything out, but eliminate the term if it is a cancellable zero
      let ⟨l₁'', pf''⟩ ← tryClearZero disch iM 0 e i l₁'
      let pf'' : Q(NF.eval ((0, $e) ::ᵣ $(l₁'.toNF)) = NF.eval $(l₁''.toNF)) := pf''
      return ⟨L, l₁'', l₂', (q(NF.eval_mul_eval_cons_zero $pf₁ $pf''):), q($pf₂), pf₀⟩
    try
      let (pf, b) ← mkDenomConditionProofSucc disch pf₀ e n i
      -- if nonzeroness proof succeeds
      return ⟨((n, e), i) :: L, l₁', ((-n, e), i) :: l₂', (q(NF.eval_cons_mul_eval $n $e $pf₁):),
        (q(NF.eval_cons_mul_eval_cons_neg $n $pf $pf₂):), b⟩
    catch _ =>
      -- if we can't prove nonzeroness, don't pull out e.
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩

  /- Handle the case where atom `i` is present in both lists. -/
  let bothPresent (t₁ t₂ : qNF M) (n₁ n₂ : Int) (e : Q($M)) (i : Nat) :
MetaM Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n₁, e), i) :: t₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(qNF.toNF (((n₂, e), i) :: t₂))) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch cond
    if n₁ < n₂ then
      let N : Int := n₂ - n₁
      return ⟨((n₁, e), i) :: L, l₁', ((n₂ - n₁, e), i) :: l₂',
        (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):), (q(NF.mul_eq_eval₂ $n₁ $N $e $pf₂):),
        ← mkDenomConditionProofSucc' disch pf₀ e n₁ i⟩
    else if n₁ = n₂ then
      return ⟨((n₁, e), i) :: L, l₁', l₂', (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):),
        (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):), ← mkDenomConditionProofSucc' disch pf₀ e n₁ i⟩
    else
      let N : Int := n₁ - n₂
      return ⟨((n₂, e), i) :: L, ((n₁ - n₂, e), i) :: l₁', l₂',
        (q(NF.mul_eq_eval₂ $n₂ $N $e $pf₁):), (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):),
        ← mkDenomConditionProofSucc' disch pf₀ e n₂ i⟩

  match l₁, l₂ with
  | [], [] => pure ⟨[], [], [],
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):),
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):), cond.proofZero⟩
  | ((n, e), i) :: t, [] => do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | [], ((n, e), i) :: t => do
    let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | ((n₁, e₁), i₁) :: t₁, ((n₂, e₂), i₂) :: t₂ => do
    if i₁ > i₂ then
      let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t₁ (((n₂, e₂), i₂) :: t₂) n₁ e₁ i₁
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
    else if i₁ == i₂ then
      try
        bothPresent t₁ t₂ n₁ n₂ e₁ i₁
      catch _ =>
        -- if `bothPresent` fails, don't pull out `e`
        -- the failure case of `bothPresent` should be:
        -- * `.none` case: never
        -- * `.nonzero` case: if `e` can't be proved nonzero
        -- * `.positive _` case: if `e` can't be proved positive
        let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch cond
        return ⟨L, ((n₁, e₁), i₁) :: l₁', ((n₂, e₂), i₂) :: l₂',
          (q(NF.eval_mul_eval_cons $n₁ $e₁ $pf₁):), (q(NF.eval_mul_eval_cons $n₂ $e₂ $pf₂):), pf₀⟩
    else
      let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t₂ (((n₁, e₁), i₁) :: t₁) n₂ e₂ i₂
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩

end qNF

/-! ### Core of the `field_simp` tactic -/

/--
Definition of `normalize` / `normalize` 的定义

English:
definition normalize
  signature: (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
  body: do
  let baseCase (y : Q($M)) (normalize? : Bool) :
      AtomM (Σ (l : qNF M), Q($y = NF.eval $(l.toNF))) := do
    if normalize? then
      let r ← (← read).evalAtom y
      have y' : Q($M) := r.expr
      have pf : Q($y = $y') := ← r.getProof
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y'
      pure ⟨[((1, x'), k)], q(Eq.trans $pf (NF.atom_eq_eval $x'))⟩
    else
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y
      pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    have pf := qNF.mkMulProof iM l₁ l₂
    let ⟨G, pf_y⟩ ← Sign.mul iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ * $y₂), ⟨G, q(Eq.trans (congr_arg₂ HMul.hMul $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.mul l₁ l₂, q(NF.mul_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize a division: `x₁ / x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    let ⟨G, pf_y⟩ ← Sign.div iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ / $y₂), ⟨G, q(Eq.trans (congr_arg₂ HDiv.hDiv $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.div l₁ l₂, q(NF.div_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize an inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
    let pf_y ← Sign.inv iM y' g
    -- build the new list and proof, casing according to the sign of `x`
    pure ⟨q($y'⁻¹), ⟨g, q(Eq.trans (congr_arg Inv.inv $pf_sgn) $pf_y)⟩,
      l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : Int)) =>
    let some s := Expr.int? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(zpow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s != 0)
      let ⟨G, pf_y⟩ ← Sign.zpow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (HMul.hMul s), (q(NF.zpow_eq_eval $pf_s $pf):)⟩
  /- normalize a natural number exponentiation: `y ^ (s : ℕ)` -/
  | ~q($y ^ ($s : Nat)) =>
    let some s := Expr.nat? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(pow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s != 0)
      let ⟨G, pf_y⟩ ← Sign.pow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (↑s * ·), (q(NF.pow_eq_eval $pf_s $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) => pure ⟨q(1), ⟨Sign.plus, q(rfl)⟩, [], q(NF.one_eq_eval $M)⟩
  /- normalize an addition: `a + b` -/
  | ~q(HAdd.hAdd (self := @instHAdd _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Semifield $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) + $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_add $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a subtraction: `a - b` -/
  | ~q(HSub.hSub (self := @instHSub _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) - $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_sub $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a negation: `-a` -/
  | ~q(Neg.neg (self := $i) $a) =>
    try
      let iM' ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM a
      let ⟨G, pf_y⟩ ← Sign.neg iM' y g
      pure ⟨y, ⟨G, q(Eq.trans (congr_arg Neg.neg $pf_sgn) $pf_y)⟩, l, pf⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  -- TODO special-case handling of zero? maybe not necessary
  /- anything else should be treated as an atom -/
  | _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩

中文:
定义 normalize
  签名: (disch : 对任意 {u : Level} (type : Q(类型层 u)), MetaM Q($type))
  定义体: do
  let baseCase (y : Q($M)) (normalize? : Bool) :
      AtomM (Σ (l : qNF M), Q($y = NF.eval $(l.toNF))) := do
    if normalize? then
      let r ← (← read).evalAtom y
      have y' : Q($M) := r.expr
      have pf : Q($y = $y') := ← r.getProof
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y'
      pure ⟨[((1, x'), k)], q(Eq.trans $pf (NF.atom_eq_eval $x'))⟩
    else
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y
      pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    have pf := qNF.mkMulProof iM l₁ l₂
    let ⟨G, pf_y⟩ ← Sign.mul iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ * $y₂), ⟨G, q(Eq.trans (congr_arg₂ HMul.hMul $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.mul l₁ l₂, q(NF.mul_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize a division: `x₁ / x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    let ⟨G, pf_y⟩ ← Sign.div iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ / $y₂), ⟨G, q(Eq.trans (congr_arg₂ HDiv.hDiv $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.div l₁ l₂, q(NF.div_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize an inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
    let pf_y ← Sign.inv iM y' g
    -- build the new list and proof, casing according to the sign of `x`
    pure ⟨q($y'⁻¹), ⟨g, q(Eq.trans (congr_arg Inv.inv $pf_sgn) $pf_y)⟩,
      l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : Int)) =>
    let some s := Expr.int? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(zpow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s != 0)
      let ⟨G, pf_y⟩ ← Sign.zpow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (HMul.hMul s), (q(NF.zpow_eq_eval $pf_s $pf):)⟩
  /- normalize a natural number exponentiation: `y ^ (s : ℕ)` -/
  | ~q($y ^ ($s : Nat)) =>
    let some s := Expr.nat? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(pow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s != 0)
      let ⟨G, pf_y⟩ ← Sign.pow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (↑s * ·), (q(NF.pow_eq_eval $pf_s $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) => pure ⟨q(1), ⟨Sign.plus, q(rfl)⟩, [], q(NF.one_eq_eval $M)⟩
  /- normalize an addition: `a + b` -/
  | ~q(HAdd.hAdd (self := @instHAdd _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Semifield $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) + $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_add $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a subtraction: `a - b` -/
  | ~q(HSub.hSub (self := @instHSub _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) - $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_sub $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a negation: `-a` -/
  | ~q(Neg.neg (self := $i) $a) =>
    try
      let iM' ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM a
      let ⟨G, pf_y⟩ ← Sign.neg iM' y g
      pure ⟨y, ⟨G, q(Eq.trans (congr_arg Neg.neg $pf_sgn) $pf_y)⟩, l, pf⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  -- TODO special-case handling of zero? maybe not necessary
  /- anything else should be treated as an atom -/
  | _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
-/
partial def normalize (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (x : Q($M)) :
    AtomM (Σ y : Q($M), (Σ g : Sign M, Q($x = $(g.expr y))) ×
      Σ l : qNF M, Q($y = NF.eval $(l.toNF))) := do
  let baseCase (y : Q($M)) (normalize? : Bool) :
      AtomM (Σ (l : qNF M), Q($y = NF.eval $(l.toNF))) := do
    if normalize? then
      let r ← (← read).evalAtom y
      have y' : Q($M) := r.expr
      have pf : Q($y = $y') := ← r.getProof
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y'
      pure ⟨[((1, x'), k)], q(Eq.trans $pf (NF.atom_eq_eval $x'))⟩
    else
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y
      pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    have pf := qNF.mkMulProof iM l₁ l₂
    let ⟨G, pf_y⟩ ← Sign.mul iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ * $y₂), ⟨G, q(Eq.trans (congr_arg₂ HMul.hMul $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.mul l₁ l₂, q(NF.mul_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize a division: `x₁ / x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    let ⟨G, pf_y⟩ ← Sign.div iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ / $y₂), ⟨G, q(Eq.trans (congr_arg₂ HDiv.hDiv $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.div l₁ l₂, q(NF.div_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize an inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
    let pf_y ← Sign.inv iM y' g
    -- build the new list and proof, casing according to the sign of `x`
    pure ⟨q($y'⁻¹), ⟨g, q(Eq.trans (congr_arg Inv.inv $pf_sgn) $pf_y)⟩,
      l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : Int)) =>
    let some s := Expr.int? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(zpow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s != 0)
      let ⟨G, pf_y⟩ ← Sign.zpow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (HMul.hMul s), (q(NF.zpow_eq_eval $pf_s $pf):)⟩
  /- normalize a natural number exponentiation: `y ^ (s : ℕ)` -/
  | ~q($y ^ ($s : Nat)) =>
    let some s := Expr.nat? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(pow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s != 0)
      let ⟨G, pf_y⟩ ← Sign.pow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (↑s * ·), (q(NF.pow_eq_eval $pf_s $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) => pure ⟨q(1), ⟨Sign.plus, q(rfl)⟩, [], q(NF.one_eq_eval $M)⟩
  /- normalize an addition: `a + b` -/
  | ~q(HAdd.hAdd (self := @instHAdd _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Semifield $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) + $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_add $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a subtraction: `a - b` -/
  | ~q(HSub.hSub (self := @instHSub _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) - $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_sub $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a negation: `-a` -/
  | ~q(Neg.neg (self := $i) $a) =>
    try
      let iM' ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM a
      let ⟨G, pf_y⟩ ← Sign.neg iM' y g
      pure ⟨y, ⟨G, q(Eq.trans (congr_arg Neg.neg $pf_sgn) $pf_y)⟩, l, pf⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  -- TODO special-case handling of zero? maybe not necessary
  /- anything else should be treated as an atom -/
  | _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩

/--
Definition of `reduceExprQ` / `reduceExprQ` 的定义

English:
definition reduceExprQ
  signature: (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
  body: do
  let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM x
  let ⟨l', pf'⟩ ← qNF.removeZeros disch iM l
  let ⟨x', pf''⟩ ← qNF.evalPretty iM l'
  let pf_yx : Q($y = $x') := q(Eq.trans (Eq.trans $pf $pf') $pf'')
  return ⟨g.expr x', q(Eq.trans $pf_sgn $(g.congr pf_yx))⟩

中文:
定义 reduceExprQ
  签名: (disch : 对任意 {u : Level} (type : Q(类型层 u)), MetaM Q($type))
  定义体: do
  let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM x
  let ⟨l', pf'⟩ ← qNF.removeZeros disch iM l
  let ⟨x', pf''⟩ ← qNF.evalPretty iM l'
  let pf_yx : Q($y = $x') := q(Eq.trans (Eq.trans $pf $pf') $pf'')
  return ⟨g.expr x', q(Eq.trans $pf_sgn $(g.congr pf_yx))⟩
-/
def reduceExprQ (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (x : Q($M)) : AtomM (Σ x' : Q($M), Q($x = $x')) := do
  let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM x
  let ⟨l', pf'⟩ ← qNF.removeZeros disch iM l
  let ⟨x', pf''⟩ ← qNF.evalPretty iM l'
  let pf_yx : Q($y = $x') := q(Eq.trans (Eq.trans $pf $pf') $pf'')
  return ⟨g.expr x', q(Eq.trans $pf_sgn $(g.congr pf_yx))⟩

/--
Definition of `reduceEqQ` / `reduceEqQ` 的定义

English:
definition reduceEqQ
  signature: (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
  body: do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩ ← l₁.gcd iM l₂ disch .nonzero
  let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(eq_eq_cancel_eq $pf_ef₁ $pf_ef₂ $pf₀)⟩

中文:
定义 reduceEqQ
  签名: (disch : 对任意 {u : Level} (type : Q(类型层 u)), MetaM Q($type))
  定义体: do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩ ← l₁.gcd iM l₂ disch .nonzero
  let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(eq_eq_cancel_eq $pf_ef₁ $pf_ef₂ $pf₀)⟩
-/
def reduceEqQ (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (e₁ e₂ : Q($M)) :
    AtomM (Σ f₁ f₂ : Q($M), Q(($e₁ = $e₂) = ($f₁ = $f₂))) := do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩ ← l₁.gcd iM l₂ disch .nonzero
  let pf₀ : Q(NF.eval $(qNF.toNF L) != 0) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(eq_eq_cancel_eq $pf_ef₁ $pf_ef₂ $pf₀)⟩

/--
Definition of `reduceLeQ` / `reduceLeQ` 的定义

English:
definition reduceLeQ
  signature: (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
  body: do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ disch (.positive iM' iM'' q(inferInstance) iM'''')
  let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(le_eq_cancel_le $pf_ef₁ $pf_ef₂ $pf₀)⟩

中文:
定义 reduceLeQ
  签名: (disch : 对任意 {u : Level} (type : Q(类型层 u)), MetaM Q($type))
  定义体: do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ disch (.positive iM' iM'' q(inferInstance) iM'''')
  let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(le_eq_cancel_le $pf_ef₁ $pf_ef₂ $pf₀)⟩
-/
def reduceLeQ (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (iM' : Q(PartialOrder $M))
    (iM'' : Q(PosMulStrictMono $M)) (iM''' : Q(PosMulReflectLE $M)) (iM'''' : Q(ZeroLEOneClass $M))
    (e₁ e₂ : Q($M)) :
    AtomM (Σ f₁ f₂ : Q($M), Q(($e₁ <= $e₂) = ($f₁ <= $f₂))) := do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ disch (.positive iM' iM'' q(inferInstance) iM'''')
  let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(le_eq_cancel_le $pf_ef₁ $pf_ef₂ $pf₀)⟩

/--
Definition of `reduceLtQ` / `reduceLtQ` 的定义

English:
definition reduceLtQ
  signature: (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
  body: do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ disch (.positive iM' iM'' iM''' iM'''')
  let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(lt_eq_cancel_lt $pf_ef₁ $pf_ef₂ $pf₀)⟩

中文:
定义 reduceLtQ
  签名: (disch : 对任意 {u : Level} (type : Q(类型层 u)), MetaM Q($type))
  定义体: do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ disch (.positive iM' iM'' iM''' iM'''')
  let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(lt_eq_cancel_lt $pf_ef₁ $pf_ef₂ $pf₀)⟩
-/
def reduceLtQ (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (iM' : Q(PartialOrder $M))
    (iM'' : Q(PosMulStrictMono $M)) (iM''' : Q(PosMulReflectLT $M)) (iM'''' : Q(ZeroLEOneClass $M))
    (e₁ e₂ : Q($M)) :
    AtomM (Σ f₁ f₂ : Q($M), Q(($e₁ < $e₂) = ($f₁ < $f₂))) := do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ disch (.positive iM' iM'' iM''' iM'''')
  let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(lt_eq_cancel_lt $pf_ef₁ $pf_ef₂ $pf₀)⟩

/--
Definition of `reduceExpr` / `reduceExpr` 的定义

English:
definition reduceExpr
  signature: (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type)) (x : Expr)
  body: do
  -- for `field_simp` to work with the recursive infrastructure in `AtomM.recurse`, we need to fail
  -- on things `field_simp` would treat as atoms
  guard x.isApp
  let ⟨f, _⟩ := x.getAppFnArgs
guard
    f in [``HMul.hMul, ``HDiv.hDiv, ``Inv.inv, ``HPow.hPow, ``HAdd.hAdd, ``HSub.hSub, ``Neg.neg]
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  -- run the core normalization function `normalizePretty` on `x`
  trace[Tactic.field_simp] "putting {x} in \"field_simp\"-normal-form"
  let ⟨e, pf⟩ ← reduceExprQ disch iK x
  return { expr := e, proof? := some pf }

中文:
定义 reduceExpr
  签名: (disch : 对任意 {u : Level} (type : Q(类型层 u)), MetaM Q($type)) (x : Expr)
  定义体: do
  -- for `field_simp` to work with the recursive infrastructure in `AtomM.recurse`, we need to fail
  -- on things `field_simp` would treat as atoms
  guard x.isApp
  let ⟨f, _⟩ := x.getAppFnArgs
guard
    f in [``HMul.hMul, ``HDiv.hDiv, ``Inv.inv, ``HPow.hPow, ``HAdd.hAdd, ``HSub.hSub, ``Neg.neg]
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  -- run the core normalization function `normalizePretty` on `x`
  trace[Tactic.field_simp] "putting {x} in \"field_simp\"-normal-form"
  let ⟨e, pf⟩ ← reduceExprQ disch iK x
  return { expr := e, proof? := some pf }
-/
def reduceExpr (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type)) (x : Expr) :
    AtomM Simp.Result := do
  -- for `field_simp` to work with the recursive infrastructure in `AtomM.recurse`, we need to fail
  -- on things `field_simp` would treat as atoms
  guard x.isApp
  let ⟨f, _⟩ := x.getAppFnArgs
guard
    f in [``HMul.hMul, ``HDiv.hDiv, ``Inv.inv, ``HPow.hPow, ``HAdd.hAdd, ``HSub.hSub, ``Neg.neg]
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  -- run the core normalization function `normalizePretty` on `x`
  trace[Tactic.field_simp] "putting {x} in \"field_simp\"-normal-form"
  let ⟨e, pf⟩ ← reduceExprQ disch iK x
  return { expr := e, proof? := some pf }

/--
Definition of `reduceProp` / `reduceProp` 的定义

English:
definition reduceProp
  signature: (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type)) (t : Expr)
  body: do
  let ⟨i, _, a, b⟩ ← t.ineq?
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, a⟩ ← inferTypeQ' a
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  trace[Tactic.field_simp] "clearing denominators in {a} ~ {b}"
  -- run the core (in)equality-transforming mechanism on `a =/≤/< b`
  match i with
  | .eq =>
    let ⟨a', b', pf⟩ ← reduceEqQ disch iK a b
    let t' ← mkAppM `Eq #[a', b']
    return { expr := t', proof? := pf }
  | .le =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLE $K) ← synthInstanceQ q(PosMulReflectLE $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLeQ disch iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LE.le #[a', b']
    return { expr := t', proof? := pf }
  | _ =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLT $K) ← synthInstanceQ q(PosMulReflectLT $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLtQ disch iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LT.lt #[a', b']
    return { expr := t', proof? := pf }

中文:
定义 reduceProp
  签名: (disch : 对任意 {u : Level} (type : Q(类型层 u)), MetaM Q($type)) (t : Expr)
  定义体: do
  let ⟨i, _, a, b⟩ ← t.ineq?
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, a⟩ ← inferTypeQ' a
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  trace[Tactic.field_simp] "clearing denominators in {a} ~ {b}"
  -- run the core (in)equality-transforming mechanism on `a =/≤/< b`
  match i with
  | .eq =>
    let ⟨a', b', pf⟩ ← reduceEqQ disch iK a b
    let t' ← mkAppM `Eq #[a', b']
    return { expr := t', proof? := pf }
  | .le =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLE $K) ← synthInstanceQ q(PosMulReflectLE $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLeQ disch iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LE.le #[a', b']
    return { expr := t', proof? := pf }
  | _ =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLT $K) ← synthInstanceQ q(PosMulReflectLT $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLtQ disch iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LT.lt #[a', b']
    return { expr := t', proof? := pf }
-/
def reduceProp (disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type)) (t : Expr) :
    AtomM Simp.Result := do
  let ⟨i, _, a, b⟩ ← t.ineq?
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, a⟩ ← inferTypeQ' a
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  trace[Tactic.field_simp] "clearing denominators in {a} ~ {b}"
  -- run the core (in)equality-transforming mechanism on `a =/≤/< b`
  match i with
  | .eq =>
    let ⟨a', b', pf⟩ ← reduceEqQ disch iK a b
    let t' ← mkAppM `Eq #[a', b']
    return { expr := t', proof? := pf }
  | .le =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLE $K) ← synthInstanceQ q(PosMulReflectLE $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLeQ disch iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LE.le #[a', b']
    return { expr := t', proof? := pf }
  | _ =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLT $K) ← synthInstanceQ q(PosMulReflectLT $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLtQ disch iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LT.lt #[a', b']
    return { expr := t', proof? := pf }

/-! ### Frontend -/

open Elab Tactic Lean.Parser.Tactic

/--
Definition of `parseDischarger` / `parseDischarger` 的定义

English:
definition parseDischarger
  signature: (d : Option (TSyntax ``discharger)) (args : Option (TSyntax ``simpArgs))
  body: do
  match d with
  | none =>
    let ctx ← Simp.Context.ofArgs (args.getD ⟨.missing⟩) { contextual := true }
return fun e => Prod.fst < > (FieldSimp.discharge e).run ctx >>= Option.getM
  | some d =>
    if args.isSome then
      logWarningAt args.get!
        "Custom `field_simp` dischargers do not make use of the `field_simp` arguments list"
    match d with
    | `(discharger| (discharger := $tac)) =>
      let tac := (evalTactic (← `(tactic| ($tac))) *> pruneSolvedGoals)
      return (synthesizeUsing' · tac)
    | _ => throwError "could not parse the provided discharger {d}"

中文:
定义 parseDischarger
  签名: (d : 选项类型 (TSyntax ``discharger)) (args : 选项类型 (TSyntax ``simpArgs))
  定义体: do
  match d with
  | none =>
    let ctx ← Simp.Context.ofArgs (args.getD ⟨.missing⟩) { contextual := true }
return fun e => Prod.fst < > (FieldSimp.discharge e).run ctx >>= Option.getM
  | some d =>
    if args.isSome then
      logWarningAt args.get!
        "Custom `field_simp` dischargers do not make use of the `field_simp` arguments list"
    match d with
    | `(discharger| (discharger := $tac)) =>
      let tac := (evalTactic (← `(tactic| ($tac))) *> pruneSolvedGoals)
      return (synthesizeUsing' · tac)
    | _ => throwError "could not parse the provided discharger {d}"
-/
def parseDischarger (d : Option (TSyntax ``discharger)) (args : Option (TSyntax ``simpArgs)) :
    TacticM (forall {u : Level} (type : Q(Sort u)), MetaM Q($type)) := do
  match d with
  | none =>
    let ctx ← Simp.Context.ofArgs (args.getD ⟨.missing⟩) { contextual := true }
return fun e => Prod.fst < > (FieldSimp.discharge e).run ctx >>= Option.getM
  | some d =>
    if args.isSome then
      logWarningAt args.get!
        "Custom `field_simp` dischargers do not make use of the `field_simp` arguments list"
    match d with
    | `(discharger| (discharger := $tac)) =>
      let tac := (evalTactic (← `(tactic| ($tac))) *> pruneSolvedGoals)
      return (synthesizeUsing' · tac)
    | _ => throwError "could not parse the provided discharger {d}"

/--
`field_simp` normalizes expressions in (semi-)fields (i.e., does not require additive inverses)
by rewriting them to a common denominator, i.e. to reduce them to expressions of the form `n / d`
where neither `n` nor `d` contains any division symbol. The `field_simp` tactic will also clear
denominators in field *(in)equalities*, by cross-multiplying.

A very common pattern is `field_simp; ring` (clear denominators, then the resulting goal is
solvable by the axioms of a commutative ring). The finishing tactic `field` is a shorthand for this
pattern.

The tactic will try discharge proofs of nonzeroness of denominators, and skip steps if discharging
fails. These denominators are made out of denominators appearing in the input expression,
by repeatedly taking products or divisors. The default discharger can be non-universal, i.e. can be
specific to the field at hand (order properties, explicit `≠ 0` hypotheses, `CharZero` if that is
known, etc). See `field_simp_discharge` for full details of the default discharger algorithm.

* `field_simp at l1 l2 ...` can be used to normalize at the given locations.
* `field_simp (disch := tac)` uses the tactic sequence `tac` to discharge nonzeroness/positivity
  proofs.
* `field_simp [t₁, ..., tₙ]` provides terms `t₁`, ..., `tₙ` to the discharger for
  nonzeroness/positivity proofs.

Examples:
```
-- `x / (1 - y) / (1 + y / (1 - y))` is reduced to `x / (1 - y + y)`
example (x y z : ℚ) (hy : 1 - y ≠ 0) :
    ⌊x / (1 - y) / (1 + y / (1 - y))⌋ < 3 := by
  field_simp
  -- new goal: `⊢ ⌊x / (1 - y + y)⌋ < 3`
  sorry

-- `field_simp` will clear the `x` denominators in the following equation
example {K : Type*} [Field K] {x : K} (hx0 : x ≠ 0) :
    (x + 1 / x) ^ 2 + (x + 1 / x) = 1 := by
  field_simp
  -- new goal: `⊢ (x ^ 2 + 1) * (x ^ 2 + 1 + x) = x ^ 2`
  sorry
```
-/
elab (name := fieldSimp) "field_simp" d:(discharger)? args:(simpArgs)? loc:(location)? :
    tactic => withMainContext do
  let disch ← parseDischarger d args
  let s ← IO.mkRef {}
  let cleanup r := do r.mkEqTrans (← simpOnlyNames [] r.expr) -- convert e.g. `x = x` to `True`
  let m := AtomM.recurse s { contextual := true } (wellBehavedDischarge := false)
    (fun e => reduceProp disch e <|> reduceExpr disch e) cleanup
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (m ·) "field_simp" (ifUnchanged := .error) (mayCloseGoalFromHyp := true) loc

/--
`field_simp` normalizes an expression in a (semi-)field by rewriting it to a common denominator,
i.e. to reduce it to an expression of the form `n / d` where neither `n` nor `d` contains any
division symbol.

The `field_simp` conv tactic is a variant of the main (i.e., not conv) `field_simp` tactic. The
latter operates recursively on subexpressions, bringing *every* field-expression encountered to the
form `n / d`.

The tactic will try discharge proofs of nonzeroness of denominators, and skip steps if discharging
fails. These denominators are made out of denominators appearing in the input expression,
by repeatedly taking products or divisors. The default discharger can be non-universal, i.e. can be
specific to the field at hand (order properties, explicit `≠ 0` hypotheses, `CharZero` if that is
known, etc). See `field_simp_discharge` for full details of the default discharger algorithm.

* `field_simp (disch := tac)` uses the tactic sequence `tac` to discharge nonzeroness/positivity
  proofs.
* `field_simp [t₁, ..., tₙ]` provides terms `t₁`, ..., `tₙ` to the discharger for
  nonzeroness/positivity proofs.

Examples:

```
-- `x / (1 - y) / (1 + y / (1 - y))` is reduced to `x / (1 - y + y)`:
example (x y z : ℚ) (hy : 1 - y ≠ 0) :
    ⌊x / (1 - y) / (1 + y / (1 - y))⌋ < 3 := by
  conv => enter [1, 1]; field_simp
  -- new goal: `⊢ ⌊x / (1 - y + y)⌋ < 3`
```
-/
elab "field_simp" d:(discharger)? args:(simpArgs)? : conv => do
  -- find the expression `x` to `conv` on
  let x ← Conv.getLhs
  let disch : forall {u : Level} (type : Q(Sort u)), MetaM Q($type) ← parseDischarger d args
  -- bring into field_simp standard form
let r ← AtomM.run .reducible reduceExpr disch x
  -- convert `x` to the output of the normalization
  Conv.applySimpResult r

/--
Definition of `proc` / `proc` 的定义

English:
definition proc
  signature: : Simp.Simproc
  body: fun (t : Expr) => do
  let ctx ← Simp.getContext
let disch e : MetaM Expr := Prod.fst < > (FieldSimp.discharge e).run ctx >>= Option.getM
  try
let r ← AtomM.run .reducible FieldSimp.reduceProp disch t
    -- the `field_simp`-normal form is in opposition to the `simp`-lemmas `one_div` and `mul_inv`,
    -- so we need to undo any such lemma applications, otherwise we can get infinite loops
return .visit ← r.mkEqTrans (← simpOnlyNames [``one_div, ``mul_inv] r.expr)
  catch _ =>
    return .continue

中文:
定义 proc
  签名: : Simp.Simproc
  定义体: fun (t : Expr) => do
  let ctx ← Simp.getContext
let disch e : MetaM Expr := Prod.fst < > (FieldSimp.discharge e).run ctx >>= Option.getM
  try
let r ← AtomM.run .reducible FieldSimp.reduceProp disch t
    -- the `field_simp`-normal form is in opposition to the `simp`-lemmas `one_div` and `mul_inv`,
    -- so we need to undo any such lemma applications, otherwise we can get infinite loops
return .visit ← r.mkEqTrans (← simpOnlyNames [``one_div, ``mul_inv] r.expr)
  catch _ =>
    return .continue
-/
def proc : Simp.Simproc := fun (t : Expr) => do
  let ctx ← Simp.getContext
let disch e : MetaM Expr := Prod.fst < > (FieldSimp.discharge e).run ctx >>= Option.getM
  try
let r ← AtomM.run .reducible FieldSimp.reduceProp disch t
    -- the `field_simp`-normal form is in opposition to the `simp`-lemmas `one_div` and `mul_inv`,
    -- so we need to undo any such lemma applications, otherwise we can get infinite loops
return .visit ← r.mkEqTrans (← simpOnlyNames [``one_div, ``mul_inv] r.expr)
  catch _ =>
    return .continue

end Mathlib.Tactic.FieldSimp

open Mathlib.Tactic

simproc_decl fieldEq (Eq _ _) := FieldSimp.proc
simproc_decl fieldLe (LE.le _ _) := FieldSimp.proc
simproc_decl fieldLt (LT.lt _ _) := FieldSimp.proc

attribute [field, inherit_doc FieldSimp.proc] fieldEq fieldLe fieldLt

/-!
We register `field_simp` with the `hint` tactic.
-/
register_hint 1000 field_simp
register_try?_tactic (priority := 1000) field_simp
