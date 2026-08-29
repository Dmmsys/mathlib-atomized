/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Tactic.Algebra.Lemmas -- shake: keep (Qq output dependency)
public import Mathlib.Tactic.Ring.RingNF

/-!
# The `algebra` tactic

A suite of three tactics for solving equations in commutative algebras over commutative (semi)rings,
where the exponents can also contain variables.

Based largely on the implementation of `ring`. The `algebra` normal form mirrors that of `ring`
except that the constants are expressions in the base ring that are kept in ring normal form.

## Organization
This tactic is implemented using the machinery of `Ring.Common`

* Normalized expressions are stored as an `Common.ExSum`, with a custom type for
representing coefficients in `R`.
* While `ring` stores coefficients as rational numbers normalized by `norm_num`, `algebra` stores
coefficients as experssions in the base ring `R`, normalized by `ring`.
* These coefficients are sums, not products. The normal form of `a • x + b • x` is `(a + b) • x`.

This tactic is used internally to implement the `polynomial` tactic.

## Limitations
The main limitation of the current implementation is that it does not handle rational constants
when the algebra `A` is a field but the base ring `R` is not. This is never an issue when working
with polynomials, but would be an issue when working with a number field over its ring of integers.

When inferring the base ring, we assume that any two rings `R` and `S` that appear are comparable,
in the sense that either `R` is an `S`-algebra or `S` is an `R`-algebra.

-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic Mathlib.Meta AtomM

public meta section

namespace Mathlib.Tactic.Algebra

attribute [local instance] monadLiftOptionMetaM

open NormNum hiding Result

/--
Definition of `Cache` / `Cache` 的定义

English:
structure Cache
  parameters: {u : Level} {A : Q(Type u)}
  extends: Ring.Common.Cache sA
  axioms and operations (1):
    - field : Option Q(Field $A)

中文:
结构 Cache
  参数: {u : Level} {A : Q(类型u)}
  继承: 环.Common.Cache sA
  公理与运算 (1 个):
    - field : 选项类型 Q(域 $A)
-/
structure Cache {u : Level} {A : Q(Type u)}
    (sA : Q(CommSemiring $A)) extends Ring.Common.Cache sA where
  /-- A Field instance on `A`, if available. -/
  field : Option Q(Field $A)

/--
Definition of `mkCache` / `mkCache` 的定义

English:
definition mkCache
  signature: {u : Level} {A : Q(Type u)} (sA : Q(CommSemiring $A))
  body: do return {
  field := (← trySynthInstanceQ q(Field $A)).toOption
  toCache := ← Ring.Common.mkCache sA
}

中文:
定义 mkCache
  签名: {u : Level} {A : Q(类型u)} (sA : Q(交换半环 $A))
  定义体: do return {
  field := (← trySynthInstanceQ q(Field $A)).toOption
  toCache := ← Ring.Common.mkCache sA
}

Depends on / 依赖: return
-/
def mkCache {u : Level} {A : Q(Type u)} (sA : Q(CommSemiring $A)) : MetaM (Cache sA) := do return {
  field := (← trySynthInstanceQ q(Field $A)).toOption
  toCache := ← Ring.Common.mkCache sA
}

open Mathlib.Tactic.Ring hiding ExSum ExProd ExBase

section BaseType

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

/--
Inductive type `BaseType` / 归纳类型 `BaseType`

English:
inductive BaseType
  parameters: : (a : Q($A)) -> Type
  constructors (1):
    - mk: (r : Q($R)) (_ : Ring.ExSum q($sR) r) : BaseType q(algebraMap $R $A $r)

中文:
归纳类型 BaseType
  参数: : (a : Q($A)) -> 类型
  构造子 (1 个):
    - mk: (r : Q($R)) (_ : 环.ExSum q($sR) r) : BaseType q(algebraMap $R $A $r)
-/
inductive BaseType : (a : Q($A)) -> Type
  | mk (r : Q($R)) (_ : Ring.ExSum q($sR) r) : BaseType q(algebraMap $R $A $r)

@[expose, inherit_doc Common.ExBase]
/--
Definition of `ExBase` / `ExBase` 的定义

English:
definition ExBase
  body: Common.ExBase (BaseType sAlg) sA
@[expose, inherit_doc Common.ExProd]

中文:
定义 ExBase
  定义体: Common.ExBase (BaseType sAlg) sA
@[expose, inherit_doc Common.ExProd]

Depends on / 依赖: BaseType, Common, Common.ExBase, ExBase
-/
def ExBase := Common.ExBase (BaseType sAlg) sA
@[expose, inherit_doc Common.ExProd]
/--
Definition of `ExProd` / `ExProd` 的定义

English:
definition ExProd
  body: Common.ExProd (BaseType sAlg) sA
@[expose, inherit_doc Common.ExSum]

中文:
定义 ExProd
  定义体: Common.ExProd (BaseType sAlg) sA
@[expose, inherit_doc Common.ExSum]

Depends on / 依赖: BaseType, Common, Common.ExProd, ExProd, PseudoEMetricSpace, PseudoEMetricSpace.pseudoMetrizableSpace, pseudoMetrizableSpace
-/
def ExProd := Common.ExProd (BaseType sAlg) sA
@[expose, inherit_doc Common.ExSum]
/--
Definition of `ExSum` / `ExSum` 的定义

English:
definition ExSum
  body: Common.ExSum (BaseType sAlg) sA

中文:
定义 ExSum
  定义体: Common.ExSum (BaseType sAlg) sA

Depends on / 依赖: BaseType, Common, Common.ExSum, EMetricSpace, EMetricSpace.metrizableSpace, metrizableSpace
-/
def ExSum := Common.ExSum (BaseType sAlg) sA

set_option linter.unusedVariables false in
variable {a} in
/--
Definition of `evalCast` / `evalCast` 的定义

English:
definition evalCast
  signature: (cR : Algebra.Cache q($sR)) (cA : Algebra.Cache q($sA))
  body: Ring.ExProd.mkNat sR lit.natLit!
    -- Lift the literal to the base ring as a scalar multiple of 1
    pure ⟨_, (Common.ExProd.const ⟨_, (vr.toSum)⟩).toSum,
have : r =Q Nat.rawCast lit := ⟨⟩
      (q(isNat_eq_rawCast $p))⟩
  | .isNegNat rA lit p => do
    let some crR := cR.rα | none
    let some crA := cA.rα | none
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNat q($sR) q(inferInstance) lit.natLit!
have : r =Q Int.rawCast (Int.negOfNat $lit) := ⟨⟩
    assumeInstancesCommute
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isInt_negOfNat_eq $p))⟩
  | .isNNRat rA q n d p => do
    let some dsR := cR.dsα | none
    let some dsA := cA.dsα | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNNRat q($sR) q(inferInstance) q n d q(IsNNRat.den_nz (α := $A) $p)
have : r =Q (NNRat.rawCast $n $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, q(isNNRat_eq_rawCast (a := $a) $p)⟩
  | .isNegNNRat dA q n d p => do
    let some fR := cR.field | none
    let some fA := cA.field | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNNRat q($sR) q(inferInstance) q n d q(IsRat.den_nz $p)
have : r =Q (Rat.rawCast (.negOfNat $n) $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isRat_eq_rawCast (a := $a) $p))⟩
  | _ => none

中文:
定义 evalCast
  签名: (cR : 代数.Cache q($sR)) (cA : 代数.Cache q($sA))
  定义体: Ring.ExProd.mkNat sR lit.natLit!
    -- Lift the literal to the base ring as a scalar multiple of 1
    pure ⟨_, (Common.ExProd.const ⟨_, (vr.toSum)⟩).toSum,
have : r =Q Nat.rawCast lit := ⟨⟩
      (q(isNat_eq_rawCast $p))⟩
  | .isNegNat rA lit p => do
    let some crR := cR.rα | none
    let some crA := cA.rα | none
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNat q($sR) q(inferInstance) lit.natLit!
have : r =Q Int.rawCast (Int.negOfNat $lit) := ⟨⟩
    assumeInstancesCommute
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isInt_negOfNat_eq $p))⟩
  | .isNNRat rA q n d p => do
    let some dsR := cR.dsα | none
    let some dsA := cA.dsα | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNNRat q($sR) q(inferInstance) q n d q(IsNNRat.den_nz (α := $A) $p)
have : r =Q (NNRat.rawCast $n $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, q(isNNRat_eq_rawCast (a := $a) $p)⟩
  | .isNegNNRat dA q n d p => do
    let some fR := cR.field | none
    let some fA := cA.field | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNNRat q($sR) q(inferInstance) q n d q(IsRat.den_nz $p)
have : r =Q (Rat.rawCast (.negOfNat $n) $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isRat_eq_rawCast (a := $a) $p))⟩
  | _ => none

Depends on / 依赖: ExProd, Ring.ExProd.mkNat, lit.natLit, natLit
-/
def evalCast (cR : Algebra.Cache q($sR)) (cA : Algebra.Cache q($sA)):
    NormNum.Result a -> Option (Common.Result (ExSum sAlg) q($a))
  | .isNat _ (.lit (.natVal 0)) p => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(isNat_zero_eq $p)⟩
  | .isNat _ lit p => do
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNat sR lit.natLit!
    -- Lift the literal to the base ring as a scalar multiple of 1
    pure ⟨_, (Common.ExProd.const ⟨_, (vr.toSum)⟩).toSum,
have : r =Q Nat.rawCast lit := ⟨⟩
      (q(isNat_eq_rawCast $p))⟩
  | .isNegNat rA lit p => do
    let some crR := cR.rα | none
    let some crA := cA.rα | none
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNat q($sR) q(inferInstance) lit.natLit!
have : r =Q Int.rawCast (Int.negOfNat $lit) := ⟨⟩
    assumeInstancesCommute
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isInt_negOfNat_eq $p))⟩
  | .isNNRat rA q n d p => do
    let some dsR := cR.dsα | none
    let some dsA := cA.dsα | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNNRat q($sR) q(inferInstance) q n d q(IsNNRat.den_nz (α := $A) $p)
have : r =Q (NNRat.rawCast $n $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, q(isNNRat_eq_rawCast (a := $a) $p)⟩
  | .isNegNNRat dA q n d p => do
    let some fR := cR.field | none
    let some fA := cA.field | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNNRat q($sR) q(inferInstance) q n d q(IsRat.den_nz $p)
have : r =Q (Rat.rawCast (.negOfNat $n) $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isRat_eq_rawCast (a := $a) $p))⟩
  | _ => none

/--
Definition of `pushCast` / `pushCast` 的定义

English:
definition pushCast
  signature: (e : Expr)
  body: do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems ← NormCast.pushCastExt.getTheorems
  let simps : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]
  for thm in simps do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  -- now run `simp` with these lemmas, and (importantly) *no* simprocs
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (r, _) ← simp e ctx (simprocs := #[])
  return r

中文:
定义 pushCast
  签名: (e : Expr)
  定义体: do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems ← NormCast.pushCastExt.getTheorems
  let simps : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]
  for thm in simps do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  -- now run `simp` with these lemmas, and (importantly) *no* simprocs
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (r, _) ← simp e ctx (simprocs := #[])
  return r

Depends on / 依赖: PseudoMetrizableSpace, PseudoMetrizableSpace.of_regularSpace_secondCountableTopology, of_regularSpace_secondCountableTopology
-/
def pushCast (e : Expr) : MetaM Simp.Result := do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems ← NormCast.pushCastExt.getTheorems
  let simps : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]
  for thm in simps do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  -- now run `simp` with these lemmas, and (importantly) *no* simprocs
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (r, _) ← simp e ctx (simprocs := #[])
  return r


/--
Definition of `evalSMulCast` / `evalSMulCast` 的定义

English:
definition evalSMulCast
  signature: {u u' v : Lean.Level} {R : Q(Type u)} {R' : Q(Type u')} {A : Q(Type v)}
  body: do
  if (← isDefEq R R') then
    have : u =QL u' := ⟨⟩
have : R =Q R' := ⟨⟩
    assumeInstancesCommute
    return ⟨q($r'), q(fun _ => rfl)⟩
  let _sR' ← synthInstanceQ q(CommSemiring $R')
  let _algR'R ← synthInstanceQ q(Algebra $R' $R)
  let _mod ← synthInstanceQ q(Module $R' $A)
  let _ist ← synthInstanceQ q(IsScalarTower $R' $R $A)
  assumeInstancesCommute
  let r_cast : Q($R) := q(algebraMap $R' $R $r')
  let res ← pushCast r_cast
  have r₀ : Q($R) := res.expr
  let pf : Q($r_cast = $r₀) ← res.getProof
  return ⟨r₀, q(fun a => $pf ▸ algebraMap_smul $R $r' a)⟩

中文:
定义 evalSMulCast
  签名: {u u' v : Lean.Level} {R : Q(类型u)} {R' : Q(类型u')} {A : Q(类型v)}
  定义体: do
  if (← isDefEq R R') then
    have : u =QL u' := ⟨⟩
have : R =Q R' := ⟨⟩
    assumeInstancesCommute
    return ⟨q($r'), q(fun _ => rfl)⟩
  let _sR' ← synthInstanceQ q(CommSemiring $R')
  let _algR'R ← synthInstanceQ q(Algebra $R' $R)
  let _mod ← synthInstanceQ q(Module $R' $A)
  let _ist ← synthInstanceQ q(IsScalarTower $R' $R $A)
  assumeInstancesCommute
  let r_cast : Q($R) := q(algebraMap $R' $R $r')
  let res ← pushCast r_cast
  have r₀ : Q($R) := res.expr
  let pf : Q($r_cast = $r₀) ← res.getProof
  return ⟨r₀, q(fun a => $pf ▸ algebraMap_smul $R $r' a)⟩
-/
def evalSMulCast {u u' v : Lean.Level} {R : Q(Type u)} {R' : Q(Type u')} {A : Q(Type v)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
    (smul : Q(SMul $R' $A)) (r' : Q($R')) :
MetaM Σ r : Q($R), Q(forall a : $A, $r • a = $r' • a) := do
  if (← isDefEq R R') then
    have : u =QL u' := ⟨⟩
have : R =Q R' := ⟨⟩
    assumeInstancesCommute
    return ⟨q($r'), q(fun _ => rfl)⟩
  let _sR' ← synthInstanceQ q(CommSemiring $R')
  let _algR'R ← synthInstanceQ q(Algebra $R' $R)
  let _mod ← synthInstanceQ q(Module $R' $A)
  let _ist ← synthInstanceQ q(IsScalarTower $R' $R $A)
  assumeInstancesCommute
  let r_cast : Q($R) := q(algebraMap $R' $R $r')
  let res ← pushCast r_cast
  have r₀ : Q($R) := res.expr
  let pf : Q($r_cast = $r₀) ← res.getProof
  return ⟨r₀, q(fun a => $pf ▸ algebraMap_smul $R $r' a)⟩

namespace RingCompute

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b)
  body: match za, zb with
  | .mk r vr, .mk s vs => do
    let ⟨t, vt, pt⟩ ← Common.evalAdd (Ring.ringCompute cR) rcNat vr vs
    match (dependent := true) vt with
    | .zero =>
have : t =Q 0 := ⟨⟩
      return ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, some q(add_algebraMap_isNat_zero $pt)⟩
    | vt =>
      return ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, none⟩

中文:
定义 add
  签名: (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b)
  定义体: match za, zb with
  | .mk r vr, .mk s vs => do
    let ⟨t, vt, pt⟩ ← Common.evalAdd (Ring.ringCompute cR) rcNat vr vs
    match (dependent := true) vt with
    | .zero =>
have : t =Q 0 := ⟨⟩
      return ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, some q(add_algebraMap_isNat_zero $pt)⟩
    | vt =>
      return ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, none⟩

Depends on / 依赖: Common, Common.evalAdd, MetrizableSpace, Ring.ringCompute, add_algebraMap, add_algebraMap_isNat_zero, dependent, evalAdd, metrizableSpace_of_t3_secondCountable, return, ringCompute
-/
def add (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b) :
    MetaM (Common.Result (BaseType sAlg) q($a + $b) × Option Q(IsNat ($a + $b) 0)) :=
  match za, zb with
  | .mk r vr, .mk s vs => do
    let ⟨t, vt, pt⟩ ← Common.evalAdd (Ring.ringCompute cR) rcNat vr vs
    match (dependent := true) vt with
    | .zero =>
have : t =Q 0 := ⟨⟩
      return ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, some q(add_algebraMap_isNat_zero $pt)⟩
    | vt =>
      return ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, none⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b)
  body: match za, zb with
  | .mk r vr, .mk s vs => do
    let ⟨t, vt, pt⟩ ← Common.evalMul (Ring.ringCompute cR) rcNat vr vs
    return ⟨_, .mk _ vt, q(by simp [← $pt, map_mul])⟩

中文:
定义 mul
  签名: (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b)
  定义体: match za, zb with
  | .mk r vr, .mk s vs => do
    let ⟨t, vt, pt⟩ ← Common.evalMul (Ring.ringCompute cR) rcNat vr vs
    return ⟨_, .mk _ vt, q(by simp [← $pt, map_mul])⟩

Depends on / 依赖: Common, Common.evalMul, Ring.ringCompute, evalMul, map_mul, return, ringCompute
-/
def mul (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b) :
    MetaM (Common.Result (BaseType sAlg) q($a * $b)) :=
  match za, zb with
  | .mk r vr, .mk s vs => do
    let ⟨t, vt, pt⟩ ← Common.evalMul (Ring.ringCompute cR) rcNat vr vs
    return ⟨_, .mk _ vt, q(by simp [← $pt, map_mul])⟩

/-- Take an expression `r'` in a ring `R'` such that `R` is an `R'`-algebra and cast `r'` to `R`
using `algebraMap R' R`, so that the scalar multiplication action on `A` is preserved. -/
/- We include the CharZero argument to match the type signature of the ringCompute entry. -/
@[nolint unusedArguments]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: (cR : Algebra.Cache sR) (u' : Level) (R' : Q(Type u'))
  body: do
  let ⟨r, pf_smul⟩ ← evalSMulCast q($sAlg) q($_smul) r'
  let ⟨_r'', vr, pr⟩ ←
    Common.eval rcNat (Ring.ringCompute cR.toCache) cR.toCache q($r)
  match (dependent := true) vr with
  | .zero .. =>
    assumeInstancesCommute
    return ⟨_, .zero, q(cast_zero_smul_eq_zero_mul $pr $pf_smul)⟩
  | vr =>
    assumeInstancesCommute
    return ⟨_, Common.ExSum.add (Common.ExProd.const (.mk _ vr)) .zero,
      q(cast_smul_eq_mul $pr $pf_smul)⟩

中文:
定义 cast
  签名: (cR : 代数.Cache sR) (u' : Level) (R' : Q(类型u'))
  定义体: do
  let ⟨r, pf_smul⟩ ← evalSMulCast q($sAlg) q($_smul) r'
  let ⟨_r'', vr, pr⟩ ←
    Common.eval rcNat (Ring.ringCompute cR.toCache) cR.toCache q($r)
  match (dependent := true) vr with
  | .zero .. =>
    assumeInstancesCommute
    return ⟨_, .zero, q(cast_zero_smul_eq_zero_mul $pr $pf_smul)⟩
  | vr =>
    assumeInstancesCommute
    return ⟨_, Common.ExSum.add (Common.ExProd.const (.mk _ vr)) .zero,
      q(cast_smul_eq_mul $pr $pf_smul)⟩
-/
def cast (cR : Algebra.Cache sR) (u' : Level) (R' : Q(Type u'))
    (_ : Q(CommSemiring $R')) (_smul : Q(SMul $R' $A)) (r' : Q($R')) :
    AtomM ((y : Q($A)) × Common.ExSum (BaseType sAlg) sA q($y) ×
      Q(forall (a : $A), $r' • a = $y * a)) := do
  let ⟨r, pf_smul⟩ ← evalSMulCast q($sAlg) q($_smul) r'
  let ⟨_r'', vr, pr⟩ ←
    Common.eval rcNat (Ring.ringCompute cR.toCache) cR.toCache q($r)
  match (dependent := true) vr with
  | .zero .. =>
    assumeInstancesCommute
    return ⟨_, .zero, q(cast_zero_smul_eq_zero_mul $pr $pf_smul)⟩
  | vr =>
    assumeInstancesCommute
    return ⟨_, Common.ExSum.add (Common.ExProd.const (.mk _ vr)) .zero,
      q(cast_smul_eq_mul $pr $pf_smul)⟩

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: (cR : Algebra.Cache sR) {a : Q($A)} (_rA : Q(CommRing $A)) (za : BaseType sAlg a)
  body: match za with
  | .mk r vr => do
    match cR.rα with
    | some rR =>
      let ⟨_, vt, pt⟩ ← Common.evalNeg (Ring.ringCompute cR.toCache) q($rR) vr
      assumeInstancesCommute
      return ⟨_, .mk _ vt, q(neg_algebraMap $pt)⟩
    | none => failure

中文:
定义 neg
  签名: (cR : 代数.Cache sR) {a : Q($A)} (_rA : Q(交换环 $A)) (za : BaseType sAlg a)
  定义体: match za with
  | .mk r vr => do
    match cR.rα with
    | some rR =>
      let ⟨_, vt, pt⟩ ← Common.evalNeg (Ring.ringCompute cR.toCache) q($rR) vr
      assumeInstancesCommute
      return ⟨_, .mk _ vt, q(neg_algebraMap $pt)⟩
    | none => failure

Depends on / 依赖: Common, Common.evalNeg, Ring.ringCompute, assumeInstancesCommute, cR.r, cR.toCache, evalNeg, failure, neg_algebraMap, return, ringCompute, toCache
-/
def neg (cR : Algebra.Cache sR) {a : Q($A)} (_rA : Q(CommRing $A)) (za : BaseType sAlg a) :
    MetaM (Common.Result (BaseType sAlg) q(-$a)) :=
  match za with
  | .mk r vr => do
    match cR.rα with
    | some rR =>
      let ⟨_, vt, pt⟩ ← Common.evalNeg (Ring.ringCompute cR.toCache) q($rR) vr
      assumeInstancesCommute
      return ⟨_, .mk _ vt, q(neg_algebraMap $pt)⟩
    | none => failure

/--
Definition of `pow` / `pow` 的定义

English:
definition pow
  signature: (cR : Common.Cache sR) {a : Q($A)} {b : Q(Nat)} (za : BaseType sAlg a)
  body: match za with
  | .mk r vr => do
    let ⟨_, vs, ps⟩ ← Common.evalPow₁ (Ring.ringCompute cR) rcNat vr vb
    return ⟨_, ⟨_, vs⟩, q(pow_algebraMap $ps)⟩

中文:
定义 pow
  签名: (cR : Common.Cache sR) {a : Q($A)} {b : Q(自然数)} (za : BaseType sAlg a)
  定义体: match za with
  | .mk r vr => do
    let ⟨_, vs, ps⟩ ← Common.evalPow₁ (Ring.ringCompute cR) rcNat vr vb
    return ⟨_, ⟨_, vs⟩, q(pow_algebraMap $ps)⟩

Depends on / 依赖: Common, Common.evalPow, Ring.ringCompute, pow_algebraMap, return, ringCompute
-/
def pow (cR : Common.Cache sR) {a : Q($A)} {b : Q(Nat)} (za : BaseType sAlg a)
    (vb : Common.ExProdNat q($b)) :
    OptionT MetaM (Common.Result (BaseType sAlg) q($a ^ $b)) :=
  match za with
  | .mk r vr => do
    let ⟨_, vs, ps⟩ ← Common.evalPow₁ (Ring.ringCompute cR) rcNat vr vb
    return ⟨_, ⟨_, vs⟩, q(pow_algebraMap $ps)⟩

/-- Evaluate the inverse of two normalized expressions in `R` using `ring`. -/
/- We include the CharZero argument to match the type signature of the ringCompute entry. -/
@[nolint unusedArguments]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (cR : Algebra.Cache sR) {a : Q($A)} (_ : Option Q(CharZero $A)) (fA : Q(Semifield $A))
  body: match za with
  | .mk r vr => do
    match cR.dsα with
    | some fR =>
      let ⟨_, vs, ps⟩ ← Common.ExSum.evalInv (Ring.ringCompute cR.toCache) rcNat q($fR) cR.czα vr
      assumeInstancesCommute
      return some ⟨_, ⟨_, vs⟩, q(inv_algebraMap $ps)⟩
    | none =>
      return none

中文:
定义 inv
  签名: (cR : 代数.Cache sR) {a : Q($A)} (_ : 选项类型 Q(特征零 $A)) (fA : Q(半域 $A))
  定义体: match za with
  | .mk r vr => do
    match cR.dsα with
    | some fR =>
      let ⟨_, vs, ps⟩ ← Common.ExSum.evalInv (Ring.ringCompute cR.toCache) rcNat q($fR) cR.czα vr
      assumeInstancesCommute
      return some ⟨_, ⟨_, vs⟩, q(inv_algebraMap $ps)⟩
    | none =>
      return none

Depends on / 依赖: Common, Common.ExSum.evalInv, Ring.ringCompute, assumeInstancesCommute, cR.cz, cR.ds, cR.toCache, evalInv, inv_algebraMap, return, ringCompute, toCache
-/
def inv (cR : Algebra.Cache sR) {a : Q($A)} (_ : Option Q(CharZero $A)) (fA : Q(Semifield $A))
    (za : BaseType sAlg a) : AtomM (Option (Common.Result (BaseType sAlg) q($a⁻¹))) :=
  match za with
  | .mk r vr => do
    match cR.dsα with
    | some fR =>
      let ⟨_, vs, ps⟩ ← Common.ExSum.evalInv (Ring.ringCompute cR.toCache) rcNat q($fR) cR.czα vr
      assumeInstancesCommute
      return some ⟨_, ⟨_, vs⟩, q(inv_algebraMap $ps)⟩
    | none =>
      return none

/--
Definition of `derive` / `derive` 的定义

English:
definition derive
  signature: (cR : Algebra.Cache sR) (cA : Algebra.Cache sA) (x : Q($A))
  body: do
  let res ← NormNum.derive x
  let ⟨_, vr, pr⟩ ← evalCast sAlg cR cA res
  return ⟨_, vr, q($pr)⟩

中文:
定义 derive
  签名: (cR : 代数.Cache sR) (cA : 代数.Cache sA) (x : Q($A))
  定义体: do
  let res ← NormNum.derive x
  let ⟨_, vr, pr⟩ ← evalCast sAlg cR cA res
  return ⟨_, vr, q($pr)⟩
-/
def derive (cR : Algebra.Cache sR) (cA : Algebra.Cache sA) (x : Q($A)) :
    MetaM (Common.Result (Common.ExSum (BaseType sAlg) sA) q($x)) := do
  let res ← NormNum.derive x
  let ⟨_, vr, pr⟩ ← evalCast sAlg cR cA res
  return ⟨_, vr, q($pr)⟩

/--
Definition of `isOne` / `isOne` 的定义

English:
definition isOne
  signature: (cR : Common.Cache sR) {x : Q($A)} (zx : BaseType sAlg x)
  body: let ⟨_, vx⟩ := zx
  match vx with
  | .add (.const c) .zero =>
    match (Ring.ringCompute cR).isOne c with
    | some pf => some q(isOne_algebraMap $pf)
    | none => none
  | .zero => none
  | _ => none

中文:
定义 isOne
  签名: (cR : Common.Cache sR) {x : Q($A)} (zx : BaseType sAlg x)
  定义体: let ⟨_, vx⟩ := zx
  match vx with
  | .add (.const c) .zero =>
    match (Ring.ringCompute cR).isOne c with
    | some pf => some q(isOne_algebraMap $pf)
    | none => none
  | .zero => none
  | _ => none

Depends on / 依赖: Ring.ringCompute, isOne_algebraMap, ringCompute
-/
def isOne (cR : Common.Cache sR) {x : Q($A)} (zx : BaseType sAlg x) : Option Q(IsNat $x 1) :=
  let ⟨_, vx⟩ := zx
  match vx with
  | .add (.const c) .zero =>
    match (Ring.ringCompute cR).isOne c with
    | some pf => some q(isOne_algebraMap $pf)
    | none => none
  | .zero => none
  | _ => none

end RingCompute

open RingCompute in
/--
Definition of `ringCompare` / `ringCompare` 的定义

English:
definition ringCompare
  signature: :
  body: fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.eq rcNat Ring.ringCompare vy
  compare := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.cmp rcNat Ring.ringCompare vy

中文:
定义 ringCompare
  签名: :
  定义体: fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.eq rcNat Ring.ringCompare vy
  compare := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.cmp rcNat Ring.ringCompare vy

Depends on / 依赖: Ring.ringCompare, ringCompare, vx.eq
-/
def ringCompare :
    Common.RingCompare (BaseType sAlg) where
  eq := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.eq rcNat Ring.ringCompare vy
  compare := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.cmp rcNat Ring.ringCompare vy

open Algebra.RingCompute in
/--
Definition of `ringCompute` / `ringCompute` 的定义

English:
definition ringCompute
  signature: (cR : Algebra.Cache sR) (cA : Algebra.Cache sA)
  body: add sAlg cR.toCache
  mul := mul sAlg cR.toCache
  cast := cast sAlg cR
  neg := neg sAlg cR
  pow := pow sAlg cR.toCache
  inv := inv sAlg cR
  derive := derive sAlg cR cA
  isOne := isOne sAlg cR.toCache
  one :=
    let ⟨r, vr⟩ := Ring.ExProd.mkNat sR 1
have hr : r =Q (nat_lit 1).rawCast := ⟨⟩
    ⟨_, ⟨_, vr.toSum⟩, q(by simp +zetaDelta)⟩
  toRingCompare := ringCompare sAlg

中文:
定义 ringCompute
  签名: (cR : 代数.Cache sR) (cA : 代数.Cache sA)
  定义体: add sAlg cR.toCache
  mul := mul sAlg cR.toCache
  cast := cast sAlg cR
  neg := neg sAlg cR
  pow := pow sAlg cR.toCache
  inv := inv sAlg cR
  derive := derive sAlg cR cA
  isOne := isOne sAlg cR.toCache
  one :=
    let ⟨r, vr⟩ := Ring.ExProd.mkNat sR 1
have hr : r =Q (nat_lit 1).rawCast := ⟨⟩
    ⟨_, ⟨_, vr.toSum⟩, q(by simp +zetaDelta)⟩
  toRingCompare := ringCompare sAlg

Depends on / 依赖: cR.toCache, toCache
-/
def ringCompute (cR : Algebra.Cache sR) (cA : Algebra.Cache sA) :
    Common.RingCompute (BaseType sAlg) sA where
  add := add sAlg cR.toCache
  mul := mul sAlg cR.toCache
  cast := cast sAlg cR
  neg := neg sAlg cR
  pow := pow sAlg cR.toCache
  inv := inv sAlg cR
  derive := derive sAlg cR cA
  isOne := isOne sAlg cR.toCache
  one :=
    let ⟨r, vr⟩ := Ring.ExProd.mkNat sR 1
have hr : r =Q (nat_lit 1).rawCast := ⟨⟩
    ⟨_, ⟨_, vr.toSum⟩, q(by simp +zetaDelta)⟩
  toRingCompare := ringCompare sAlg

end BaseType


open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

/--
theorem `Nat.cast_eq_algebraMap` / 定理 `Nat.cast_eq_algebraMap`

English:
theorem Nat.cast_eq_algebraMap
  given: (A : Type*) [CommSemiring A] (n : Nat)
  proof: rfl

中文:
定理 自然数.cast_eq_algebraMap
  条件: (A : 类型) [交换半环 A] (n : 自然数)
  证明: rfl
-/
theorem Nat.cast_eq_algebraMap (A : Type*) [CommSemiring A] (n : Nat) :
    Nat.cast n = algebraMap Nat A n := rfl

/--
theorem `Int.cast_eq_algebraMap` / 定理 `Int.cast_eq_algebraMap`

English:
theorem Int.cast_eq_algebraMap
  given: (A : Type*) [CommRing A] (n : Int)
  proof: rfl

中文:
定理 整数.cast_eq_algebraMap
  条件: (A : 类型) [交换环 A] (n : 整数)
  证明: rfl
-/
theorem Int.cast_eq_algebraMap (A : Type*) [CommRing A] (n : Int) :
    Int.cast n = algebraMap Int A n := rfl

/--
Definition of `preprocess` / `preprocess` 的定义

English:
definition preprocess
  signature: (e : Expr)
  body: do
  -- collect the available `push_cast` lemmas
  let thms : SimpTheorems := {}
  let thms ← [``Nat.cast_eq_algebraMap, ``Int.cast_eq_algebraMap,
    ``Algebra.algebraMap_eq_smul_one].foldlM (·.addConst ·) thms
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  return (← Simp.main e ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

中文:
定义 preprocess
  签名: (e : Expr)
  定义体: do
  -- collect the available `push_cast` lemmas
  let thms : SimpTheorems := {}
  let thms ← [``Nat.cast_eq_algebraMap, ``Int.cast_eq_algebraMap,
    ``Algebra.algebraMap_eq_smul_one].foldlM (·.addConst ·) thms
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  return (← Simp.main e ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1
-/
def preprocess (e : Expr) : MetaM Simp.Result := do
  -- collect the available `push_cast` lemmas
  let thms : SimpTheorems := {}
  let thms ← [``Nat.cast_eq_algebraMap, ``Int.cast_eq_algebraMap,
    ``Algebra.algebraMap_eq_smul_one].foldlM (·.addConst ·) thms
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  return (← Simp.main e ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/--
Definition of `collectScalarRingsAux` / `collectScalarRingsAux` 的定义

English:
definition collectScalarRingsAux
  signature: (e : Expr)
  body: do
  match_expr e with
  | SMul.smul R _ _ _ a =>
    modify fun l => R :: l
    collectScalarRingsAux a
  | DFunLike.coe _ _R _A _inst φ _ =>
      match_expr φ with
      | algebraMap R _ _ _ _ =>
        modify fun l => R :: l
      | _ => return
  | HSMul.hSMul R _ _ _ _ a =>
    modify fun l => R :: l
    collectScalarRingsAux a
  | Eq _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HAdd.hAdd _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Add.add _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HMul.hMul _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Mul.mul _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HSub.hSub _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Sub.sub _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HPow.hPow _ _ _ _ a _ => collectScalarRingsAux a
  | Neg.neg _ _ a => collectScalarRingsAux a
  | _ => return

中文:
定义 collectScalarRingsAux
  签名: (e : Expr)
  定义体: do
  match_expr e with
  | SMul.smul R _ _ _ a =>
    modify fun l => R :: l
    collectScalarRingsAux a
  | DFunLike.coe _ _R _A _inst φ _ =>
      match_expr φ with
      | algebraMap R _ _ _ _ =>
        modify fun l => R :: l
      | _ => return
  | HSMul.hSMul R _ _ _ _ a =>
    modify fun l => R :: l
    collectScalarRingsAux a
  | Eq _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HAdd.hAdd _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Add.add _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HMul.hMul _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Mul.mul _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HSub.hSub _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Sub.sub _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HPow.hPow _ _ _ _ a _ => collectScalarRingsAux a
  | Neg.neg _ _ a => collectScalarRingsAux a
  | _ => return
-/
partial def collectScalarRingsAux (e : Expr) : StateT (List Expr) MetaM Unit := do
  match_expr e with
  | SMul.smul R _ _ _ a =>
    modify fun l => R :: l
    collectScalarRingsAux a
  | DFunLike.coe _ _R _A _inst φ _ =>
      match_expr φ with
      | algebraMap R _ _ _ _ =>
        modify fun l => R :: l
      | _ => return
  | HSMul.hSMul R _ _ _ _ a =>
    modify fun l => R :: l
    collectScalarRingsAux a
  | Eq _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HAdd.hAdd _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Add.add _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HMul.hMul _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Mul.mul _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HSub.hSub _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Sub.sub _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HPow.hPow _ _ _ _ a _ => collectScalarRingsAux a
  | Neg.neg _ _ a => collectScalarRingsAux a
  | _ => return

/--
Definition of `collectScalarRings` / `collectScalarRings` 的定义

English:
definition collectScalarRings
  signature: (e : Expr)
  body: do
  let ⟨_, l⟩ ← (collectScalarRingsAux e).run []
  return l

中文:
定义 collectScalarRings
  签名: (e : Expr)
  定义体: do
  let ⟨_, l⟩ ← (collectScalarRingsAux e).run []
  return l
-/
partial def collectScalarRings (e : Expr) : MetaM (List Expr) := do
  let ⟨_, l⟩ ← (collectScalarRingsAux e).run []
  return l

/--
Definition of `pickLargerRing` / `pickLargerRing` 的定义

English:
definition pickLargerRing
  signature: (r1 r2 : Σ u : Lean.Level, Q(Type u))
  body: do
  let ⟨u1, R1⟩ := r1
  let ⟨u2, R2⟩ := r2
if ← withReducible isDefEq R1 R2 then
    return r1
  try
    let _i1 ← synthInstanceQ q(CommSemiring $R1)
    let _i2 ← synthInstanceQ q(Semiring $R2)
    let _i3 ← synthInstanceQ q(Algebra $R1 $R2)
    return r2
  catch _ => try
    let _i1 ← synthInstanceQ q(CommSemiring $R2)
    let _i2 ← synthInstanceQ q(Semiring $R1)
    let _i3 ← synthInstanceQ q(Algebra $R2 $R1)
    return r1
  catch _ =>
    return r1

中文:
定义 pickLargerRing
  签名: (r1 r2 : Σ u : Lean.Level, Q(类型u))
  定义体: do
  let ⟨u1, R1⟩ := r1
  let ⟨u2, R2⟩ := r2
if ← withReducible isDefEq R1 R2 then
    return r1
  try
    let _i1 ← synthInstanceQ q(CommSemiring $R1)
    let _i2 ← synthInstanceQ q(Semiring $R2)
    let _i3 ← synthInstanceQ q(Algebra $R1 $R2)
    return r2
  catch _ => try
    let _i1 ← synthInstanceQ q(CommSemiring $R2)
    let _i2 ← synthInstanceQ q(Semiring $R1)
    let _i3 ← synthInstanceQ q(Algebra $R2 $R1)
    return r1
  catch _ =>
    return r1
-/
def pickLargerRing (r1 r2 : Σ u : Lean.Level, Q(Type u)) :
    MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let ⟨u1, R1⟩ := r1
  let ⟨u2, R2⟩ := r2
if ← withReducible isDefEq R1 R2 then
    return r1
  try
    let _i1 ← synthInstanceQ q(CommSemiring $R1)
    let _i2 ← synthInstanceQ q(Semiring $R2)
    let _i3 ← synthInstanceQ q(Algebra $R1 $R2)
    return r2
  catch _ => try
    let _i1 ← synthInstanceQ q(CommSemiring $R2)
    let _i2 ← synthInstanceQ q(Semiring $R1)
    let _i3 ← synthInstanceQ q(Algebra $R2 $R1)
    return r1
  catch _ =>
    return r1

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

/--
Definition of `inferBase` / `inferBase` 的定义

English:
definition inferBase
  signature: (ca : Cache q($sA)) (e : Expr)
  body: do
  let rings ← (← collectScalarRings e).mapM getLevelQ'
  let res ← match rings with
  | [] =>
    match ca.field, ca.czα, ca.rα with
    | some _, some _, _ =>
      -- A is a Field
      return ⟨0, q(Rat)⟩
    | _, _, some _ =>
      -- A is a CommRing
      return ⟨0, q(Int)⟩
    | _, _, _ =>
      return ⟨0, q(Nat)⟩
  | r :: rs => rs.foldlM pickLargerRing r
  return res

中文:
定义 inferBase
  签名: (ca : Cache q($sA)) (e : Expr)
  定义体: do
  let rings ← (← collectScalarRings e).mapM getLevelQ'
  let res ← match rings with
  | [] =>
    match ca.field, ca.czα, ca.rα with
    | some _, some _, _ =>
      -- A is a Field
      return ⟨0, q(Rat)⟩
    | _, _, some _ =>
      -- A is a CommRing
      return ⟨0, q(Int)⟩
    | _, _, _ =>
      return ⟨0, q(Nat)⟩
  | r :: rs => rs.foldlM pickLargerRing r
  return res
-/
def inferBase (ca : Cache q($sA)) (e : Expr) : MetaM Σ u : Lean.Level, Q(Type u) := do
  let rings ← (← collectScalarRings e).mapM getLevelQ'
  let res ← match rings with
  | [] =>
    match ca.field, ca.czα, ca.rα with
    | some _, some _, _ =>
      -- A is a Field
      return ⟨0, q(Rat)⟩
    | _, _, some _ =>
      -- A is a CommRing
      return ⟨0, q(Int)⟩
    | _, _, _ =>
      return ⟨0, q(Nat)⟩
  | r :: rs => rs.foldlM pickLargerRing r
  return res

/--
Definition of `proveEq` / `proveEq` 的定义

English:
definition proveEq
  signature: (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId)
  body: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let ⟨v, A⟩ ← getLevelQ' α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← Algebra.mkCache sA
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase cA (← g.getType))
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cR ← Algebra.mkCache sR
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let eq ← algCore q($sAlg) cR cA e₁ e₂
  g.assign eq

中文:
定义 proveEq
  签名: (base : 选项类型 (Σ u : Lean.Level, Q(类型u))) (g : MVarId)
  定义体: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let ⟨v, A⟩ ← getLevelQ' α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← Algebra.mkCache sA
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase cA (← g.getType))
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cR ← Algebra.mkCache sR
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let eq ← algCore q($sAlg) cR cA e₁ e₂
  g.assign eq
-/
def proveEq (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let ⟨v, A⟩ ← getLevelQ' α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← Algebra.mkCache sA
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase cA (← g.getType))
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cR ← Algebra.mkCache sR
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let eq ← algCore q($sAlg) cR cA e₁ e₂
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  algCore {u v : Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
      (cR : Cache q($sR)) (cA : Cache q($sA)) (e₁ e₂ : Q($A)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "algebra" (← getOptions) do
      let ⟨a, va, pa⟩ ← Common.eval rcNat (ringCompute sAlg cR cA) cA.toCache e₁
      let ⟨b, vb, pb⟩ ← Common.eval rcNat (ringCompute sAlg cR cA) cA.toCache e₂
      unless va.eq rcNat (ringCompute sAlg cR cA) vb do
        let g ← mkFreshExprMVar (← (← Ring.ringCleanupRef.get) q($a = $b))
        throwError "algebra failed, algebra expressions not equal\n{g.mvarId!}"
have : a =Q b := ⟨⟩
      return q($pb ▸ $pa)

/-- `algebra` solves equalities in the language of algebras: ring operations and scalar
multiplications.

Given a goal which is an equality in a commutative `R`-algebra `A`, `algebra` parses the LHS and
RHS of the goal as polynomial expressions of `A`-atoms with coefficients in some semiring `R`, and
closes the goal if the two expressions are the same. The `R`-coefficients are put into ring normal
form.

By default, the scalar ring `R` is inferred automatically by looking for scalar multiplications and
`algebraMap`s present in the expressions. The inference procedure assumes that any two rings `R`
and `S` that appear are comparable, in the sense that either `R` is an `S`-algebra or `S` is an
`R`-algebra.

* `algebra with R` uses the term `R` as the scalar ring, instead of attempting to infer it
automatically.
-/
elab (name := algebra) "algebra":tactic =>
  withMainContext do
    liftMetaTactic1 (transformAtTarget (fun e _ => preprocess e) "algebra" .silent · default)
    let g ← getMainGoal
    AtomM.run .default (proveEq none g)

@[tactic_alt algebra]
elab (name := algebraWith) "algebra" " with " R:term : tactic =>
  withMainContext do
    liftMetaTactic1 (transformAtTarget (fun e _ => preprocess e) "algebra" .silent · default)
    let ⟨u, R⟩ ← getLevelQ' (← elabTerm R none)
    let g ← getMainGoal
    AtomM.run .default (proveEq (some ⟨u, R⟩) g)

end Mathlib.Tactic.Algebra
