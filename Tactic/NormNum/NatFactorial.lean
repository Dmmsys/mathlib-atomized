/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
module

public meta import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for factorials

Extensions for `norm_num` that compute `Nat.factorial`, `Nat.ascFactorial` and `Nat.descFactorial`.

This is done by reducing each of these to `ascFactorial`, which is computed using a divide and
conquer strategy that improves performance and avoids exceeding the recursion depth.

-/

public meta section

namespace Mathlib.Meta.NormNum

open Nat Qq Lean Elab.Tactic Meta

/--
lemma `asc_factorial_aux` / 引理 `asc_factorial_aux`

English:
lemma asc_factorial_aux
  statement: (n l m a b : Nat) (h₁ : n.ascFactorial l = a)
  proof: by
  rw [← h₁]; rw [← h₂]
  symm
  apply ascFactorial_mul_ascFactorial

中文:
引理 asc_factorial_aux
  结论: (n l m a b : 自然数) (h₁ : n.ascFactorial l = a)
  证明: by
  rw [← h₁]; rw [← h₂]
  symm
  apply ascFactorial_mul_ascFactorial

Depends on / 依赖: R1Space, RegularSpace, WeaklyLocallyCompactSpace, ascFactorial_mul_ascFactorial
-/
lemma asc_factorial_aux (n l m a b : Nat) (h₁ : n.ascFactorial l = a)
    (h₂ : (n + l).ascFactorial m = b) : n.ascFactorial (l + m) = a * b := by
  rw [← h₁]; rw [← h₂]
  symm
  apply ascFactorial_mul_ascFactorial

/--
Definition of `proveAscFactorial` / `proveAscFactorial` 的定义

English:
definition proveAscFactorial
  signature: (n l : Nat) (en el : Q(Nat))
  body: if l <= 50 then
    have res : Nat := n.ascFactorial l
    have eres : Q(Nat) := mkRawNatLit (n.ascFactorial l)
have : ($en).ascFactorial el =Q eres := ⟨⟩
    ⟨res, eres, q(Eq.refl $eres)⟩
  else
    have m : Nat := l / 2
    have em : Q(Nat) := mkRawNatLit m
have : em =Q el / 2 := ⟨⟩

    have r : Nat := l - m
    have er : Q(Nat) := mkRawNatLit r
have : er =Q el - em := ⟨⟩
have : el =Q ($em + $er) := ⟨⟩

    have nm : Nat := n + m
    have enm : Q(Nat) := mkRawNatLit nm
have : enm =Q en + em := ⟨⟩

    let ⟨a, ea, a_prf⟩ := proveAscFactorial n m en em
    let ⟨b, eb, b_prf⟩ := proveAscFactorial (n + m) r enm er
    have eab : Q(Nat) := mkRawNatLit (a * b)
have : eab =Q ea * eb := ⟨⟩
    ⟨a * b, eab, q(by convert! asc_factorial_aux «$en» «$em» «$er» «$ea» «$eb» «$a_prf» «$b_prf»)⟩

中文:
定义 proveAscFactorial
  签名: (n l : 自然数) (en el : Q(自然数))
  定义体: if l <= 50 then
    have res : Nat := n.ascFactorial l
    have eres : Q(Nat) := mkRawNatLit (n.ascFactorial l)
have : ($en).ascFactorial el =Q eres := ⟨⟩
    ⟨res, eres, q(Eq.refl $eres)⟩
  else
    have m : Nat := l / 2
    have em : Q(Nat) := mkRawNatLit m
have : em =Q el / 2 := ⟨⟩

    have r : Nat := l - m
    have er : Q(Nat) := mkRawNatLit r
have : er =Q el - em := ⟨⟩
have : el =Q ($em + $er) := ⟨⟩

    have nm : Nat := n + m
    have enm : Q(Nat) := mkRawNatLit nm
have : enm =Q en + em := ⟨⟩

    let ⟨a, ea, a_prf⟩ := proveAscFactorial n m en em
    let ⟨b, eb, b_prf⟩ := proveAscFactorial (n + m) r enm er
    have eab : Q(Nat) := mkRawNatLit (a * b)
have : eab =Q ea * eb := ⟨⟩
    ⟨a * b, eab, q(by convert! asc_factorial_aux «$en» «$em» «$er» «$ea» «$eb» «$a_prf» «$b_prf»)⟩
-/
partial def proveAscFactorial (n l : Nat) (en el : Q(Nat)) :
    Nat × (eresult : Q(Nat)) × Q(($en).ascFactorial $el = $eresult) :=
  if l <= 50 then
    have res : Nat := n.ascFactorial l
    have eres : Q(Nat) := mkRawNatLit (n.ascFactorial l)
have : ($en).ascFactorial el =Q eres := ⟨⟩
    ⟨res, eres, q(Eq.refl $eres)⟩
  else
    have m : Nat := l / 2
    have em : Q(Nat) := mkRawNatLit m
have : em =Q el / 2 := ⟨⟩

    have r : Nat := l - m
    have er : Q(Nat) := mkRawNatLit r
have : er =Q el - em := ⟨⟩
have : el =Q ($em + $er) := ⟨⟩

    have nm : Nat := n + m
    have enm : Q(Nat) := mkRawNatLit nm
have : enm =Q en + em := ⟨⟩

    let ⟨a, ea, a_prf⟩ := proveAscFactorial n m en em
    let ⟨b, eb, b_prf⟩ := proveAscFactorial (n + m) r enm er
    have eab : Q(Nat) := mkRawNatLit (a * b)
have : eab =Q ea * eb := ⟨⟩
    ⟨a * b, eab, q(by convert! asc_factorial_aux «$en» «$em» «$er» «$ea» «$eb» «$a_prf» «$b_prf»)⟩

/--
lemma `isNat_factorial` / 引理 `isNat_factorial`

English:
lemma isNat_factorial
  given: {n x : Nat} (h₁ : IsNat n x) (a : Nat) (h₂ : (1).ascFactorial x = a)
  proof: by
  constructor
  simp only [h₁.out, cast_id, ← h₂, one_ascFactorial]

中文:
引理 is自然数_factorial
  条件: {n x : 自然数} (h₁ : 是自然数 n x) (a : 自然数) (h₂ : (1).ascFactorial x = a)
  证明: by
  constructor
  simp only [h₁.out, cast_id, ← h₂, one_ascFactorial]

Depends on / 依赖: cast_id, one_ascFactorial
-/
lemma isNat_factorial {n x : Nat} (h₁ : IsNat n x) (a : Nat) (h₂ : (1).ascFactorial x = a) :
    IsNat (n !) a := by
  constructor
  simp only [h₁.out, cast_id, ← h₂, one_ascFactorial]

/-- Evaluates the `Nat.factorial` function. -/
@[nolint unusedHavesSuffices, norm_num Nat.factorial _]
/--
Definition of `evalNatFactorial` / `evalNatFactorial` 的定义

English:
definition evalNatFactorial
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Nat.factorial x := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨_, val, ascPrf⟩ := proveAscFactorial 1 ex.natLit! q(nat_lit 1) ex
  return .isNat sNat q($val) q(isNat_factorial $p $val $ascPrf)

中文:
定义 eval自然数Factorial
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Nat.factorial x := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨_, val, ascPrf⟩ := proveAscFactorial 1 ex.natLit! q(nat_lit 1) ex
  return .isNat sNat q($val) q(isNat_factorial $p $val $ascPrf)
-/
def evalNatFactorial : NormNumExt where eval {u α} e := do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Nat.factorial x := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨_, val, ascPrf⟩ := proveAscFactorial 1 ex.natLit! q(nat_lit 1) ex
  return .isNat sNat q($val) q(isNat_factorial $p $val $ascPrf)

/--
lemma `isNat_ascFactorial` / 引理 `isNat_ascFactorial`

English:
lemma isNat_ascFactorial
  statement: {n x l y : Nat} (h₁ : IsNat n x) (h₂ : IsNat l y) (a : Nat)
  proof: by
  constructor
  simp [h₁.out, h₂.out, ← p]

中文:
引理 is自然数_ascFactorial
  结论: {n x l y : 自然数} (h₁ : 是自然数 n x) (h₂ : 是自然数 l y) (a : 自然数)
  证明: by
  constructor
  simp [h₁.out, h₂.out, ← p]

Depends on / 依赖: R1Space
-/
lemma isNat_ascFactorial {n x l y : Nat} (h₁ : IsNat n x) (h₂ : IsNat l y) (a : Nat)
    (p : x.ascFactorial y = a) : IsNat (n.ascFactorial l) a := by
  constructor
  simp [h₁.out, h₂.out, ← p]

/-- Evaluates the Nat.ascFactorial function. -/
@[nolint unusedHavesSuffices, norm_num Nat.ascFactorial _ _]
/--
Definition of `evalNatAscFactorial` / `evalNatAscFactorial` 的定义

English:
definition evalNatAscFactorial
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Nat.ascFactorial x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex₁, p₁⟩ ← deriveNat x sNat
  let ⟨ex₂, p₂⟩ ← deriveNat y sNat
  let ⟨_, val, ascPrf⟩ := proveAscFactorial ex₁.natLit! ex₂.natLit! ex₁ ex₂
  return .isNat sNat q($val) q(isNat_ascFactorial $p₁ $p₂ $val $ascPrf)

中文:
定义 eval自然数AscFactorial
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Nat.ascFactorial x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex₁, p₁⟩ ← deriveNat x sNat
  let ⟨ex₂, p₂⟩ ← deriveNat y sNat
  let ⟨_, val, ascPrf⟩ := proveAscFactorial ex₁.natLit! ex₂.natLit! ex₁ ex₂
  return .isNat sNat q($val) q(isNat_ascFactorial $p₁ $p₂ $val $ascPrf)
-/
def evalNatAscFactorial : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Nat.ascFactorial x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex₁, p₁⟩ ← deriveNat x sNat
  let ⟨ex₂, p₂⟩ ← deriveNat y sNat
  let ⟨_, val, ascPrf⟩ := proveAscFactorial ex₁.natLit! ex₂.natLit! ex₁ ex₂
  return .isNat sNat q($val) q(isNat_ascFactorial $p₁ $p₂ $val $ascPrf)

/--
lemma `isNat_descFactorial` / 引理 `isNat_descFactorial`

English:
lemma isNat_descFactorial
  statement: {n x l y : Nat} (z : Nat) (h₁ : IsNat n x) (h₂ : IsNat l y)
  proof: by
  constructor
  simpa [h₁.out, h₂.out, ← p, h₃] using Nat.add_descFactorial_eq_ascFactorial _ _

中文:
引理 is自然数_descFactorial
  结论: {n x l y : 自然数} (z : 自然数) (h₁ : 是自然数 n x) (h₂ : 是自然数 l y)
  证明: by
  constructor
  simpa [h₁.out, h₂.out, ← p, h₃] using Nat.add_descFactorial_eq_ascFactorial _ _

Depends on / 依赖: Nat.add_descFactorial_eq_ascFactorial, add_descFactorial_eq_ascFactorial
-/
lemma isNat_descFactorial {n x l y : Nat} (z : Nat) (h₁ : IsNat n x) (h₂ : IsNat l y)
    (h₃ : x = z + y) (a : Nat) (p : (z + 1).ascFactorial y = a) : IsNat (n.descFactorial l) a := by
  constructor
  simpa [h₁.out, h₂.out, ← p, h₃] using Nat.add_descFactorial_eq_ascFactorial _ _

/--
lemma `isNat_descFactorial_zero` / 引理 `isNat_descFactorial_zero`

English:
lemma isNat_descFactorial_zero
  statement: {n x l y : Nat} (z : Nat) (h₁ : IsNat n x) (h₂ : IsNat l y)
  proof: by
  constructor
  simp [h₁.out, h₂.out, h₃]

中文:
引理 is自然数_descFactorial_zero
  结论: {n x l y : 自然数} (z : 自然数) (h₁ : 是自然数 n x) (h₂ : 是自然数 l y)
  证明: by
  constructor
  simp [h₁.out, h₂.out, h₃]

Depends on / 依赖: And.right, _closure_eq_self, closed_nhds_basis
-/
lemma isNat_descFactorial_zero {n x l y : Nat} (z : Nat) (h₁ : IsNat n x) (h₂ : IsNat l y)
    (h₃ : y = z + x + 1) : IsNat (n.descFactorial l) 0 := by
  constructor
  simp [h₁.out, h₂.out, h₃]

/--
Definition of `evalNatDescFactorialNotZero` / `evalNatDescFactorialNotZero` 的定义

English:
definition evalNatDescFactorialNotZero
  signature: {x' y' : Q(Nat)} (x y z : Q(Nat))
  body: have zp1 :Q(Nat) := mkRawNatLit (z.natLit! + 1)
have : zp1 =Q z + 1 := ⟨⟩
  let ⟨_, val, ascPrf⟩ := proveAscFactorial (z.natLit! + 1) y.natLit! zp1 y
  ⟨val, q(isNat_descFactorial $z $px $py rfl $val $ascPrf)⟩

中文:
定义 eval自然数DescFactorialNotZero
  签名: {x' y' : Q(自然数)} (x y z : Q(自然数))
  定义体: have zp1 :Q(Nat) := mkRawNatLit (z.natLit! + 1)
have : zp1 =Q z + 1 := ⟨⟩
  let ⟨_, val, ascPrf⟩ := proveAscFactorial (z.natLit! + 1) y.natLit! zp1 y
  ⟨val, q(isNat_descFactorial $z $px $py rfl $val $ascPrf)⟩
-/
private partial def evalNatDescFactorialNotZero {x' y' : Q(Nat)} (x y z : Q(Nat))
    (_hx : $x =Q $z + $y)
    (px : Q(IsNat $x' $x)) (py : Q(IsNat $y' $y)) :
    (n : Q(Nat)) × Q(IsNat (descFactorial $x' $y') $n) :=
  have zp1 :Q(Nat) := mkRawNatLit (z.natLit! + 1)
have : zp1 =Q z + 1 := ⟨⟩
  let ⟨_, val, ascPrf⟩ := proveAscFactorial (z.natLit! + 1) y.natLit! zp1 y
  ⟨val, q(isNat_descFactorial $z $px $py rfl $val $ascPrf)⟩

/--
Definition of `evalNatDescFactorialZero` / `evalNatDescFactorialZero` 的定义

English:
definition evalNatDescFactorialZero
  signature: {x' y' : Q(Nat)} (x y z : Q(Nat))
  body: ⟨q(nat_lit 0), q(isNat_descFactorial_zero $z $px $py rfl)⟩

中文:
定义 eval自然数DescFactorialZero
  签名: {x' y' : Q(自然数)} (x y z : Q(自然数))
  定义体: ⟨q(nat_lit 0), q(isNat_descFactorial_zero $z $px $py rfl)⟩
-/
private partial def evalNatDescFactorialZero {x' y' : Q(Nat)} (x y z : Q(Nat))
    (_hy : $y =Q $z + $x + 1)
    (px : Q(IsNat $x' $x)) (py : Q(IsNat $y' $y)) :
    (n : Q(Nat)) × Q(IsNat (descFactorial $x' $y') $n) :=
  ⟨q(nat_lit 0), q(isNat_descFactorial_zero $z $px $py rfl)⟩

/-- Evaluates the `Nat.descFactorial` function. -/
@[nolint unusedHavesSuffices, norm_num Nat.descFactorial _ _]
/--
Definition of `evalNatDescFactorial` / `evalNatDescFactorial` 的定义

English:
definition evalNatDescFactorial
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app _ (x' : Q(Nat))) (y' : Q(Nat)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩
have : α =Q Nat := ⟨⟩
have : e =Q Nat.descFactorial x' y' := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨x, p₁⟩ ← deriveNat x' sNat
  let ⟨y, p₂⟩ ← deriveNat y' sNat
  if x.natLit! >= y.natLit! then
    have z : Q(Nat) := mkRawNatLit (x.natLit! - y.natLit!)
have : x =Q z + y := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialNotZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sNat val q($prf)
  else
    have z : Q(Nat) := mkRawNatLit (y.natLit! - x.natLit! - 1)
have : y =Q z + x + 1 := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sNat val q($prf)

中文:
定义 eval自然数DescFactorial
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app _ (x' : Q(Nat))) (y' : Q(Nat)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩
have : α =Q Nat := ⟨⟩
have : e =Q Nat.descFactorial x' y' := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨x, p₁⟩ ← deriveNat x' sNat
  let ⟨y, p₂⟩ ← deriveNat y' sNat
  if x.natLit! >= y.natLit! then
    have z : Q(Nat) := mkRawNatLit (x.natLit! - y.natLit!)
have : x =Q z + y := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialNotZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sNat val q($prf)
  else
    have z : Q(Nat) := mkRawNatLit (y.natLit! - x.natLit! - 1)
have : y =Q z + x + 1 := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sNat val q($prf)
-/
def evalNatDescFactorial : NormNumExt where eval {u α} e := do
  let .app (.app _ (x' : Q(Nat))) (y' : Q(Nat)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩
have : α =Q Nat := ⟨⟩
have : e =Q Nat.descFactorial x' y' := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨x, p₁⟩ ← deriveNat x' sNat
  let ⟨y, p₂⟩ ← deriveNat y' sNat
  if x.natLit! >= y.natLit! then
    have z : Q(Nat) := mkRawNatLit (x.natLit! - y.natLit!)
have : x =Q z + y := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialNotZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sNat val q($prf)
  else
    have z : Q(Nat) := mkRawNatLit (y.natLit! - x.natLit! - 1)
have : y =Q z + x + 1 := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sNat val q($prf)

end NormNum

end Meta

end Mathlib
