/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.BitVec


/-!
# Adds Mathlib specific instances to the `UIntX` data types.

The `CommRing` instances (and the `NatCast` and `IntCast` instances from which they is built) are
scoped in the `UIntX.CommRing` namespace, rather than available globally. As a result, the `ring`
tactic will not work on `UIntX` types without `open scoped UIntX.Ring`.

This is because the presence of these casting operations contradicts assumptions made by the
expression tree elaborator, namely that coercions do not form a cycle.

The UInt
version also interferes more with software-verification use-cases, which is reason to be more
cautious here.
-/

@[expose] public section

set_option linter.style.emptyLine false in
-- these theorems are fragile, so do them first
set_option hygiene false in
run_cmd
  for typeName' in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do
  let typeName := Lean.mkIdent typeName'
  Lean.Elab.Command.elabCommand (← `(
namespace typeName

open typeName (toBitVec_mul) in
/--
theorem `toBitVec_nsmul` / 定理 `toBitVec_nsmul`

English:
theorem toBitVec_nsmul
  given: (n : Nat) (a : $typeName)
  proof: by
        rw [Lean.Grind.Semiring.nsmul_eq_natCast_mul]; rw [toBitVec_mul]; rw [nsmul_eq_mul]; rw [BitVec.natCast_eq_ofNat]
        rfl

中文:
定理 toBitVec_nsmul
  条件: (n : 自然数) (a : $typeName)
  证明: by
        rw [Lean.Grind.Semiring.nsmul_eq_natCast_mul]; rw [toBitVec_mul]; rw [nsmul_eq_mul]; rw [BitVec.natCast_eq_ofNat]
        rfl
-/
      protected theorem toBitVec_nsmul (n : Nat) (a : $typeName) :
          (n • a).toBitVec = n • a.toBitVec := by
        rw [Lean.Grind.Semiring.nsmul_eq_natCast_mul]; rw [toBitVec_mul]; rw [nsmul_eq_mul]; rw [BitVec.natCast_eq_ofNat]
        rfl

      attribute [local instance] natCast intCast

      @[simp, int_toBitVec]
/--
theorem `toBitVec_natCast` / 定理 `toBitVec_natCast`

English:
theorem toBitVec_natCast
  given: (n : Nat)
  proof: rfl

中文:
定理 toBitVec_natCast
  条件: (n : 自然数)
  证明: rfl
-/
      protected theorem toBitVec_natCast (n : Nat) :
          (n : $typeName).toBitVec = n := rfl

open typeName (toBitVec_neg) in
      @[simp, int_toBitVec]
/--
theorem `toBitVec_intCast` / 定理 `toBitVec_intCast`

English:
theorem toBitVec_intCast
  given: (z : Int)
  proof: by
        obtain ⟨z, rfl | rfl⟩ := z.eq_nat_or_neg
        · erw [intCast_ofNat]; rfl
        · rw [intCast_neg, toBitVec_neg]
          erw [intCast_ofNat]
          simp

中文:
定理 toBitVec_intCast
  条件: (z : 整数)
  证明: by
        obtain ⟨z, rfl | rfl⟩ := z.eq_nat_or_neg
        · erw [intCast_ofNat]; rfl
        · rw [intCast_neg, toBitVec_neg]
          erw [intCast_ofNat]
          simp
-/
      protected theorem toBitVec_intCast (z : Int) :
          (z : $typeName).toBitVec = z := by
        obtain ⟨z, rfl | rfl⟩ := z.eq_nat_or_neg
        · erw [intCast_ofNat]; rfl
        · rw [intCast_neg, toBitVec_neg]
          erw [intCast_ofNat]
          simp

open typeName (toBitVec_mul toBitVec_intCast) in
      @[simp, int_toBitVec]
/--
theorem `toBitVec_zsmul` / 定理 `toBitVec_zsmul`

English:
theorem toBitVec_zsmul
  given: (z : Int) (a : $typeName)
  proof: by
        change (z * a).toBitVec = BitVec.ofInt _ z * a.toBitVec
        rw [toBitVec_mul]
        congr 1
        rw [toBitVec_intCast]
        rfl

中文:
定理 toBitVec_zsmul
  条件: (z : 整数) (a : $typeName)
  证明: by
        change (z * a).toBitVec = BitVec.ofInt _ z * a.toBitVec
        rw [toBitVec_mul]
        congr 1
        rw [toBitVec_intCast]
        rfl
-/
      protected theorem toBitVec_zsmul (z : Int) (a : $typeName) :
          (z • a).toBitVec = z • a.toBitVec := by
        change (z * a).toBitVec = BitVec.ofInt _ z * a.toBitVec
        rw [toBitVec_mul]
        congr 1
        rw [toBitVec_intCast]
        rfl

end typeName
  ))

set_option linter.style.emptyLine false in
-- Note that these construct no new data, so cannot form diamonds with core.
set_option hygiene false in
run_cmd
  for typeName' in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do
  let typeName := Lean.mkIdent typeName'
  Lean.Elab.Command.elabCommand (← `(
namespace typeName

open typeName (eq_of_toFin_eq) in
/--
lemma `toFin_injective` / 引理 `toFin_injective`

English:
lemma toFin_injective
  statement: Function.Injective toFin
  proof: @eq_of_toFin_eq

中文:
引理 toFin_injective
  结论: 函数.单射 toFin
  证明: @eq_of_toFin_eq

Depends on / 依赖: eq_of_toFin_eq
-/
      lemma toFin_injective : Function.Injective toFin := @eq_of_toFin_eq

open typeName (eq_of_toBitVec_eq) in
/--
lemma `toBitVec_injective` / 引理 `toBitVec_injective`

English:
lemma toBitVec_injective
  statement: Function.Injective toBitVec
  proof: @eq_of_toBitVec_eq

中文:
引理 toBitVec_injective
  结论: 函数.单射 toBitVec
  证明: @eq_of_toBitVec_eq

Depends on / 依赖: eq_of_toBitVec_eq
-/
      lemma toBitVec_injective : Function.Injective toBitVec := @eq_of_toBitVec_eq

open typeName (toBitVec_one toBitVec_mul toBitVec_pow) in
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: : CommMonoid typeName
  body: Function.Injective.commMonoid toBitVec toBitVec_injective
          toBitVec_one (fun _ _ => toBitVec_mul) (fun _ _ => toBitVec_pow _ _)

中文:
实例 instCommMonoid
  签名: : 交换幺半群 typeName
  定义体: Function.Injective.commMonoid toBitVec toBitVec_injective
          toBitVec_one (fun _ _ => toBitVec_mul) (fun _ _ => toBitVec_pow _ _)

Depends on / 依赖: Function, Function.Injective.commMonoid, Injective, commMonoid, toBitVec, toBitVec_injective, toBitVec_mul, toBitVec_one, toBitVec_pow
-/
instance instCommMonoid : CommMonoid typeName :=
        Function.Injective.commMonoid toBitVec toBitVec_injective
          toBitVec_one (fun _ _ => toBitVec_mul) (fun _ _ => toBitVec_pow _ _)

open typeName (
        toBitVec_zero toBitVec_add toBitVec_mul toBitVec_neg toBitVec_sub toBitVec_nsmul
        toBitVec_zsmul) in
/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: : NonUnitalCommRing typeName
  body: Function.Injective.nonUnitalCommRing toBitVec toBitVec_injective
          toBitVec_zero (fun _ _ => toBitVec_add) (fun _ _ => toBitVec_mul) (fun _ => toBitVec_neg)
          (fun _ _ => toBitVec_sub)
          (fun _ _ => toBitVec_nsmul _ _) (fun _ _ => toBitVec_zsmul _ _)

      attribute [local instance] intCast natCast

中文:
实例 instNonUnitalCommRing
  签名: : 非幺交换环 typeName
  定义体: Function.Injective.nonUnitalCommRing toBitVec toBitVec_injective
          toBitVec_zero (fun _ _ => toBitVec_add) (fun _ _ => toBitVec_mul) (fun _ => toBitVec_neg)
          (fun _ _ => toBitVec_sub)
          (fun _ _ => toBitVec_nsmul _ _) (fun _ _ => toBitVec_zsmul _ _)

      attribute [local instance] intCast natCast

Depends on / 依赖: Function, Function.Injective.nonUnitalCommRing, Injective, nonUnitalCommRing, toBitVec, toBitVec_add, toBitVec_injective, toBitVec_mul, toBitVec_neg, toBitVec_nsmul, toBitVec_sub, toBitVec_zero, toBitVec_zsmul
-/
instance instNonUnitalCommRing : NonUnitalCommRing typeName :=
        Function.Injective.nonUnitalCommRing toBitVec toBitVec_injective
          toBitVec_zero (fun _ _ => toBitVec_add) (fun _ _ => toBitVec_mul) (fun _ => toBitVec_neg)
          (fun _ _ => toBitVec_sub)
          (fun _ _ => toBitVec_nsmul _ _) (fun _ _ => toBitVec_zsmul _ _)

      attribute [local instance] intCast natCast

open typeName (
        toBitVec_zero toBitVec_one toBitVec_add toBitVec_mul toBitVec_neg
        toBitVec_sub toBitVec_nsmul toBitVec_zsmul toBitVec_pow
        toBitVec_natCast toBitVec_intCast) in
      -- `noncomputable` should not be necessary but triggers some codegen assertion
noncomputable local instance instCommRing : CommRing typeName :=
        Function.Injective.commRing toBitVec toBitVec_injective
          toBitVec_zero toBitVec_one (fun _ _ => toBitVec_add) (fun _ _ => toBitVec_mul)
          (fun _ => toBitVec_neg) (fun _ _ => toBitVec_sub)
          (fun _ _ => toBitVec_nsmul _ _) (fun _ _ => toBitVec_zsmul _ _)
          (fun _ _ => toBitVec_pow _ _)
          toBitVec_natCast toBitVec_intCast

      namespace CommRing
      attribute [scoped instance] instCommRing natCast intCast
      end CommRing

end typeName
  ))
  -- interpolating docstrings above is more trouble than it's worth
  let docString :=
    s!"To use this instance, use `open scoped {typeName'}.CommRing`.\n\n" ++
    "See the module docstring for an explanation"
  Lean.addDocStringCore (typeName'.mkStr "instCommRing") docString
  -- TODO: add these docstrings in core?
  -- Lean.addDocStringCore (typeName'.mkStr "instNatCast") docString
  -- Lean.addDocStringCore (typeName'.mkStr "instIntCast") docString

namespace UInt8

/--
Definition of `isASCIIUpper` / `isASCIIUpper` 的定义

English:
definition isASCIIUpper
  signature: (c : UInt8)
  body: c >= 65 && c <= 90

中文:
定义 isASCIIUpper
  签名: (c : U整数8)
  定义体: c >= 65 && c <= 90
-/
def isASCIIUpper (c : UInt8) : Bool :=
  c >= 65 && c <= 90

/--
Definition of `isASCIILower` / `isASCIILower` 的定义

English:
definition isASCIILower
  signature: (c : UInt8)
  body: c >= 97 && c <= 122

中文:
定义 isASCIILower
  签名: (c : U整数8)
  定义体: c >= 97 && c <= 122
-/
def isASCIILower (c : UInt8) : Bool :=
  c >= 97 && c <= 122

/--
Definition of `isASCIIAlpha` / `isASCIIAlpha` 的定义

English:
definition isASCIIAlpha
  signature: (c : UInt8)
  body: c.isASCIIUpper || c.isASCIILower

中文:
定义 isASCIIAlpha
  签名: (c : U整数8)
  定义体: c.isASCIIUpper || c.isASCIILower

Depends on / 依赖: c.isASCIILower, c.isASCIIUpper, isASCIILower, isASCIIUpper
-/
def isASCIIAlpha (c : UInt8) : Bool :=
  c.isASCIIUpper || c.isASCIILower

/--
Definition of `isASCIIDigit` / `isASCIIDigit` 的定义

English:
definition isASCIIDigit
  signature: (c : UInt8)
  body: c >= 48 && c <= 57

中文:
定义 isASCIIDigit
  签名: (c : U整数8)
  定义体: c >= 48 && c <= 57
-/
def isASCIIDigit (c : UInt8) : Bool :=
  c >= 48 && c <= 57

/--
Definition of `isASCIIAlphanum` / `isASCIIAlphanum` 的定义

English:
definition isASCIIAlphanum
  signature: (c : UInt8)
  body: c.isASCIIAlpha || c.isASCIIDigit

中文:
定义 isASCIIAlphanum
  签名: (c : U整数8)
  定义体: c.isASCIIAlpha || c.isASCIIDigit

Depends on / 依赖: c.isASCIIAlpha, c.isASCIIDigit, isASCIIAlpha, isASCIIDigit
-/
def isASCIIAlphanum (c : UInt8) : Bool :=
  c.isASCIIAlpha || c.isASCIIDigit

/--
Definition of `toChar` / `toChar` 的定义

English:
definition toChar
  signature: (n : UInt8)
  body: ⟨n.toUInt32, .inl (Nat.lt_trans n.toBitVec.isLt (by decide))⟩

中文:
定义 toChar
  签名: (n : U整数8)
  定义体: ⟨n.toUInt32, .inl (Nat.lt_trans n.toBitVec.isLt (by decide))⟩

Depends on / 依赖: Nat.lt_trans, lt_trans, n.toBitVec.isLt, n.toUInt32, toBitVec, toUInt32
-/
def toChar (n : UInt8) : Char := ⟨n.toUInt32, .inl (Nat.lt_trans n.toBitVec.isLt (by decide))⟩

end UInt8
