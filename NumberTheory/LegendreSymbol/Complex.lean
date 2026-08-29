/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Additive characters on finite fields

We construct a primitive additive character on a finite field `F` with values in `ℂ`.
This file is kept separate from `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` to avoid
importing the fundamental theorem of algebra and Bochner integral into that file.
-/

namespace AddChar

section Field

variable (F : Type*) [Field F] [Finite F]

/--
lemma `ringChar_ne` / 引理 `ringChar_ne`

English:
lemma ringChar_ne
  statement: ringChar Complex != ringChar F
  proof: by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

中文:
引理 ringChar_ne
  结论: ringChar 复形 != ringChar F
  证明: by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

Depends on / 依赖: CharP.ringChar_ne_zero_of_finite, eq_zero, ringChar, ringChar.eq_zero, ringChar_ne_zero_of_finite
-/
lemma ringChar_ne : ringChar Complex != ringChar F := by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

/-- A primitive additive character on the finite field `F` with values in `ℂ`. -/
public noncomputable def FiniteField.primitiveChar_to_Complex : AddChar F Complex := by
letI ch := primitiveChar F Complex by exact ringChar_ne F
  refine MonoidHom.compAddChar ?_ ch.char
  exact (IsCyclotomicExtension.algEquiv {(ch.n : Nat)} Complex (CyclotomicField ch.n Complex) Complex).toMonoidHom

public lemma FiniteField.primitiveChar_to_Complex_isPrimitive :
    (primitiveChar_to_Complex F).IsPrimitive := by
  refine IsPrimitive.compMulHom_of_isPrimitive (PrimitiveAddChar.prim _) ?_
  let nn := (primitiveChar F Complex <| ringChar_ne F).n
  exact (IsCyclotomicExtension.algEquiv {(nn : Nat)} Complex (CyclotomicField nn Complex) Complex).injective

end Field

end AddChar
