/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Orientation

/-!
# The standard orientation on `ℂ`.

This had previously been in `LinearAlgebra.Orientation`,
but keeping it separate results in a significant import reduction.
-/

@[expose] public section


namespace Complex

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def orientation
  body: Complex.basisOneI.orientation

中文:
定义 noncomputable
  签名: def orientation
  定义体: Complex.basisOneI.orientation
-/
protected noncomputable def orientation : Orientation Real Complex (Fin 2) :=
  Complex.basisOneI.orientation

end Complex
