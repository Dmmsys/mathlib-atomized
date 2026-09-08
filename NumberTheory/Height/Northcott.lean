/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.Order.Northcott

/-!
# Results on the Northcott property for heights

Assume that `K` is a field with a family of admissible absolute values that satisfies
the Northcott property for `mulHeight₁`.
We provide instances showing that `K` also satisfies the Northcott property
* for `logHeight₁`,
* (TODO) for `Projectivization.mulHeight`,
* (TODO) for `Projectivization.logHeight`.

## TODO

Add instances for heights on projectivizations.
-/

namespace Height

public section

open Real Northcott

variable {K : Type*} [Field K]

/-- A field that satisfies the Northcott property for `mulHeight₁` also does for `logHeight₁`. -/
/-
**Height.** 是 Mathlib 中的一个实例，位于命名空间 `Height`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field that satisfies the Northcott property for `mulHeight₁` also does for `lo
gHeight₁`.
-/
instance [AdmissibleAbsValues K] [Northcott (mulHeight₁ (K := K))] :
    Northcott (logHeight₁ (K := K)) :=
  comp_of_bddAbove mulHeight₁ log fun B ↦ bddAbove_def.mpr ⟨exp B, fun _ ↦ le_exp_of_log_le⟩

end

end Height

