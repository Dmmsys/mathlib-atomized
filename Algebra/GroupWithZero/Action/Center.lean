/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# The center of a group with zero
-/

@[expose] public section

assert_not_exists Ring

/-- For a group with zero, the center of the units is the same as the units of the center. -/
@[simps! apply_val_coe symm_apply_coe_val]
/-
**Subgroup.centerUnitsEquivUnitsCenter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.centerUnitsEquivUnitsCenter (G₀ : Type*) [GroupWithZero G₀] : cen
ter G₀ˣ ≃* (Submonoid.center G₀)ˣ where toFun
参数：G₀ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a group with zero, the center of the units is the same as the units of the c
enter.
-/
def Subgroup.centerUnitsEquivUnitsCenter (G₀ : Type*) [GroupWithZero G₀] :
    center G₀ˣ ≃* (Submonoid.center G₀)ˣ where
  toFun := MonoidHom.toHomUnits
    { toFun u := by
        refine ⟨(u : G₀ˣ), Submonoid.mem_center_iff.mpr fun r ↦ ?_⟩
        obtain rfl | hr := eq_or_ne r 0
        · rw [mul_zero, zero_mul]
        · exact congrArg Units.val <| (u.2.comm <| Units.mk0 r hr).symm
      map_one' := rfl
      map_mul' _ _ := rfl }
  invFun u := unitsCenterToCenterUnits G₀ u
  map_mul' := map_mul _
