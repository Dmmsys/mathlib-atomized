/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Additive characters valued in the unit circle

This file defines additive characters, valued in the unit circle, from either
* the ring `ZMod N` for any non-zero natural `N`,
* the additive circle `ℝ / T ⬝ ℤ`, for any real `T`.

These results are separate from `Analysis.SpecialFunctions.Complex.Circle` in order to reduce
the imports of that file.
-/

@[expose] public section

open Complex Function

open scoped Real

/--
Definition of `AddCircle.toCircle_addChar` / `AddCircle.toCircle_addChar` 的定义

English:
definition AddCircle.toCircle_addChar
  signature: {T : Real}
  body: toCircle
  map_zero_eq_one' := toCircle_zero
  map_add_eq_mul' := toCircle_add

中文:
定义 AddCircle.toCircle_addChar
  签名: {T : 实数}
  定义体: toCircle
  map_zero_eq_one' := toCircle_zero
  map_add_eq_mul' := toCircle_add

Depends on / 依赖: CochainComplex, CochainComplex.isIso_liftCycles_iff, F.map_isZero, InjectiveResolution, InjectiveResolution.toRightDerivedZero, ShortComplex, ShortComplex.Splitting.exact, Splitting, eq_of_src, isIso_liftCycles_iff, isZero_zero, map_isZero, toCircle, toRightDerivedZero
-/
noncomputable def AddCircle.toCircle_addChar {T : Real} : AddChar (AddCircle T) Circle where
  toFun := toCircle
  map_zero_eq_one' := toCircle_zero
  map_add_eq_mul' := toCircle_add

open AddCircle

namespace ZMod

/-!
### Additive characters valued in the complex circle
-/

open scoped Real

variable {N : Nat} [NeZero N]

/--
Definition of `toCircle` / `toCircle` 的定义

English:
definition toCircle
  signature: : AddChar (ZMod N) Circle
  body: toCircle_addChar.compAddMonoidHom toAddCircle

中文:
定义 toCircle
  签名: : 加法特征 (ZMod N) Circle
  定义体: toCircle_addChar.compAddMonoidHom toAddCircle

Depends on / 依赖: compAddMonoidHom, toAddCircle, toCircle_addChar, toCircle_addChar.compAddMonoidHom
-/
noncomputable def toCircle : AddChar (ZMod N) Circle :=
  toCircle_addChar.compAddMonoidHom toAddCircle

/--
lemma `toCircle_intCast` / 引理 `toCircle_intCast`

English:
lemma toCircle_intCast
  given: (j : Int)
  proof: by
  rw [toCircle]; rw [AddChar.compAddMonoidHom_apply]; rw [toCircle_addChar]; rw [AddChar.coe_mk]; rw [AddCircle.toCircle]; rw [toAddCircle_intCast]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]
  push_cast
  ring_nf

中文:
引理 toCircle_intCast
  条件: (j : 整数)
  证明: by
  rw [toCircle]; rw [AddChar.compAddMonoidHom_apply]; rw [toCircle_addChar]; rw [AddChar.coe_mk]; rw [AddCircle.toCircle]; rw [toAddCircle_intCast]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]
  push_cast
  ring_nf

Depends on / 依赖: AddChar, AddChar.coe_mk, AddChar.compAddMonoidHom_apply, AddCircle, AddCircle.toCircle, Circle, Circle.coe_exp, Function, Function.Periodic.lift_coe, Periodic, coe_exp, coe_mk, compAddMonoidHom_apply, lift_coe, ring_nf, toAddCircle_intCast, toCircle, toCircle_addChar
-/
lemma toCircle_intCast (j : Int) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  rw [toCircle]; rw [AddChar.compAddMonoidHom_apply]; rw [toCircle_addChar]; rw [AddChar.coe_mk]; rw [AddCircle.toCircle]; rw [toAddCircle_intCast]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]
  push_cast
  ring_nf

/--
lemma `toCircle_natCast` / 引理 `toCircle_natCast`

English:
lemma toCircle_natCast
  given: (j : Nat)
  proof: by
  simpa using toCircle_intCast (N := N) j

中文:
引理 toCircle_natCast
  条件: (j : 自然数)
  证明: by
  simpa using toCircle_intCast (N := N) j

Depends on / 依赖: InjectiveResolution, InjectiveResolution.self, infer_instance, toCircle_intCast, toRightDerivedZero_eq
-/
lemma toCircle_natCast (j : Nat) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  simpa using toCircle_intCast (N := N) j

/--
lemma `toCircle_apply` / 引理 `toCircle_apply`

English:
lemma toCircle_apply
  given: (j : ZMod N)
  proof: by
  rw [← toCircle_natCast]; rw [natCast_zmod_val]

中文:
引理 toCircle_apply
  条件: (j : ZMod N)
  证明: by
  rw [← toCircle_natCast]; rw [natCast_zmod_val]

Depends on / 依赖: CochainComplex, CochainComplex.isIso_liftCycles_iff, InjectiveResolution, InjectiveResolution.toRightDerivedZero, KernelFork, KernelFork.mapIsLimit, P.isLimitKernelFork, ShortComplex, ShortComplex.exact_and_mono_f_iff_f_is_kernel, exact_and_mono_f_iff_f_is_kernel, isIso_liftCycles_iff, isLimitKernelFork, mapIsLimit, natCast_zmod_val, toCircle_natCast, toRightDerivedZero
-/
lemma toCircle_apply (j : ZMod N) :
    toCircle j = exp (2 * π * I * j.val / N) := by
  rw [← toCircle_natCast]; rw [natCast_zmod_val]

/--
lemma `toCircle_eq_circleExp` / 引理 `toCircle_eq_circleExp`

English:
lemma toCircle_eq_circleExp
  given: (j : ZMod N)
  proof: by
  ext
  rw [toCircle_apply]; rw [Circle.coe_exp]
  push_cast
  congr; ring

中文:
引理 toCircle_eq_circleExp
  条件: (j : ZMod N)
  证明: by
  ext
  rw [toCircle_apply]; rw [Circle.coe_exp]
  push_cast
  congr; ring

Depends on / 依赖: Circle, Circle.coe_exp, Functor, Functor.toRightDerivedZero, coe_exp, infer_instance, toCircle_apply, toRightDerivedZero
-/
lemma toCircle_eq_circleExp (j : ZMod N) :
    toCircle j = Circle.exp (2 * π * (j.val / N)) := by
  ext
  rw [toCircle_apply]; rw [Circle.coe_exp]
  push_cast
  congr; ring

/--
lemma `injective_toCircle` / 引理 `injective_toCircle`

English:
lemma injective_toCircle
  statement: Injective (toCircle : ZMod N -> Circle)
  proof: (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)

中文:
引理 injective_toCircle
  结论: 单射 (toCircle : ZMod N -> Circle)
  证明: (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)

Depends on / 依赖: AddCircle, AddCircle.injective_toCircle, injective_toCircle, one_ne_zero, toAddCircle_injective
-/
lemma injective_toCircle : Injective (toCircle : ZMod N -> Circle) :=
  (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)

/--
Definition of `stdAddChar` / `stdAddChar` 的定义

English:
definition stdAddChar
  signature: : AddChar (ZMod N) Complex
  body: Circle.coeHom.compAddChar toCircle

中文:
定义 stdAddChar
  签名: : 加法特征 (ZMod N) 复形
  定义体: Circle.coeHom.compAddChar toCircle

Depends on / 依赖: Circle, Circle.coeHom.compAddChar, coeHom, compAddChar, toCircle
-/
noncomputable def stdAddChar : AddChar (ZMod N) Complex := Circle.coeHom.compAddChar toCircle

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stdAddChar_coe` / 引理 `stdAddChar_coe`

English:
lemma stdAddChar_coe
  given: (j : Int)
  proof: by simp [stdAddChar, toCircle_intCast]

中文:
引理 stdAddChar_coe
  条件: (j : 整数)
  证明: by simp [stdAddChar, toCircle_intCast]

Depends on / 依赖: stdAddChar, toCircle_intCast
-/
lemma stdAddChar_coe (j : Int) :
    stdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by simp [stdAddChar, toCircle_intCast]

/--
lemma `stdAddChar_apply` / 引理 `stdAddChar_apply`

English:
lemma stdAddChar_apply
  given: (j : ZMod N)
  statement: stdAddChar j = ↑(toCircle j)
  proof: rfl

中文:
引理 stdAddChar_apply
  条件: (j : ZMod N)
  结论: stdAddChar j = ↑(toCircle j)
  证明: rfl
-/
lemma stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(toCircle j) := rfl

/--
lemma `injective_stdAddChar` / 引理 `injective_stdAddChar`

English:
lemma injective_stdAddChar
  statement: Injective (stdAddChar : AddChar (ZMod N) Complex)
  proof: Subtype.coe_injective.comp injective_toCircle

中文:
引理 injective_stdAddChar
  结论: 单射 (stdAddChar : 加法特征 (ZMod N) 复形)
  证明: Subtype.coe_injective.comp injective_toCircle

Depends on / 依赖: Subtype, Subtype.coe_injective.comp, coe_injective, injective_toCircle
-/
lemma injective_stdAddChar : Injective (stdAddChar : AddChar (ZMod N) Complex) :=
  Subtype.coe_injective.comp injective_toCircle

/--
lemma `isPrimitive_stdAddChar` / 引理 `isPrimitive_stdAddChar`

English:
lemma isPrimitive_stdAddChar
  given: (N : Nat) [NeZero N]
  proof: by
  refine AddChar.zmod_char_primitive_of_eq_one_only_at_zero _ _ (fun t ht => ?_)
  rwa [← (stdAddChar (N := N)).map_zero_eq_one, injective_stdAddChar.eq_iff] at ht

中文:
引理 isPrimitive_stdAddChar
  条件: (N : 自然数) [NeZero N]
  证明: by
  refine AddChar.zmod_char_primitive_of_eq_one_only_at_zero _ _ (fun t ht => ?_)
  rwa [← (stdAddChar (N := N)).map_zero_eq_one, injective_stdAddChar.eq_iff] at ht

Depends on / 依赖: AddChar, AddChar.zmod_char_primitive_of_eq_one_only_at_zero, IsPrimitive, eq_iff, injective_stdAddChar, injective_stdAddChar.eq_iff, map_zero_eq_one, stdAddChar, zmod_char_primitive_of_eq_one_only_at_zero
-/
lemma isPrimitive_stdAddChar (N : Nat) [NeZero N] :
    (stdAddChar (N := N)).IsPrimitive := by
  refine AddChar.zmod_char_primitive_of_eq_one_only_at_zero _ _ (fun t ht => ?_)
  rwa [← (stdAddChar (N := N)).map_zero_eq_one, injective_stdAddChar.eq_iff] at ht

/--
Definition of `rootsOfUnityAddChar` / `rootsOfUnityAddChar` 的定义

English:
definition rootsOfUnityAddChar
  signature: (n : Nat) [NeZero n]
  body: ⟨toUnits (ZMod.toCircle x), by ext; simp [← AddChar.map_nsmul_eq_pow]⟩
  map_zero_eq_one' := by simp
  map_add_eq_mul' _ _ := by ext; simp [AddChar.map_add_eq_mul]

中文:
定义 rootsOfUnityAddChar
  签名: (n : 自然数) [NeZero n]
  定义体: ⟨toUnits (ZMod.toCircle x), by ext; simp [← AddChar.map_nsmul_eq_pow]⟩
  map_zero_eq_one' := by simp
  map_add_eq_mul' _ _ := by ext; simp [AddChar.map_add_eq_mul]

Depends on / 依赖: AddChar, AddChar.map_nsmul_eq_pow, ZMod.toCircle, map_nsmul_eq_pow, toCircle, toUnits
-/
noncomputable def rootsOfUnityAddChar (n : Nat) [NeZero n] :
    AddChar (ZMod n) (rootsOfUnity n Circle) where
  toFun x := ⟨toUnits (ZMod.toCircle x), by ext; simp [← AddChar.map_nsmul_eq_pow]⟩
  map_zero_eq_one' := by simp
  map_add_eq_mul' _ _ := by ext; simp [AddChar.map_add_eq_mul]

/--
lemma `rootsOfUnityAddChar_val` / 引理 `rootsOfUnityAddChar_val`

English:
lemma rootsOfUnityAddChar_val
  given: (n : Nat) [NeZero n] (x : ZMod n)
  proof: by
  rfl

中文:
引理 rootsOfUnityAddChar_val
  条件: (n : 自然数) [NeZero n] (x : ZMod n)
  证明: by
  rfl
-/
@[simp] lemma rootsOfUnityAddChar_val (n : Nat) [NeZero n] (x : ZMod n) :
    (rootsOfUnityAddChar n x).val = toCircle x := by
  rfl

end ZMod

variable (n : Nat) [NeZero n]

/--
Definition of `rootsOfUnitytoCircle` / `rootsOfUnitytoCircle` 的定义

English:
definition rootsOfUnitytoCircle
  signature: : (rootsOfUnity n Complex) ->* Circle where
  body: fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 rootsOfUnitytoCircle
  签名: : (rootsOfUnity n 复形) ->* Circle where
  定义体: fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: z.val.val
-/
noncomputable def rootsOfUnitytoCircle : (rootsOfUnity n Complex) ->* Circle where
  toFun := fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Definition of `rootsOfUnityCircleEquiv` / `rootsOfUnityCircleEquiv` 的定义

English:
definition rootsOfUnityCircleEquiv
  signature: : rootsOfUnity n Circle ≃* rootsOfUnity n Complex where
  body: (rootsOfUnityUnitsMulEquiv Complex n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨(rootsOfUnitytoCircle n).toHomUnits z, by
    rw [mem_rootsOfUnity']; rw [MonoidHom.coe_toHomUnits]; rw [← map_pow]; rw [← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

中文:
定义 rootsOfUnityCircleEquiv
  签名: : rootsOfUnity n Circle ≃* rootsOfUnity n 复形 where
  定义体: (rootsOfUnityUnitsMulEquiv Complex n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨(rootsOfUnitytoCircle n).toHomUnits z, by
    rw [mem_rootsOfUnity']; rw [MonoidHom.coe_toHomUnits]; rw [← map_pow]; rw [← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

Depends on / 依赖: Circle, Circle.toUnits, restrictRootsOfUnity, rootsOfUnityUnitsMulEquiv, toMonoidHom, toMonoidHom.comp, toUnits
-/
noncomputable def rootsOfUnityCircleEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n Complex where
  __ := (rootsOfUnityUnitsMulEquiv Complex n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨(rootsOfUnitytoCircle n).toHomUnits z, by
    rw [mem_rootsOfUnity']; rw [MonoidHom.coe_toHomUnits]; rw [← map_pow]; rw [← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasEnoughRootsOfUnity Circle n
  body: (rootsOfUnityCircleEquiv n).symm.hasEnoughRootsOfUnity

中文:
实例 :
  签名: 有EnoughRootsOfUnity Circle n
  定义体: (rootsOfUnityCircleEquiv n).symm.hasEnoughRootsOfUnity

Depends on / 依赖: hasEnoughRootsOfUnity, rootsOfUnityCircleEquiv, symm.hasEnoughRootsOfUnity
-/
instance : HasEnoughRootsOfUnity Circle n := (rootsOfUnityCircleEquiv n).symm.hasEnoughRootsOfUnity

/--
lemma `rootsOfUnityCircleEquiv_apply` / 引理 `rootsOfUnityCircleEquiv_apply`

English:
lemma rootsOfUnityCircleEquiv_apply
  given: (w : rootsOfUnity n Circle)
  proof: rfl

中文:
引理 rootsOfUnityCircleEquiv_apply
  条件: (w : rootsOfUnity n Circle)
  证明: rfl
-/
@[simp] lemma rootsOfUnityCircleEquiv_apply (w : rootsOfUnity n Circle) :
    ((rootsOfUnityCircleEquiv n w).val : Complex) = ((w.val : Circle) : Complex) :=
  rfl

open Real in
/--
lemma `rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val` / 引理 `rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val`

English:
lemma rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val
  given: (j : ZMod n)
  proof: by
  simp [← ZMod.toCircle_natCast, -ZMod.natCast_val, ZMod.natCast_zmod_val]

中文:
引理 rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val
  条件: (j : ZMod n)
  证明: by
  simp [← ZMod.toCircle_natCast, -ZMod.natCast_val, ZMod.natCast_zmod_val]

Depends on / 依赖: ZMod.natCast_val, ZMod.natCast_zmod_val, ZMod.toCircle_natCast, natCast_val, natCast_zmod_val, toCircle_natCast
-/
lemma rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val (j : ZMod n) :
    (rootsOfUnityCircleEquiv n (ZMod.rootsOfUnityAddChar n j)).val
      = Complex.exp (2 * π * I * j.val / n) := by
  simp [← ZMod.toCircle_natCast, -ZMod.natCast_val, ZMod.natCast_zmod_val]

/--
theorem `surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar` / 定理 `surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar`

English:
theorem surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar
  given: (n : Nat) [NeZero n]
  proof: fun ⟨w, hw⟩ => by
  obtain ⟨j, hj1, hj2⟩ := (Complex.mem_rootsOfUnity n w).mp hw
  exact ⟨j, by simp [Units.ext_iff, Subtype.ext_iff, ← hj2, ZMod.toCircle_natCast, mul_div_assoc]⟩

中文:
定理 surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar
  条件: (n : 自然数) [NeZero n]
  证明: fun ⟨w, hw⟩ => by
  obtain ⟨j, hj1, hj2⟩ := (Complex.mem_rootsOfUnity n w).mp hw
  exact ⟨j, by simp [Units.ext_iff, Subtype.ext_iff, ← hj2, ZMod.toCircle_natCast, mul_div_assoc]⟩

Depends on / 依赖: Complex.mem_rootsOfUnity, Subtype, Subtype.ext_iff, Units.ext_iff, ZMod.toCircle_natCast, ext_iff, mem_rootsOfUnity, mul_div_assoc, toCircle_natCast
-/
theorem surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar (n : Nat) [NeZero n] :
    Surjective (rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnityAddChar n) := fun ⟨w, hw⟩ => by
  obtain ⟨j, hj1, hj2⟩ := (Complex.mem_rootsOfUnity n w).mp hw
  exact ⟨j, by simp [Units.ext_iff, Subtype.ext_iff, ← hj2, ZMod.toCircle_natCast, mul_div_assoc]⟩

/--
lemma `bijective_rootsOfUnityAddChar` / 引理 `bijective_rootsOfUnityAddChar`

English:
lemma bijective_rootsOfUnityAddChar
  proof: by simp [ZMod.rootsOfUnityAddChar, ZMod.injective_toCircle.eq_iff]
  right := (surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar n).of_comp_left
    (rootsOfUnityCircleEquiv n).injective

中文:
引理 bijective_rootsOfUnityAddChar
  证明: by simp [ZMod.rootsOfUnityAddChar, ZMod.injective_toCircle.eq_iff]
  right := (surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar n).of_comp_left
    (rootsOfUnityCircleEquiv n).injective

Depends on / 依赖: ZMod.injective_toCircle.eq_iff, ZMod.rootsOfUnityAddChar, eq_iff, injective, injective_toCircle, of_comp_left, rootsOfUnityAddChar, rootsOfUnityCircleEquiv, surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar
-/
lemma bijective_rootsOfUnityAddChar :
    Bijective (ZMod.rootsOfUnityAddChar n) where
  left _ _ := by simp [ZMod.rootsOfUnityAddChar, ZMod.injective_toCircle.eq_iff]
  right := (surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar n).of_comp_left
    (rootsOfUnityCircleEquiv n).injective
