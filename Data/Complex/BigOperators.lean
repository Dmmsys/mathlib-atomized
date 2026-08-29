/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Balance
public import Mathlib.Data.Complex.Basic

/-!
# Finite sums and products of complex numbers
-/

public section

open Fintype
open scoped BigOperators

namespace Complex

variable {α : Type*} (s : Finset α)

@[simp, norm_cast]
/--
theorem `ofReal_prod` / 定理 `ofReal_prod`

English:
theorem ofReal_prod
  given: (f : α -> Real)
  statement: ((∏ i in s, f i : Real) : Complex) = ∏ i in s, (f i : Complex)
  proof: map_prod ofRealHom _ _

@[simp, norm_cast]

中文:
定理 ofReal_prod
  条件: (f : α -> 实数)
  结论: ((∏ i in s, f i : 实数) : Complex) = ∏ i in s, (f i : Complex)
  证明: map_prod ofRealHom _ _

@[simp, norm_cast]

Depends on / 依赖: map_prod, ofRealHom
-/
theorem ofReal_prod (f : α -> Real) : ((∏ i in s, f i : Real) : Complex) = ∏ i in s, (f i : Complex) :=
  map_prod ofRealHom _ _

@[simp, norm_cast]
/--
theorem `ofReal_sum` / 定理 `ofReal_sum`

English:
theorem ofReal_sum
  given: (f : α -> Real)
  statement: ((∑ i in s, f i : Real) : Complex) = ∑ i in s, (f i : Complex)
  proof: map_sum ofRealHom _ _

@[simp, norm_cast]

中文:
定理 ofReal_sum
  条件: (f : α -> 实数)
  结论: ((∑ i in s, f i : 实数) : Complex) = ∑ i in s, (f i : Complex)
  证明: map_sum ofRealHom _ _

@[simp, norm_cast]

Depends on / 依赖: map_sum, ofRealHom
-/
theorem ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real) : Complex) = ∑ i in s, (f i : Complex) :=
  map_sum ofRealHom _ _

@[simp, norm_cast]
/--
lemma `ofReal_expect` / 引理 `ofReal_expect`

English:
lemma ofReal_expect
  given: (f : α -> Real)
  statement: (𝔼 i in s, f i : Real) = 𝔼 i in s, (f i : Complex)
  proof: map_expect ofRealHom ..

@[simp, norm_cast]

中文:
引理 ofReal_expect
  条件: (f : α -> 实数)
  结论: (𝔼 i in s, f i : 实数) = 𝔼 i in s, (f i : Complex)
  证明: map_expect ofRealHom ..

@[simp, norm_cast]

Depends on / 依赖: map_expect, ofRealHom
-/
lemma ofReal_expect (f : α -> Real) : (𝔼 i in s, f i : Real) = 𝔼 i in s, (f i : Complex) :=
  map_expect ofRealHom ..

@[simp, norm_cast]
/--
lemma `ofReal_balance` / 引理 `ofReal_balance`

English:
lemma ofReal_balance
  given: [Fintype α] (f : α -> Real) (a : α)
  proof: by simp [balance]

中文:
引理 ofReal_balance
  条件: [Fintype α] (f : α -> 实数) (a : α)
  证明: by simp [balance]

Depends on / 依赖: balance
-/
lemma ofReal_balance [Fintype α] (f : α -> Real) (a : α) :
    ((balance f a : Real) : Complex) = balance ((↑) ∘ f) a := by simp [balance]

/--
lemma `ofReal_comp_balance` / 引理 `ofReal_comp_balance`

English:
lemma ofReal_comp_balance
  given: {ι : Type*} [Fintype ι] (f : ι -> Real)
  proof: funext ofReal_balance _

@[simp]

中文:
引理 ofReal_comp_balance
  条件: {ι : 类型} [Fintype ι] (f : ι -> 实数)
  证明: funext ofReal_balance _

@[simp]
-/
@[simp] lemma ofReal_comp_balance {ι : Type*} [Fintype ι] (f : ι -> Real) :
ofReal ∘ balance f = balance (ofReal ∘ f : ι -> Complex) := funext ofReal_balance _

@[simp]
/--
theorem `re_sum` / 定理 `re_sum`

English:
theorem re_sum
  given: (f : α -> Complex)
  statement: (∑ i in s, f i).re = ∑ i in s, (f i).re
  proof: map_sum reAddGroupHom f s

@[simp]

中文:
定理 re_sum
  条件: (f : α -> Complex)
  结论: (∑ i in s, f i).re = ∑ i in s, (f i).re
  证明: map_sum reAddGroupHom f s

@[simp]

Depends on / 依赖: map_sum, reAddGroupHom
-/
theorem re_sum (f : α -> Complex) : (∑ i in s, f i).re = ∑ i in s, (f i).re :=
  map_sum reAddGroupHom f s

@[simp]
/--
lemma `re_expect` / 引理 `re_expect`

English:
lemma re_expect
  given: (f : α -> Complex)
  statement: (𝔼 i in s, f i).re = 𝔼 i in s, (f i).re
  proof: map_expect (LinearMap.mk reAddGroupHom.toAddHom (by simp)) f s

@[simp]

中文:
引理 re_expect
  条件: (f : α -> Complex)
  结论: (𝔼 i in s, f i).re = 𝔼 i in s, (f i).re
  证明: map_expect (LinearMap.mk reAddGroupHom.toAddHom (by simp)) f s

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mk, map_expect, reAddGroupHom, reAddGroupHom.toAddHom, toAddHom
-/
lemma re_expect (f : α -> Complex) : (𝔼 i in s, f i).re = 𝔼 i in s, (f i).re :=
  map_expect (LinearMap.mk reAddGroupHom.toAddHom (by simp)) f s

@[simp]
/--
lemma `re_balance` / 引理 `re_balance`

English:
lemma re_balance
  given: [Fintype α] (f : α -> Complex) (a : α)
  statement: re (balance f a) = balance (re ∘ f) a
  proof: by
  simp [balance]

中文:
引理 re_balance
  条件: [Fintype α] (f : α -> Complex) (a : α)
  结论: re (balance f a) = balance (re ∘ f) a
  证明: by
  simp [balance]

Depends on / 依赖: balance
-/
lemma re_balance [Fintype α] (f : α -> Complex) (a : α) : re (balance f a) = balance (re ∘ f) a := by
  simp [balance]

/--
lemma `re_comp_balance` / 引理 `re_comp_balance`

English:
lemma re_comp_balance
  given: {ι : Type*} [Fintype ι] (f : ι -> Complex)
  proof: funext re_balance _

@[simp]

中文:
引理 re_comp_balance
  条件: {ι : 类型} [Fintype ι] (f : ι -> Complex)
  证明: funext re_balance _

@[simp]
-/
@[simp] lemma re_comp_balance {ι : Type*} [Fintype ι] (f : ι -> Complex) :
re ∘ balance f = balance (re ∘ f) := funext re_balance _

@[simp]
/--
theorem `im_sum` / 定理 `im_sum`

English:
theorem im_sum
  given: (f : α -> Complex)
  statement: (∑ i in s, f i).im = ∑ i in s, (f i).im
  proof: map_sum imAddGroupHom f s

@[simp]

中文:
定理 im_sum
  条件: (f : α -> Complex)
  结论: (∑ i in s, f i).im = ∑ i in s, (f i).im
  证明: map_sum imAddGroupHom f s

@[simp]

Depends on / 依赖: imAddGroupHom, map_sum
-/
theorem im_sum (f : α -> Complex) : (∑ i in s, f i).im = ∑ i in s, (f i).im :=
  map_sum imAddGroupHom f s

@[simp]
/--
lemma `im_expect` / 引理 `im_expect`

English:
lemma im_expect
  given: (f : α -> Complex)
  statement: (𝔼 i in s, f i).im = 𝔼 i in s, (f i).im
  proof: map_expect (LinearMap.mk imAddGroupHom.toAddHom (by simp)) f s

@[simp]

中文:
引理 im_expect
  条件: (f : α -> Complex)
  结论: (𝔼 i in s, f i).im = 𝔼 i in s, (f i).im
  证明: map_expect (LinearMap.mk imAddGroupHom.toAddHom (by simp)) f s

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mk, imAddGroupHom, imAddGroupHom.toAddHom, map_expect, toAddHom
-/
lemma im_expect (f : α -> Complex) : (𝔼 i in s, f i).im = 𝔼 i in s, (f i).im :=
  map_expect (LinearMap.mk imAddGroupHom.toAddHom (by simp)) f s

@[simp]
/--
lemma `im_balance` / 引理 `im_balance`

English:
lemma im_balance
  given: [Fintype α] (f : α -> Complex) (a : α)
  statement: im (balance f a) = balance (im ∘ f) a
  proof: by
  simp [balance]

中文:
引理 im_balance
  条件: [Fintype α] (f : α -> Complex) (a : α)
  结论: im (balance f a) = balance (im ∘ f) a
  证明: by
  simp [balance]

Depends on / 依赖: balance
-/
lemma im_balance [Fintype α] (f : α -> Complex) (a : α) : im (balance f a) = balance (im ∘ f) a := by
  simp [balance]

/--
lemma `im_comp_balance` / 引理 `im_comp_balance`

English:
lemma im_comp_balance
  given: {ι : Type*} [Fintype ι] (f : ι -> Complex)
  proof: funext im_balance _

中文:
引理 im_comp_balance
  条件: {ι : 类型} [Fintype ι] (f : ι -> Complex)
  证明: funext im_balance _
-/
@[simp] lemma im_comp_balance {ι : Type*} [Fintype ι] (f : ι -> Complex) :
im ∘ balance f = balance (im ∘ f) := funext im_balance _

end Complex
