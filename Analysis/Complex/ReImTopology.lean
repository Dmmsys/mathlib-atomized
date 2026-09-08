/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-!
# Closure, interior, and frontier of preimages under `re` and `im`

In this fact we use the fact that `ℂ` is naturally homeomorphic to `ℝ × ℝ` to deduce some
topological properties of `Complex.re` and `Complex.im`.

## Main statements

Each statement about `Complex.re` listed below has a counterpart about `Complex.im`.

* `Complex.isHomeomorphicTrivialFiberBundle_re`: `Complex.re` turns `ℂ` into a trivial
  topological fiber bundle over `ℝ`;
* `Complex.isOpenMap_re`, `Complex.isQuotientMap_re`: in particular, `Complex.re` is an open map
  and is a quotient map;
* `Complex.interior_preimage_re`, `Complex.closure_preimage_re`, `Complex.frontier_preimage_re`:
  formulas for `interior (Complex.re ⁻¹' s)` etc;
* `Complex.interior_setOfPred_re_le` etc: particular cases of the above formulas in the cases
  when `s` is one of the infinite intervals `Set.Ioi a`, `Set.Ici a`, `Set.Iio a`, and `Set.Iic a`,
  formulated as `interior {z : ℂ | z.re ≤ a} = {z | z.re < a}` etc.

## Tags

complex, real part, imaginary part, closure, interior, frontier
-/

public section

open Set Topology

noncomputable section

namespace Complex

/-- `Complex.re` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
/-
**Complex.isHomeomorphicTrivialFiberBundle_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：isHomeomorphicTrivialFiberBundle_re : IsHomeomorphicTrivialFiberBundle Rea
l re
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Complex.re` turns `ℂ` into a trivial topological fiber bundle over `ℝ`.
-/
theorem isHomeomorphicTrivialFiberBundle_re : IsHomeomorphicTrivialFiberBundle ℝ re :=
  ⟨equivRealProdCLM.toHomeomorph, fun _ => rfl⟩

/-- `Complex.im` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
/-
**Complex.isHomeomorphicTrivialFiberBundle_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：isHomeomorphicTrivialFiberBundle_im : IsHomeomorphicTrivialFiberBundle Rea
l im
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Complex.im` turns `ℂ` into a trivial topological fiber bundle over `ℝ`.
-/
theorem isHomeomorphicTrivialFiberBundle_im : IsHomeomorphicTrivialFiberBundle ℝ im :=
  ⟨equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ), fun _ => rfl⟩
/-
**Complex.isOpenMap_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isOpenMap_re : IsOpenMap re
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorphicTrivialFiberBundle.isOpenMap_proj`：∀ {B : Type u_1} {F : T
ype u_2} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : TopologicalSpace Z] {pr…
· 使用定理 `Complex.isHomeomorphicTrivialFiberBundle_re`：isHomeomorphicTrivialFiberB
undle_re : IsHomeomorphicTrivialFiberBundle Real re
-/
theorem isOpenMap_re : IsOpenMap re :=
  isHomeomorphicTrivialFiberBundle_re.isOpenMap_proj
/-
**Complex.isOpenMap_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isOpenMap_im : IsOpenMap im
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorphicTrivialFiberBundle.isOpenMap_proj`：∀ {B : Type u_1} {F : T
ype u_2} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : TopologicalSpace Z] {pr…
· 使用定理 `Complex.isHomeomorphicTrivialFiberBundle_im`：isHomeomorphicTrivialFiberB
undle_im : IsHomeomorphicTrivialFiberBundle Real im
-/
theorem isOpenMap_im : IsOpenMap im :=
  isHomeomorphicTrivialFiberBundle_im.isOpenMap_proj
/-
**Complex.isQuotientMap_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isQuotientMap_re : IsQuotientMap re
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorphicTrivialFiberBundle.isQuotientMap_proj`：∀ {B : Type u_1} {F
 : Type u_2} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalSpace Z] {pr…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Complex.isHomeomorphicTrivialFiberBundle_re`：isHomeomorphicTrivialFiberB
undle_re : IsHomeomorphicTrivialFiberBundle Real re
-/
theorem isQuotientMap_re : IsQuotientMap re :=
  isHomeomorphicTrivialFiberBundle_re.isQuotientMap_proj
/-
**Complex.isQuotientMap_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isQuotientMap_im : IsQuotientMap im
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorphicTrivialFiberBundle.isQuotientMap_proj`：∀ {B : Type u_1} {F
 : Type u_2} {Z : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalSpace Z] {pr…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Complex.isHomeomorphicTrivialFiberBundle_im`：isHomeomorphicTrivialFiberB
undle_im : IsHomeomorphicTrivialFiberBundle Real im
-/
theorem isQuotientMap_im : IsQuotientMap im :=
  isHomeomorphicTrivialFiberBundle_im.isQuotientMap_proj
/-
**Complex.interior_preimage_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：interior_preimage_re (s : Set Real) : interior (re ⁻¹' s) = re ⁻¹' interio
r s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Complex.isOpenMap_re`：isOpenMap_re : IsOpenMap re
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
-/
theorem interior_preimage_re (s : Set ℝ) : interior (re ⁻¹' s) = re ⁻¹' interior s :=
  (isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re _).symm
/-
**Complex.interior_preimage_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：interior_preimage_im (s : Set Real) : interior (im ⁻¹' s) = im ⁻¹' interio
r s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Complex.isOpenMap_im`：isOpenMap_im : IsOpenMap im
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
theorem interior_preimage_im (s : Set ℝ) : interior (im ⁻¹' s) = im ⁻¹' interior s :=
  (isOpenMap_im.preimage_interior_eq_interior_preimage continuous_im _).symm
/-
**Complex.closure_preimage_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：closure_preimage_re (s : Set Real) : closure (re ⁻¹' s) = re ⁻¹' closure s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Complex.isOpenMap_re`：isOpenMap_re : IsOpenMap re
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
-/
theorem closure_preimage_re (s : Set ℝ) : closure (re ⁻¹' s) = re ⁻¹' closure s :=
  (isOpenMap_re.preimage_closure_eq_closure_preimage continuous_re _).symm
/-
**Complex.closure_preimage_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：closure_preimage_im (s : Set Real) : closure (im ⁻¹' s) = im ⁻¹' closure s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Complex.isOpenMap_im`：isOpenMap_im : IsOpenMap im
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
theorem closure_preimage_im (s : Set ℝ) : closure (im ⁻¹' s) = im ⁻¹' closure s :=
  (isOpenMap_im.preimage_closure_eq_closure_preimage continuous_im _).symm
/-
**Complex.frontier_preimage_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_preimage_re (s : Set Real) : frontier (re ⁻¹' s) = re ⁻¹' frontie
r s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_frontier_eq_frontier_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Complex.isOpenMap_re`：isOpenMap_re : IsOpenMap re
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
-/
theorem frontier_preimage_re (s : Set ℝ) : frontier (re ⁻¹' s) = re ⁻¹' frontier s :=
  (isOpenMap_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm
/-
**Complex.frontier_preimage_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_preimage_im (s : Set Real) : frontier (im ⁻¹' s) = im ⁻¹' frontie
r s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_frontier_eq_frontier_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Complex.isOpenMap_im`：isOpenMap_im : IsOpenMap im
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
theorem frontier_preimage_im (s : Set ℝ) : frontier (im ⁻¹' s) = im ⁻¹' frontier s :=
  (isOpenMap_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm

@[simp]
/-
**Complex.interior_setOfPred_re_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：interior_setOfPred_re_le (a : Real) : interior { z : Complex | z.re <= a }
 = { z | z.re < a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic`：interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = I
io a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.interior_preimage_re`：interior_preimage_re (s : Set Real) : inte
rior (re ⁻¹' s) = re ⁻¹' interior s
-/
theorem interior_setOfPred_re_le (a : ℝ) : interior { z : ℂ | z.re ≤ a } = { z | z.re < a } := by
  simpa only [interior_Iic] using! interior_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_re_le := interior_setOfPred_re_le

@[simp]
/-
**Complex.interior_setOfPred_im_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：interior_setOfPred_im_le (a : Real) : interior { z : Complex | z.im <= a }
 = { z | z.im < a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic`：interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = I
io a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.interior_preimage_im`：interior_preimage_im (s : Set Real) : inte
rior (im ⁻¹' s) = im ⁻¹' interior s
-/
theorem interior_setOfPred_im_le (a : ℝ) : interior { z : ℂ | z.im ≤ a } = { z | z.im < a } := by
  simpa only [interior_Iic] using! interior_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_im_le := interior_setOfPred_im_le

@[simp]
/-
**Complex.interior_setOfPred_le_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：interior_setOfPred_le_re (a : Real) : interior { z : Complex | a <= z.re }
 = { z | a < z.re }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.interior_preimage_re`：interior_preimage_re (s : Set Real) : inte
rior (re ⁻¹' s) = re ⁻¹' interior s
-/
theorem interior_setOfPred_le_re (a : ℝ) : interior { z : ℂ | a ≤ z.re } = { z | a < z.re } := by
  simpa only [interior_Ici] using! interior_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_re := interior_setOfPred_le_re

@[simp]
/-
**Complex.interior_setOfPred_le_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：interior_setOfPred_le_im (a : Real) : interior { z : Complex | a <= z.im }
 = { z | a < z.im }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.interior_preimage_im`：interior_preimage_im (s : Set Real) : inte
rior (im ⁻¹' s) = im ⁻¹' interior s
-/
theorem interior_setOfPred_le_im (a : ℝ) : interior { z : ℂ | a ≤ z.im } = { z | a < z.im } := by
  simpa only [interior_Ici] using! interior_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_im := interior_setOfPred_le_im

@[simp]
/-
**Complex.closure_setOfPred_re_lt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：closure_setOfPred_re_lt (a : Real) : closure { z : Complex | z.re < a } = 
{ z | z.re <= a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Iio`：closure_Iio (a : α) [NoMinOrder α] : closure (Iio a) = Iic 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.closure_preimage_re`：closure_preimage_re (s : Set Real) : closur
e (re ⁻¹' s) = re ⁻¹' closure s
-/
theorem closure_setOfPred_re_lt (a : ℝ) : closure { z : ℂ | z.re < a } = { z | z.re ≤ a } := by
  simpa only [closure_Iio] using! closure_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_re_lt := closure_setOfPred_re_lt

@[simp]
/-
**Complex.closure_setOfPred_im_lt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：closure_setOfPred_im_lt (a : Real) : closure { z : Complex | z.im < a } = 
{ z | z.im <= a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Iio`：closure_Iio (a : α) [NoMinOrder α] : closure (Iio a) = Iic 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.closure_preimage_im`：closure_preimage_im (s : Set Real) : closur
e (im ⁻¹' s) = im ⁻¹' closure s
-/
theorem closure_setOfPred_im_lt (a : ℝ) : closure { z : ℂ | z.im < a } = { z | z.im ≤ a } := by
  simpa only [closure_Iio] using! closure_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_im_lt := closure_setOfPred_im_lt

@[simp]
/-
**Complex.closure_setOfPred_lt_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：closure_setOfPred_lt_re (a : Real) : closure { z : Complex | a < z.re } = 
{ z | a <= z.re }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioi`：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.closure_preimage_re`：closure_preimage_re (s : Set Real) : closur
e (re ⁻¹' s) = re ⁻¹' closure s
-/
theorem closure_setOfPred_lt_re (a : ℝ) : closure { z : ℂ | a < z.re } = { z | a ≤ z.re } := by
  simpa only [closure_Ioi] using! closure_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_lt_re := closure_setOfPred_lt_re

@[simp]
/-
**Complex.closure_setOfPred_lt_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：closure_setOfPred_lt_im (a : Real) : closure { z : Complex | a < z.im } = 
{ z | a <= z.im }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioi`：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.closure_preimage_im`：closure_preimage_im (s : Set Real) : closur
e (im ⁻¹' s) = im ⁻¹' closure s
-/
theorem closure_setOfPred_lt_im (a : ℝ) : closure { z : ℂ | a < z.im } = { z | a ≤ z.im } := by
  simpa only [closure_Ioi] using! closure_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_lt_im := closure_setOfPred_lt_im

@[simp]
/-
**Complex.frontier_setOfPred_re_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_re_le (a : Real) : frontier { z : Complex | z.re <= a }
 = { z | z.re = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Iic`：frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.frontier_preimage_re`：frontier_preimage_re (s : Set Real) : fron
tier (re ⁻¹' s) = re ⁻¹' frontier s
-/
theorem frontier_setOfPred_re_le (a : ℝ) : frontier { z : ℂ | z.re ≤ a } = { z | z.re = a } := by
  simpa only [frontier_Iic] using! frontier_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_le := frontier_setOfPred_re_le

@[simp]
/-
**Complex.frontier_setOfPred_im_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_im_le (a : Real) : frontier { z : Complex | z.im <= a }
 = { z | z.im = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Iic`：frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.frontier_preimage_im`：frontier_preimage_im (s : Set Real) : fron
tier (im ⁻¹' s) = im ⁻¹' frontier s
-/
theorem frontier_setOfPred_im_le (a : ℝ) : frontier { z : ℂ | z.im ≤ a } = { z | z.im = a } := by
  simpa only [frontier_Iic] using! frontier_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_le := frontier_setOfPred_im_le

@[simp]
/-
**Complex.frontier_setOfPred_le_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_le_re (a : Real) : frontier { z : Complex | a <= z.re }
 = { z | z.re = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Ici`：frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.frontier_preimage_re`：frontier_preimage_re (s : Set Real) : fron
tier (re ⁻¹' s) = re ⁻¹' frontier s
-/
theorem frontier_setOfPred_le_re (a : ℝ) : frontier { z : ℂ | a ≤ z.re } = { z | z.re = a } := by
  simpa only [frontier_Ici] using! frontier_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re := frontier_setOfPred_le_re

@[simp]
/-
**Complex.frontier_setOfPred_le_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_le_im (a : Real) : frontier { z : Complex | a <= z.im }
 = { z | z.im = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Ici`：frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.frontier_preimage_im`：frontier_preimage_im (s : Set Real) : fron
tier (im ⁻¹' s) = im ⁻¹' frontier s
-/
theorem frontier_setOfPred_le_im (a : ℝ) : frontier { z : ℂ | a ≤ z.im } = { z | z.im = a } := by
  simpa only [frontier_Ici] using! frontier_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_im := frontier_setOfPred_le_im

@[simp]
/-
**Complex.frontier_setOfPred_re_lt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_re_lt (a : Real) : frontier { z : Complex | z.re < a } 
= { z | z.re = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Iio`：frontier_Iio [NoMinOrder α] {a : α} : frontier (Iio a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.frontier_preimage_re`：frontier_preimage_re (s : Set Real) : fron
tier (re ⁻¹' s) = re ⁻¹' frontier s
-/
theorem frontier_setOfPred_re_lt (a : ℝ) : frontier { z : ℂ | z.re < a } = { z | z.re = a } := by
  simpa only [frontier_Iio] using! frontier_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_lt := frontier_setOfPred_re_lt

@[simp]
/-
**Complex.frontier_setOfPred_im_lt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_im_lt (a : Real) : frontier { z : Complex | z.im < a } 
= { z | z.im = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Iio`：frontier_Iio [NoMinOrder α] {a : α} : frontier (Iio a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.frontier_preimage_im`：frontier_preimage_im (s : Set Real) : fron
tier (im ⁻¹' s) = im ⁻¹' frontier s
-/
theorem frontier_setOfPred_im_lt (a : ℝ) : frontier { z : ℂ | z.im < a } = { z | z.im = a } := by
  simpa only [frontier_Iio] using! frontier_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_lt := frontier_setOfPred_im_lt

@[simp]
/-
**Complex.frontier_setOfPred_lt_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_lt_re (a : Real) : frontier { z : Complex | a < z.re } 
= { z | z.re = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Ioi`：frontier_Ioi [NoMaxOrder α] {a : α} : frontier (Ioi a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.frontier_preimage_re`：frontier_preimage_re (s : Set Real) : fron
tier (re ⁻¹' s) = re ⁻¹' frontier s
-/
theorem frontier_setOfPred_lt_re (a : ℝ) : frontier { z : ℂ | a < z.re } = { z | z.re = a } := by
  simpa only [frontier_Ioi] using! frontier_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_re := frontier_setOfPred_lt_re

@[simp]
/-
**Complex.frontier_setOfPred_lt_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_setOfPred_lt_im (a : Real) : frontier { z : Complex | a < z.im } 
= { z | z.im = a }
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Ioi`：frontier_Ioi [NoMaxOrder α] {a : α} : frontier (Ioi a) = {
a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.frontier_preimage_im`：frontier_preimage_im (s : Set Real) : fron
tier (im ⁻¹' s) = im ⁻¹' frontier s
-/
theorem frontier_setOfPred_lt_im (a : ℝ) : frontier { z : ℂ | a < z.im } = { z | z.im = a } := by
  simpa only [frontier_Ioi] using! frontier_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_im := frontier_setOfPred_lt_im
/-
**Complex.closure_reProdIm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：closure_reProdIm (s t : Set Real) : closure (s ×Complex t) = closure s ×Co
mplex closure t
参数：s t : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_eq_preimage`：preimage_eq_preimage {f : β -> α} (hf : Surjec
tive f) : f ⁻¹' s = f ⁻¹' t ↔ s = t
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.preimage_closure`：preimage_closure (h : X ≃ₜ Y) (s : Set Y) :
 h ⁻¹' closure s = closure (h ⁻¹' s)
· 使用定理 `closure_prod_eq`：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ
 t) = closure s ×ˢ closure t
-/
theorem closure_reProdIm (s t : Set ℝ) : closure (s ×ℂ t) = closure s ×ℂ closure t := by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_closure] using! @closure_prod_eq _ _ _ _ s t
/-
**Complex.interior_reProdIm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：interior_reProdIm (s t : Set Real) : interior (s ×Complex t) = interior s 
×Complex interior t
参数：s t : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.reProdIm.eq_1`：∀ (s t : Set ℝ), s ×ℂ t = Complex.re ⁻¹' s ∩ Comp
lex.im ⁻¹' t
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `Complex.interior_preimage_re`：interior_preimage_re (s : Set Real) : inte
rior (re ⁻¹' s) = re ⁻¹' interior s
· 使用定理 `Complex.interior_preimage_im`：interior_preimage_im (s : Set Real) : inte
rior (im ⁻¹' s) = im ⁻¹' interior s
-/
theorem interior_reProdIm (s t : Set ℝ) : interior (s ×ℂ t) = interior s ×ℂ interior t := by
  rw [reProdIm, reProdIm, interior_inter, interior_preimage_re, interior_preimage_im]
/-
**Complex.frontier_reProdIm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：frontier_reProdIm (s t : Set Real) : frontier (s ×Complex t) = closure s ×
Complex frontier t union frontier s ×Complex closure t
参数：s t : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_eq_preimage`：preimage_eq_preimage {f : β -> α} (hf : Surjec
tive f) : f ⁻¹' s = f ⁻¹' t ↔ s = t
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.preimage_frontier`：preimage_frontier (h : X ≃ₜ Y) (s : Set Y)
 : h ⁻¹' frontier s = frontier (h ⁻¹' s)
· 使用定理 `frontier_prod_eq`：frontier_prod_eq (s : Set X) (t : Set Y) : frontier (s
 ×ˢ t) = closure s ×ˢ frontier t union frontier s ×ˢ closure t
-/
theorem frontier_reProdIm (s t : Set ℝ) :
    frontier (s ×ℂ t) = closure s ×ℂ frontier t ∪ frontier s ×ℂ closure t := by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_frontier] using! frontier_prod_eq s t
/-
**Complex.frontier_setOfPred_le_re_and_le_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：frontier_setOfPred_le_re_and_le_im (a b : Real) : frontier { z | a <= re z
 ∧ b <= im z } = { z | a <= re z ∧ im z = b ∨ re z = a ∧ b <= im z }
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `closure_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preord
er α] [ClosedIciTopology α] (a : α),   closure (Set.Ici a) = Set.Ici a
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `frontier_Ici`：frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {
a}
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Complex.frontier_reProdIm`：frontier_reProdIm (s t : Set Real) : frontier
 (s ×Complex t) = closure s ×Complex frontier t union frontier s ×Complex closur
e t
-/
theorem frontier_setOfPred_le_re_and_le_im (a b : ℝ) :
    frontier { z | a ≤ re z ∧ b ≤ im z } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ b ≤ im z } := by
  simpa only [closure_Ici, frontier_Ici] using! frontier_reProdIm (Ici a) (Ici b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_le_im := frontier_setOfPred_le_re_and_le_im
/-
**Complex.frontier_setOfPred_le_re_and_im_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：frontier_setOfPred_le_re_and_im_le (a b : Real) : frontier { z | a <= re z
 ∧ im z <= b } = { z | a <= re z ∧ im z = b ∨ re z = a ∧ im z <= b }
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `closure_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preord
er α] [ClosedIciTopology α] (a : α),   closure (Set.Ici a) = Set.Ici a
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `frontier_Iic`：frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {
a}
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `frontier_Ici`：frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {
a}
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `closure_Iic`：closure_Iic (a : α) : closure (Iic a) = Iic a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Complex.frontier_reProdIm`：frontier_reProdIm (s t : Set Real) : frontier
 (s ×Complex t) = closure s ×Complex frontier t union frontier s ×Complex closur
e t
-/
theorem frontier_setOfPred_le_re_and_im_le (a b : ℝ) :
    frontier { z | a ≤ re z ∧ im z ≤ b } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ im z ≤ b } := by
  simpa only [closure_Ici, closure_Iic, frontier_Ici, frontier_Iic] using!
    frontier_reProdIm (Ici a) (Iic b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_im_le := frontier_setOfPred_le_re_and_im_le

end Complex

open Complex Metric

variable {s t : Set ℝ}

/-
**IsOpen.reProdIm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.reProdIm (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×Complex t)
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
theorem IsOpen.reProdIm (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ℂ t) :=
  (hs.preimage continuous_re).inter (ht.preimage continuous_im)
/-
**IsClosed.reProdIm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.reProdIm (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ×Compl
ex t)
参数：hs : IsClosed s；ht : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
theorem IsClosed.reProdIm (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ×ℂ t) :=
  (hs.preimage continuous_re).inter (ht.preimage continuous_im)
/-
**Bornology.IsBounded.reProdIm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.reProdIm (hs : IsBounded s) (ht : IsBounded t) : IsBou
nded (s ×Complex t)
参数：hs : IsBounded s；ht : IsBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isBounded_preimage`：isBounded_preimage (hf : Antilipsc
hitzWith K f) {s : Set β} (hs : IsBounded s) : IsBounded (f ⁻¹' s)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.antilipschitz_equivRealProd`：AntilipschitzWith (NNReal.sqrt 2) ⇑
Complex.equivRealProd
· 使用定理 `Bornology.IsBounded.prod`：∀ {α : Type u_1} {β : Type u_2} [inst : Bornol
ogy α] [inst_1 : Bornology β] {s : Set α} {t : Set β},   Bornology.IsBounded s →
 Bornology.IsB…
-/
theorem Bornology.IsBounded.reProdIm (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ℂ t) :=
  antilipschitz_equivRealProd.isBounded_preimage (hs.prod ht)

section continuity

variable {α ι : Type*}

/-
**TendstoUniformlyOn.re** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformlyOn`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ}
 {K : Set α},   TendstoUniformlyOn f g p K → TendstoUniformlyOn (fun n x => (f n
 x).re) (fun y => (g y).re) p K
参数：fun n x => (f n x).re；fun y => (g y).re。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoUniformlyOn`：UniformContinuous.comp_tendst
oUniformlyOn [UniformSpace γ] {g : β -> γ} (hg : UniformContinuous g) (h : Tends
toUniformlyOn F f p s) : Tendst…
· 使用定理 `Complex.uniformContinuous_re`：UniformContinuous Complex.re
-/
protected lemma TendstoUniformlyOn.re {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ} {K : Set α}
    (hf : TendstoUniformlyOn f g p K) :
    TendstoUniformlyOn (fun n x => (f n x).re) (fun y => (g y).re) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_re hf
/-
**TendstoUniformly.re** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformly`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ}
,   TendstoUniformly f g p → TendstoUniformly (fun n x => (f n x).re) (fun y => 
(g y).re) p
参数：fun n x => (f n x).re；fun y => (g y).re。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoUniformly`：UniformContinuous.comp_tendstoU
niformly [UniformSpace γ] {g : β -> γ} (hg : UniformContinuous g) (h : TendstoUn
iformly F f p) : TendstoUnifo…
· 使用定理 `Complex.uniformContinuous_re`：UniformContinuous Complex.re
-/
protected lemma TendstoUniformly.re {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ}
    (hf : TendstoUniformly f g p) :
    TendstoUniformly (fun n x => (f n x).re) (fun y => (g y).re) p := by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_re hf
/-
**TendstoUniformlyOn.im** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformlyOn`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ}
 {K : Set α},   TendstoUniformlyOn f g p K → TendstoUniformlyOn (fun n x => (f n
 x).im) (fun y => (g y).im) p K
参数：fun n x => (f n x).im；fun y => (g y).im。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoUniformlyOn`：UniformContinuous.comp_tendst
oUniformlyOn [UniformSpace γ] {g : β -> γ} (hg : UniformContinuous g) (h : Tends
toUniformlyOn F f p s) : Tendst…
· 使用定理 `Complex.uniformContinuous_im`：UniformContinuous Complex.im
-/
protected lemma TendstoUniformlyOn.im {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ} {K : Set α}
    (hf : TendstoUniformlyOn f g p K) :
    TendstoUniformlyOn (fun n x => (f n x).im) (fun y => (g y).im) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_im hf
/-
**TendstoUniformly.im** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformly`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ}
,   TendstoUniformly f g p → TendstoUniformly (fun n x => (f n x).im) (fun y => 
(g y).im) p
参数：fun n x => (f n x).im；fun y => (g y).im。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoUniformly`：UniformContinuous.comp_tendstoU
niformly [UniformSpace γ] {g : β -> γ} (hg : UniformContinuous g) (h : TendstoUn
iformly F f p) : TendstoUnifo…
· 使用定理 `Complex.uniformContinuous_im`：UniformContinuous Complex.im
-/
protected lemma TendstoUniformly.im {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ}
    (hf : TendstoUniformly f g p) :
    TendstoUniformly (fun n x => (f n x).im) (fun y => (g y).im) p := by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_im hf

end continuity

