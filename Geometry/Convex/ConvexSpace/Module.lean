/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Star
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Modules are convex spaces

This file shows that every module over ordered coefficients is a convex space.

## Main declarations

* `ConvexSpace.ofModule`: A semimodule space over a semiring is a convex space.
* `convexSpaceSelf`: A semiring is a convex space over itself.
* `IsModuleConvexSpace`: Predicate for a convex space and module structures to be compatible.
-/

open scoped Pointwise

public noncomputable section

namespace Convexity
variable {F R M N I : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

section AddCommMonoid
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [SetLike F M]
  [AddSubmonoidClass F M] [SMulMemClass F R M] {f g : M → N}

/-- Any semimodule over an ordered semiring is a convex space.

This is not an instance because it creates a diamond with structural instances such as
`ConvexSpace R X → ConvexSpace R Y → ConvexSpace R (X × Y)` because
`(∑ i, f i).fst = ∑ i, (f i).fst` isn't defeq, ultimately because `Finset.sum` isn't a field of
`AddCommMonoid` but derived from them through recursion. -/
@[expose, implicit_reducible]
/-
**Convexity.ConvexSpace.ofModule** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.ConvexSpac
e`。
形式化陈述：{R : Type u_2} →   {M : Type u_3} →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : IsStrictOrderedRing R] → [inst_3 : AddCo
mmMonoid M] → [_root_.Module R M] → Convexity.ConvexSpace R M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any semimodule over an ordered semiring is a convex space.

This is not an instance because it creates a diamond with structural instances s
uch as
`ConvexSpace R X → ConvexSpace R Y → ConvexSpace R (X × Y)` because
`(∑ i, f i).fst = ∑ i, (f i).fst` isn't defeq, ultimately because `Finset.sum` i
sn't a field of
`AddCommMonoid` but derived from them through recursion.
-/
def ConvexSpace.ofModule : ConvexSpace R M where
  sConvexComb w := w.weights.sum fun m r ↦ r • m
  sConvexComb_single := by simp
  assoc := by
    simp [Finsupp.sum_mapDomain_index, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      mul_smul, Finsupp.smul_sum]
/-
**Convexity.convexSpaceSelf** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
形式化陈述：convexSpaceSelf : ConvexSpace R R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance convexSpaceSelf : ConvexSpace R R := .ofModule

variable (R M) [ConvexSpace R M] in
/-- Typeclass for a convex space structure on a module to be given by weighted sums. -/
/-
**Convexity.IsModuleConvexSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `Convexity`。
形式化陈述：(R : Type u_2) →   (M : Type u_3) →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : IsStrictOrderedRing R] →           [inst
_3 : AddCommMonoid M] → [_root_.Module R M] → [Convexity.ConvexSpace R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a convex space structure on a module to be given by weighted sums.
-/
class IsModuleConvexSpace : Prop where
  sConvexComb_eq_sum (w : StdSimplex R M) : w.sConvexComb = w.weights.sum fun m r ↦ r • m

export IsModuleConvexSpace (sConvexComb_eq_sum)
attribute [simp] sConvexComb_eq_sum

@[deprecated (since := "2026-04-03")]
alias _root_.convexCombination_eq_sum := sConvexComb_eq_sum

attribute [local instance] ConvexSpace.ofModule in
/-
**Convexity.IsModuleConvexSpace.ofModule** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.Is
ModuleConvexSpace`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : AddCommMonoid M] [inst_4 : _roo
t_.Module R M], Convexity.IsModuleConvexSpace R M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsModuleConvexSpace.ofModule : IsModuleConvexSpace R M where
  sConvexComb_eq_sum _ := rfl
/-
**Convexity.isModuleConvexSpace_self** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
形式化陈述：isModuleConvexSpace_self : IsModuleConvexSpace R R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsModuleConvexSpace.ofModule`：∀ {R : Type u_2} {M : Type u_3} 
[inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]  
 [inst_3 : AddCommMonoid M] …
-/
instance isModuleConvexSpace_self : IsModuleConvexSpace R R := .ofModule

section IsModuleConvexSpace
variable [ConvexSpace R M] [IsModuleConvexSpace R M] [ConvexSpace R N] [IsModuleConvexSpace R N]
  {x y : M} {s t : Set M} {a b : R}

/-- `iConvexComb` in a module can be expressed as a sum. -/
@[simp]
/-
**Convexity.iConvexComb_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_eq_sum (w : StdSimplex R I) (f : I -> M) : w.iConvexComb f = w
.weights.sum fun i r => r • f i
参数：w : StdSimplex R I；f : I -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsModuleConvexSpace.sConvexComb_eq_sum`：∀ {R : Type u_2} {M : 
Type u_3} {inst : Semiring R} {inst_1 : PartialOrder R} {inst_2 : IsStrictOrdere
dRing R}   {inst_3 : AddCommMonoid M} …
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x

--- 原说明 ---
`iConvexComb` in a module can be expressed as a sum.
-/
lemma iConvexComb_eq_sum (w : StdSimplex R I) (f : I → M) :
    w.iConvexComb f = w.weights.sum fun i r ↦ r • f i := by
  simp [iConvexComb, sConvexComb_eq_sum, Finsupp.sum_mapDomain_index, add_smul]

/-- `convexCombPair` in a module can be expressed as a sum. -/
@[simp]
/-
**Convexity.convexCombPair_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_eq_sum (a b : R) (ha hb hab) (x y : M) : convexCombPair a b
 ha hb hab x y = a • x + b • y
参数：a b : R；ha hb hab；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsModuleConvexSpace.sConvexComb_eq_sum`：∀ {R : Type u_2} {M : 
Type u_3} {inst : Semiring R} {inst_1 : PartialOrder R} {inst_2 : IsStrictOrdere
dRing R}   {inst_3 : AddCommMonoid M} …
· 使用定理 `Convexity.StdSimplex.weights_duple`：∀ {R : Type u} [inst : PartialOrder 
R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x y : 
M)   {s t : R} (hs : 0 ≤…
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…

--- 原说明 ---
`convexCombPair` in a module can be expressed as a sum.
-/
lemma convexCombPair_eq_sum (a b : R) (ha hb hab) (x y : M) :
    convexCombPair a b ha hb hab x y = a • x + b • y := by
  classical simp [convexCombPair, sConvexComb_eq_sum, Finsupp.sum_add_index, add_smul]
/-
**Convexity.IsAffineMap.map_sum_weights** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsA
ffineMap`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4} {I : Type u_5} [inst : Semi
ring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : A
ddCommMonoid M] [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid N]   [inst_
6 : _root_.Module R N] {f : M → N} [inst_7 : Convexity.ConvexSpace R M] [Convexi
ty.IsModuleConvexSpace R M]   [inst_9 : Convexity.ConvexSpace R N] [Convexity.Is
ModuleConvexSpace R N],   Convexity.IsAffineMap R f →     ∀ (w : Convexity.StdSi
mplex R I) (g : I → M),       f (w.weights.sum fun i r => r • g i) = w.weights.s
um fun i r => r • f (g i)
参数：w : Convexity.StdSimplex R I；g : I → M；w.weights.sum fun i r => r • g i；g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.IsAffineMap.map_iConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [in
st_2 : IsStrictOrderedRing …
-/
lemma IsAffineMap.map_sum_weights (hf : IsAffineMap R f) (w : StdSimplex R I) (g : I → M) :
    f (w.weights.sum fun i r ↦ r • g i) = w.weights.sum fun i r ↦ r • f (g i) := by
  simpa using hf.map_iConvexComb w g
/-
**Convexity.IsAffineMap.map_smul_add_smul** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.I
sAffineMap`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommMonoid M]
 [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Modu
le R N] {f : M → N} [inst_7 : Convexity.ConvexSpace R M] [Convexity.IsModuleConv
exSpace R M]   [inst_9 : Convexity.ConvexSpace R N] [Convexity.IsModuleConvexSpa
ce R N] {a b : R},   Convexity.IsAffineMap R f → 0 ≤ a → 0 ≤ b → a + b = 1 → ∀ (
x y : M), f (a • x + b • y) = a • f x + b • f y
参数：x y : M；a • x + b • y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.convexCombPair_eq_sum`：convexCombPair_eq_sum (a b : R) (ha hb 
hab) (x y : M) : convexCombPair a b ha hb hab x y = a • x + b • y
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
-/
lemma IsAffineMap.map_smul_add_smul (hf : IsAffineMap R f) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (x y : M) : f (a • x + b • y) = a • f x + b • f y := by
  simpa using hf.map_convexCombPair ha hb hab x y
/-
**Convexity.isConvexSet_coe** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {F : Type u_1} {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommMonoid M]
 [inst_4 : _root_.Module R M] [inst_5 : SetLike F M]   [AddSubmonoidClass F M] [
SMulMemClass F R M] [inst_8 : Convexity.ConvexSpace R M] [Convexity.IsModuleConv
exSpace R M]   (S : F), Convexity.IsConvexSet R ↑S
参数：S : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.of_sConvexComb_mem`：∀ {R : Type u_3} {X : Type u_5
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]
   [inst_3 : Convexity.ConvexS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsModuleConvexSpace.sConvexComb_eq_sum`：∀ {R : Type u_2} {M : 
Type u_3} {inst : Semiring R} {inst_1 : PartialOrder R} {inst_2 : IsStrictOrdere
dRing R}   {inst_3 : AddCommMonoid M} …
· 使用定理 `AddSubmonoidClass.finsuppSum_mem`：∀ {α : Type u_1} {M : Type u_8} {N : T
ype u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {S : Type u_16}   [inst_2 :
 SetLike S N] [AddSubm…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma isConvexSet_coe (S : F) : IsConvexSet R (S : Set M) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  rw [sConvexComb_eq_sum]
  exact AddSubmonoidClass.finsuppSum_mem _ _ _ fun m hm ↦ SMulMemClass.smul_mem _ <| hw <| by simpa
/-
**Convexity.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : F) : ConvexSpace R S := .subtype _ <| isConvexSet_coe _

@[simp]
/-
**Convexity.subtypeVal_submodule_sConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Convexit
y`。
形式化陈述：subtypeVal_submodule_sConvexComb (S : F) (w : StdSimplex R S) : (w.sConvex
Comb : M) = w.iConvexComb (↑)
参数：S : F；w : StdSimplex R S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_submodule_sConvexComb (S : F) (w : StdSimplex R S) :
    (w.sConvexComb : M) = w.iConvexComb (↑) := rfl
/-
**Convexity.subtypeVal_submodule_iConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Convexit
y`。
形式化陈述：subtypeVal_submodule_iConvexComb (S : F) (w : StdSimplex R I) (f : I -> S)
 : (↑(w.iConvexComb f) : M) = w.iConvexComb (fun i => (f i).val)
参数：S : F；w : StdSimplex R I；f : I -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Convexity.subtypeVal_iConvexComb`：subtypeVal_iConvexComb (s : Set X) (hs
 : IsConvexSet R s) (w : StdSimplex R I) (f : I -> s) : letI : ConvexSpace R s
· 使用定理 `Convexity.isConvexSet_coe`：∀ {F : Type u_1} {R : Type u_2} {M : Type u_3
} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : Ad…
-/
lemma subtypeVal_submodule_iConvexComb (S : F) (w : StdSimplex R I) (f : I → S) :
    (↑(w.iConvexComb f) : M) = w.iConvexComb (fun i ↦ (f i).val) := subtypeVal_iConvexComb ..
/-
**Convexity.subtypeVal_submodule_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Conve
xity`。
形式化陈述：subtypeVal_submodule_convexCombPair (S : F) (a b : R) (ha hb hab) (x y : S
) : (↑(convexCombPair a b ha hb hab x y) : M) = convexCombPair a b ha hb hab x.v
al y.val
参数：S : F；a b : R；ha hb hab；x y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Convexity.subtypeVal_convexCombPair`：subtypeVal_convexCombPair (s : Set 
X) (hs : IsConvexSet R s) (a b : R) (ha hb hab) (x y : s) : letI : ConvexSpace R
 s
· 使用定理 `Convexity.isConvexSet_coe`：∀ {F : Type u_1} {R : Type u_2} {M : Type u_3
} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : Ad…
-/
lemma subtypeVal_submodule_convexCombPair (S : F) (a b : R) (ha hb hab) (x y : S) :
    (↑(convexCombPair a b ha hb hab x y) : M) = convexCombPair a b ha hb hab x.val y.val :=
  subtypeVal_convexCombPair ..
/-
**Convexity.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : F) : IsModuleConvexSpace R S where sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]
/-
**Convexity.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsModuleConvexSpace R (M × N) where
  sConvexComb_eq_sum w := by ext <;> simp [Finsupp.sum, Prod.fst_sum, Prod.snd_sum]
/-
**Convexity.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, ConvexSpace R (M i)] [∀ i, IsModuleConvexSpace R (M i)] :
    IsModuleConvexSpace R (∀ i, M i) where
  sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]
/-
**Convexity.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} : IsModuleConvexSpace R (ι →₀ M) where
  sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]

@[to_fun (attr := fun_prop)]
/-
**Convexity.IsAffineMap.add** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsAffineMap`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommMonoid M]
 [inst_4 : _root_.Module R M] [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Modu
le R N] {f g : M → N} [inst_7 : Convexity.ConvexSpace R M] [Convexity.IsModuleCo
nvexSpace R M]   [inst_9 : Convexity.ConvexSpace R N] [Convexity.IsModuleConvexS
pace R N],   Convexity.IsAffineMap R f → Convexity.IsAffineMap R g → Convexity.I
sAffineMap R (f + g)
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsModuleConvexSpace.sConvexComb_eq_sum`：∀ {R : Type u_2} {M : 
Type u_3} {inst : Semiring R} {inst_1 : PartialOrder R} {inst_2 : IsStrictOrdere
dRing R}   {inst_3 : AddCommMonoid M} …
· 使用定理 `Convexity.IsAffineMap.map_sum_weights`：∀ {R : Type u_2} {M : Type u_3} {
N : Type u_4} {I : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder R]   [in
st_2 : IsStrictOrderedRing …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finsupp.sum_add`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst :
 Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {h₁ h₂ : α → M → N}, (f.sum f
un a …
-/
lemma IsAffineMap.add (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (f + g) where
  map_sConvexComb w := by
    simp [hf.map_sum_weights, hg.map_sum_weights, Finsupp.sum_mapDomain_index, add_smul]
/-
**Convexity.IsStarConvexSet.add** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarConve
xSet`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : AddCommMonoid M] [inst_4 : _roo
t_.Module R M] [inst_5 : Convexity.ConvexSpace R M]   [Convexity.IsModuleConvexS
pace R M] {x y : M} {s t : Set M},   Convexity.IsStarConvexSet R x s → Convexity
.IsStarConvexSet R y t → Convexity.IsStarConvexSet R (x + y) (s + t)
参数：x + y；s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.add_image_prod`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, (fun 
x => x.1 + x.2) '' s ×ˢ t = s + t
· 使用定理 `Convexity.IsStarConvexSet.image`：∀ {R : Type u_1} {X : Type u_2} {Y : Ty
pe u_3} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrdere
dRing R] [inst_3 : Co…
· 使用定理 `Convexity.IsAffineMap.fun_add`：∀ {R : Type u_2} {M : Type u_3} {N : Type
 u_4} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `Convexity.instIsModuleConvexSpaceProd`：∀ {R : Type u_2} {M : Type u_3} {
N : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Ad…
· 使用引理 `Prod.isAffineMap_fst`：isAffineMap_fst : IsAffineMap R (fst : X × Y -> X)
 where map_sConvexComb
· 使用引理 `Prod.isAffineMap_snd`：isAffineMap_snd : IsAffineMap R (snd : X × Y -> Y)
 where map_sConvexComb
· 使用定理 `Convexity.IsStarConvexSet.prod`：∀ {R : Type u_1} {X : Type u_2} {Y : Typ
e u_3} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrdered
Ring R] [inst_3 : Co…
-/
lemma IsStarConvexSet.add (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R y t) :
    IsStarConvexSet R (x + y) (s + t) := by
  rw [← Set.add_image_prod]; exact (hs.prod ht).image (by fun_prop)

end IsModuleConvexSpace

variable (R I) in
/-
**Convexity.StdSimplex.isAffineMap_weights** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.
StdSimplex`。
形式化陈述：∀ (R : Type u_2) (I : Type u_5) [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R],   Convexity.IsAffineMap R Convexity.StdSim
plex.weights
参数：R : Type u_2；I : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_sConvexComb`：∀ {R : Type u_1} {I : Type u_6
} [inst : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]
   (f : Convexity.StdSimplex R…
· 使用定理 `Convexity.IsModuleConvexSpace.sConvexComb_eq_sum`：∀ {R : Type u_2} {M : 
Type u_3} {inst : Semiring R} {inst_1 : PartialOrder R} {inst_2 : IsStrictOrdere
dRing R}   {inst_3 : AddCommMonoid M} …
· 使用定理 `Convexity.instIsModuleConvexSpaceFinsupp`：∀ {R : Type u_2} {M : Type u_3
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]
   [inst_3 : AddCommMonoid M] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
lemma StdSimplex.isAffineMap_weights : IsAffineMap R (weights (R := R) (M := I)) where
  map_sConvexComb s := by simp [sConvexComb_eq_sum, Finsupp.sum_mapDomain_index, add_smul]

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [ConvexSpace R M] [IsModuleConvexSpace R M] [ConvexSpace R N] [IsModuleConvexSpace R N]
  {x y : M} {s t : Set M} {f g : M → N}

@[to_fun (attr := fun_prop)]
/-
**Convexity.IsAffineMap.neg** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsAffineMap`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup M] 
[inst_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Module
 R N] [inst_7 : Convexity.ConvexSpace R M] [Convexity.IsModuleConvexSpace R M]  
 [inst_9 : Convexity.ConvexSpace R N] [Convexity.IsModuleConvexSpace R N] {f : M
 → N},   Convexity.IsAffineMap R f → Convexity.IsAffineMap R (-f)
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsModuleConvexSpace.sConvexComb_eq_sum`：∀ {R : Type u_2} {M : 
Type u_3} {inst : Semiring R} {inst_1 : PartialOrder R} {inst_2 : IsStrictOrdere
dRing R}   {inst_3 : AddCommMonoid M} …
· 使用定理 `Convexity.IsAffineMap.map_sum_weights`：∀ {R : Type u_2} {M : Type u_3} {
N : Type u_4} {I : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder R]   [in
st_2 : IsStrictOrderedRing …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Finsupp.sum_neg`：∀ {α : Type u_1} {M : Type u_8} {G : Type u_12} [inst :
 Zero M] [inst_1 : AddCommGroup G] {f : α →₀ M} {h : α → M → G},   (f.sum fun a 
b => …
-/
lemma IsAffineMap.neg (hf : IsAffineMap R f) : IsAffineMap R (-f) where
  map_sConvexComb w := by simp [hf.map_sum_weights, Finsupp.sum_mapDomain_index, add_smul]

@[to_fun (attr := fun_prop)]
/-
**Convexity.IsAffineMap.sub** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsAffineMap`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup M] 
[inst_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Module
 R N] [inst_7 : Convexity.ConvexSpace R M] [Convexity.IsModuleConvexSpace R M]  
 [inst_9 : Convexity.ConvexSpace R N] [Convexity.IsModuleConvexSpace R N] {f g :
 M → N},   Convexity.IsAffineMap R f → Convexity.IsAffineMap R g → Convexity.IsA
ffineMap R (f - g)
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Convexity.IsAffineMap.add`：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4
} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : Ad…
· 使用定理 `Convexity.IsAffineMap.neg`：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4
} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : Ad…
-/
lemma IsAffineMap.sub (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg
/-
**Convexity.IsStarConvexSet.neg** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarConve
xSet`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : AddCommGroup M] [inst_4 : _root
_.Module R M] [inst_5 : Convexity.ConvexSpace R M]   [Convexity.IsModuleConvexSp
ace R M] {x : M} {s : Set M},   Convexity.IsStarConvexSet R x s → Convexity.IsSt
arConvexSet R (-x) (-s)
参数：-x；-s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_neg_eq_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set
 α}, (fun x => -x) '' s = -s
· 使用定理 `Convexity.IsStarConvexSet.image`：∀ {R : Type u_1} {X : Type u_2} {Y : Ty
pe u_3} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrdere
dRing R] [inst_3 : Co…
· 使用定理 `Convexity.IsAffineMap.fun_neg`：∀ {R : Type u_2} {M : Type u_3} {N : Type
 u_4} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `Convexity.IsAffineMap.id`：∀ {R : Type u_1} {M : Type u_3} [inst : Partia
lOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Con
vexity.ConvexS…
-/
lemma IsStarConvexSet.neg (hs : IsStarConvexSet R x s) : IsStarConvexSet R (-x) (-s) := by
  rw [← Set.image_neg_eq_neg]; exact hs.image (by fun_prop)
/-
**Convexity.IsStarConvexSet.sub** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarConve
xSet`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : AddCommGroup M] [inst_4 : _root
_.Module R M] [inst_5 : Convexity.ConvexSpace R M]   [Convexity.IsModuleConvexSp
ace R M] {x y : M} {s t : Set M},   Convexity.IsStarConvexSet R x s → Convexity.
IsStarConvexSet R y t → Convexity.IsStarConvexSet R (x - y) (s - t)
参数：x - y；s - t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sub_image_prod`：∀ {α : Type u_2} [inst : Sub α] {s t : Set α}, (fun 
x => x.1 - x.2) '' s ×ˢ t = s - t
· 使用定理 `Convexity.IsStarConvexSet.image`：∀ {R : Type u_1} {X : Type u_2} {Y : Ty
pe u_3} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrdere
dRing R] [inst_3 : Co…
· 使用定理 `Convexity.IsAffineMap.fun_sub`：∀ {R : Type u_2} {M : Type u_3} {N : Type
 u_4} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `Convexity.instIsModuleConvexSpaceProd`：∀ {R : Type u_2} {M : Type u_3} {
N : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Ad…
· 使用引理 `Prod.isAffineMap_fst`：isAffineMap_fst : IsAffineMap R (fst : X × Y -> X)
 where map_sConvexComb
· 使用引理 `Prod.isAffineMap_snd`：isAffineMap_snd : IsAffineMap R (snd : X × Y -> Y)
 where map_sConvexComb
· 使用定理 `Convexity.IsStarConvexSet.prod`：∀ {R : Type u_1} {X : Type u_2} {Y : Typ
e u_3} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrdered
Ring R] [inst_3 : Co…
-/
lemma IsStarConvexSet.sub (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R y t) :
    IsStarConvexSet R (x - y) (s - t) := by
  rw [← Set.sub_image_prod]; exact (hs.prod ht).image (by fun_prop)

end AddCommGroup
end Convexity

