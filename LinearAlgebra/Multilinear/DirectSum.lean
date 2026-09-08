/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Multilinear maps from direct sums

This file describes multilinear maps on direct sums.

## Main results

* `MultilinearMap.fromDirectSumEquiv` : If `ι` is a `Fintype`, `κ i` is a family of types
  indexed by `ι` and we are given an `R`-module `M i j` for every `i : ι` and `j : κ i`, this is
  the linear equivalence between `Π p : (i : ι) → κ i, MultilinearMap R (fun i ↦ M i (p i)) M'` and
  `MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'`.
-/

@[expose] public section

namespace MultilinearMap

open DirectSum

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
variable [CommSemiring R]
variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

/-- Two multilinear maps from direct sums are equal if they agree on the generators. -/
@[ext]
/-
**MultilinearMap.directSum_ext** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：directSum_ext [Finite ι] [(i : ι) -> DecidableEq (κ i)] ⦃f g : Multilinear
Map R (fun i => ⨁ j : κ i, M i j) M'⦄ (h : forall p : (i : ι) -> κ i, f.compLine
arMap (fun i => DirectSum.lof _ _ _ (p i)) = g.compLinearMap (fun i => DirectSum
.lof _ _ _ (p i))) : f = g
参数：i : ι；κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.dfinsupp_ext`：dfinsupp_ext [forall i, DecidableEq (κ i)] 
⦃f g : MultilinearMap R (fun i => Π₀ j : κ i, M i j) N⦄ (h : forall p : Π i, κ i
, f.compLinearMap…

--- 原说明 ---
Two multilinear maps from direct sums are equal if they agree on the generators.
-/
theorem directSum_ext [Finite ι] [(i : ι) → DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'⦄
    (h : ∀ p : (i : ι) → κ i,
      f.compLinearMap (fun i => DirectSum.lof _ _ _ (p i)) =
      g.compLinearMap (fun i => DirectSum.lof _ _ _ (p i))) : f = g :=
  dfinsupp_ext h

variable [DecidableEq ι]

/-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ ⨁ j : κ i, M i j`. -/
/-
**MultilinearMap.fromDirectSumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：fromDirectSumEquiv [Finite ι] : ((p : (i : ι) -> κ i) -> MultilinearMap R 
(fun i => M i (p i)) M') ≃ₗ[R] MultilinearMap R (fun i => ⨁ j : κ i, M i j) M'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between families indexed by `p : Π i : ι, κ i` of multili
near maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ ⨁ j : κ 
i, M i j`.
-/
noncomputable def fromDirectSumEquiv [Finite ι] :
    ((p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') ≃ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' :=
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : (i : ι) → DecidableEq (κ i) := fun i ↦ Classical.typeDecidableEq (κ i)
  fromDFinsuppEquiv _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MultilinearMap.fromDirectSumEquiv_lof** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMa
p`。
形式化陈述：fromDirectSumEquiv_lof [Finite ι] [(i : ι) -> DecidableEq (κ i)] (f : (p :
 (i : ι) -> κ i) -> MultilinearMap R (fun i => M i (p i)) M') (p : (i : ι) -> κ 
i) (x : (i : ι) -> M i (p i)) : fromDirectSumEquiv f (fun i => lof R _ _ _ (x i)
) = f p x
参数：i : ι；κ i；f : (p : (i : ι) -> κ i) -> MultilinearMap R (fun i => M i (p i)) M
'；p : (i : ι) -> κ i；x : (i : ι) -> M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.fromDirectSumEquiv.eq_1`：∀ {R : Type u_1} {ι : Type u_2} 
{M' : Type u_3} {κ : ι → Type u_4} {M : (i : ι) → κ i → Type u_5}   [inst : Comm
Semiring R] [inst_1 : (i : ι…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.fromDFinsuppEquiv_single`：fromDFinsuppEquiv_single (f : Π
 (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) N) (p : Π i, κ i) (x : Π 
i, M i (p i)) : fromDFinsuppE…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem fromDirectSumEquiv_lof [Finite ι] [(i : ι) → DecidableEq (κ i)]
    (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (p : (i : ι) → κ i) (x : (i : ι) → M i (p i)) :
    fromDirectSumEquiv f (fun i => lof R _ _ _ (x i)) = f p x := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [fromDirectSumEquiv, ← fromDFinsuppEquiv_single]
  convert! rfl

set_option backward.isDefEq.respectTransparency false in
/-- Prefer using `fromDirectSumEquiv_lof` where possible. -/
/-
**MultilinearMap.fromDirectSumEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multilinear
Map`。
形式化陈述：fromDirectSumEquiv_apply [Fintype ι] [(i : ι) -> DecidableEq (κ i)] [Π i (
j : κ i) (x : M i j), Decidable (x != 0)] (f : (p : (i : ι) -> κ i) -> Multiline
arMap R (fun i => M i (p i)) M') (x : ⨁ i, ⨁ (j : κ i), M i j) : fromDirectSumEq
uiv f x = ∑ p in Fintype.piFinset (fun i => (x i).support), f p (fun i => x i (p
 i))
参数：i : ι；κ i；j : κ i；x : M i j；x != 0；f : (p : (i : ι) -> κ i) -> MultilinearMap
 R (fun i => M i (p i)) M'；x : ⨁ i, ⨁ (j : κ i), M i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.fromDirectSumEquiv.eq_1`：∀ {R : Type u_1} {ι : Type u_2} 
{M' : Type u_3} {κ : ι → Type u_4} {M : (i : ι) → κ i → Type u_5}   [inst : Comm
Semiring R] [inst_1 : (i : ι…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.fromDFinsuppEquiv_apply`：fromDFinsuppEquiv_apply [Π i (j 
: κ i) (x : M i j), Decidable (x != 0)] (f : Π (p : Π i, κ i), MultilinearMap R 
(fun i => M i (p i)) N) (x :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)

--- 原说明 ---
Prefer using `fromDirectSumEquiv_lof` where possible.
-/
theorem fromDirectSumEquiv_apply [Fintype ι] [(i : ι) → DecidableEq (κ i)]
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : ⨁ i, ⨁ (j : κ i), M i j) :
    fromDirectSumEquiv f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  rw [fromDirectSumEquiv, ← fromDFinsuppEquiv_apply]
  convert! rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MultilinearMap.fromDirectSumEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multil
inearMap`。
形式化陈述：fromDirectSumEquiv_symm_apply [Finite ι] [(i : ι) -> DecidableEq (κ i)] (f
 : MultilinearMap R (fun i => ⨁ j : κ i, M i j) M') (p : (i : ι) -> κ i) : fromD
irectSumEquiv.symm f p = f.compLinearMap (fun i => DirectSum.lof _ _ _ (p i))
参数：i : ι；κ i；f : MultilinearMap R (fun i => ⨁ j : κ i, M i j) M'；p : (i : ι) -> 
κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem fromDirectSumEquiv_symm_apply [Finite ι] [(i : ι) → DecidableEq (κ i)]
    (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : (i : ι) → κ i) :
    fromDirectSumEquiv.symm f p = f.compLinearMap (fun i ↦ DirectSum.lof _ _ _ (p i)) := by
  have : Fintype ι := Fintype.ofFinite ι
  simp_rw [fromDirectSumEquiv, DirectSum.lof, ← fromDFinsuppEquiv_symm_apply]
  convert! rfl

end MultilinearMap

