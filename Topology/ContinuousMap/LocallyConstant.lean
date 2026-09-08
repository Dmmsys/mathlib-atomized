/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/

@[expose] public section


namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive (attr := simps) /-- The inclusion of locally-constant functions into continuous
functions as an additive monoid hom. -/]
/-
**LocallyConstant.toContinuousMapMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyCon
stant`。
形式化陈述：toContinuousMapMonoidHom [Monoid Y] [ContinuousMul Y] : LocallyConstant X 
Y ->* C(X, Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toContinuousMapMonoidHom [Monoid Y] [ContinuousMul Y] : LocallyConstant X Y →* C(X, Y) where
  toFun := (↑)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
/-
**LocallyConstant.toContinuousMapLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LocallyCon
stant`。
形式化陈述：toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y] [Modul
e R Y] [ContinuousAdd Y] [ContinuousConstSMul R Y] : LocallyConstant X Y ->ₗ[R] 
C(X, Y) where toFun
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of locally-constant functions into continuous functions as a linea
r map.
-/
def toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [ContinuousAdd Y] [ContinuousConstSMul R Y] : LocallyConstant X Y →ₗ[R] C(X, Y) where
  toFun := (↑)
  __ := toContinuousMapAddMonoidHom
  map_smul' x y := by
    ext
    simp
/-
**LocallyConstant.toAddMonoidHom_toContinuousMapLinearMap** 是 Mathlib 中的一个定理，位于命
名空间 `LocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (R : Type u_3)   [inst_2 : Semiring R] [inst_3 : AddCommMonoid Y
] [inst_4 : _root_.Module R Y] [inst_5 : ContinuousAdd Y]   [inst_6 : Continuous
ConstSMul R Y],   (LocallyConstant.toContinuousMapLinearMap R).toAddMonoidHom = 
LocallyConstant.toContinuousMapAddMonoidHom
参数：R : Type u_3；LocallyConstant.toContinuousMapLinearMap R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddMonoidHom_toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] [ContinuousAdd Y] [ContinuousConstSMul R Y] :
    (toContinuousMapLinearMap R (X := X) (Y := Y)).toAddMonoidHom = toContinuousMapAddMonoidHom :=
  rfl

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
/-
**LocallyConstant.toContinuousMapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConsta
nt`。
形式化陈述：toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R
 Y] [IsTopologicalSemiring Y] : LocallyConstant X Y ->ₐ[R] C(X, Y) where toFun
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of locally-constant functions into continuous functions as an alge
bra map.
-/
def toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [IsTopologicalSemiring Y] : LocallyConstant X Y →ₐ[R] C(X, Y) where
  toFun := (↑)
  __ := toContinuousMapMonoidHom
  __ := toContinuousMapAddMonoidHom
  commutes' r := by
    ext x
    simp [Algebra.smul_def]
/-
**LocallyConstant.toLinearMap_toContinuousMapAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `L
ocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (R : Type u_3)   [inst_2 : CommSemiring R] [inst_3 : Semiring Y]
 [inst_4 : Algebra R Y] [inst_5 : IsTopologicalSemiring Y],   (LocallyConstant.t
oContinuousMapAlgHom R).toLinearMap = LocallyConstant.toContinuousMapLinearMap R
参数：R : Type u_3；LocallyConstant.toContinuousMapAlgHom R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y]
    [Algebra R Y] [IsTopologicalSemiring Y] :
    (toContinuousMapAlgHom R (X := X) (Y := Y)).toLinearMap = toContinuousMapLinearMap R := rfl
/-
**LocallyConstant.separatesPoints_range_toContinuousMapAlgHom** 是 Mathlib 中的一个定理
，位于命名空间 `LocallyConstant`。
形式化陈述：separatesPoints_range_toContinuousMapAlgHom (R : Type*) [CommSemiring R] [
TotallySeparatedSpace X] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y] [N
ontrivial Y] : (toContinuousMapAlgHom R : _ ->ₐ[R] C(X, Y)).range.SeparatesPoint
s
参数：R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isClopen_of_totally_separated`：exists_isClopen_of_totally_separat
ed {α : Type*} [TopologicalSpace α] [TotallySeparatedSpace α] : Pairwise (exists
 U : Set α, IsClopen U ∧ ·…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocallyConstant.toContinuousMapAlgHom_apply`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (R : Type u_3)   
[inst_2 : CommSemiring R] [inst_3…
· 使用定理 `LocallyConstant.indicator_apply`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {R : Type u_5} [inst_1 : Zero R] {U : Set X} (f : LocallyConstant X R)   (
hU : IsClopen U) (x :…
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem separatesPoints_range_toContinuousMapAlgHom (R : Type*) [CommSemiring R]
    [TotallySeparatedSpace X] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y] [Nontrivial Y] :
    (toContinuousMapAlgHom R : _ →ₐ[R] C(X, Y)).range.SeparatesPoints := fun _ _ hxy ↦
  have ⟨_, hU, _, _⟩ := exists_isClopen_of_totally_separated hxy
  ⟨charFn Y hU, by simp_all [charFn]⟩

end LocallyConstant

