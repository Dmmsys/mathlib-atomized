/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Lie.Derivation.Basic

/-!
# Graded Lie algebras

This file defines typeclasses `SetLike.GradedBracket` and `GradedLieAlgebra`, for working with Lie
algebras that are graded by a collection `ℒ` of submodules.

## Main definitions

* `SetLike.GradedBracket`: A typeclass for a bracket to respect an additive grading.
* `GradedLieAlgebra`: A typeclass for a Lie algebra to respect an additive grading.
* `LieDerivation.ofGradingSum`: A Lie derivation on the direct sum of graded pieces, that scalar-
  multiplies the pieces by an additive map applied to degree.
* `LieDerivation.ofGrading`: A Lie derivation on a graded Lie algebra, that scalar-multiplies graded
  pieces by an additive map applied to degree.

## Implementation notes

For now we only implement internally-graded Lie algebras; supporting the externally-graded case
would be achieved by generalizing the `LieRing (⨁ i, ℒ i)` instance to take a family of types,
and defining a new `GradedMonoid.GBracket` class to provide the data piecewise.

-/

@[expose] public section

open DirectSum

variable {ι σ R L : Type*}

section SetLike

/-- A class that ensures a bracket product preserves an additive grading. -/
/-
**SetLike.GradedBracket** 是 Mathlib 中的一个归纳类型，位于命名空间 `SetLike`。
形式化陈述：{ι : Type u_1} → {σ : Type u_2} → {L : Type u_4} → [SetLike σ L] → [Bracke
t L L] → [Add ι] → (ι → σ) → Prop
参数：ι → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class that ensures a bracket product preserves an additive grading.
-/
class SetLike.GradedBracket [SetLike σ L] [Bracket L L] [Add ι] (ℒ : ι → σ) : Prop where
  /-- Bracket is homogeneous -/
  bracket_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ ℒ i → gj ∈ ℒ j → ⁅gi, gj⁆ ∈ ℒ (i + j)

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L)

/-- A class that ensures a Lie algebra has a bracket that preserves a decomposition. -/
/-
**GradedLieAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     {L : Type u_4} →       [DecidableE
q ι] →         [AddCommMonoid ι] →           [inst : CommRing R] →             [
inst_1 : LieRing L] → [inst_2 : LieAlgebra R L] → (ι → Submodule R L) → Type (ma
x u_1 u_4)
参数：ι → Submodule R L；max u_1 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class that ensures a Lie algebra has a bracket that preserves a decomposition.
-/
class GradedLieAlgebra extends SetLike.GradedBracket ℒ, DirectSum.Decomposition ℒ

end SetLike

namespace DirectSum

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRing (⨁ i, ℒ i) where
  bracket x y := decomposeLinearEquiv ℒ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp
/-
**DirectSum.bracket_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：bracket_apply_apply (x y : ⨁ i, ℒ i) : ⁅x, y⁆ = decomposeLinearEquiv ℒ ⁅(d
ecomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆
参数：x y : ⨁ i, ℒ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bracket_apply_apply (x y : ⨁ i, ℒ i) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℒ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆ :=
  rfl

attribute [local simp] bracket_apply_apply

@[simp]
/-
**DirectSum.decompose_bracket** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decompose_bracket (x y : L) : decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompo
se ℒ y⁆
参数：x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma decompose_bracket (x y : L) : decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℒ y⁆ := by
  simp only [← decomposeLinearEquiv_apply]
  simp

@[simp]
/-
**DirectSum.decompose_symm_bracket** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_bracket (x y : ⨁ i, ℒ i) : (decompose ℒ).symm ⁅x, y⁆ = ⁅(de
compose ℒ).symm x, (decompose ℒ).symm y⁆
参数：x y : ⨁ i, ℒ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma decompose_symm_bracket (x y : ⨁ i, ℒ i) :
    (decompose ℒ).symm ⁅x, y⁆ = ⁅(decompose ℒ).symm x, (decompose ℒ).symm y⁆ := by
  simp only [← decomposeLinearEquiv_symm_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieAlgebra R (⨁ i, ℒ i) where
  add_smul _ _ _ := by simp [add_smul]
  zero_smul _ := by simp
  lie_smul _ _ _ := by simp

/-- If `L` is graded by `ι` with degree `i` component `ℒ i`, then it is isomorphic as
a Lie algebra to a direct sum of components. -/
/-
**DirectSum.decomposeLieEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decomposeLieEquiv : L ≃ₗ⁅R⁆ ⨁ i, ℒ i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` is graded by `ι` with degree `i` component `ℒ i`, then it is isomorphic a
s
a Lie algebra to a direct sum of components.
-/
def decomposeLieEquiv : L ≃ₗ⁅R⁆ ⨁ i, ℒ i :=
  { decomposeLinearEquiv ℒ with
    map_lie' := by simp }

end DirectSum

namespace LieDerivation

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

/-- A derivation on the direct sum of graded pieces of a graded Lie algebra, induced by an additive
map on the grading monoid. -/
/-
**LieDerivation.ofGradingSum** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation`。
形式化陈述：ofGradingSum (φ : ι ->+ R) : LieDerivation R (⨁ i, ℒ i) (⨁ i, ℒ i)
参数：φ : ι ->+ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A derivation on the direct sum of graded pieces of a graded Lie algebra, induced
 by an additive
map on the grading monoid.
-/
def ofGradingSum (φ : ι →+ R) : LieDerivation R (⨁ i, ℒ i) (⨁ i, ℒ i) :=
  { __ := DirectSum.toModule R ι (⨁ i, ℒ i)
      fun i ↦ (lof R ι (ℒ ·) i).comp (Module.End.smulLeft (φ i) (by simp))
    leibniz' x y := by
      have hM (k : ι) (b : ⨁ i, ℒ i) (hb : (decompose ℒ).symm b ∈ ℒ k) :
          (toModule R ι (⨁ (i : ι), ℒ i) fun i ↦ lof R ι (ℒ ·) i ∘ₗ (φ i • .id)) b = (φ k) • b := by
        obtain ⟨_, rfl⟩ : b ∈ LinearMap.range (lof R ι (ℒ ·) k) := by
          use ⟨(decompose ℒ).symm b, hb⟩
          simp [lof_eq_of, ← decompose_of_mem]
        simp
      ext j
      induction x using DirectSum.induction_on' with
      | h0 => simp
      | hadd i a f _ _ ih =>
        simp only [Module.End.smulLeft_eq, DirectSum.sub_apply, AddSubgroupClass.coe_sub] at ih
        simp only [Module.End.smulLeft_eq, add_lie, map_add, DirectSum.add_apply, Submodule.coe_add,
          ih, lie_add, DirectSum.sub_apply, AddSubgroupClass.coe_sub]
        rw [add_sub_add_comm, add_right_cancel_iff, hM i (of (ℒ ·) i a) (by simp)]
        clear ih
        induction y using DirectSum.induction_on' with
        | h0 => simp
        | hadd k b f _ _ ih =>
          simp only [lie_add, map_add, DirectSum.add_apply, Submodule.coe_add, ih, lie_smul,
            add_lie, smul_add, add_sub, ← sub_sub]
          congr 1
          have : (decompose ℒ).symm ⁅of (fun i ↦ ℒ i) i a, of (fun i ↦ ℒ i) k b⁆ ∈ ℒ (i + k) := by
            simp [SetLike.GradedBracket.bracket_mem (Submodule.coe_mem a) (Submodule.coe_mem b)]
          rw [hM _ _ this, hM k (of (ℒ ·) k b) (by simp), ← lie_skew (of (ℒ ·) k b),
            add_sub_right_comm, add_right_cancel_iff, add_comm i k, map_add, add_smul,
            DirectSum.add_apply, Submodule.coe_add, sub_eq_add_neg, lie_smul, add_left_cancel_iff,
            smul_neg, ← sub_eq_zero, sub_neg_eq_add, ← Submodule.coe_add, Submodule.coe_eq_zero,
            ← DirectSum.add_apply, add_neg_cancel, DirectSum.zero_apply] }

@[simp]
/-
**LieDerivation.ofGradingSum_of** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：ofGradingSum_of (φ : ι ->+ R) (i : ι) (a : ℒ i) : ofGradingSum ℒ φ (of (ℒ 
·) i a) = (φ i) • (of (ℒ ·) i a)
参数：φ : ι ->+ R；i : ι；a : ℒ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.toModule_lof`：toModule_lof (i) (x : M i) : toModule R ι N φ (l
of R ι M i x) = φ i x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofGradingSum_of (φ : ι →+ R) (i : ι) (a : ℒ i) :
    ofGradingSum ℒ φ (of (ℒ ·) i a) = (φ i) • (of (ℒ ·) i a) := by
  simp [← lof_eq_of R, ofGradingSum]

set_option backward.isDefEq.respectTransparency false in
/-- The Lie derivation on a graded Lie algebra that scalar-multiplies by an additive function of
the degree. -/
/-
**LieDerivation.ofGrading** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation`。
形式化陈述：ofGrading (φ : ι ->+ R) : LieDerivation R L L where toFun x
参数：φ : ι ->+ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie derivation on a graded Lie algebra that scalar-multiplies by an additive
 function of
the degree.
-/
def ofGrading (φ : ι →+ R) :
    LieDerivation R L L where
  toFun x := (decomposeLinearEquiv ℒ).symm <| ofGradingSum ℒ φ <| decomposeLinearEquiv ℒ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  leibniz' x y := by simp [decomposeLinearEquiv_apply, decomposeLinearEquiv_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**LieDerivation.ofGrading_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：ofGrading_apply_apply (φ : ι ->+ R) {i : ι} {a : L} (ha : a in ℒ i) : ofGr
ading ℒ φ a = φ i • a
参数：φ : ι ->+ R；ha : a in ℒ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DirectSum.decompose_of_mem`：decompose_of_mem {x : M} {i : ι} (hx : x in 
ℳ i) : decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩
· 使用引理 `LieDerivation.ofGradingSum_of`：ofGradingSum_of (φ : ι ->+ R) (i : ι) (a 
: ℒ i) : ofGradingSum ℒ φ (of (ℒ ·) i a) = (φ i) • (of (ℒ ·) i a)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DirectSum.decompose_symm_of`：decompose_symm_of {i : ι} (x : ℳ i) : (deco
mpose ℳ).symm (DirectSum.of _ i x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofGrading_apply_apply (φ : ι →+ R) {i : ι} {a : L} (ha : a ∈ ℒ i) :
    ofGrading ℒ φ a = φ i • a := by
  simp [ofGrading, decomposeLinearEquiv_apply, decompose_of_mem ℒ ha]
  simp [decomposeLinearEquiv_symm_apply]

end LieDerivation

