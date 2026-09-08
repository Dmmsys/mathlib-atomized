/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.Weights.Cartan
public import Mathlib.Algebra.Lie.Weights.Linear
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.PID

/-!
# The trace and Killing forms of a Lie algebra.

Let `L` be a Lie algebra with coefficients in a commutative ring `R`. Suppose `M` is a finite, free
`R`-module and we have a representation `φ : L → End M`. This data induces a natural bilinear form
`B` on `L`, called the trace form associated to `M`; it is defined as `B(x, y) = Tr (φ x) (φ y)`.

In the special case that `M` is `L` itself and `φ` is the adjoint representation, the trace form
is known as the Killing form.

We define the trace / Killing form in this file and prove some basic properties.

## Main definitions

* `LieModule.traceForm`: a finite, free representation of a Lie algebra `L` induces a bilinear form
  on `L` called the trace form.
* `LieModule.traceForm_eq_zero_of_isNilpotent`: the trace form induced by a nilpotent
  representation of a Lie algebra vanishes.
* `killingForm`: the adjoint representation of a (finite, free) Lie algebra `L` induces a bilinear
  form on `L` via the trace form construction.
-/

@[expose] public section

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "φ" => LieModule.toEnd R L M

open LinearMap (trace)
open Set Module

namespace LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A finite, free representation of a Lie algebra `L` induces a bilinear form on `L` called
the trace form. See also `killingForm`. -/
/-
**LieModule.traceForm** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：traceForm : LinearMap.BilinForm R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite, free representation of a Lie algebra `L` induces a bilinear form on `L
` called
the trace form. See also `killingForm`.
-/
noncomputable def traceForm : LinearMap.BilinForm R L :=
  ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)
/-
**LieModule.traceForm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：traceForm_apply_apply (x y : L) : traceForm R L M x y = trace R _ (φ x ∘ₗ 
φ y)
参数：x y : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma traceForm_apply_apply (x y : L) :
    traceForm R L M x y = trace R _ (φ x ∘ₗ φ y) :=
  rfl
/-
**LieModule.traceForm_comm** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x
参数：x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
-/
lemma traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x :=
  LinearMap.trace_mul_comm R (φ x) (φ y)
/-
**LieModule.traceForm_isSymm** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：traceForm_isSymm : LinearMap.IsSymm (traceForm R L M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.traceForm_comm`：traceForm_comm (x y : L) : traceForm R L M x y
 = traceForm R L M y x
-/
lemma traceForm_isSymm : LinearMap.IsSymm (traceForm R L M) := ⟨LieModule.traceForm_comm R L M⟩
/-
**LieModule.traceForm_flip** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M],   Line
arMap.flip (LieModule.traceForm R L M) = LieModule.traceForm R L M
参数：R : Type u_1；L : Type u_3；M : Type u_4；LieModule.traceForm R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
· 使用引理 `LieModule.traceForm_comm`：traceForm_comm (x y : L) : traceForm R L M x y
 = traceForm R L M y x
-/
@[simp] lemma traceForm_flip : LinearMap.flip (traceForm R L M) = traceForm R L M :=
  Eq.symm <| LinearMap.ext₂ <| traceForm_comm R L M

/-- The trace form of a Lie module is compatible with the action of the Lie algebra.

See also `LieModule.traceForm_apply_lie_apply'`. -/
/-
**LieModule.traceForm_apply_lie_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：traceForm_apply_lie_apply (x y z : L) : traceForm R L M ⁅x, y⁆ z = traceFo
rm R L M x ⁅y, z⁆
参数：x y z : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `LinearMap.trace_mul_cycle'`：trace_mul_cycle' (f g h : M ->ₗ[R] M) : trac
e R M (f * (g * h)) = trace R M (h * (f * g))
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c

--- 原说明 ---
The trace form of a Lie module is compatible with the action of the Lie algebra.

See also `LieModule.traceForm_apply_lie_apply'`.
-/
lemma traceForm_apply_lie_apply (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆ := by
  calc traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← Module.End.mul_eq_comp]
  · simp only [sub_mul, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← Module.End.mul_eq_comp]

/-- Given a representation `M` of a Lie algebra `L`, the action of any `x : L` is skew-adjoint
w.r.t. the trace form. -/
/-
**LieModule.traceForm_apply_lie_apply'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：traceForm_apply_lie_apply' (x y z : L) : traceForm R L M ⁅x, y⁆ z = - trac
eForm R L M y ⁅x, z⁆
参数：x y z : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.neg_apply`：neg_apply (f : M ->ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -
f x
· 使用引理 `LieModule.traceForm_apply_lie_apply`：traceForm_apply_lie_apply (x y z : 
L) : traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆

--- 原说明 ---
Given a representation `M` of a Lie algebra `L`, the action of any `x : L` is sk
ew-adjoint
w.r.t. the trace form.
-/
lemma traceForm_apply_lie_apply' (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = - traceForm R L M y ⁅x, z⁆ :=
  calc traceForm R L M ⁅x, y⁆ z
      = - traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - traceForm R L M y ⁅x, z⁆ := by rw [traceForm_apply_lie_apply]
/-
**LieModule.traceForm_lieInvariant** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：traceForm_lieInvariant : (traceForm R L M).lieInvariant L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.neg_apply`：neg_apply (f : M ->ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -
f x
· 使用引理 `LieModule.traceForm_apply_lie_apply`：traceForm_apply_lie_apply (x y z : 
L) : traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆
-/
lemma traceForm_lieInvariant : (traceForm R L M).lieInvariant L := by
  intro x y z
  rw [← lie_skew, map_neg, LinearMap.neg_apply, LieModule.traceForm_apply_lie_apply R L M]

/-- This lemma justifies the terminology "invariant" for trace forms. -/
/-
**LieModule.lie_traceForm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (x : 
L), ⁅x, LieModule.traceForm R L M⁆ = 0
参数：R : Type u_1；L : Type u_3；M : Type u_4；x : L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.lie_apply`：LieHom.lie_apply (f : M ->ₗ[R] N) (x : L) (m : M) : ⁅x
, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用定理 `Module.Dual.lie_apply`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGr
oup M] [ins…
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用引理 `LieModule.traceForm_apply_lie_apply'`：traceForm_apply_lie_apply' (x y z 
: L) : traceForm R L M ⁅x, y⁆ z = - traceForm R L M y ⁅x, z⁆
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
This lemma justifies the terminology "invariant" for trace forms.
-/
@[simp] lemma lie_traceForm_eq_zero (x : L) : ⁅x, traceForm R L M⁆ = 0 := by
  ext y z
  rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
    LinearMap.zero_apply, traceForm_apply_lie_apply', sub_self]
/-
**LieModule.traceForm_eq_zero_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `LieModul
e`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [IsRe
duced R] [LieModule.IsNilpotent L M], LieModule.traceForm R L M = 0
参数：R : Type u_1；L : Type u_3；M : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用引理 `LinearMap.isNilpotent_trace_of_isNilpotent`：isNilpotent_trace_of_isNilpo
tent {f : M ->ₗ[R] M} (hf : IsNilpotent f) : IsNilpotent (trace R M f)
· 使用定理 `LieModule.isNilpotent_toEnd_of_isNilpotent₂`：isNilpotent_toEnd_of_isNilp
otent₂ [IsNilpotent L M] (x y : L) : _root_.IsNilpotent (toEnd R L M x ∘ₗ toEnd 
R L M y)
-/
@[simp] lemma traceForm_eq_zero_of_isNilpotent [IsReduced R] [IsNilpotent L M] :
    traceForm R L M = 0 := by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEnd_of_isNilpotent₂ R L M x y

open scoped TensorProduct in
/-
**LieModule.traceForm_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [Modu
le.Free R M] [Module.Finite R M] (A : Type u_5) [inst_9 : CommRing A] [inst_10 :
 Algebra R A],   LieModule.traceForm A (TensorProduct R A L) (TensorProduct R A 
M) =     LinearMap.BilinForm.baseChange A (LieModule.traceForm R L M)
参数：R : Type u_1；L : Type u_3；M : Type u_4；A : Type u_5；TensorProduct R A L；Tenso
rProduct R A M；LieModule.traceForm R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `LieModule.toEnd_baseChange`：LieModule.toEnd_baseChange (x : L) : toEnd A
 (A otimes[R] L) (A otimes[R] M) (1 otimesₜ x) = (toEnd R L M x).baseChange A
· 使用引理 `LinearMap.trace_baseChange`：trace_baseChange [Module.Free R M] [Module.F
inite R M] (f : M ->ₗ[R] M) (A : Type*) [CommRing A] [Algebra R A] : trace A _ (
f.baseChange A) …
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma traceForm_baseChange [Module.Free R M] [Module.Finite R M]
    (A : Type*) [CommRing A] [Algebra R A] :
    traceForm A (A ⊗[R] L) (A ⊗[R] M) = (traceForm R L M).baseChange A := by
  ext; simp [traceForm_apply_apply, ← LinearMap.baseChange_comp, Algebra.algebraMap_eq_smul_one]

variable {R L M} in
/-
**LieModule.trace_toEnd_mul_eq_zero_of_traceForm_eq_zero** 是 Mathlib 中的一个引理，位于命名
空间 `LieModule`。
形式化陈述：trace_toEnd_mul_eq_zero_of_traceForm_eq_zero (h : traceForm R L M = 0) (y 
: End R M) (hy : forall z in LieHom.range φ, ⁅y, z⁆ in LieHom.range φ) (x : L) (
hx : x in LieAlgebra.derivedSeries R L 1) : trace R M (φ x * y) = 0
参数：h : traceForm R L M = 0；y : End R M；hy : forall z in LieHom.range φ, ⁅y, z⁆ i
n LieHom.range φ；x : L；hx : x in LieAlgebra.derivedSeries R L 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.coe_derivedSeries_one_eq`：coe_derivedSeries_one_eq : derivedS
eries R L 1 = Submodule.span R {⁅x, y⁆ | (x : L) (y : L)}
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `LieHom.mem_range_self`：mem_range_self (x : L) : f x in f.range
· 使用定理 `Module.End.instLieRingModule_eq`：Module.End.instLieRingModule_eq : Linea
rMap.instLieRingModule (L
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用引理 `LinearMap.trace_lie_mul_eq`：trace_lie_mul_eq {R M : Type*} [CommRing R] 
[AddCommGroup M] [Module R M] (f g h : M ->ₗ[R] M) : trace R M (⁅f, g⁆ * h) = tr
ace R M (f * ⁅g,…
· 使用定理 `Ring.lie_def`：lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `LieRing.of_associative_ring_bracket`：of_associative_ring_bracket (x y : 
A) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用引理 `LieModule.traceForm_apply_apply`：traceForm_apply_apply (x y : L) : trace
Form R L M x y = trace R _ (φ x ∘ₗ φ y)
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
（共 37 条，此处仅展示前 30 条）
-/
lemma trace_toEnd_mul_eq_zero_of_traceForm_eq_zero (h : traceForm R L M = 0)
    (y : End R M) (hy : ∀ z ∈ LieHom.range φ, ⁅y, z⁆ ∈ LieHom.range φ)
    (x : L) (hx : x ∈ LieAlgebra.derivedSeries R L 1) :
    trace R M (φ x * y) = 0 := by
  replace hx : x ∈ Submodule.span R {⁅u, v⁆ | (u : L) (v : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]; exact hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨c : L, hbc : φ c = ⁅y, φ b⁆⟩ := hy (φ b) (LieHom.mem_range_self φ b)
    replace hbc : ⁅φ b, y⁆ = -φ c := by rw [hbc, Module.End.instLieRingModule_eq, lie_skew]
    rw [LieHom.map_lie, LinearMap.trace_lie_mul_eq, Ring.lie_def,
      ← LieRing.of_associative_ring_bracket, hbc, mul_neg, map_neg, neg_eq_zero,
      Module.End.mul_eq_comp, ← traceForm_apply_apply, h, LinearMap.zero_apply,
      LinearMap.zero_apply]
  | zero => simp
  | add u v _ _ hu hv => simp [add_mul, hu, hv]
  | smul t u _ hu => simp [hu]

@[simp]
/-
**LieModule.traceForm_genWeightSpace_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：traceForm_genWeightSpace_eq [Module.Free R M] [IsDomain R] [IsPrincipalIde
alRing R] [LieRing.IsNilpotent L] [IsNoetherian R M] [LinearWeights R L M] (χ : 
L -> R) (x y : L) : traceForm R L (genWeightSpace M χ) x y = finrank R (genWeigh
tSpace M χ) • (χ x * χ y)
参数：χ : L -> R；x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `LieModule.shiftedGenWeightSpace.instSubtypeMemLieSubmodule`：∀ (R : Type 
u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [ins
t_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `LieModule.traceForm_eq_zero_of_isNilpotent`：∀ (R : Type u_1) (L : Type u
_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra
 R L]   [inst_3 : AddCommGroup M…
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `LieModule.shiftedGenWeightSpace.instIsNilpotentSubtypeMemLieSubmoduleOfI
sNoetherian`：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.traceForm_apply_apply`：traceForm_apply_apply (x y : L) : trace
Form R L M x y = trace R _ (φ x ∘ₗ φ y)
· 使用定理 `LinearMap.trace_id`：trace_id : trace R M id = (finrank R M : R)
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `LieSubmodule.instIsTorsionFreeSubtypeMem`：∀ {R : Type u} {L : Type v} {M
 : Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   
[inst_3 : _root_.Module R M] […
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `Module.instIsReflexiveOfFiniteOfProjective`：∀ (R : Type u_1) (N : Type u
_3) [inst : CommSemiring R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R
 N]   [Module.Finite R N] [Modul…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 45 条，此处仅展示前 30 条）
-/
lemma traceForm_genWeightSpace_eq [Module.Free R M]
    [IsDomain R] [IsPrincipalIdealRing R]
    [LieRing.IsNilpotent L] [IsNoetherian R M] [LinearWeights R L M] (χ : L → R) (x y : L) :
    traceForm R L (genWeightSpace M χ) x y = finrank R (genWeightSpace M χ) • (χ x * χ y) := by
  set d := finrank R (genWeightSpace M χ)
  have h₁ : χ y • d • χ x - χ y • χ x • (d : R) = 0 := by simp [mul_comm (χ x)]
  have h₂ : χ x • d • χ y = d • (χ x * χ y) := by
    simpa [nsmul_eq_mul, smul_eq_mul] using mul_left_comm (χ x) d (χ y)
  have := traceForm_eq_zero_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)
  replace this := LinearMap.congr_fun (LinearMap.congr_fun this x) y
  rwa [LinearMap.zero_apply, LinearMap.zero_apply, traceForm_apply_apply,
    shiftedGenWeightSpace.toEnd_eq, shiftedGenWeightSpace.toEnd_eq,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj', LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, map_sub, map_sub, map_sub, LinearMap.comp_smul, LinearMap.smul_comp,
    LinearMap.comp_id, LinearMap.id_comp, map_smul, map_smul,
    trace_toEnd_genWeightSpace, trace_toEnd_genWeightSpace,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, map_smul, map_smul,
    LinearMap.trace_id, ← traceForm_apply_apply, h₁, h₂, sub_zero, sub_eq_zero] at this

/-- The upper and lower central series of `L` are orthogonal w.r.t. the trace form of any Lie module
`M`. -/
/-
**LieModule.traceForm_eq_zero_if_mem_lcs_of_mem_ucs** 是 Mathlib 中的一个引理，位于命名空间 `L
ieModule`。
形式化陈述：traceForm_eq_zero_if_mem_lcs_of_mem_ucs {x y : L} (k : Nat) (hx : x in (⊤ 
: LieIdeal R L).lcs L k) (hy : y in (⊥ : LieIdeal R L).ucs k) : traceForm R L M 
x y = 0
参数：k : Nat；hx : x in (⊤ : LieIdeal R L).lcs L k；hy : y in (⊥ : LieIdeal R L).ucs
 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `LinearMap.neg_apply`：neg_apply (f : M ->ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -
f x
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用引理 `LieModule.traceForm_apply_lie_apply`：traceForm_apply_lie_apply (x y z : 
L) : traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆
· 使用定理 `LieSubmodule.mem_normalizer`：mem_normalizer (m : M) : m in N.normalizer 
↔ forall x : L, ⁅x, m⁆ in N
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `LieIdeal.lcs_succ`：lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆

--- 原说明 ---
The upper and lower central series of `L` are orthogonal w.r.t. the trace form o
f any Lie module
`M`.
-/
lemma traceForm_eq_zero_if_mem_lcs_of_mem_ucs {x y : L} (k : ℕ)
    (hx : x ∈ (⊤ : LieIdeal R L).lcs L k) (hy : y ∈ (⊥ : LieIdeal R L).ucs k) :
    traceForm R L M x y = 0 := by
  induction k generalizing x y with
  | zero =>
    replace hy : y = 0 := by simpa using hy
    simp [hy]
  | succ k ih =>
    rw [LieSubmodule.ucs_succ, LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction ?_ ?_ (fun z w _ _ hz hw ↦ ?_) (fun t z _ hz ↦ ?_) hx
    · rintro - ⟨z, w, hw, rfl⟩
      rw [← lie_skew, map_neg, LinearMap.neg_apply, neg_eq_zero, traceForm_apply_lie_apply]
      exact ih hw (hy _)
    · simp
    · simp [hz, hw]
    · simp [hz]
/-
**LieModule.traceForm_apply_eq_zero_of_mem_lcs_of_mem_center** 是 Mathlib 中的一个引理，
位于命名空间 `LieModule`。
形式化陈述：traceForm_apply_eq_zero_of_mem_lcs_of_mem_center {x y : L} (hx : x in lowe
rCentralSeries R L L 1) (hy : y in LieAlgebra.center R L) : traceForm R L M x y 
= 0
参数：hx : x in lowerCentralSeries R L L 1；hy : y in LieAlgebra.center R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.traceForm_eq_zero_if_mem_lcs_of_mem_ucs`：traceForm_eq_zero_if_
mem_lcs_of_mem_ucs {x y : L} (k : Nat) (hx : x in (⊤ : LieIdeal R L).lcs L k) (h
y : y in (⊥ : LieIdeal R L).ucs k) : tr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.lcs_succ`：lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma traceForm_apply_eq_zero_of_mem_lcs_of_mem_center {x y : L}
    (hx : x ∈ lowerCentralSeries R L L 1) (hy : y ∈ LieAlgebra.center R L) :
    traceForm R L M x y = 0 := by
  apply traceForm_eq_zero_if_mem_lcs_of_mem_ucs R L M 1
  · simpa using hx
  · simpa using hy

-- This is barely worth having: it usually follows from `LieModule.traceForm_eq_zero_of_isNilpotent`
/-
**LieModule.traceForm_eq_zero_of_isTrivial** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`
。
形式化陈述：traceForm_eq_zero_of_isTrivial [IsTrivial L M] : traceForm R L M = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma traceForm_eq_zero_of_isTrivial [IsTrivial L M] :
    traceForm R L M = 0 := by
  ext x y
  suffices φ x ∘ₗ φ y = 0 by simp [traceForm_apply_apply, this]
  ext m
  simp [trivial_lie_zero]

/-- Given a bilinear form `B` on a representation `M` of a nilpotent Lie algebra `L`, if `B` is
invariant (in the sense that the action of `L` is skew-adjoint w.r.t. `B`) then components of the
Fitting decomposition of `M` are orthogonal w.r.t. `B`. -/
/-
**LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting** 是 Mathlib 中的一个引理，位于命名
空间 `LieModule`。
形式化陈述：eq_zero_of_mem_genWeightSpace_mem_posFitting [LieRing.IsNilpotent L] {B : 
LinearMap.BilinForm R M} (hB : forall (x : L) (m n : M), B ⁅x, m⁆ n = -B m ⁅x, n
⁆) {m₀ m₁ : M} (hm₀ : m₀ in genWeightSpace M (0 : L -> R)) (hm₁ : m₁ in posFitti
ngComp R L M) : B m₀ m₁ = 0
参数：hB : forall (x : L) (m n : M), B ⁅x, m⁆ n = -B m ⁅x, n⁆；hm₀ : m₀ in genWeight
Space M (0 : L -> R)；hm₁ : m₁ in posFittingComp R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieModule.mem_posFittingCompOf`：mem_posFittingCompOf (x : L) (m : M) : m
 in posFittingCompOf R M x ↔ forall (k : Nat), exists n, (toEnd R L M x ^ k) n =
 m
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Given a bilinear form `B` on a representation `M` of a nilpotent Lie algebra `L`
, if `B` is
invariant (in the sense that the action of `L` is skew-adjoint w.r.t. `B`) then 
components of the
Fitting decomposition of `M` are orthogonal w.r.t. `B`.
-/
lemma eq_zero_of_mem_genWeightSpace_mem_posFitting [LieRing.IsNilpotent L]
    {B : LinearMap.BilinForm R M} (hB : ∀ (x : L) (m n : M), B ⁅x, m⁆ n = -B m ⁅x, n⁆)
    {m₀ m₁ : M} (hm₀ : m₀ ∈ genWeightSpace M (0 : L → R)) (hm₁ : m₁ ∈ posFittingComp R L M) :
    B m₀ m₁ = 0 := by
  replace hB : ∀ x (k : ℕ) m n, B m ((φ x ^ k) n) = (-1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
    intro m n
    replace hB : ∀ m, B m (φ x n) = (-1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← Module.End.mul_eq_comp, ← pow_succ', ← smul_assoc, this]
  suffices ∀ (x : L) m, m ∈ posFittingCompOf R M x → B m₀ m = 0 by
    refine LieSubmodule.iSup_induction (motive := fun m ↦ (B m₀) m = 0) _ hm₁ this (map_zero _) ?_
    simp_all
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]
/-
**LieModule.trace_toEnd_eq_zero_of_mem_lcs** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`
。
形式化陈述：trace_toEnd_eq_zero_of_mem_lcs {k : Nat} {x : L} (hk : 1 <= k) (hx : x in 
lowerCentralSeries R L L k) : trace R _ (toEnd R L M x) = 0
参数：hk : 1 <= k；hx : x in lowerCentralSeries R L L k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.antitone_lowerCentralSeries`：antitone_lowerCentralSeries : Ant
itone lowerCentralSeries R L M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用引理 `LinearMap.trace_lie`：trace_lie {R M : Type*} [CommRing R] [AddCommGroup 
M] [Module R M] (f g : Module.End R M) : trace R M ⁅f, g⁆ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma trace_toEnd_eq_zero_of_mem_lcs
    {k : ℕ} {x : L} (hk : 1 ≤ k) (hx : x ∈ lowerCentralSeries R L L k) :
    trace R _ (toEnd R L M x) = 0 := by
  replace hx : x ∈ lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x ∈ Submodule.span R {m | ∃ u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x _ ↦ trace R _ (toEnd R L M x) = 0)
    ?_ ?_ (fun u v _ _ hu hv ↦ ?_) (fun t u _ hu ↦ ?_) hx
  · intro y ⟨u, v, huv⟩
    simp [← huv]
  · simp
  · simp [hu, hv]
  · simp [hu]

@[simp]
/-
**LieModule.traceForm_lieSubalgebra_mk_left** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
`。
形式化陈述：traceForm_lieSubalgebra_mk_left (L' : LieSubalgebra R L) {x : L} (hx : x i
n L') (y : L') : traceForm R L' M ⟨x, hx⟩ y = traceForm R L M x y
参数：L' : LieSubalgebra R L；hx : x in L'；y : L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma traceForm_lieSubalgebra_mk_left (L' : LieSubalgebra R L) {x : L} (hx : x ∈ L') (y : L') :
    traceForm R L' M ⟨x, hx⟩ y = traceForm R L M x y :=
  rfl

@[simp]
/-
**LieModule.traceForm_lieSubalgebra_mk_right** 是 Mathlib 中的一个引理，位于命名空间 `LieModul
e`。
形式化陈述：traceForm_lieSubalgebra_mk_right (L' : LieSubalgebra R L) {x : L'} {y : L}
 (hy : y in L') : traceForm R L' M x ⟨y, hy⟩ = traceForm R L M x y
参数：L' : LieSubalgebra R L；hy : y in L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma traceForm_lieSubalgebra_mk_right (L' : LieSubalgebra R L) {x : L'} {y : L} (hy : y ∈ L') :
    traceForm R L' M x ⟨y, hy⟩ = traceForm R L M x y :=
  rfl

open TensorProduct

variable [LieRing.IsNilpotent L] [IsDomain R]
/-
**LieModule.traceForm_eq_sum_genWeightSpaceOf** 是 Mathlib 中的一个引理，位于命名空间 `LieModu
le`。
形式化陈述：traceForm_eq_sum_genWeightSpaceOf [IsPrincipalIdealRing R] [Module.IsTorsi
onFree R M] [IsNoetherian R M] [IsTriangularizable R L M] (z : L) : traceForm R 
L M = ∑ χ in (finite_genWeightSpaceOf_ne_bot R L M z).toFinset, traceForm R L (g
enWeightSpaceOf M χ z)
参数：z : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用引理 `LieModule.finite_genWeightSpaceOf_ne_bot`：finite_genWeightSpaceOf_ne_bot
 [IsNoetherian R M] (x : L) : {χ : R | genWeightSpaceOf M χ x != ⊥}.Finite
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.toSubmodule_eq_bot`：toSubmodule_eq_bot : (N : Submodule R M
) = ⊥ ↔ N = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.iSupIndep_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Typ
e w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_
3 : _root_.Module R M] […
· 使用引理 `LieModule.iSupIndep_genWeightSpaceOf`：iSupIndep_genWeightSpaceOf (x : L)
 : iSupIndep fun (χ : R) => genWeightSpaceOf M χ x
· 使用定理 `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`：isInternal_s
ubmodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M} (hi : iSupIndep A)
 (hs : iSup A = ⊤) : IsInternal A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieModule.iSup_genWeightSpaceOf_eq_top`：iSup_genWeightSpaceOf_eq_top [Is
Triangularizable R L M] (x : L) : ⨆ (φ : R), genWeightSpaceOf M φ x = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LinearMap.trace_eq_sum_trace_restrict'`：trace_eq_sum_trace_restrict' (h 
: IsInternal N) (hN : {i | N i != ⊥}.Finite) {f : M ->ₗ[R] M} (hf : forall i, Ma
psTo f (N i) (N i)) : trace …
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
-/
lemma traceForm_eq_sum_genWeightSpaceOf [IsPrincipalIdealRing R]
    [Module.IsTorsionFree R M] [IsNoetherian R M] [IsTriangularizable R L M] (z : L) :
    traceForm R L M =
    ∑ χ ∈ (finite_genWeightSpaceOf_ne_bot R L M z).toFinset,
      traceForm R L (genWeightSpaceOf M χ z) := by
  ext x y
  have hxy : ∀ χ : R, MapsTo ((toEnd R L M x).comp (toEnd R L M y))
      (genWeightSpaceOf M χ z) (genWeightSpaceOf M χ z) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (genWeightSpaceOf M χ z : Submodule R M) ≠ ⊥}.Finite := by
    simp_rw [ne_eq, LieSubmodule.toSubmodule_eq_bot (genWeightSpaceOf M _ _)]
    exact finite_genWeightSpaceOf_ne_bot R L M z
  classical
  have h := LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpaceOf R L M z
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h <| by
    simp [← LieSubmodule.iSup_toSubmodule]
  simp only [LinearMap.coe_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ ↦ rfl)

-- In characteristic zero (or even just `LinearWeights R L M`) a stronger result holds (no
-- `⊓ LieAlgebra.center R L`) TODO prove this using `LieModule.traceForm_eq_sum_finrank_nsmul_mul`.
/-
**LieModule.lowerCentralSeries_one_inf_center_le_ker_traceForm** 是 Mathlib 中的一个引
理，位于命名空间 `LieModule`。
形式化陈述：lowerCentralSeries_one_inf_center_le_ker_traceForm [Module.Free R M] [Modu
le.Finite R M] : lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L <= LinearMap
.ker (traceForm R L M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.traceForm_apply_apply`：traceForm_apply_apply (x y : L) : trace
Form R L M x y = trace R _ (φ x ∘ₗ φ y)
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.trace_baseChange`：trace_baseChange [Module.Free R M] [Module.F
inite R M] (f : M ->ₗ[R] M) (A : Type*) [CommRing A] [Algebra R A] : trace A _ (
f.baseChange A) …
· 使用引理 `LinearMap.baseChange_comp`：baseChange_comp (g : N ->ₗ[R] P) : (g ∘ₗ f).b
aseChange A = g.baseChange A ∘ₗ f.baseChange A
· 使用引理 `LieModule.toEnd_baseChange`：LieModule.toEnd_baseChange (x : L) : toEnd A
 (A otimes[R] L) (A otimes[R] M) (1 otimesₜ x) = (toEnd R L M x).baseChange A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用引理 `LieSubmodule.baseChange_top`：baseChange_top : (⊤ : LieSubmodule R L M).b
aseChange A = ⊤
· 使用引理 `LieSubmodule.lie_baseChange`：lie_baseChange {I : LieIdeal R L} {N : LieS
ubmodule R L M} : ⁅I, N⁆.baseChange A = ⁅I.baseChange A, N.baseChange A⁆
· 使用引理 `Submodule.tmul_mem_baseChange_of_mem`：tmul_mem_baseChange_of_mem (a : A)
 {m : M} (hm : m in p) : a otimesₜ[R] m in p.baseChange A
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`：trace
_comp_eq_zero_of_commute_of_trace_restrict_eq_zero [IsDomain R] [IsPrincipalIdea
lRing R] [Module.Free R M] [Module.Finite R M] {f g : M…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用引理 `LieModule.commute_toEnd_of_mem_center_right`：commute_toEnd_of_mem_center
_right : Commute (toEnd R L M y) (toEnd R L M x)
· 使用定理 `LieModule.IsTriangularizable.maxGenEigenspace_eq_top`：∀ {R : Type u_2} {
L : Type u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : 
LieAlgebra R L}   {inst_3 : AddCommGroup M…
（共 50 条，此处仅展示前 30 条）
-/
lemma lowerCentralSeries_one_inf_center_le_ker_traceForm [Module.Free R M] [Module.Finite R M] :
    lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L ≤ LinearMap.ker (traceForm R L M) := by
  /- Sketch of proof (due to Zassenhaus):

  Let `z ∈ lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L` and `x : L`. We must show that
  `trace (φ x ∘ φ z) = 0` where `φ z : End R M` indicates the action of `z` on `M` (and likewise
  for `φ x`).

  Because `z` belongs to the indicated intersection, it has two key properties:
  (a) the trace of the action of `z` vanishes on any Lie module of `L`
      (see `LieModule.trace_toEnd_eq_zero_of_mem_lcs`),
  (b) `z` commutes with all elements of `L`.

  If `φ x` were triangularizable, we could write `M` as a direct sum of generalized eigenspaces of
  `φ x`. Because `L` is nilpotent these are all Lie submodules, thus Lie modules in their own right,
  and thus by (a) above we learn that `trace (φ z) = 0` restricted to each generalized eigenspace.
  Because `z` commutes with `x`, this forces `trace (φ x ∘ φ z) = 0` on each generalized eigenspace,
  and so by summing the traces on each generalized eigenspace we learn the total trace is zero, as
  required (see `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`).

  To cater for the fact that `φ x` may not be triangularizable, we first extend the scalars from `R`
  to `AlgebraicClosure (FractionRing R)` and argue using the action of `A ⊗ L` on `A ⊗ M`. -/
  rintro z ⟨hz : z ∈ lowerCentralSeries R L L 1, hzc : z ∈ LieAlgebra.center R L⟩
  ext x
  rw [traceForm_apply_apply, LinearMap.zero_apply]
  let A := AlgebraicClosure (FractionRing R)
  suffices algebraMap R A (trace R _ ((φ z).comp (φ x))) = 0 by
    have that : Module.IsTorsionFree R A := .trans_faithfulSMul R (FractionRing R) A
    rw [← map_zero (algebraMap R A)] at this
    exact FaithfulSMul.algebraMap_injective R A this
  rw [← LinearMap.trace_baseChange, LinearMap.baseChange_comp, ← toEnd_baseChange,
    ← toEnd_baseChange]
  replace hz : 1 ⊗ₜ z ∈ lowerCentralSeries A (A ⊗[R] L) (A ⊗[R] L) 1 := by
    simp only [lowerCentralSeries_succ, lowerCentralSeries_zero] at hz ⊢
    rw [← LieSubmodule.baseChange_top, ← LieSubmodule.lie_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hz
  replace hzc : 1 ⊗ₜ[R] z ∈ LieAlgebra.center A (A ⊗[R] L) := by
    simp only [mem_maxTrivSubmodule] at hzc ⊢
    intro y
    exact y.induction_on rfl (fun a u ↦ by simp [hzc u])
      (fun u v hu hv ↦ by simp [A, hu, hv])
  apply LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
  · exact IsTriangularizable.maxGenEigenspace_eq_top (1 ⊗ₜ[R] x)
  · exact fun μ ↦ trace_toEnd_eq_zero_of_mem_lcs A (A ⊗[R] L)
      (genWeightSpaceOf (A ⊗[R] M) μ ((1 : A) ⊗ₜ[R] x)) (le_refl 1) hz
  · exact commute_toEnd_of_mem_center_right (A ⊗[R] M) hzc (1 ⊗ₜ x)

/-- A nilpotent Lie algebra with a representation whose trace form is non-singular is Abelian. -/
/-
**LieModule.isLieAbelian_of_ker_traceForm_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieM
odule`。
形式化陈述：isLieAbelian_of_ker_traceForm_eq_bot [Module.Free R M] [Module.Finite R M]
 (h : LinearMap.ker (traceForm R L M) = ⊥) : IsLieAbelian L
参数：h : LinearMap.ker (traceForm R L M) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.disjoint_lowerCentralSeries_maxTrivSubmodule_iff`：disjoint_low
erCentralSeries_maxTrivSubmodule_iff [IsNilpotent L M] : Disjoint (lowerCentralS
eries R L M 1) (maxTrivSubmodule R L M) ↔ IsTriv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.lowerCentralSeries_one_inf_center_le_ker_traceForm`：lowerCentr
alSeries_one_inf_center_le_ker_traceForm [Module.Free R M] [Module.Finite R M] :
 lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R …

--- 原说明 ---
A nilpotent Lie algebra with a representation whose trace form is non-singular i
s Abelian.
-/
lemma isLieAbelian_of_ker_traceForm_eq_bot [Module.Free R M] [Module.Finite R M]
    (h : LinearMap.ker (traceForm R L M) = ⊥) : IsLieAbelian L := by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.toSubmodule_eq_bot, h]
    using! lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

end LieModule

namespace LieSubmodule

open LieModule (traceForm)

variable {R L M}
variable [Module.Free R M] [Module.Finite R M]
variable [IsDomain R] [IsPrincipalIdealRing R]
  (N : LieSubmodule R L M) (I : LieIdeal R L) (h : I ≤ N.idealizer) (x : L) {y : L} (hy : y ∈ I)

/-
**LieSubmodule.trace_eq_trace_restrict_of_le_idealizer** 是 Mathlib 中的一个引理，位于命名空间
 `LieSubmodule`。
形式化陈述：trace_eq_trace_restrict_of_le_idealizer (hy' : forall m in N, (φ x ∘ₗ φ y)
 m in N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LinearMap.trace_restrict_eq_of_forall_mem`：trace_restrict_eq_of_forall_m
em [IsDomain R] [IsPrincipalIdealRing R] (p : Submodule R M) (f : M ->ₗ[R] M) (h
f : forall x, f x in p) (hf' : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trace_eq_trace_restrict_of_le_idealizer
    (hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)) :
    trace R M (φ x ∘ₗ φ y) = trace R N ((φ x ∘ₗ φ y).restrict hy') := by
  suffices ∀ m, ⁅x, ⁅y, m⁆⁆ ∈ N by
    have : (trace R { x // x ∈ N }) ((φ x ∘ₗ φ y).restrict _) = (trace R M) (φ x ∘ₗ φ y) :=
      (φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this
    simp [this]
  exact fun m ↦ N.lie_mem (h hy m)

include h in
/-
**LieSubmodule.traceForm_eq_of_le_idealizer** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmod
ule`。
形式化陈述：traceForm_eq_of_le_idealizer : traceForm R I N = (traceForm R L M).restric
t I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieSubmodule.mem_idealizer`：mem_idealizer {x : L} : x in N.idealizer ↔ f
orall m : M, ⁅x, m⁆ in N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieSubmodule.trace_eq_trace_restrict_of_le_idealizer`：trace_eq_trace_res
trict_of_le_idealizer (hy' : forall m in N, (φ x ∘ₗ φ y) m in N
-/
lemma traceForm_eq_of_le_idealizer :
    traceForm R I N = (traceForm R L M).restrict I := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

include h hy in
/-- Note that this result is slightly stronger than it might look at first glance: we only assume
that `N` is trivial over `I` rather than all of `L`. This means that it applies in the important
case of an Abelian ideal (which has `M = L` and `N = I`). -/
/-
**LieSubmodule.traceForm_eq_zero_of_isTrivial** 是 Mathlib 中的一个引理，位于命名空间 `LieSubm
odule`。
形式化陈述：traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] : trace R M (φ x 
∘ₗ φ y) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieSubmodule.mem_idealizer`：mem_idealizer {x : L} : x in N.idealizer ↔ f
orall m : M, ⁅x, m⁆ in N
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `LieModule.IsTrivial.trivial`：∀ {L : Type v} {M : Type w} {inst : Bracket
 L M} {inst_1 : Zero M} [self : LieModule.IsTrivial L M] (x : L) (m : M),   ⁅x, 
m⁆ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LieSubmodule.trace_eq_trace_restrict_of_le_idealizer`：trace_eq_trace_res
trict_of_le_idealizer (hy' : forall m in N, (φ x ∘ₗ φ y) m in N
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…

--- 原说明 ---
Note that this result is slightly stronger than it might look at first glance: w
e only assume
that `N` is trivial over `I` rather than all of `L`. This means that it applies 
in the important
case of an Abelian ideal (which has `M = L` and `N = I`).
-/
lemma traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] :
    trace R M (φ x ∘ₗ φ y) = 0 := by
  let hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices (φ x ∘ₗ φ y).restrict hy' = 0 by
    simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext (n : N)
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

end LieSubmodule

section LieAlgebra

/-- A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`.

This is a specialisation of `LieModule.traceForm` to the adjoint representation of `L`. -/
/-
**killingForm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：killingForm : LinearMap.BilinForm R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`
.

This is a specialisation of `LieModule.traceForm` to the adjoint representation 
of `L`.
-/
noncomputable abbrev killingForm : LinearMap.BilinForm R L := LieModule.traceForm R L L

open LieAlgebra in
/-
**killingForm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：killingForm_apply_apply (x y : L) : killingForm R L x y = trace R L (ad R 
L x ∘ₗ ad R L y)
参数：x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.traceForm_apply_apply`：traceForm_apply_apply (x y : L) : trace
Form R L M x y = trace R _ (φ x ∘ₗ φ y)
-/
lemma killingForm_apply_apply (x y : L) : killingForm R L x y = trace R L (ad R L x ∘ₗ ad R L y) :=
  LieModule.traceForm_apply_apply R L L x y
/-
**killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting (H : LieSubalgebra R L)
 [LieRing.IsNilpotent H] {x₀ x₁ : L} (hx₀ : x₀ in LieAlgebra.zeroRootSubalgebra 
R L H) (hx₁ : x₁ in LieModule.posFittingComp R H L) : killingForm R L x₀ x₁ = 0
参数：H : LieSubalgebra R L；hx₀ : x₀ in LieAlgebra.zeroRootSubalgebra R L H；hx₁ : x
₁ in LieModule.posFittingComp R H L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting`：eq_zero_of_mem_g
enWeightSpace_mem_posFitting [LieRing.IsNilpotent L] {B : LinearMap.BilinForm R 
M} (hB : forall (x : L) (m n : M), B ⁅x, m⁆ …
· 使用引理 `LieModule.traceForm_apply_lie_apply'`：traceForm_apply_lie_apply' (x y z 
: L) : traceForm R L M ⁅x, y⁆ z = - traceForm R L M y ⁅x, z⁆
-/
lemma killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting
    (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
    {x₀ x₁ : L}
    (hx₀ : x₀ ∈ LieAlgebra.zeroRootSubalgebra R L H)
    (hx₁ : x₁ ∈ LieModule.posFittingComp R H L) :
    killingForm R L x₀ x₁ = 0 :=
  LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting R H L
    (fun x y z ↦ LieModule.traceForm_apply_lie_apply' R L L x y z) hx₀ hx₁

namespace LieIdeal

variable (I : LieIdeal R L)

/-- The orthogonal complement of an ideal with respect to the killing form is an ideal. -/
/-
**LieIdeal.killingCompl** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：killingCompl : LieIdeal R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal complement of an ideal with respect to the killing form is an ide
al.
-/
noncomputable def killingCompl : LieIdeal R L :=
  LieAlgebra.InvariantForm.orthogonal (killingForm R L) (LieModule.traceForm_lieInvariant R L L) I
/-
**LieIdeal.toSubmodule_killingCompl** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] (I : LieIdeal R L),   ↑(LieIdeal.killingCompl R L I) = 
(killingForm R L).orthogonal ↑I
参数：R : Type u_1；L : Type u_3；I : LieIdeal R L；LieIdeal.killingCompl R L I；killin
gForm R L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toSubmodule_killingCompl :
    LieSubmodule.toSubmodule I.killingCompl = (killingForm R L).orthogonal I.toSubmodule :=
  rfl
/-
**LieIdeal.mem_killingCompl** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] (I : LieIdeal R L)   {x : L}, x ∈ LieIdeal.killingCompl
 R L I ↔ ∀ y ∈ I, ((killingForm R L) y) x = 0
参数：R : Type u_1；L : Type u_3；I : LieIdeal R L；(killingForm R L) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_killingCompl {x : L} :
    x ∈ I.killingCompl ↔ ∀ y ∈ I, killingForm R L y x = 0 := by
  rfl
/-
**LieIdeal.coe_killingCompl_top** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：coe_killingCompl_top : killingCompl R L ⊤ = LinearMap.ker (killingForm R L
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieModule.traceForm_comm`：traceForm_comm (x y : L) : traceForm R L M x y
 = traceForm R L M y x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_killingCompl_top :
    killingCompl R L ⊤ = LinearMap.ker (killingForm R L) := by
  ext x
  simp [LinearMap.ext_iff, LieModule.traceForm_comm R L L x]
/-
**LieIdeal.restrict_killingForm** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：restrict_killingForm : (killingForm R L).restrict I = LieModule.traceForm 
R I L
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_killingForm :
    (killingForm R L).restrict I = LieModule.traceForm R I L :=
  rfl

variable [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]
/-
**LieIdeal.killingForm_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：killingForm_eq : killingForm R I = (killingForm R L).restrict I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieSubmodule.traceForm_eq_of_le_idealizer`：traceForm_eq_of_le_idealizer 
: traceForm R I N = (traceForm R L M).restrict I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.idealizer_eq_normalizer`：∀ {R : Type u_1} {L : Type u_2} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (I : LieIdeal R L),
   LieSubmodule.ideali…
-/
lemma killingForm_eq :
    killingForm R I = (killingForm R L).restrict I :=
  LieSubmodule.traceForm_eq_of_le_idealizer I I <| by simp
/-
**LieIdeal.le_killingCompl_top_of_isLieAbelian** 是 Mathlib 中的一个定理，位于命名空间 `LieIde
al`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] (I : LieIdeal R L)   [Module.Free R L] [Module.Finite R
 L] [IsDomain R] [IsPrincipalIdealRing R] [IsLieAbelian ↥I],   I ≤ LieIdeal.kill
ingCompl R L ⊤
参数：R : Type u_1；L : Type u_3；I : LieIdeal R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.traceForm_apply_apply`：traceForm_apply_apply (x y : L) : trace
Form R L M x y = trace R _ (φ x ∘ₗ φ y)
· 使用引理 `LieSubmodule.traceForm_eq_zero_of_isTrivial`：traceForm_eq_zero_of_isTriv
ial [LieModule.IsTrivial I N] : trace R M (φ x ∘ₗ φ y) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieIdeal.idealizer_eq_normalizer`：∀ {R : Type u_1} {L : Type u_2} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (I : LieIdeal R L),
   LieSubmodule.ideali…
-/
@[simp] lemma le_killingCompl_top_of_isLieAbelian [IsLieAbelian I] :
    I ≤ LieIdeal.killingCompl R L ⊤ := by
  intro x (hx : x ∈ I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx

end LieIdeal

open LieModule Module
open Submodule (span subset_span)

namespace LieModule

variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]
variable [LieRing.IsNilpotent L] [LinearWeights K L M] [IsTriangularizable K L M]

/-
**LieModule.traceForm_eq_sum_finrank_nsmul_mul** 是 Mathlib 中的一个引理，位于命名空间 `LieMod
ule`。
形式化陈述：traceForm_eq_sum_finrank_nsmul_mul (x y : L) : traceForm K L M x y = ∑ χ :
 Weight K L M, finrank K (genWeightSpace M χ) • (χ x * χ y)
参数：x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`：isInternal_s
ubmodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M} (hi : iSupIndep A)
 (hs : iSup A = ⊤) : IsInternal A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.iSupIndep_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Typ
e w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_
3 : _root_.Module R M] […
· 使用引理 `LieModule.iSupIndep_genWeightSpace'`：iSupIndep_genWeightSpace' : iSupInd
ep fun χ : Weight R L M => genWeightSpace M χ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LieSubmodule.iSup_toSubmodule_eq_top`：∀ {R : Type u} {L : Type v} {M : T
ype w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [ins
t_3 : _root_.Module R M] […
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top'`：iSup_genWeightSpace_eq_top' [IsTr
iangularizable K L M] : ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.trace_eq_sum_trace_restrict`：trace_eq_sum_trace_restrict (h : 
IsInternal N) [Fintype ι] {f : M ->ₗ[R] M} (hf : forall i, MapsTo f (N i) (N i))
 : trace R M f = ∑ i, trace…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.traceForm_genWeightSpace_eq`：traceForm_genWeightSpace_eq [Modu
le.Free R M] [IsDomain R] [IsPrincipalIdealRing R] [LieRing.IsNilpotent L] [IsNo
etherian R M] [LinearWeight…
-/
lemma traceForm_eq_sum_finrank_nsmul_mul (x y : L) :
    traceForm K L M x y = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ x * χ y) := by
  have hxy : ∀ χ : Weight K L M, MapsTo (toEnd K L M x ∘ₗ toEnd K L M y)
      (genWeightSpace M χ) (genWeightSpace M χ) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace' K L M)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top' K L M)
  simp_rw [traceForm_apply_apply, LinearMap.trace_eq_sum_trace_restrict hds hxy,
    ← traceForm_genWeightSpace_eq K L M _ x y]
  rfl

/-- See also `LieModule.traceForm_eq_sum_finrank_nsmul'` for an expression omitting the zero
weights. -/
/-
**LieModule.traceForm_eq_sum_finrank_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`
。
形式化陈述：traceForm_eq_sum_finrank_nsmul : traceForm K L M = ∑ χ : Weight K L M, fin
rank K (genWeightSpace M χ) • (χ : L ->ₗ[K] K).smulRight (χ : L ->ₗ[K] K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.traceForm_eq_sum_finrank_nsmul_mul`：traceForm_eq_sum_finrank_n
smul_mul (x y : L) : traceForm K L M x y = ∑ χ : Weight K L M, finrank K (genWei
ghtSpace M χ) • (χ x * χ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_attach_univ`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] (f : ↥Finset.univ → M),   ∑ i ∈ Finset.univ.attach
, f i = ∑ i,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `LieModule.traceForm_eq_sum_finrank_nsmul'` for an expression omitting 
the zero
weights.
-/
lemma traceForm_eq_sum_finrank_nsmul :
    traceForm K L M = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) := by
  ext
  rw [traceForm_eq_sum_finrank_nsmul_mul, ← Finset.sum_attach]
  simp [-LinearMap.coe_smul]

/-- A variant of `LieModule.traceForm_eq_sum_finrank_nsmul` in which the sum is taken only over the
non-zero weights. -/
/-
**LieModule.traceForm_eq_sum_finrank_nsmul'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
`。
形式化陈述：traceForm_eq_sum_finrank_nsmul' : traceForm K L M = ∑ χ in {χ : Weight K L
 M | χ.IsNonZero}, finrank K (genWeightSpace M χ) • (χ : L ->ₗ[K] K).smulRight (
χ : L ->ₗ[K] K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.smulRight.congr_simp`：∀ {R : Type u_1} {S : Type u_3} {M : Typ
e u_4} {M₁ : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid M₁] …
· 使用引理 `LinearMap.smulRight_zero`：smulRight_zero (f : M₁ ->ₗ[R] S) : f.smulRight
 (0 : M) = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LieModule.traceForm_eq_sum_finrank_nsmul`：traceForm_eq_sum_finrank_nsmul
 : traceForm K L M = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ : L
 ->ₗ[K] K).smulRight (χ : L ->…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
A variant of `LieModule.traceForm_eq_sum_finrank_nsmul` in which the sum is take
n only over the
non-zero weights.
-/
lemma traceForm_eq_sum_finrank_nsmul' :
    traceForm K L M = ∑ χ ∈ {χ : Weight K L M | χ.IsNonZero}, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) := by
  classical
  suffices ∑ χ ∈ {χ : Weight K L M | χ.IsZero}, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) = 0 by
    rw [traceForm_eq_sum_finrank_nsmul,
      ← Finset.sum_filter_add_sum_filter_not (p := fun χ : Weight K L M ↦ χ.IsNonZero)]
    simp [this]
  refine Finset.sum_eq_zero fun χ hχ ↦ ?_
  replace hχ : (χ : L →ₗ[K] K) = 0 := by simpa [← Weight.coe_toLinear_eq_zero_iff] using hχ
  simp [hχ]

-- The reverse inclusion should also hold: TODO prove this!
/-
**LieModule.range_traceForm_le_span_weight** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`
。
形式化陈述：range_traceForm_le_span_weight : LinearMap.range (traceForm K L M) <= span
 K (range (Weight.toLinear K L M))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.traceForm_eq_sum_finrank_nsmul`：traceForm_eq_sum_finrank_nsmul
 : traceForm K L M = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ : L
 ->ₗ[K] K).smulRight (χ : L ->…
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma range_traceForm_le_span_weight :
    LinearMap.range (traceForm K L M) ≤ span K (range (Weight.toLinear K L M)) := by
  rintro - ⟨x, rfl⟩
  rw [LieModule.traceForm_eq_sum_finrank_nsmul, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun χ _ ↦ ?_
  simp_rw [LinearMap.smul_apply, LinearMap.coe_smulRight, Weight.toLinear_apply,
    ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem _ _ <| Submodule.smul_mem _ _ <| subset_span <| mem_range_self χ

end LieModule

end LieAlgebra

