/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Trace of a linear map

This file defines the trace of a linear map.

See also `Mathlib/LinearAlgebra/Matrix/Trace.lean` for the trace of a matrix.

## Tags

linear map, trace, diagonal
-/

@[expose] public section

noncomputable section

universe u v w

namespace LinearMap

open scoped Matrix
open Module TensorProduct

section

variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [DecidableEq ι] [Fintype ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ]
variable (b : Basis ι R M) (c : Basis κ R M)

/-- The trace of an endomorphism given a basis. -/
/-
**LinearMap.traceAux** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：traceAux : (M ->ₗ[R] M) ->ₗ[R] R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The trace of an endomorphism given a basis.
-/
def traceAux : (M →ₗ[R] M) →ₗ[R] R :=
  Matrix.traceLinearMap ι R R ∘ₗ ↑(LinearMap.toMatrix b b)

-- Can't be `simp` because it would cause a loop.
/-
**LinearMap.traceAux_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：traceAux_def (b : Basis ι R M) (f : M ->ₗ[R] M) : traceAux R b f = Matrix.
trace (LinearMap.toMatrix b b f)
参数：b : Basis ι R M；f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem traceAux_def (b : Basis ι R M) (f : M →ₗ[R] M) :
    traceAux R b f = Matrix.trace (LinearMap.toMatrix b b f) :=
  rfl
/-
**LinearMap.traceAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：traceAux_eq : traceAux R b = traceAux R c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.trace_mul_comm`：trace_mul_comm [AddCommMonoid R] [CommMagma R] (A
 : Matrix m n R) (B : Matrix n m R) : trace (A * B) = trace (B * A)
-/
theorem traceAux_eq : traceAux R b = traceAux R c :=
  LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix b b f) =
          Matrix.trace (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) := by
        rw [LinearMap.id_comp, LinearMap.comp_id]
      _ = Matrix.trace (LinearMap.toMatrix c b LinearMap.id * LinearMap.toMatrix c c f *
          LinearMap.toMatrix b c LinearMap.id) := by
        rw [LinearMap.toMatrix_comp _ c, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f * LinearMap.toMatrix b c LinearMap.id *
          LinearMap.toMatrix c b LinearMap.id) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.toMatrix_comp _ b, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f) := by rw [LinearMap.comp_id, LinearMap.comp_id]

variable (M) in
open scoped Classical in
/-- Trace of an endomorphism independent of basis. -/
/-
**LinearMap.trace** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：trace : (M ->ₗ[R] M) ->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Trace of an endomorphism independent of basis.
-/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
  if H : ∃ s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0

open scoped Classical in
/-- Auxiliary lemma for `trace_eq_matrix_trace`. -/
/-
**LinearMap.trace_eq_matrix_trace_of_finset** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：trace_eq_matrix_trace_of_finset {s : Finset M} (b : Basis s R M) (f : M ->
ₗ[R] M) : trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
参数：b : Basis s R M；f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace.eq_1`：∀ (R : Type u) [inst : CommSemiring R] (M : Type v
) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   LinearMap.trace R M
 = if H : …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.traceAux_def`：traceAux_def (b : Basis ι R M) (f : M ->ₗ[R] M) 
: traceAux R b f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `LinearMap.traceAux_eq`：traceAux_eq : traceAux R b = traceAux R c

--- 原说明 ---
Auxiliary lemma for `trace_eq_matrix_trace`.
-/
theorem trace_eq_matrix_trace_of_finset {s : Finset M} (b : Basis s R M) (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace, dif_pos this, ← traceAux_def]
  congr 1
  apply traceAux_eq
/-
**LinearMap.trace_eq_matrix_trace** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_matrix_trace (f : M ->ₗ[R] M) : trace R M f = Matrix.trace (Linea
rMap.toMatrix b b f)
参数：f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace_of_finset`：trace_eq_matrix_trace_of_fins
et {s : Finset M} (b : Basis s R M) (f : M ->ₗ[R] M) : trace R M f = Matrix.trac
e (LinearMap.toMatrix b b f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.traceAux_def`：traceAux_def (b : Basis ι R M) (f : M ->ₗ[R] M) 
: traceAux R b f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `LinearMap.traceAux_eq`：traceAux_eq : traceAux R b = traceAux R c
-/
theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  classical
  rw [trace_eq_matrix_trace_of_finset R b.reindexFinsetRange, ← traceAux_def, ← traceAux_def,
    traceAux_eq R b b.reindexFinsetRange]

variable {R} in
/-
**LinearMap._root_.Matrix.trace_toLin_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Matrix.trace_toLin_eq (A : Matrix ι ι R) (b : Basis ι R M) :
    LinearMap.trace R _ (Matrix.toLin b b A) = A.trace := by
  simp [trace_eq_matrix_trace R b]

variable {R} in
/-
**LinearMap._root_.Matrix.trace_toLin'_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Matrix.trace_toLin'_eq (A : Matrix ι ι R) :
    LinearMap.trace R _ A.toLin' = A.trace :=
  A.trace_toLin_eq (Pi.basisFun R ι)
/-
**LinearMap.trace_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M (f * g) = trace R M (g * f)
参数：f g : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `LinearMap.toMatrix_mul`：LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) : Li
nearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix
 v₁ v₁ g
· 使用定理 `Matrix.trace_mul_comm`：trace_mul_comm [AddCommMonoid R] [CommMagma R] (A
 : Matrix m n R) (B : Matrix n m R) : trace (A * B) = trace (B * A)
· 使用定理 `LinearMap.trace.eq_1`：∀ (R : Type u) [inst : CommSemiring R] (M : Type v
) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   LinearMap.trace R M
 = if H : …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
-/
theorem trace_mul_comm (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Basis s R M)
  · let ⟨s, ⟨b⟩⟩ := H
    simp_rw [trace_eq_matrix_trace R b, LinearMap.toMatrix_mul]
    apply Matrix.trace_mul_comm
  · rw [trace, dif_neg H, LinearMap.zero_apply, LinearMap.zero_apply]
/-
**LinearMap.trace_mul_cycle** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_mul_cycle (f g h : M ->ₗ[R] M) : trace R M (f * g * h) = trace R M (
h * f * g)
参数：f g h : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma trace_mul_cycle (f g h : M →ₗ[R] M) :
    trace R M (f * g * h) = trace R M (h * f * g) := by
  rw [LinearMap.trace_mul_comm, ← mul_assoc]
/-
**LinearMap.trace_mul_cycle'** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_mul_cycle' (f g h : M ->ₗ[R] M) : trace R M (f * (g * h)) = trace R 
M (h * (f * g))
参数：f g h : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
-/
lemma trace_mul_cycle' (f g h : M →ₗ[R] M) :
    trace R M (f * (g * h)) = trace R M (h * (f * g)) := by
  rw [← mul_assoc, LinearMap.trace_mul_comm]
/-
**LinearMap.trace_lie_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_lie_mul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] 
(f g h : M ->ₗ[R] M) : trace R M (⁅f, g⁆ * h) = trace R M (f * ⁅g, h⁆)
参数：f g h : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
-/
lemma trace_lie_mul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g h : M →ₗ[R] M) : trace R M (⁅f, g⁆ * h) = trace R M (f * ⁅g, h⁆) := by
  simp only [Ring.lie_def, sub_mul, mul_sub, map_sub, mul_assoc]
  rw [trace_mul_comm R g (f * h), mul_assoc]

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
/-
**LinearMap.trace_conj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_conj (g : M ->ₗ[R] M) (f : (M ->ₗ[R] M)ˣ) : trace R M (↑f * g * ↑f⁻¹
) = trace R M g
参数：g : M ->ₗ[R] M；f : (M ->ₗ[R] M)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trace of an endomorphism is invariant under conjugation
-/
theorem trace_conj (g : M →ₗ[R] M) (f : (M →ₗ[R] M)ˣ) :
    trace R M (↑f * g * ↑f⁻¹) = trace R M g := by
  rw [trace_mul_comm]
  simp

@[simp]
/-
**LinearMap.trace_lie** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_lie {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f g : 
Module.End R M) : trace R M ⁅f, g⁆ = 0
参数：f g : Module.End R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.lie_def`：lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma trace_lie {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f g : Module.End R M) :
    trace R M ⁅f, g⁆ = 0 := by
  rw [Ring.lie_def, map_sub, trace_mul_comm]
  exact sub_self _

end

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable (N P : Type*) [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {ι : Type*}

/-- The trace of a linear map corresponds to the contraction pairing under the isomorphism
`End(M) ≃ M* ⊗ M` -/
/-
**LinearMap.trace_eq_contract_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_contract_of_basis [Finite ι] (b : Basis ι R M) : LinearMap.trace 
R M ∘ₗ dualTensorHom R M M = contractLeft R M
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.tensorProduct_apply`：tensorProduct_apply (b : Basis ι S M) 
(c : Basis κ R N) (i : ι) (j : κ) : tensorProduct b c (i, j) = b i otimesₜ c j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `toMatrix_dualTensorHom`：toMatrix_dualTensorHom {m : Type*} {n : Type*} [
Fintype m] [Finite n] [DecidableEq m] [DecidableEq n] (bM : Basis m R M) (bN : B
asis n R N) …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.trace_single_eq_same`：trace_single_eq_same : trace (single i i c)
 = c
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.trace_single_eq_of_ne`：trace_single_eq_of_ne (h : i != j) : trace
 (single i j c) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The trace of a linear map corresponds to the contraction pairing under the isomo
rphism
`End(M) ≃ M* ⊗ M`
-/
theorem trace_eq_contract_of_basis [Finite ι] (b : Basis ι R M) :
    LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M := by
  classical
    cases nonempty_fintype ι
    apply Basis.ext (Basis.tensorProduct (Basis.dualBasis b) b)
    rintro ⟨i, j⟩
    simp only [Function.comp_apply, Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp]
    rw [trace_eq_matrix_trace R b, toMatrix_dualTensorHom]
    obtain rfl | hij := eq_or_ne i j
    · simp
    rw [Matrix.trace_single_eq_of_ne j i (1 : R) hij.symm]
    simp [hij]

/-- The trace of a linear map corresponds to the contraction pairing under the isomorphism
`End(M) ≃ M* ⊗ M`. -/
/-
**LinearMap.trace_eq_contract_of_basis'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_contract_of_basis' [Fintype ι] [DecidableEq ι] (b : Basis ι R M) 
: LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquivOfBasis b).symm.t
oLinearMap
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_contract_of_basis`：trace_eq_contract_of_basis [Finite
 ι] (b : Basis ι R M) : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLef
t R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trace of a linear map corresponds to the contraction pairing under the isomo
rphism
`End(M) ≃ M* ⊗ M`.
-/
theorem trace_eq_contract_of_basis' [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquivOfBasis b).symm.toLinearMap := by
  simp [LinearEquiv.eq_comp_toLinearMap_symm, trace_eq_contract_of_basis b]

section
variable (R M)
variable [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]

/-- When `M` is finite free, the trace of a linear map corresponds to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`. -/
@[simp]
/-
**LinearMap.trace_eq_contract** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_contract : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractL
eft R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.trace_eq_contract_of_basis`：trace_eq_contract_of_basis [Finite
 ι] (b : Basis ι R M) : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLef
t R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
When `M` is finite free, the trace of a linear map corresponds to the contractio
n pairing under
the isomorphism `End(M) ≃ M* ⊗ M`.
-/
theorem trace_eq_contract : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M :=
  trace_eq_contract_of_basis (Module.Free.chooseBasis R M)

@[simp]
/-
**LinearMap.trace_eq_contract_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_contract_apply (x : Module.Dual R M otimes[R] M) : (LinearMap.tra
ce R M) ((dualTensorHom R M M) x) = contractLeft R M x
参数：x : Module.Dual R M otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.trace_eq_contract`：trace_eq_contract : LinearMap.trace R M ∘ₗ 
dualTensorHom R M M = contractLeft R M
-/
theorem trace_eq_contract_apply (x : Module.Dual R M ⊗[R] M) :
    (LinearMap.trace R M) ((dualTensorHom R M M) x) = contractLeft R M x := by
  rw [← comp_apply, trace_eq_contract]

/-- When `M` is finite free, the trace of a linear map corresponds to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`. -/
/-
**LinearMap.trace_eq_contract'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_contract' : LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensor
HomEquiv R M M).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis`：dualTensorHomEquiv_eq_d
ualTensorHomEquivOfBasis (b : Basis ι R M) [DecidableEq ι] [Fintype ι] : have
· 使用定理 `LinearMap.trace_eq_contract_of_basis'`：trace_eq_contract_of_basis' [Fint
ype ι] [DecidableEq ι] (b : Basis ι R M) : LinearMap.trace R M = contractLeft R 
M ∘ₗ (dualTensorHomEquivOfB…

--- 原说明 ---
When `M` is finite free, the trace of a linear map corresponds to the contractio
n pairing under
the isomorphism `End(M) ≃ M* ⊗ M`.
-/
theorem trace_eq_contract' :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap := by
  rw [dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis (Module.Free.chooseBasis R M)]
  exact trace_eq_contract_of_basis' _

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
/-
**LinearMap.trace_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_one : trace R M 1 = (finrank R M : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.trace_one`：trace_one : trace (1 : Matrix n n R) = Fintype.card n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trace of the identity endomorphism is the dimension of the free module.
-/
theorem trace_one : trace R M 1 = (finrank R M : R) := by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b, toMatrix_one, finrank_eq_card_chooseBasisIndex]
  simp

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
/-
**LinearMap.trace_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_id : trace R M id = (finrank R M : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.one_eq_id`：one_eq_id : (1 : Module.End R M) = .id
· 使用定理 `LinearMap.trace_one`：trace_one : trace R M 1 = (finrank R M : R)

--- 原说明 ---
The trace of the identity endomorphism is the dimension of the free module.
-/
theorem trace_id : trace R M id = (finrank R M : R) := by rw [← Module.End.one_eq_id, trace_one]

@[simp]
/-
**LinearMap.trace_transpose** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_transpose : trace R (Module.Dual R M) ∘ₗ Module.Dual.transpose = tra
ce R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.cancel_right`：cancel_right (hg : Surjective g) : f.comp g = f'
.comp g ↔ f = f'
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dualTensorHom_bijective`：dualTensorHom_bijective [Module.Finite R M] [Pr
ojective R M] : Function.Bijective (dualTensorHom R M N)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `dualTensorHomEquiv.eq_1`：∀ (R : Type u_2) (M : Type u_3) (N : Type u_4) 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `transpose_dualTensorHom`：transpose_dualTensorHom (f : Module.Dual R M) (
m : M) : Dual.transpose (R
· 使用定理 `LinearMap.trace_eq_contract_apply`：trace_eq_contract_apply (x : Module.D
ual R M otimes[R] M) : (LinearMap.trace R M) ((dualTensorHom R M M) x) = contrac
tLeft R M x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_transpose : trace R (Module.Dual R M) ∘ₗ Module.Dual.transpose = trace R M := by
  let e := dualTensorHomEquiv R M M
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f m; simp [e]
/-
**LinearMap.trace_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_prodMap : trace R (M × N) ∘ₗ prodMapLinear R M N M N R = (coprod id 
id : R × R ->ₗ[R] R) ∘ₗ prodMap (trace R M) (trace R N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.cancel_right`：cancel_right (hg : Surjective g) : f.comp g = f'
.comp g ↔ f = f'
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dualTensorHom_bijective`：dualTensorHom_bijective [Module.Finite R M] [Pr
ojective R M] : Function.Bijective (dualTensorHom R M N)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
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
· 使用定理 `LinearMap.prodMapLinear_apply`：∀ (R : Type u) (M : Type v) (M₂ : Type w)
 (M₃ : Type y) (M₄ : Type z) (S : Type u_3) [inst : Semiring R]   [inst_1 : Semi
ring S] [inst_2 : A…
· 使用定理 `dualTensorHom_prodMap_zero`：dualTensorHom_prodMap_zero (f : Module.Dual 
R M) (p : P) : ((dualTensorHom R M P) (f otimesₜ[R] p)).prodMap (0 : N ->ₗ[R] Q)
 = dualTensorHom…
· 使用定理 `LinearMap.trace_eq_contract_apply`：trace_eq_contract_apply (x : Module.D
ual R M otimes[R] M) : (LinearMap.trace R M) ((dualTensorHom R M M) x) = contrac
tLeft R M x
· 使用定理 `Module.Free.prod`：∀ (R : Type u_7) (M : Type u_8) (N : Type u_9) [inst :
 Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 :
 AddCo…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_prodMap_dualTensorHom`：zero_prodMap_dualTensorHom (g : Module.Dual 
R N) (q : Q) : (0 : M ->ₗ[R] P).prodMap ((dualTensorHom R N Q) (g otimesₜ[R] q))
 = dualTensorHom…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem trace_prodMap :
    trace R (M × N) ∘ₗ prodMapLinear R M N M N R =
      (coprod id id : R × R →ₗ[R] R) ∘ₗ prodMap (trace R M) (trace R N) := by
  let e := (dualTensorHomEquiv R M M).prodCongr (dualTensorHomEquiv R N N)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext <;> simp [e]

variable {R M N P}
/-
**LinearMap.trace_prodMap'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_prodMap' (f : M ->ₗ[R] M) (g : N ->ₗ[R] N) : trace R (M × N) (prodMa
p f g) = trace R M f + trace R N g
参数：f : M ->ₗ[R] M；g : N ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.trace_prodMap`：trace_prodMap : trace R (M × N) ∘ₗ prodMapLinea
r R M N M N R = (coprod id id : R × R ->ₗ[R] R) ∘ₗ prodMap (trace R M) (trace R 
N)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.prodMapLinear_apply`：∀ (R : Type u) (M : Type v) (M₂ : Type w)
 (M₃ : Type y) (M₄ : Type z) (S : Type u_3) [inst : Semiring R]   [inst_1 : Semi
ring S] [inst_2 : A…
-/
theorem trace_prodMap' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M × N) (prodMap f g) = trace R M f + trace R N g := by
  have h := LinearMap.ext_iff.1 (trace_prodMap R M N) (f, g)
  simp only [coe_comp, Function.comp_apply, prodMap_apply, coprod_apply, id,
    prodMapLinear_apply] at h
  exact h

variable (R M N P)

open TensorProduct Function
/-
**LinearMap.trace_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_tensorProduct : compr₂ (mapBilinear (.id R) M N M N) (trace R (M oti
mes N)) = compl₁₂ (lsmul R R : R ->ₗ[R] R ->ₗ[R] R) (trace R M) (trace R N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.compl₁₂_inj`：compl₁₂_inj [SMulCommClass R₂ R₁ Pₗ] {f₁ f₂ : Mₗ 
->ₗ[R₁] N ->ₗ[R₂] Pₗ} {g : Qₗ ->ₗ[R₁] Mₗ} {g' : Qₗ' ->ₗ[R₂] N} (hₗ : Function.Su
rjective g)…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `map_dualTensorHom`：map_dualTensorHom (f : Module.Dual R M) (p : P) (g : 
Module.Dual R N) (q : Q) : TensorProduct.map (dualTensorHom R M P (f otimesₜ[R] 
p)) (du…
· 使用定理 `LinearMap.trace_eq_contract_apply`：trace_eq_contract_apply (x : Module.D
ual R M otimes[R] M) : (LinearMap.trace R M) ((dualTensorHom R M M) x) = contrac
tLeft R M x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_tensorProduct : compr₂ (mapBilinear (.id R) M N M N) (trace R (M ⊗ N)) =
    compl₁₂ (lsmul R R : R →ₗ[R] R →ₗ[R] R) (trace R M) (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R M M) from (dualTensorHomEquiv R M M).surjective)
        (show Surjective (dualTensorHom R N N) from (dualTensorHomEquiv R N N).surjective)).1
  ext f m g n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, mapBilinear_apply,
    trace_eq_contract_apply, contractLeft_apply, lsmul_apply, smul_eq_mul,
    map_dualTensorHom, dualDistrib_apply]
/-
**LinearMap.trace_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_comp_comm : compr₂ (llcomp R M N M) (trace R M) = compr₂ (llcomp R N
 M N).flip (trace R N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.compl₁₂_inj`：compl₁₂_inj [SMulCommClass R₂ R₁ Pₗ] {f₁ f₂ : Mₗ 
->ₗ[R₁] N ->ₗ[R₂] Pₗ} {g : Qₗ ->ₗ[R₁] Mₗ} {g' : Qₗ' ->ₗ[R₂] N} (hₗ : Function.Su
rjective g)…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `comp_dualTensorHom`：comp_dualTensorHom (f : Module.Dual R M) (n : N) (g 
: Module.Dual R N) (p : P) : dualTensorHom R N P (g otimesₜ[R] p) ∘ₗ dualTensorH
om R M N…
· 使用定理 `LinearMapClass.map_smul`：∀ {R : outParam (Type u_14)} {M : outParam (Typ
e u_15)} {M₂ : outParam (Type u_16)} [inst : Semiring R]   [inst_1 : AddCommMono
id M] [inst_2…
· 使用定理 `LinearMap.trace_eq_contract_apply`：trace_eq_contract_apply (x : Module.D
ual R M otimes[R] M) : (LinearMap.trace R M) ((dualTensorHom R M M) x) = contrac
tLeft R M x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_comp_comm :
    compr₂ (llcomp R M N M) (trace R M) = compr₂ (llcomp R N M N).flip (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R N M) from (dualTensorHomEquiv R N M).surjective)
        (show Surjective (dualTensorHom R M N) from (dualTensorHomEquiv R M N).surjective)).1
  ext g m f n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, flip_apply, llcomp_apply',
    comp_dualTensorHom, LinearMapClass.map_smul, trace_eq_contract_apply,
    contractLeft_apply, smul_eq_mul, mul_comm]

variable {R M N P}

@[simp]
/-
**LinearMap.trace_transpose'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_transpose' (f : M ->ₗ[R] M) : trace R _ (Module.Dual.transpose (R
参数：f : M ->ₗ[R] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.trace_transpose`：trace_transpose : trace R (Module.Dual R M) ∘
ₗ Module.Dual.transpose = trace R M
-/
theorem trace_transpose' (f : M →ₗ[R] M) :
    trace R _ (Module.Dual.transpose (R := R) f) = trace R M f := by
  rw [← comp_apply, trace_transpose]
/-
**LinearMap.trace_tensorProduct'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_tensorProduct' (f : M ->ₗ[R] M) (g : N ->ₗ[R] N) : trace R (M otimes
 N) (map f g) = trace R M f * trace R N g
参数：f : M ->ₗ[R] M；g : N ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.trace_tensorProduct`：trace_tensorProduct : compr₂ (mapBilinear
 (.id R) M N M N) (trace R (M otimes N)) = compl₁₂ (lsmul R R : R ->ₗ[R] R ->ₗ[R
] R) (trace R M) (t…
-/
theorem trace_tensorProduct' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M ⊗ N) (map f g) = trace R M f * trace R N g := by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_tensorProduct R M N) f) g
  simp only [compr₂_apply, mapBilinear_apply, compl₁₂_apply, lsmul_apply,
    smul_eq_mul] at h
  exact h
/-
**LinearMap.trace_comp_comm'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_comp_comm' (f : M ->ₗ[R] N) (g : N ->ₗ[R] M) : trace R M (g ∘ₗ f) = 
trace R N (f ∘ₗ g)
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.trace_comp_comm`：trace_comp_comm : compr₂ (llcomp R M N M) (tr
ace R M) = compr₂ (llcomp R N M N).flip (trace R N)
-/
theorem trace_comp_comm' (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g) := by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_comp_comm R M N) g) f
  simp only [llcomp_apply', compr₂_apply, flip_apply] at h
  exact h

@[simp]
/-
**LinearMap.trace_smulRight** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_smulRight (f : M ->ₗ[R] R) (x : M) : trace R M (f.smulRight x) = f x
参数：f : M ->ₗ[R] R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LinearMap.toMatrix_smulRight`：LinearMap.toMatrix_smulRight [Finite m] (f
 : M₁ ->ₗ[R] R) (x : M₂) : toMatrix v₁ v₂ (f.smulRight x) = vecMulVec (v₂.repr x
) (f ∘ v₁)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.univ_sum_single`：univ_sum_single [Fintype α] [AddCommMonoid M] (
f : α ->₀ M) : ∑ a : α, single a (f a) = f
· 使用定理 `Matrix.trace_vecMulVec`：trace_vecMulVec [NonUnitalNonAssocSemiring R] (a
 b : n -> R) : trace (vecMulVec a b) = a ⬝ᵥ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trace_smulRight (f : M →ₗ[R] R) (x : M) :
    trace R M (f.smulRight x) = f x := by
  rw [trace_eq_matrix_trace _ (Free.chooseBasis R M), ← (Free.chooseBasis R M).sum_repr x]
  simp [-Basis.sum_repr, dotProduct]

end

variable {N P}

variable [Module.Free R N] [Module.Finite R N] [Module.Free R P] [Module.Finite R P] in
/-
**LinearMap.trace_comp_cycle** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_comp_cycle (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M) : trac
e R P (g ∘ₗ f ∘ₗ h) = trace R N (f ∘ₗ h ∘ₗ g)
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；h : P ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_comp_comm'`：trace_comp_comm' (f : M ->ₗ[R] N) (g : N ->ₗ
[R] M) : trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g)
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
-/
lemma trace_comp_cycle (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] M) :
    trace R P (g ∘ₗ f ∘ₗ h) = trace R N (f ∘ₗ h ∘ₗ g) := by
  rw [trace_comp_comm', comp_assoc]

variable [Module.Free R M] [Module.Finite R M] [Module.Free R P] [Module.Finite R P] in
/-
**LinearMap.trace_comp_cycle'** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_comp_cycle' (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M) : tra
ce R P ((g ∘ₗ f) ∘ₗ h) = trace R M ((h ∘ₗ g) ∘ₗ f)
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；h : P ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_comp_comm'`：trace_comp_comm' (f : M ->ₗ[R] N) (g : N ->ₗ
[R] M) : trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
-/
lemma trace_comp_cycle' (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] M) :
    trace R P ((g ∘ₗ f) ∘ₗ h) = trace R M ((h ∘ₗ g) ∘ₗ f) := by
  rw [trace_comp_comm', ← comp_assoc]

@[simp]
/-
**LinearMap.trace_conj'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : trace R N (e.conj f) = trac
e R M f
参数：f : M ->ₗ[R] M；e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.free_def`：free_def [Small.{w, v} M] : Free R M ↔ exists I : Type 
w, Nonempty (Basis I R M) where mp h
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.conj_apply`：conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.
End R₁' M₁') : e.conj f = ((↑e : M₁' ->ₛₗ[σ₁'₂'] M₂').comp f).comp (e.symm : M₂'
 ->ₛₗ[σ₂'₁']…
· 使用定理 `LinearMap.trace_comp_comm'`：trace_comp_comm' (f : M ->ₗ[R] N) (g : N ->ₗ
[R] M) : trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.comp_coe`：comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃
) : (f' : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃
] M₃)
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `LinearEquiv.refl_toLinearMap`：refl_toLinearMap [Module R M] : (LinearEqu
iv.refl R M : M ->ₗ[R] M) = LinearMap.id
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
· 使用定理 `LinearMap.trace.eq_1`：∀ (R : Type u) [inst : CommSemiring R] (M : Type v
) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   LinearMap.trace R M
 = if H : …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
-/
theorem trace_conj' (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) : trace R N (e.conj f) = trace R M f := by
  classical
  by_cases hM : ∃ s : Finset M, Nonempty (Basis s R M)
  · obtain ⟨s, ⟨b⟩⟩ := hM
    have := Module.Finite.of_basis b
    have := (Module.free_def R M).mpr ⟨_, ⟨b⟩⟩
    have := Module.Finite.of_basis (b.map e)
    have := (Module.free_def R N).mpr ⟨_, ⟨(b.map e).reindex (e.toEquiv.image _)⟩⟩
    rw [e.conj_apply, trace_comp_comm', ← comp_assoc, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, id_comp]
  · rw [trace, trace, dif_neg hM, dif_neg ?_, zero_apply, zero_apply]
    rintro ⟨s, ⟨b⟩⟩
    exact hM ⟨s.image e.symm, ⟨(b.map e.symm).reindex
      ((e.symm.toEquiv.image s).trans (Equiv.setCongr Finset.coe_image.symm))⟩⟩
/-
**LinearMap.trace_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {K : Type u_6} {V : Type u_7} {W : Type u_8} [inst : Field K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup W] [inst_4
 : _root_.Module K W] {F : Type u_9}   [inst_5 : EquivLike F (Module.End K V) (M
odule.End K W)] [AlgEquivClass F K (Module.End K V) (Module.End K W)] (f : F)   
(x : Module.End K V), (LinearMap.trace K W) (f x) = (LinearMap.trace K V) x
参数：Module.End K V；Module.End K W；Module.End K V；Module.End K W；f : F；x : Module.
End K V；LinearMap.trace K W；f x；LinearMap.trace K V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.eq_linearEquivConjAlgEquiv`：∀ {K : Type u_1} {V : Type u_2} {W 
: Type u_3} [inst : Semifield K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.M
odule K V] [Module.Projec…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearMap.trace_conj'`：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : tr
ace R N (e.conj f) = trace R M f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] theorem trace_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] {F : Type*} [EquivLike F (End K V) (End K W)] [AlgEquivClass F K _ _]
    (f : F) (x : End K V) : (f x).trace K W = x.trace K V :=
  have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ trace_conj' _ _
/-
**LinearMap._root_.Matrix.trace_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Matrix.trace_map {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {F : Type*} [EquivLike F (Matrix m m K) (Matrix n n K)]
    [AlgEquivClass F K _ _] (f : F) (x : Matrix m m K) : (f x).trace = x.trace := by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.trace_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'
/-
**LinearMap._root_.Matrix.trace_map'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Matrix.trace_map' {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
    [FunLike F (Matrix m m K) (Matrix m m K)] [AlgHomClass F K _ _] (f : F) (x : Matrix m m K) :
    (f x).trace = x.trace := by
  by_cases! Nonempty m
  · exact Matrix.trace_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp
/-
**LinearMap.IsProj.trace** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsProj`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {p : Submodule R M} {f : M →ₗ[R] M},   Linear
Map.IsProj p f →     ∀ [Module.Free R ↥p] [Module.Finite R ↥p] [Module.Free R ↥f
.ker] [Module.Finite R ↥f.ker],       (LinearMap.trace R M) f = ↑(Module.finrank
 R ↥p)
参数：LinearMap.trace R M；Module.finrank R ↥p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.isCompl`：isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : Is
Compl p (ker f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsProj.eq_conj_prodMap`：∀ {R : Type u_1} [inst : CommRing R] {
E : Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   {p : Subm
odule R E} {f : E →ₗ[R…
· 使用定理 `LinearMap.trace_conj'`：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : tr
ace R N (e.conj f) = trace R M f
· 使用定理 `LinearMap.trace_prodMap'`：trace_prodMap' (f : M ->ₗ[R] M) (g : N ->ₗ[R] 
N) : trace R (M × N) (prodMap f g) = trace R M f + trace R N g
· 使用定理 `LinearMap.trace_id`：trace_id : trace R M id = (finrank R M : R)
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem IsProj.trace {p : Submodule R M} {f : M →ₗ[R] M} (h : IsProj p f) [Module.Free R p]
    [Module.Finite R p] [Module.Free R (ker f)] [Module.Finite R (ker f)] :
    trace R M f = (finrank R p : R) := by
  rw [h.eq_conj_prodMap, trace_conj', trace_prodMap', trace_id, map_zero, add_zero]

open LinearMap in
/-- An idempotent endomorphism of a module over a characteristic-zero commutative ring
with vanishing trace is the zero map, provided its range and kernel are finite and free.

The `Module.Free` and `Module.Finite` instance arguments on `range e` and `ker e` are
automatic over a field, and more generally over any principal ideal domain `R` for which
`M` itself is finite and free (submodules of finite free modules over a PID are finite
and free). -/
/-
**LinearMap.IsIdempotentElem.trace_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.IsIdempotentElem`。
形式化陈述：∀ {R : Type u_6} [inst : CommRing R] [CharZero R] {M : Type u_7} [inst_2 :
 AddCommGroup M] [inst_3 : _root_.Module R M]   {e : M →ₗ[R] M},   IsIdempotentE
lem e →     ∀ [Module.Free R ↥e.range] [Module.Finite R ↥e.range] [Module.Free R
 ↥e.ker] [Module.Finite R ↥e.ker],       (LinearMap.trace R M) e = 0 ↔ e = 0
参数：LinearMap.trace R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsProj.trace`：∀ {R : Type u_1} [inst : CommRing R] {M : Type u
_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodule R M}
 {f : M →ₗ[R…
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Module.finrank_eq_zero_iff_of_free`：finrank_eq_zero_iff_of_free [Module.
Free R M] [Module.Finite R M] : Module.finrank R M = 0 ↔ Subsingleton M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用定理 `LinearMap.range_eq_bot`：range_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊥ 
↔ f = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An idempotent endomorphism of a module over a characteristic-zero commutative ri
ng
with vanishing trace is the zero map, provided its range and kernel are finite a
nd free.

The `Module.Free` and `Module.Finite` instance arguments on `range e` and `ker e
` are
automatic over a field, and more generally over any principal ideal domain `R` f
or which
`M` itself is finite and free (submodules of finite free modules over a PID are 
finite
and free).
-/
theorem IsIdempotentElem.trace_eq_zero_iff {R : Type*} [CommRing R] [CharZero R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {e : M →ₗ[R] M} (he : IsIdempotentElem e)
    [Module.Free R (range e)] [Module.Finite R (range e)]
    [Module.Free R (ker e)] [Module.Finite R (ker e)] :
    trace R M e = 0 ↔ e = 0 := by
  rw [he.isProj_range.trace, Nat.cast_eq_zero, finrank_eq_zero_iff_of_free,
    Submodule.subsingleton_iff_eq_bot, range_eq_bot]

alias ⟨IsIdempotentElem.eq_zero_of_trace_eq_zero, _⟩ := IsIdempotentElem.trace_eq_zero_iff
/-
**LinearMap.isNilpotent_trace_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `LinearMa
p`。
形式化陈述：isNilpotent_trace_of_isNilpotent {f : M ->ₗ[R] M} (hf : IsNilpotent f) : I
sNilpotent (trace R M f)
参数：hf : IsNilpotent f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用引理 `Matrix.isNilpotent_trace_of_isNilpotent`：isNilpotent_trace_of_isNilpoten
t (hM : IsNilpotent M) : IsNilpotent (trace M)
· 使用定理 `LinearMap.trace.eq_1`：∀ (R : Type u) [inst : CommSemiring R] (M : Type v
) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   LinearMap.trace R M
 = if H : …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `IsNilpotent.zero`：∀ {R : Type u_3} [inst : MonoidWithZero R], IsNilpoten
t 0
-/
lemma isNilpotent_trace_of_isNilpotent {f : M →ₗ[R] M} (hf : IsNilpotent f) :
    IsNilpotent (trace R M f) := by
  by_cases H : ∃ s : Finset M, Nonempty (Basis s R M)
  swap
  · rw [LinearMap.trace, dif_neg H]
    exact IsNilpotent.zero
  obtain ⟨s, ⟨b⟩⟩ := H
  classical
  rw [trace_eq_matrix_trace R b]
  apply Matrix.isNilpotent_trace_of_isNilpotent
  simpa
/-
**LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空
间 `LinearMap`。
形式化陈述：trace_comp_eq_mul_of_commute_of_isNilpotent [IsReduced R] {f g : Module.En
d R M} (μ : R) (h_comm : Commute f g) (hg : IsNilpotent (g - algebraMap R _ μ)) 
: trace R M (f ∘ₗ g) = μ * trace R M f
参数：μ : R；h_comm : Commute f g；hg : IsNilpotent (g - algebraMap R _ μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isNilpotent_iff_eq_zero`：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsR
educed R] : IsNilpotent x ↔ x = 0
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用引理 `LinearMap.isNilpotent_trace_of_isNilpotent`：isNilpotent_trace_of_isNilpo
tent {f : M ->ₗ[R] M} (hf : IsNilpotent f) : IsNilpotent (trace R M f)
· 使用定理 `Commute.isNilpotent_mul_left`：isNilpotent_mul_left (h_comm : Commute x y
) (h : IsNilpotent y) : IsNilpotent (x * y)
· 使用定理 `Commute.sub_right`：sub_right : Commute a b -> Commute a c -> Commute a (
b - c)
· 使用引理 `Algebra.commute_algebraMap_right`：commute_algebraMap_right (r : R) (x : 
A) : Commute x (algebraMap R A r)
· 使用定理 `eq_add_of_sub_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 a - b = c → a = b + c
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.comp_add`：comp_add (f g : M ->ₛₗ[σ₁₂] M₂) (h : M₂ ->ₛₗ[σ₂₃] M₃
) : (h.comp (f + g) : M ->ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
lemma trace_comp_eq_mul_of_commute_of_isNilpotent [IsReduced R] {f g : Module.End R M}
    (μ : R) (h_comm : Commute f g) (hg : IsNilpotent (g - algebraMap R _ μ)) :
    trace R M (f ∘ₗ g) = μ * trace R M f := by
  set n := g - algebraMap R _ μ
  replace hg : trace R M (f ∘ₗ n) = 0 := by
    rw [← isNilpotent_iff_eq_zero, ← Module.End.mul_eq_comp]
    refine isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_left ?_ hg)
    exact h_comm.sub_right (Algebra.commute_algebraMap_right μ f)
  have hμ : g = algebraMap R _ μ + n := eq_add_of_sub_eq' rfl
  have : f ∘ₗ algebraMap R _ μ = μ • f := by ext; simp -- TODO Surely exists?
  rw [hμ, comp_add, map_add, hg, add_zero, this, map_smul, smul_eq_mul]

-- This result requires `Mathlib/RingTheory/TensorProduct/Free.lean`.
-- Maybe it should move elsewhere?
@[simp]
/-
**LinearMap.trace_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_baseChange [Module.Free R M] [Module.Finite R M] (f : M ->ₗ[R] M) (A
 : Type*) [CommRing A] [Algebra R A] : trace A _ (f.baseChange A) = algebraMap R
 A (trace R _ f)
参数：f : M ->ₗ[R] M；A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用引理 `LinearMap.toMatrix_baseChange`：toMatrix_baseChange (f : M₁ ->ₗ[R] M₂) (b
₁ : Basis ι R M₁) (b₂ : Basis ι₂ R M₂) : toMatrix (basis A b₁) (basis A b₂) (f.b
aseChange A) = (toM…
· 使用定理 `AddMonoidHom.map_trace`：∀ {n : Type u_3} {R : Type u_6} {S : Type u_7} [
inst : Fintype n] [inst_1 : AddCommMonoid R] [inst_2 : AddCommMonoid S]   {F : T
ype u_8} [in…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trace_baseChange [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (A : Type*) [CommRing A] [Algebra R A] :
    trace A _ (f.baseChange A) = algebraMap R A (trace R _ f) := by
  let b := Module.Free.chooseBasis R M
  let b' := Algebra.TensorProduct.basis A b
  change _ = (algebraMap R A : R →+ A) _
  simp [b', trace_eq_matrix_trace R b, trace_eq_matrix_trace A b', AddMonoidHom.map_trace]

end

end LinearMap

/-- If `S` is an `R-algebra that is free of rank `1` over `R`, the map `R →+* S` is an
isomorphism. -/
/-
**Module.Free.bijective_algebraMap_of_finrank_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Module.Free.bijective_algebraMap_of_finrank_eq_one {R S : Type*} [CommRing
 R] [Ring S] [Algebra R S] [Nontrivial R] [Free R S] (h : finrank R S = 1) : Fun
ction.Bijective (algebraMap R S)
参数：h : finrank R S = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `LinearMap.trace_one`：trace_one : trace R M 1 = (finrank R M : R)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `dualTensorHom_bijective`：dualTensorHom_bijective [Module.Finite R M] [Pr
ojective R M] : Function.Bijective (dualTensorHom R M N)
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If `S` is an `R-algebra that is free of rank `1` over `R`, the map `R →+* S` is 
an
isomorphism.
-/
lemma Module.Free.bijective_algebraMap_of_finrank_eq_one {R S : Type*} [CommRing R] [Ring S]
    [Algebra R S] [Nontrivial R] [Free R S] (h : finrank R S = 1) :
    Function.Bijective (algebraMap R S) := by
  have : Module.Finite R S := finite_of_finrank_pos (by grind)
  have : Free R (Module.End R S) := .of_equiv (dualTensorHomEquiv R S S)
  let f : S →ₐ[R] (S →ₗ[R] S) := Algebra.lmul R S
  have h1 : LinearMap.trace R S ∘ₗ f ∘ₗ Algebra.linearMap R S = LinearMap.id := by ext; simp [h]
  let b : Basis (Unit × Unit) R (End R S) :=
    .map (.tensorProduct (.dualBasis <| basisUnique Unit h) (basisUnique Unit h))
      (dualTensorHomEquiv R S S)
  have h2 : (f ∘ₗ Algebra.linearMap R S) ∘ₗ LinearMap.trace R S = LinearMap.id :=
    b.ext fun i ↦
      (basisUnique Unit h).ext fun j ↦ (by simp [f, b, Basis.tensorProduct])
  let eq : R ≃ₗ[R] End R S := .ofLinearMap (f ∘ₗ Algebra.linearMap R S) (.trace R S) h2 h1
  have hf : Function.Bijective f := ⟨Algebra.lmul_injective, .of_comp eq.surjective⟩
  exact (Function.Bijective.of_comp_iff' hf _).mp eq.bijective
