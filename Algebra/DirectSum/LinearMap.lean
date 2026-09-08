/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Linear maps between direct sums

This file contains results about linear maps which respect direct sum decompositions of their
domain and codomain.

-/

public section

open DirectSum Module Set

namespace LinearMap

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

section IsInternal

variable [DecidableEq ι]

set_option backward.isDefEq.respectTransparency.types false in
/-- If a linear map `f : M₁ → M₂` respects direct sum decompositions of `M₁` and `M₂`, then it has a
block diagonal matrix with respect to bases compatible with the direct sum decompositions. -/
/-
**LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap`。
形式化陈述：toMatrix_directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [Com
mSemiring R] [AddCommMonoid M₁] [Module R M₁] {N₁ : ι -> Submodule R M₁} (h₁ : I
sInternal N₁) [AddCommMonoid M₂] [Module R M₂] {N₂ : ι -> Submodule R M₂} (h₂ : 
IsInternal N₂) {κ₁ κ₂ : ι -> Type*} [forall i, Fintype (κ₁ i)] [forall i, Finite
 (κ₂ i)] [forall i, DecidableEq (κ₁ i)] [Fintype ι] (b₁ : (i : ι) -> Basis (κ₁ i
) R (N₁ i)) (b₂ : (i : ι) -> Basis (κ₂ i) R (N₂ i)) {f : M₁ ->ₗ[R] M₂} (hf : for
all i, MapsTo f (N₁ i) (N₂
参数：h₁ : IsInternal N₁；h₂ : IsInternal N₂；κ₁ i；κ₂ i；κ₁ i；b₁ : (i : ι) -> Basis (κ
₁ i) R (N₁ i)；b₂ : (i : ι) -> Basis (κ₂ i) R (N₂ i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.IsInternal.collectedBasis_coe`：∀ {R : Type u} [inst : Semiring
 R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module …
· 使用定理 `DirectSum.IsInternal.collectedBasis_repr_of_mem`：∀ {R : Type u} [inst : 
Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCom
mMonoid M]   [inst_2 : _root_.Module …
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DirectSum.IsInternal.collectedBasis_repr_of_mem_ne`：∀ {R : Type u} [inst
 : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : Add
CommMonoid M]   [inst_2 : _root_.Module …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
If a linear map `f : M₁ → M₂` respects direct sum decompositions of `M₁` and `M₂
`, then it has a
block diagonal matrix with respect to bases compatible with the direct sum decom
positions.
-/
lemma toMatrix_directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] {N₁ : ι → Submodule R M₁} (h₁ : IsInternal N₁)
    [AddCommMonoid M₂] [Module R M₂] {N₂ : ι → Submodule R M₂} (h₂ : IsInternal N₂)
    {κ₁ κ₂ : ι → Type*} [∀ i, Fintype (κ₁ i)] [∀ i, Finite (κ₂ i)] [∀ i, DecidableEq (κ₁ i)]
    [Fintype ι] (b₁ : (i : ι) → Basis (κ₁ i) R (N₁ i)) (b₂ : (i : ι) → Basis (κ₂ i) R (N₂ i))
    {f : M₁ →ₗ[R] M₂} (hf : ∀ i, MapsTo f (N₁ i) (N₂ i)) :
    toMatrix (h₁.collectedBasis b₁) (h₂.collectedBasis b₂) f =
    Matrix.blockDiagonal' fun i ↦ toMatrix (b₁ i) (b₂ i) (f.restrict (hf i)) := by
  ext ⟨i, _⟩ ⟨j, _⟩
  simp only [toMatrix_apply, Matrix.blockDiagonal'_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp [h₂.collectedBasis_repr_of_mem _ (hf _ (Subtype.mem _)), restrict_apply]
  · simp [hij, h₂.collectedBasis_repr_of_mem_ne _ hij.symm (hf _ (Subtype.mem _))]
/-
**LinearMap.diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne** 是 Math
lib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne {κ : ι -> Type
*} [forall i, Fintype (κ i)] [forall i, DecidableEq (κ i)] {s : Finset ι} (h : I
sInternal fun i : s => N i) (b : (i : s) -> Basis (κ i) R (N i)) (σ : ι -> ι) (h
σ : forall i, σ i != i) {f : Module.End R M} (hf : forall i, MapsTo f (N i) (N <
| σ i)) (hN : forall i, i ∉ s -> N i = ⊥) : Matrix.diag (toMatrix (h.collectedBa
sis b) (h.collectedBasis b) f) = 0
参数：κ i；κ i；h : IsInternal fun i : s => N i；b : (i : s) -> Basis (κ i) R (N i)；σ 
: ι -> ι；hσ : forall i, σ i != i；hf : forall i, MapsTo f (N i) (N <| σ i)；hN : f
orall i, i ∉ s -> N i = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.IsInternal.collectedBasis_coe`：∀ {R : Type u} [inst : Semiring
 R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `DirectSum.IsInternal.collectedBasis_repr_of_mem_ne`：∀ {R : Type u} [inst
 : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : Add
CommMonoid M]   [inst_2 : _root_.Module …
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {s : Finset ι} (h : IsInternal fun i : s ↦ N i)
    (b : (i : s) → Basis (κ i) R (N i)) (σ : ι → ι) (hσ : ∀ i, σ i ≠ i)
    {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N <| σ i)) (hN : ∀ i, i ∉ s → N i = ⊥) :
    Matrix.diag (toMatrix (h.collectedBasis b) (h.collectedBasis b) f) = 0 := by
  ext ⟨i, k⟩
  simp only [Matrix.diag_apply, Pi.zero_apply, toMatrix_apply, IsInternal.collectedBasis_coe]
  by_cases hi : σ i ∈ s
  · let j : s := ⟨σ i, hi⟩
    replace hσ : j ≠ i := fun hij ↦ hσ i <| Subtype.ext_iff.mp hij
    exact h.collectedBasis_repr_of_mem_ne b hσ <| hf _ <| Subtype.mem (b i k)
  · suffices f (b i k) = 0 by simp [this]
    simpa [hN _ hi] using hf i <| Subtype.mem (b i k)

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

/-- The trace of an endomorphism of a direct sum is the sum of the traces on each component.

See also `LinearMap.trace_restrict_eq_sum_trace_restrict`. -/
/-
**LinearMap.trace_eq_sum_trace_restrict** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_sum_trace_restrict (h : IsInternal N) [Fintype ι] {f : M ->ₗ[R] M
} (hf : forall i, MapsTo f (N i) (N i)) : trace R M f = ∑ i, trace R (N i) (f.re
strict (hf i))
参数：h : IsInternal N；hf : forall i, MapsTo f (N i) (N i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用引理 `LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'`：toMatrix_
directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [CommSemiring R] [A
ddCommMonoid M₁] [Module R M₁] {N₁ : ι -> Submodule…
· 使用引理 `Matrix.trace_blockDiagonal'`：trace_blockDiagonal' [DecidableEq p] {m : p
 -> Type*} [forall i, Fintype (m i)] (M : forall i, Matrix (m i) (m i) R) : trac
e (blockDiagonal'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trace of an endomorphism of a direct sum is the sum of the traces on each co
mponent.

See also `LinearMap.trace_restrict_eq_sum_trace_restrict`.
-/
lemma trace_eq_sum_trace_restrict (h : IsInternal N) [Fintype ι]
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i, trace R (N i) (f.restrict (hf i)) := by
  let b : (i : ι) → Basis _ R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  simp_rw [trace_eq_matrix_trace R (h.collectedBasis b),
    toMatrix_directSum_collectedBasis_eq_blockDiagonal' h h b b hf, Matrix.trace_blockDiagonal',
    ← trace_eq_matrix_trace]
/-
**LinearMap.trace_eq_sum_trace_restrict'** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_sum_trace_restrict' (h : IsInternal N) (hN : {i | N i != ⊥}.Finit
e) {f : M ->ₗ[R] M} (hf : forall i, MapsTo f (N i) (N i)) : trace R M f = ∑ i in
 hN.toFinset, trace R (N i) (f.restrict (hf i))
参数：h : IsInternal N；hN : {i | N i != ⊥}.Finite；hf : forall i, MapsTo f (N i) (N 
i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用引理 `LinearMap.trace_eq_sum_trace_restrict`：trace_eq_sum_trace_restrict (h : 
IsInternal N) [Fintype ι] {f : M ->ₗ[R] M} (hf : forall i, MapsTo f (N i) (N i))
 : trace R M f = ∑ i, trace…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DirectSum.isInternal_ne_bot_iff`：isInternal_ne_bot_iff {A : ι -> Submodu
le R M} : IsInternal (fun i : {i // A i != ⊥} => A i) ↔ IsInternal A
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
-/
lemma trace_eq_sum_trace_restrict' (h : IsInternal N) (hN : {i | N i ≠ ⊥}.Finite)
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i ∈ hN.toFinset, trace R (N i) (f.restrict (hf i)) := by
  let _ : Fintype {i // N i ≠ ⊥} := hN.fintype
  let _ : Fintype {i | N i ≠ ⊥} := hN.fintype
  rw [← Finset.sum_coe_sort, trace_eq_sum_trace_restrict (isInternal_ne_bot_iff.mpr h) (hf ·)]
  exact Fintype.sum_equiv hN.subtypeEquivToFinset _ _ (fun i ↦ rfl)
/-
**LinearMap.trace_eq_zero_of_mapsTo_ne** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_zero_of_mapsTo_ne (h : IsInternal N) [IsNoetherian R M] (σ : ι ->
 ι) (hσ : forall i, σ i != i) {f : Module.End R M} (hf : forall i, MapsTo f (N i
) (N <| σ i)) : trace R M f = 0
参数：h : IsInternal N；σ : ι -> ι；hσ : forall i, σ i != i；hf : forall i, MapsTo f (
N i) (N <| σ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.finite_ne_bot_of_iSupIndep`：WellFoundedGT.finite_ne_bot_of
_iSupIndep [WellFoundedGT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) : Set.F
inite {i | t i != ⊥}
· 使用定理 `DirectSum.IsInternal.submodule_iSupIndep`：∀ {R : Type u} [inst : Semirin
g R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid
 M]   [inst_2 : _root_.Module …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Function.hfunext`：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> 
Sort v} {f : forall a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a'
, a ≍ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DirectSum.isInternal_ne_bot_iff`：isInternal_ne_bot_iff {A : ι -> Submodu
le R M} : IsInternal (fun i : {i // A i != ⊥} => A i) ↔ IsInternal A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用引理 `LinearMap.diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne`：d
iag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne {κ : ι -> Type*} [for
all i, Fintype (κ i)] [forall i, DecidableEq (κ i)] {s : Fi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trace_eq_zero_of_mapsTo_ne (h : IsInternal N) [IsNoetherian R M]
    (σ : ι → ι) (hσ : ∀ i, σ i ≠ i) {f : Module.End R M}
    (hf : ∀ i, MapsTo f (N i) (N <| σ i)) :
    trace R M f = 0 := by
  have hN : {i | N i ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep
    h.submodule_iSupIndep
  let s := hN.toFinset
  let κ := fun i ↦ Module.Free.ChooseBasisIndex R (N i)
  let b : (i : s) → Basis (κ i) R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  replace h : IsInternal fun i : s ↦ N i := by
    convert! DirectSum.isInternal_ne_bot_iff.mpr h <;> simp [s]
  simp_rw [trace_eq_matrix_trace R (h.collectedBasis b), Matrix.trace,
    diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne h b σ hσ hf (by simp [s]),
    Pi.zero_apply, Finset.sum_const_zero]

/-- If `f` and `g` are commuting endomorphisms of a finite, free `R`-module `M`, such that `f`
is triangularizable, then to prove that the trace of `g ∘ f` vanishes, it is sufficient to prove
that the trace of `g` vanishes on each generalized eigenspace of `f`. -/
/-
**LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero** 是 Mathlib 
中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero [IsDomain R] [IsPr
incipalIdealRing R] [Module.Free R M] [Module.Finite R M] {f g : Module.End R M}
 (h_comm : Commute f g) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) (hg : forall μ, tra
ce R _ (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ)) = 0) : trace R 
_ (g ∘ₗ f) = 0
参数：h_comm : Commute f g；hf : ⨆ μ, f.maxGenEigenspace μ = ⊤；hg : forall μ, trace 
R _ (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ)) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.mapsTo_maxGenEigenspace_of_comm`：mapsTo_maxGenEigenspace_of_c
omm {f g : End R M} (h : Commute f g) (μ : R) : MapsTo g ↑(f.maxGenEigenspace μ)
 ↑(f.maxGenEigenspace μ)
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用引理 `LinearMap.restrict_commute`：restrict_commute {f g : M ->ₗ[R] M} (h : Com
mute f g) {p : Submodule R M} (hf : MapsTo f p p) (hg : MapsTo g p p) : Commute 
(f.restrict hf) …
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Algebra.mul_sub_algebraMap_commutes`：mul_sub_algebraMap_commutes [Ring A
] [Algebra R A] (x : A) (r : R) : x * (x - algebraMap R A r) = (x - algebraMap R
 A r) * x
· 使用引理 `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`：isNilpo
tent_restrict_maxGenEigenspace_sub_algebraMap [IsNoetherian R M] (f : End R M) (
μ : R) (h : MapsTo (f - algebraMap R (End R M) μ) ↑(f…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.restrict_comp`：restrict_comp {p : Submodule R M} {p₂ : Submodu
le R₂ M₂} {p₃ : Submodule R₃ M₃} {f : M ->ₛₗ[σ₁₂] M₂} {g : M₂ ->ₛₗ[σ₂₃] M₃} (hf 
: MapsTo f p …
· 使用引理 `LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent`：trace_comp_eq_mul
_of_commute_of_isNilpotent [IsReduced R] {f g : Module.End R M} (μ : R) (h_comm 
: Commute f g) (hg : IsNilpotent (g - algeb…
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`：isInternal_s
ubmodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M} (hi : iSupIndep A)
 (hs : iSup A = ⊤) : IsInternal A
· 使用定理 `Module.End.independent_maxGenEigenspace`：independent_maxGenEigenspace [I
sDomain R] [IsTorsionFree R M] (f : End R M) : iSupIndep f.maxGenEigenspace
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `Module.instIsReflexiveOfFiniteOfProjective`：∀ (R : Type u_1) (N : Type u
_3) [inst : CommSemiring R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R
 N]   [Module.Finite R N] [Modul…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `WellFoundedGT.finite_ne_bot_of_iSupIndep`：WellFoundedGT.finite_ne_bot_of
_iSupIndep [WellFoundedGT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) : Set.F
inite {i | t i != ⊥}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LinearMap.trace_eq_sum_trace_restrict'`：trace_eq_sum_trace_restrict' (h 
: IsInternal N) (hN : {i | N i != ⊥}.Finite) {f : M ->ₗ[R] M} (hf : forall i, Ma
psTo f (N i) (N i)) : trace …
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` and `g` are commuting endomorphisms of a finite, free `R`-module `M`, suc
h that `f`
is triangularizable, then to prove that the trace of `g ∘ f` vanishes, it is suf
ficient to prove
that the trace of `g` vanishes on each generalized eigenspace of `f`.
-/
lemma trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
    {f g : Module.End R M}
    (h_comm : Commute f g)
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤)
    (hg : ∀ μ, trace R _ (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ)) = 0) :
    trace R _ (g ∘ₗ f) = 0 := by
  have hfg : ∀ μ,
      MapsTo (g ∘ₗ f) ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
    fun μ ↦ (f.mapsTo_maxGenEigenspace_of_comm h_comm μ).comp
      (f.mapsTo_maxGenEigenspace_of_comm rfl μ)
  suffices ∀ μ, trace R _ ((g ∘ₗ f).restrict (hfg μ)) = 0 by
    classical
    have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.independent_maxGenEigenspace hf
    have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
      WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
    simp [trace_eq_sum_trace_restrict' hds h_fin hfg, this]
  intro μ
  have hf' := f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hg' := f.mapsTo_maxGenEigenspace_of_comm h_comm μ
  replace h_comm : Commute (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ))
      (f.restrict (f.mapsTo_maxGenEigenspace_of_comm rfl μ)) :=
    restrict_commute h_comm.symm _ _
  have := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  rw [restrict_comp hf' hg', trace_comp_eq_mul_of_commute_of_isNilpotent μ h_comm this,
    hg, mul_zero]
/-
**LinearMap.mapsTo_biSup_of_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：mapsTo_biSup_of_mapsTo {ι : Type*} {N : ι -> Submodule R M} (s : Set ι) {f
 : Module.End R M} (hf : forall i, MapsTo f (N i) (N i)) : MapsTo f ↑(⨆ i in s, 
N i) ↑(⨆ i in s, N i)
参数：s : Set ι；hf : forall i, MapsTo f (N i) (N i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma mapsTo_biSup_of_mapsTo {ι : Type*} {N : ι → Submodule R M}
    (s : Set ι) {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    MapsTo f ↑(⨆ i ∈ s, N i) ↑(⨆ i ∈ s, N i) := by
  replace hf : ∀ i, (N i).map f ≤ N i := fun i ↦ Submodule.map_le_iff_le_comap.mpr (hf i)
  suffices (⨆ i ∈ s, N i).map f ≤ ⨆ i ∈ s, N i from Submodule.map_le_iff_le_comap.mp this
  simpa only [Submodule.map_iSup] using iSup₂_mono <| fun i _ ↦ hf i

end IsInternal

/-- The trace of an endomorphism of a direct sum is the sum of the traces on each component.

Note that it is important the statement gives the user definitional control over `p` since the
_type_ of the term `trace R p (f.restrict hp')` depends on `p`. -/
/-
**LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup** 是 Mathlib 中的一个引理，位于命名空间 `L
inearMap`。
形式化陈述：trace_eq_sum_trace_restrict_of_eq_biSup [forall i, Module.Finite R (N i)] 
[forall i, Module.Free R (N i)] (s : Finset ι) (h : iSupIndep <| fun i : s => N 
i) {f : Module.End R M} (hf : forall i, MapsTo f (N i) (N i)) (p : Submodule R M
) (hp : p = ⨆ i in s, N i) (hp' : MapsTo f p p
参数：N i；N i；s : Finset ι；h : iSupIndep <| fun i : s => N i；hf : forall i, MapsTo 
f (N i) (N i)；p : Submodule R M；hp : p = ⨆ i in s, N i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirectSum.isInternal_biSup_submodule_of_iSupIndep`：isInternal_biSup_subm
odule_of_iSupIndep {A : ι -> Submodule R M} (s : Set ι) (h : iSupIndep <| fun i 
: s => A i) : IsInternal fun (i : s) =>…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.trace_eq_sum_trace_restrict`：trace_eq_sum_trace_restrict (h : 
IsInternal N) [Fintype ι] {f : M ->ₗ[R] M} (hf : forall i, MapsTo f (N i) (N i))
 : trace R M f = ∑ i, trace…
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.trace_conj'`：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : tr
ace R N (e.conj f) = trace R M f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trace of an endomorphism of a direct sum is the sum of the traces on each co
mponent.

Note that it is important the statement gives the user definitional control over
 `p` since the
_type_ of the term `trace R p (f.restrict hp')` depends on `p`.
-/
lemma trace_eq_sum_trace_restrict_of_eq_biSup
    [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]
    (s : Finset ι) (h : iSupIndep <| fun i : s ↦ N i)
    {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N i))
    (p : Submodule R M) (hp : p = ⨆ i ∈ s, N i)
    (hp' : MapsTo f p p := hp ▸ mapsTo_biSup_of_mapsTo (s : Set ι) hf) :
    trace R p (f.restrict hp') = ∑ i ∈ s, trace R (N i) (f.restrict (hf i)) := by
  classical
  let N' : s → Submodule R p := fun i ↦ (N i).comap p.subtype
  replace h : IsInternal N' := hp ▸ isInternal_biSup_submodule_of_iSupIndep (s : Set ι) h
  have hf' : ∀ i, MapsTo (restrict f hp') (N' i) (N' i) := fun i x hx' ↦ by simpa using! hf i hx'
  let e : (i : s) → N' i ≃ₗ[R] N i := fun ⟨i, hi⟩ ↦ (N i).comapSubtypeEquivOfLe (hp ▸ le_biSup N hi)
  have _i1 : ∀ i, Module.Finite R (N' i) := fun i ↦ Module.Finite.equiv (e i).symm
  have _i2 : ∀ i, Module.Free R (N' i) := fun i ↦ Module.Free.of_equiv (e i).symm
  rw [trace_eq_sum_trace_restrict h hf', ← s.sum_coe_sort]
  have : ∀ i : s, f.restrict (hf i) = (e i).conj ((f.restrict hp').restrict (hf' i)) := fun _ ↦ rfl
  simp [this]

end LinearMap

