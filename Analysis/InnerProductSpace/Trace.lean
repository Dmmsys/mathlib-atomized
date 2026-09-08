/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Traces in inner product spaces

This file contains various results about traces of linear operators in inner product spaces.
-/

public section

namespace LinearMap

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

/-
**LinearMap.trace_eq_sum_inner** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：trace_eq_sum_inner (T : E ->ₗ[𝕜] E) (b : OrthonormalBasis ι 𝕜 E) : T.trace
 𝕜 E = ∑ i, ⟪b i, T (b i)⟫_𝕜
参数：T : E ->ₗ[𝕜] E；b : OrthonormalBasis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
· 使用定理 `Matrix.diag_apply`：diag_apply (A : Matrix n n α) (i) : diag A i = A i i
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `OrthonormalBasis.coe_toBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `OrthonormalBasis.coe_toBasis_repr_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
-/
lemma trace_eq_sum_inner (T : E →ₗ[𝕜] E) (b : OrthonormalBasis ι 𝕜 E) :
    T.trace 𝕜 E = ∑ i, ⟪b i, T (b i)⟫_𝕜 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis T]
  apply Fintype.sum_congr
  intro i
  rw [Matrix.diag_apply, T.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply,
    b.repr_apply_apply]

variable [FiniteDimensional 𝕜 E]
variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)
/-
**LinearMap.IsSymmetric.trace_eq_sum_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] {n :
 ℕ} (hn : Module.finrank 𝕜 E = n) {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric),   (Linea
rMap.trace 𝕜 E) T = ↑(∑ i, hT.eigenvalues hn i)
参数：hn : Module.finrank 𝕜 E = n；hT : T.IsSymmetric；LinearMap.trace 𝕜 E；∑ i, hT.ei
genvalues hn i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `Module.End.trace_eq_sum_roots_charpoly_of_splits`：trace_eq_sum_roots_cha
rpoly_of_splits {f : End K V} (h : f.charpoly.Splits) : f.trace K V = f.charpoly
.roots.sum
· 使用定理 `LinearMap.IsSymmetric.splits_charpoly`：splits_charpoly (hT : T.IsSymmetr
ic) : T.charpoly.Splits
· 使用定理 `LinearMap.IsSymmetric.roots_charpoly_eq_eigenvalues`：roots_charpoly_eq_e
igenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : T.charpoly.roots
 = Multiset.map (RCLike.ofReal ∘ hT.eigen…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `List.sum_ofFn`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} {f : Fi
n n → M}, (List.ofFn f).sum = ∑ i, f i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsSymmetric.trace_eq_sum_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    T.trace 𝕜 E = ∑ i, hT.eigenvalues hn i := by
  simp [Module.End.trace_eq_sum_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.sum_ofFn]
/-
**LinearMap.IsSymmetric.re_trace_eq_sum_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] {n :
 ℕ} (hn : Module.finrank 𝕜 E = n) {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric),   RCLike
.re ((LinearMap.trace 𝕜 E) T) = ∑ i, hT.eigenvalues hn i
参数：hn : Module.finrank 𝕜 E = n；hT : T.IsSymmetric；(LinearMap.trace 𝕜 E) T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.trace_eq_sum_eigenvalues`：∀ {𝕜 : Type u_1} {E : Ty
pe u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduct
Space 𝕜 E]   [inst_3 : FiniteDimensi…
· 使用定理 `RCLike.ofReal_re_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (
r : ℝ), RCLike.re ((algebraMap ℝ K) r) = r
-/
lemma IsSymmetric.re_trace_eq_sum_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    RCLike.re (T.trace 𝕜 E) = ∑ i, hT.eigenvalues hn i := by
  rw [hT.trace_eq_sum_eigenvalues]
  exact RCLike.ofReal_re_ax _

open InnerProductSpace in
/-
**LinearMap._root_.InnerProductSpace.trace_rankOne** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.InnerProductSpace.trace_rankOne (x y : E) :
    (rankOne 𝕜 x y).trace 𝕜 E = inner 𝕜 y x := by
  rw [rankOne_def', ContinuousLinearMap.toLinearMap_comp, trace_comp_comm',
    ← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.comp_toSpanSingleton]
  simp [trace_eq_sum_inner _ (OrthonormalBasis.singleton Unit 𝕜)]

end LinearMap

