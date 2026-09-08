/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-!
# Von Neumann Mean Ergodic Theorem in a Hilbert Space

In this file we prove the von Neumann Mean Ergodic Theorem for an operator in a Hilbert space.
It says that for a contracting linear self-map `f : E →ₗ[𝕜] E` of a Hilbert space,
the Birkhoff averages
```
birkhoffAverage 𝕜 f id N x = (N : 𝕜)⁻¹ • ∑ n ∈ Finset.range N, f^[n] x
```
converge to the orthogonal projection of `x` to the subspace of fixed points of `f`,
see `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`.
-/

public section

open Filter Finset Function Bornology
open scoped Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]

/-- **Von Neumann Mean Ergodic Theorem**, a version for a normed space.

Let `f : E → E` be a contracting linear self-map of a normed space.
Let `S` be the subspace of fixed points of `f`.
Let `g : E → S` be a continuous linear projection, `g|_S=id`.
If the range of `f - id` is dense in the kernel of `g`,
then for each `x`, the Birkhoff averages
```
birkhoffAverage 𝕜 f id N x = (N : 𝕜)⁻¹ • ∑ n ∈ Finset.range N, f^[n] x
```
converge to `g x` as `N → ∞`.

Usually, this fact is not formulated as a separate lemma.
I chose to do it in order to isolate parts of the proof that do not rely
on the inner product space structure.
-/
/-
**LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure [NormedSpace 𝕜 E] 
(f : E ->ₗ[𝕜] E) (hf : LipschitzWith 1 f) (g : E ->L[𝕜] LinearMap.eqLocus f 1) (
hg_proj : forall x : LinearMap.eqLocus f 1, g x = x) (hg_ker : (g.ker : Set E) s
ubseteq closure (LinearMap.range (f - 1))) (x : E) : Tendsto (birkhoffAverage 𝕜 
f _root_.id · x) atTop (𝓝 (g x))
参数：f : E ->ₗ[𝕜] E；hf : LipschitzWith 1 f；g : E ->L[𝕜] LinearMap.eqLocus f 1；hg_p
roj : forall x : LinearMap.eqLocus f 1, g x = x；hg_ker : (g.ker : Set E) subsete
q closure (LinearMap.range (f - 1))；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `isClosed_setOfPred_tendsto_birkhoffAverage`：isClosed_setOfPred_tendsto_b
irkhoffAverage (hf : LipschitzWith 1 f) (hg : UniformContinuous g) (hl : Continu
ous l) : IsClosed {x | Tendsto (…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `iterate_map_zero`：∀ {M : Type u_10} {F : Type u_11} [inst : Zero M] [ins
t_1 : FunLike F M M] [ZeroHomClass F M M] (f : F) (n : ℕ),   (⇑f)^[n] 0 = 0
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `LipschitzWith.iterate`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {K :
 NNReal} {f : α → α},   LipschitzWith K f → ∀ (n : ℕ), LipschitzWith (K ^ n) f^[
n]
· 使用定理 `iterate_map_sub`：∀ {M : Type u_10} {F : Type u_11} [inst : AddGroup M] [
inst_1 : FunLike F M M] [AddMonoidHomClass F M M] (f : F) (n : ℕ)   (x y : M), (
⇑f)^[…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
**Von Neumann Mean Ergodic Theorem**, a version for a normed space.

Let `f : E → E` be a contracting linear self-map of a normed space.
Let `S` be the subspace of fixed points of `f`.
Let `g : E → S` be a continuous linear projection, `g|_S=id`.
If the range of `f - id` is dense in the kernel of `g`,
then for each `x`, the Birkhoff averages
```
birkhoffAverage 𝕜 f id N x = (N : 𝕜)⁻¹ • ∑ n ∈ Finset.range N, f^[n] x
```
converge to `g x` as `N → ∞`.

Usually, this fact is not formulated as a separate lemma.
I chose to do it in order to isolate parts of the proof that do not rely
on the inner product space structure.
-/
theorem LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure [NormedSpace 𝕜 E]
    (f : E →ₗ[𝕜] E) (hf : LipschitzWith 1 f) (g : E →L[𝕜] LinearMap.eqLocus f 1)
    (hg_proj : ∀ x : LinearMap.eqLocus f 1, g x = x)
    (hg_ker : (g.ker : Set E) ⊆ closure (LinearMap.range (f - 1))) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 (g x)) := by
  /- Any point can be represented as a sum of `y ∈ LinearMap.ker g` and a fixed point `z`. -/
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ y, g y = 0 ∧ ∃ z, IsFixedPt f z ∧ x = y + z :=
    ⟨x - g x, by simp [hg_proj], g x, (g x).2, by simp⟩
  /- For a fixed point, the theorem is trivial,
  so it suffices to prove it for `y ∈ LinearMap.ker g`. -/
  suffices Tendsto (birkhoffAverage 𝕜 f _root_.id · y) atTop (𝓝 0) by
    have hgz : g z = z := congr_arg Subtype.val (hg_proj ⟨z, hz⟩)
    simpa [hy, hgz, birkhoffAverage, birkhoffSum, Finset.sum_add_distrib, smul_add]
      using this.add (hz.tendsto_birkhoffAverage 𝕜 _root_.id)
  /- By continuity, it suffices to prove the theorem on a dense subset of `LinearMap.ker g`.
  By assumption, `LinearMap.range (f - 1)` is dense in the kernel of `g`,
  so it suffices to prove the theorem for `y = f x - x`. -/
  have : IsClosed {x | Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 0)} :=
    isClosed_setOfPred_tendsto_birkhoffAverage 𝕜 hf uniformContinuous_id continuous_const
  refine closure_minimal (Set.forall_mem_range.2 fun x ↦ ?_) this (hg_ker hy)
  /- Finally, for `y = f x - x` the average is equal to the difference between averages
  along the orbits of `f x` and `x`, and most of the terms cancel. -/
  have : IsBounded (Set.range (_root_.id <| f^[·] x)) :=
    isBounded_iff_forall_norm_le.2 ⟨‖x‖, Set.forall_mem_range.2 fun n ↦ by
      have H : f^[n] 0 = 0 := iterate_map_zero (f : E →+ E) n
      simpa [H] using (hf.iterate n).dist_le_mul x 0⟩
  have H : ∀ n x y, f^[n] (x - y) = f^[n] x - f^[n] y := iterate_map_sub (f : E →+ E)
  simpa [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, smul_sub, H]
    using tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜 this

variable [InnerProductSpace 𝕜 E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

set_option backward.isDefEq.respectTransparency false in
/-- **Von Neumann Mean Ergodic Theorem** for an operator in a Hilbert space.
For a contracting continuous linear self-map `f : E →L[𝕜] E` of a Hilbert space, `‖f‖ ≤ 1`,
the Birkhoff averages
```
birkhoffAverage 𝕜 f id N x = (N : 𝕜)⁻¹ • ∑ n ∈ Finset.range N, f^[n] x
```
converge to the orthogonal projection of `x` to the subspace of fixed points of `f`. -/
/-
**ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (f : E ->
L[𝕜] E) (hf : ‖f‖ <= 1) (x : E) : Tendsto (birkhoffAverage 𝕜 f _root_.id · x) at
Top (𝓝 <| (f.eqLocus (1 : E ->L[𝕜] E)).orthogonalProjectionOnto x)
参数：f : E ->L[𝕜] E；hf : ‖f‖ <= 1；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure`：LinearMap.tends
to_birkhoffAverage_of_ker_subset_closure [NormedSpace 𝕜 E] (f : E ->ₗ[𝕜] E) (hf 
: LipschitzWith 1 f) (g : E ->L[𝕜] LinearMap.…
· 使用定理 `LipschitzWith.weaken`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWit
h K f → ∀ …
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`：orthogonalProje
ctionOnto_mem_subspace_eq_self (v : K) : K.orthogonalProjectionOnto v = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_orthogonalProjectionOnto`：ker_orthogonalProjectionOnto : K
.orthogonalProjectionOnto.ker = Kᗮ
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.topologicalClosure_coe`：Submodule.topologicalClosure_coe (s : 
Submodule R M) : (s.topologicalClosure : Set M) = closure (s : Set M)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.orthogonal_orthogonal_eq_closure`：orthogonal_orthogonal_eq_clo
sure [CompleteSpace E] : Kᗮᗮ = K.topologicalClosure
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `eq_of_norm_le_re_inner_eq_norm_sq`：eq_of_norm_le_re_inner_eq_norm_sq {x 
y : E} (hle : ‖x‖ <= ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2) : x = y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `RCLike.re_ofReal_pow`：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^
 n) = a ^ n
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
**Von Neumann Mean Ergodic Theorem** for an operator in a Hilbert space.
For a contracting continuous linear self-map `f : E →L[𝕜] E` of a Hilbert space,
 `‖f‖ ≤ 1`,
the Birkhoff averages
```
birkhoffAverage 𝕜 f id N x = (N : 𝕜)⁻¹ • ∑ n ∈ Finset.range N, f^[n] x
```
converge to the orthogonal projection of `x` to the subspace of fixed points of 
`f`.
-/
theorem ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (f : E →L[𝕜] E)
    (hf : ‖f‖ ≤ 1) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop
      (𝓝 <| (f.eqLocus (1 : E →L[𝕜] E)).orthogonalProjectionOnto x) := by
  /- Due to the previous theorem, it suffices to verify
  that the range of `f - 1` is dense in the orthogonal complement
  to the submodule of fixed points of `f`. -/
  apply (f : E →ₗ[𝕜] E).tendsto_birkhoffAverage_of_ker_subset_closure (f.lipschitz.weaken hf)
  · exact (f.eqLocus (1 : E →L[𝕜] E)).orthogonalProjectionOnto_mem_subspace_eq_self
  · clear x
    /- In other words, we need to verify that any vector that is orthogonal to the range of `f - 1`
    is a fixed point of `f`. -/
    rw [Submodule.ker_orthogonalProjectionOnto, ← Submodule.topologicalClosure_coe,
      SetLike.coe_subset_coe, ← Submodule.orthogonal_orthogonal_eq_closure]
    /- To verify this, we verify `‖f x‖ ≤ ‖x‖` (because `‖f‖ ≤ 1`) and `⟪f x, x⟫ = ‖x‖²`. -/
    refine Submodule.orthogonal_le fun x hx ↦ eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) ?_ ?_
    · simpa using f.le_of_opNorm_le hf x
    · have : ∀ y, ⟪f y, x⟫ = ⟪y, x⟫ := by
        simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero] using hx
      simp [this]
