/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Subspaces associated with orthogonal projections

Here, the orthogonal projection is used to prove a series of more subtle lemmas about the
orthogonal complement of subspaces of `E` (the orthogonal complement itself was
defined in `Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`) such that they admit
orthogonal projections; the lemma
`Submodule.sup_orthogonal_of_hasOrthogonalProjection`,
stating that for a subspace `K` of `E` such that `K` admits an orthogonal projection we have
`K ⊔ Kᗮ = ⊤`, is a typical example.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)

namespace Submodule

/-- If `K₁` admits an orthogonal projection and is contained in `K₂`,
then `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
/-
**Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule`。
形式化陈述：sup_orthogonal_inf_of_hasOrthogonalProjection {K₁ K₂ : Submodule 𝕜 E} (h :
 K₁ <= K₂) [K₁.HasOrthogonalProjection] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂
参数：h : K₁ <= K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
If `K₁` admits an orthogonal projection and is contained in `K₂`,
then `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`.
-/
theorem sup_orthogonal_inf_of_hasOrthogonalProjection {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂)
    [K₁.HasOrthogonalProjection] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂ := by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjectionOnto K₁ x
  have hvm : x - v ∈ K₁ᗮ := sub_starProjection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel _ _⟩

variable {K} in
/-- If `K` admits an orthogonal projection, then `K` and `Kᗮ` span the whole space. -/
/-
**Submodule.sup_orthogonal_of_hasOrthogonalProjection** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：sup_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : K 
⊔ Kᗮ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`：sup_orthogonal_
inf_of_hasOrthogonalProjection {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂) [K₁.HasOrt
hogonalProjection] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
If `K` admits an orthogonal projection, then `K` and `Kᗮ` span the whole space.
-/
theorem sup_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤ := by
  convert Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (le_top : K ≤ ⊤)
  simp

/-- If `K` admits an orthogonal projection, then the orthogonal complement of its orthogonal
complement is itself. -/
@[simp]
/-
**Submodule.orthogonal_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_orthogonal [K.HasOrthogonalProjection] : Kᗮᗮ = K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Submodule.exists_add_mem_mem_orthogonal`：exists_add_mem_mem_orthogonal [
K.HasOrthogonalProjection] (v : E) : exists y in K, exists z in Kᗮ, v = y + z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0

--- 原说明 ---
If `K` admits an orthogonal projection, then the orthogonal complement of its or
thogonal
complement is itself.
-/
theorem orthogonal_orthogonal [K.HasOrthogonalProjection] : Kᗮᗮ = K := by
  ext v
  constructor
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    intro hv
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm]
      simpa [inner_add_right, hyz] using hv z hz
    simp [hy, hz']
  · intro hv w hw
    rw [inner_eq_zero_symm]
    exact hw v hv
/-
**Submodule.orthogonal_le_orthogonal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_le_orthogonal_iff {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProj
ection] [K₁.HasOrthogonalProjection] : K₀ᗮ <= K₁ᗮ ↔ K₁ <= K₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
-/
lemma orthogonal_le_orthogonal_iff {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ ≤ K₁ᗮ ↔ K₁ ≤ K₀ :=
  ⟨fun h ↦ by simpa using orthogonal_le h, orthogonal_le⟩
/-
**Submodule.orthogonal_le_iff_orthogonal_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule
`。
形式化陈述：orthogonal_le_iff_orthogonal_le {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalP
rojection] [K₁.HasOrthogonalProjection] : K₀ᗮ <= K₁ ↔ K₁ᗮ <= K₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.orthogonal_le_orthogonal_iff`：orthogonal_le_orthogonal_iff {K₀
 K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection] [K₁.HasOrthogonalProjection] :
 K₀ᗮ <= K₁ᗮ ↔ K₁ <= K₀
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma orthogonal_le_iff_orthogonal_le {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ ≤ K₁ ↔ K₁ᗮ ≤ K₀ := by
  rw [← orthogonal_le_orthogonal_iff, orthogonal_orthogonal]
/-
**Submodule.le_orthogonal_iff_le_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Submodule
`。
形式化陈述：le_orthogonal_iff_le_orthogonal {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalP
rojection] [K₁.HasOrthogonalProjection] : K₀ <= K₁ᗮ ↔ K₁ <= K₀ᗮ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.orthogonal_le_orthogonal_iff`：orthogonal_le_orthogonal_iff {K₀
 K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection] [K₁.HasOrthogonalProjection] :
 K₀ᗮ <= K₁ᗮ ↔ K₁ <= K₀
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_orthogonal_iff_le_orthogonal {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ ≤ K₁ᗮ ↔ K₁ ≤ K₀ᗮ := by
  rw [← orthogonal_le_orthogonal_iff, orthogonal_orthogonal]

/-- In a Hilbert space, the orthogonal complement of the orthogonal complement of a subspace `K`
is the topological closure of `K`.

Note that the completeness assumption is necessary. Let `E` be the space `ℕ →₀ ℝ` with inner space
structure inherited from `PiLp 2 (fun _ : ℕ ↦ ℝ)`. Let `K` be the subspace of sequences with the sum
of all elements equal to zero. Then `Kᗮ = ⊥`, `Kᗮᗮ = ⊤`. -/
/-
**Submodule.orthogonal_orthogonal_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：orthogonal_orthogonal_eq_closure [CompleteSpace E] : Kᗮᗮ = K.topologicalCl
osure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `Submodule.orthogonal_orthogonal_monotone`：orthogonal_orthogonal_monotone
 {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂) : K₁ᗮᗮ <= K₂ᗮᗮ
· 使用定理 `Submodule.le_topologicalClosure`：Submodule.le_topologicalClosure (s : Su
bmodule R M) : s <= s.topologicalClosure
· 使用定理 `Submodule.topologicalClosure_minimal`：Submodule.topologicalClosure_minim
al (s : Submodule R M) {t : Submodule R M} (h : s <= t) (ht : IsClosed (t : Set 
M)) : s.topologicalClosure…
· 使用定理 `Submodule.le_orthogonal_orthogonal`：le_orthogonal_orthogonal : K <= Kᗮᗮ
· 使用定理 `Submodule.isClosed_orthogonal`：isClosed_orthogonal : IsClosed (Kᗮ : Set 
E)

--- 原说明 ---
In a Hilbert space, the orthogonal complement of the orthogonal complement of a 
subspace `K`
is the topological closure of `K`.

Note that the completeness assumption is necessary. Let `E` be the space `ℕ →₀ ℝ
` with inner space
structure inherited from `PiLp 2 (fun _ : ℕ ↦ ℝ)`. Let `K` be the subspace of se
quences with the sum
of all elements equal to zero. Then `Kᗮ = ⊥`, `Kᗮᗮ = ⊤`.
-/
theorem orthogonal_orthogonal_eq_closure [CompleteSpace E] :
    Kᗮᗮ = K.topologicalClosure := by
  refine le_antisymm ?_ ?_
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure
    rw [K.topologicalClosure.orthogonal_orthogonal]
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal

variable {K}

@[deprecated isCompl_orthogonal (since := "2026-05-07")]
/-
**Submodule.isCompl_orthogonal_of_hasOrthogonalProjection** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule`。
形式化陈述：isCompl_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] 
: IsCompl K Kᗮ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
-/
theorem isCompl_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : IsCompl K Kᗮ :=
  K.isCompl_orthogonal

@[simp]
/-
**Submodule.orthogonalComplement_eq_orthogonalComplement** 是 Mathlib 中的一个定理，位于命名
空间 `Submodule`。
形式化陈述：orthogonalComplement_eq_orthogonalComplement {L : Submodule 𝕜 E} [K.HasOrt
hogonalProjection] [L.HasOrthogonalProjection] : Kᗮ = Lᗮ ↔ K = L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
-/
theorem orthogonalComplement_eq_orthogonalComplement {L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : Kᗮ = Lᗮ ↔ K = L :=
  ⟨fun h ↦ by simpa using congr(Submodule.orthogonal $(h)),
    fun h ↦ congr(Submodule.orthogonal $(h))⟩

@[simp]
/-
**Submodule.orthogonal_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_eq_bot_iff [K.HasOrthogonalProjection] : Kᗮ = ⊥ ↔ K = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sup_orthogonal_of_hasOrthogonalProjection`：sup_orthogonal_of_h
asOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Submodule.top_orthogonal_eq_bot`：top_orthogonal_eq_bot : (⊤ : Submodule 
𝕜 E)ᗮ = ⊥
-/
theorem orthogonal_eq_bot_iff [K.HasOrthogonalProjection] : Kᗮ = ⊥ ↔ K = ⊤ := by
  refine ⟨?_, fun h => by rw [h, Submodule.top_orthogonal_eq_bot]⟩
  intro h
  have : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rwa [h, sup_comm, bot_sup_eq] at this

open Topology Finsupp RCLike Real Filter

/-- Given a monotone family `U` of complete submodules of `E` and a fixed `x : E`,
the orthogonal projection of `x` on `U i` tends to the orthogonal projection of `x` on
`(⨆ i, U i).topologicalClosure` along `atTop`. -/
/-
**Submodule.starProjection_tendsto_closure_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：starProjection_tendsto_closure_iSup {ι : Type*} [Preorder ι] (U : ι -> Sub
module 𝕜 E) [forall i, (U i).HasOrthogonalProjection] [(⨆ i, U i).topologicalClo
sure.HasOrthogonalProjection] (hU : Monotone U) (x : E) : Filter.Tendsto (fun i 
=> (U i).starProjection x) atTop (𝓝 ((⨆ i, U i).topologicalClosure.starProjectio
n x))
参数：U : ι -> Submodule 𝕜 E；U i；⨆ i, U i；hU : Monotone U；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Filter.Tendsto.of_neBot_imp`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {la : Filter α} {lb : Filter β},   (la.NeBot → Filter.Tendsto f la lb) → Filter
.Tendsto f la lb
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.orthogonalProjectionOnto_starProjection_of_le`：orthogonalProje
ctionOnto_starProjection_of_le {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
 [V.HasOrthogonalProjection] (h : U <= V) (x …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Submodule.le_topologicalClosure`：Submodule.le_topologicalClosure (s : Su
bmodule R M) : s <= s.topologicalClosure
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `Submodule.topologicalClosure_coe`：Submodule.topologicalClosure_coe (s : 
Submodule R M) : (s.topologicalClosure : Set M) = closure (s : Set M)
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [Nonempty ι] (S
 : ι -> Submodule R M) (H : Directed (· <= ·) S) {x} : x in iSup S ↔ exists i, x
 in S i
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `Submodule.starProjection_minimal`：starProjection_minimal {U : Submodule 
𝕜 E} [U.HasOrthogonalProjection] (y : E) : ‖y - U.starProjection y‖ = ⨅ x : U, ‖
y - x‖
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Given a monotone family `U` of complete submodules of `E` and a fixed `x : E`,
the orthogonal projection of `x` on `U i` tends to the orthogonal projection of 
`x` on
`(⨆ i, U i).topologicalClosure` along `atTop`.
-/
theorem starProjection_tendsto_closure_iSup {ι : Type*} [Preorder ι]
    (U : ι → Submodule 𝕜 E) [∀ i, (U i).HasOrthogonalProjection]
    [(⨆ i, U i).topologicalClosure.HasOrthogonalProjection] (hU : Monotone U) (x : E) :
    Filter.Tendsto (fun i => (U i).starProjection x) atTop
      (𝓝 ((⨆ i, U i).topologicalClosure.starProjection x)) := by
  refine .of_neBot_imp fun h ↦ ?_
  cases atTop_neBot_iff.mp h
  let y := (⨆ i, U i).topologicalClosure.starProjection x
  have proj_x : ∀ i, (U i).orthogonalProjectionOnto x = (U i).orthogonalProjectionOnto y := fun i =>
    (orthogonalProjectionOnto_starProjection_of_le
        ((le_iSup U i).trans (iSup U).le_topologicalClosure) _).symm
  suffices ∀ ε > 0, ∃ I, ∀ i ≥ I, ‖(U i).starProjection y - y‖ < ε by
    simpa only [starProjection_apply, proj_x, NormedAddCommGroup.tendsto_atTop] using! this
  intro ε hε
  obtain ⟨a, ha, hay⟩ : ∃ a ∈ ⨆ i, U i, dist y a < ε := by
    have y_mem : y ∈ (⨆ i, U i).topologicalClosure := Submodule.coe_mem _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at y_mem
    exact y_mem ε hε
  rw [dist_eq_norm] at hay
  obtain ⟨I, hI⟩ : ∃ I, a ∈ U I := by rwa [Submodule.mem_iSup_of_directed _ hU.directed_le] at ha
  refine ⟨I, fun i (hi : I ≤ i) => ?_⟩
  rw [norm_sub_rev, starProjection_minimal]
  refine lt_of_le_of_lt ?_ hay
  change _ ≤ ‖y - (⟨a, hU hi hI⟩ : U i)‖
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _

/-- Given a monotone family `U` of complete submodules of `E` with dense span supremum,
and a fixed `x : E`, the orthogonal projection of `x` on `U i` tends to `x` along `at_top`. -/
/-
**Submodule.starProjection_tendsto_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_tendsto_self {ι : Type*} [Preorder ι] (U : ι -> Submodule 𝕜
 E) [forall t, (U t).HasOrthogonalProjection] (hU : Monotone U) (x : E) (hU' : ⊤
 <= (⨆ t, U t).topologicalClosure) : Filter.Tendsto (fun t => (U t).starProjecti
on x) atTop (𝓝 x)
参数：U : ι -> Submodule 𝕜 E；U t；hU : Monotone U；x : E；hU' : ⊤ <= (⨆ t, U t).topolo
gicalClosure。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Submodule.instHasOrthogonalProjectionTop`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E],   ⊤.HasOrthogonalProject…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
· 使用定理 `Submodule.starProjection_tendsto_closure_iSup`：starProjection_tendsto_cl
osure_iSup {ι : Type*} [Preorder ι] (U : ι -> Submodule 𝕜 E) [forall i, (U i).Ha
sOrthogonalProjection] [(⨆ i, U i).…

--- 原说明 ---
Given a monotone family `U` of complete submodules of `E` with dense span suprem
um,
and a fixed `x : E`, the orthogonal projection of `x` on `U i` tends to `x` alon
g `at_top`.
-/
theorem starProjection_tendsto_self {ι : Type*} [Preorder ι]
    (U : ι → Submodule 𝕜 E) [∀ t, (U t).HasOrthogonalProjection] (hU : Monotone U) (x : E)
    (hU' : ⊤ ≤ (⨆ t, U t).topologicalClosure) :
    Filter.Tendsto (fun t => (U t).starProjection x) atTop (𝓝 x) := by
  have : (⨆ i, U i).topologicalClosure.HasOrthogonalProjection := by
    rw [top_unique hU']
    infer_instance
  convert! starProjection_tendsto_closure_iSup U hU x
  rw [eq_comm, starProjection_eq_self_iff, top_unique hU']
  trivial

/-- The orthogonal complement satisfies `Kᗮᗮᗮ = Kᗮ`. -/
/-
**Submodule.triorthogonal_eq_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：triorthogonal_eq_orthogonal : Kᗮᗮᗮ = Kᗮ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `Submodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Submodule 𝕜 
E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
The orthogonal complement satisfies `Kᗮᗮᗮ = Kᗮ`.
-/
theorem triorthogonal_eq_orthogonal : Kᗮᗮᗮ = Kᗮ :=
  (orthogonal_gc 𝕜 E).u_l_u_eq_u K

/-- The closure of `K` is the full space iff `Kᗮ` is trivial. -/
/-
**Submodule.topologicalClosure_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：topologicalClosure_eq_top_iff [CompleteSpace E] : K.topologicalClosure = ⊤
 ↔ Kᗮ = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.orthogonal_orthogonal_eq_closure`：orthogonal_orthogonal_eq_clo
sure [CompleteSpace E] : Kᗮᗮ = K.topologicalClosure
· 使用定理 `Submodule.triorthogonal_eq_orthogonal`：triorthogonal_eq_orthogonal : Kᗮᗮ
ᗮ = Kᗮ
· 使用定理 `Submodule.top_orthogonal_eq_bot`：top_orthogonal_eq_bot : (⊤ : Submodule 
𝕜 E)ᗮ = ⊥
· 使用定理 `Submodule.bot_orthogonal_eq_top`：bot_orthogonal_eq_top : (⊥ : Submodule 
𝕜 E)ᗮ = ⊤

--- 原说明 ---
The closure of `K` is the full space iff `Kᗮ` is trivial.
-/
theorem topologicalClosure_eq_top_iff [CompleteSpace E] :
    K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥ := by
  rw [← K.orthogonal_orthogonal_eq_closure]
  constructor <;> intro h
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
  · rw [h, Submodule.bot_orthogonal_eq_top]
/-
**Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto** 是 Mathlib 中的一个定理，
位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_apply_eq_projectionOnto [K.HasOrthogonalProjectio
n] (x : E) : K.orthogonalProjectionOnto x = K.projectionOnto _ K.isCompl_orthogo
nal x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orthogonalProjectionOnto_apply_eq_projectionOnto [K.HasOrthogonalProjection] (x : E) :
    K.orthogonalProjectionOnto x = K.projectionOnto _ K.isCompl_orthogonal x := rfl

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_apply_eq_linearProjOfIsCompl :=
  orthogonalProjectionOnto_apply_eq_projectionOnto
/-
**Submodule.toLinearMap_orthogonalProjectionOnto_eq_projectionOnto** 是 Mathlib 中
的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearMap_orthogonalProjectionOnto_eq_projectionOnto [K.HasOrthogonalPro
jection] : (K.orthogonalProjectionOnto : E ->ₗ[𝕜] K) = K.projectionOnto _ K.isCo
mpl_orthogonal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_orthogonalProjectionOnto_eq_projectionOnto [K.HasOrthogonalProjection] :
    (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) = K.projectionOnto _ K.isCompl_orthogonal := rfl

@[deprecated (since := "2026-05-05")]
alias toLinearMap_orthogonalProjection_eq_linearProjOfIsCompl :=
  toLinearMap_orthogonalProjectionOnto_eq_projectionOnto

open Submodule in
/-
**Submodule.toLinearMap_starProjection_eq_isComplProjection** 是 Mathlib 中的一个定理，位
于命名空间 `Submodule`。
形式化陈述：toLinearMap_starProjection_eq_isComplProjection [K.HasOrthogonalProjection
] : K.starProjection.toLinearMap = K.projection Kᗮ K.isCompl_orthogonal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_starProjection_eq_isComplProjection [K.HasOrthogonalProjection] :
    K.starProjection.toLinearMap = K.projection Kᗮ K.isCompl_orthogonal := rfl

open Submodule in
/-
**Submodule.starProjection_apply_eq_isComplProjection** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：starProjection_apply_eq_isComplProjection [K.HasOrthogonalProjection] (x :
 E) : K.starProjection x = K.projection Kᗮ K.isCompl_orthogonal x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starProjection_apply_eq_isComplProjection [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x = K.projection Kᗮ K.isCompl_orthogonal x := rfl

end Submodule

namespace Dense

open Submodule

variable {K} {x y : E}

/-
**Dense.eq_zero_of_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：eq_zero_of_mem_orthogonal (hK : Dense (K : Set E)) (h : x in Kᗮ) : x = 0
参数：hK : Dense (K : Set E)；h : x in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.eq_zero_of_inner_left`：Dense.eq_zero_of_inner_left (hS : Dense S) 
(h : forall v in S, ⟪x, v⟫ = 0) : x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_orthogonal'`：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u 
in K, ⟪v, u⟫ = 0
-/
theorem eq_zero_of_mem_orthogonal (hK : Dense (K : Set E)) (h : x ∈ Kᗮ) : x = 0 :=
  eq_zero_of_inner_left 𝕜 hK fun _ ↦ (mem_orthogonal' _ _).1 h _

/-- If `S` is dense and `x - y ∈ Kᗮ`, then `x = y`. -/
/-
**Dense.eq_of_sub_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：eq_of_sub_mem_orthogonal (hK : Dense (K : Set E)) (h : x - y in Kᗮ) : x = 
y
参数：hK : Dense (K : Set E)；h : x - y in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Dense.eq_zero_of_mem_orthogonal`：eq_zero_of_mem_orthogonal (hK : Dense (
K : Set E)) (h : x in Kᗮ) : x = 0

--- 原说明 ---
If `S` is dense and `x - y ∈ Kᗮ`, then `x = y`.
-/
theorem eq_of_sub_mem_orthogonal (hK : Dense (K : Set E)) (h : x - y ∈ Kᗮ) : x = y :=
  sub_eq_zero.1 <| eq_zero_of_mem_orthogonal hK h

end Dense

namespace ClosedSubmodule

@[simp]
/-
**ClosedSubmodule.orthogonal_orthogonal_eq** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubm
odule`。
形式化陈述：orthogonal_orthogonal_eq (K : ClosedSubmodule 𝕜 E) [K.HasOrthogonalProject
ion] : (Kᗮ)ᗮ = K
参数：K : ClosedSubmodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orthogonal_orthogonal_eq (K : ClosedSubmodule 𝕜 E) [K.HasOrthogonalProjection] :
    (Kᗮ)ᗮ = K := by ext x; simp
/-
**ClosedSubmodule.orthogonal_eq_orthogonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Closed
Submodule`。
形式化陈述：orthogonal_eq_orthogonal_iff (K₁ K₂ : ClosedSubmodule 𝕜 E) [K₁.HasOrthogon
alProjection] [K₂.HasOrthogonalProjection] : K₁ᗮ = K₂ᗮ ↔ K₁ = K₂
参数：K₁ K₂ : ClosedSubmodule 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.orthogonal_orthogonal_eq`：orthogonal_orthogonal_eq (K : 
ClosedSubmodule 𝕜 E) [K.HasOrthogonalProjection] : (Kᗮ)ᗮ = K
-/
theorem orthogonal_eq_orthogonal_iff (K₁ K₂ : ClosedSubmodule 𝕜 E) [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] : K₁ᗮ = K₂ᗮ ↔ K₁ = K₂ :=
  ⟨fun h ↦ by simpa using congr($hᗮ), fun h ↦ congr($hᗮ)⟩
/-
**ClosedSubmodule.orthogonal_injective** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodul
e`。
形式化陈述：orthogonal_injective [CompleteSpace E] : Function.Injective (fun K : Close
dSubmodule 𝕜 E => Kᗮ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ClosedSubmodule.orthogonal_eq_orthogonal_iff`：orthogonal_eq_orthogonal_i
ff (K₁ K₂ : ClosedSubmodule 𝕜 E) [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalP
rojection] : K₁ᗮ = K₂ᗮ ↔ K₁ = K₂
· 使用定理 `Submodule.instHasOrthogonalProjectionOfCompleteSpace`：∀ {𝕜 : Type u_1} {
E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   (K : ClosedSubmodule 𝕜 …
-/
theorem orthogonal_injective [CompleteSpace E] :
    Function.Injective (fun K : ClosedSubmodule 𝕜 E ↦ Kᗮ) :=
  (orthogonal_eq_orthogonal_iff · · |>.mp)

/-- The sup of two orthogonal subspaces equals the subspace orthogonal
to the inf. -/
/-
**ClosedSubmodule.sup_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：sup_orthogonal [CompleteSpace E] (K₁ K₂ : ClosedSubmodule 𝕜 E) : K₁ᗮ ⊔ K₂ᗮ
 = (K₁ ⊓ K₂)ᗮ
参数：K₁ K₂ : ClosedSubmodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.orthogonal_orthogonal_eq`：orthogonal_orthogonal_eq (K : 
ClosedSubmodule 𝕜 E) [K.HasOrthogonalProjection] : (Kᗮ)ᗮ = K
· 使用定理 `Submodule.instHasOrthogonalProjectionOfCompleteSpace`：∀ {𝕜 : Type u_1} {
E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   (K : ClosedSubmodule 𝕜 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ClosedSubmodule.inf_orthogonal`：inf_orthogonal (K₁ K₂ : ClosedSubmodule 
𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ

--- 原说明 ---
The sup of two orthogonal subspaces equals the subspace orthogonal
to the inf.
-/
theorem sup_orthogonal [CompleteSpace E] (K₁ K₂ : ClosedSubmodule 𝕜 E) :
    K₁ᗮ ⊔ K₂ᗮ = (K₁ ⊓ K₂)ᗮ := by
  simpa using congr($(inf_orthogonal K₁ᗮ K₂ᗮ)ᗮ).symm

end ClosedSubmodule

