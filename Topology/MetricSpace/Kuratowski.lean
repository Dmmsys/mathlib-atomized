/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Sets.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℕ, ℝ)`.
Any partially defined Lipschitz map into `ℓ^∞` can be extended to the whole space.

-/

@[expose] public section

noncomputable section


open Set Metric TopologicalSpace NNReal ENNReal lp Function

universe u

variable {α : Type u}

namespace KuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℕ, ℝ) -/


variable {n : ℕ} [MetricSpace α] (x : ℕ → α) (a : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `kuratowskiEmbedding`,
without density assumptions. -/
/-
**KuratowskiEmbedding.embeddingOfSubset** 是 Mathlib 中的一个定义，位于命名空间 `KuratowskiEmb
edding`。
形式化陈述：embeddingOfSubset : ℓ^∞(Nat, Real)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `kuratowskiEmb
edding`,
without density assumptions.
-/
def embeddingOfSubset : ℓ^∞(ℕ, ℝ) :=
  ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply memℓp_infty
    use dist a (x 0)
    rintro - ⟨n, rfl⟩
    exact abs_dist_sub_le _ _ _⟩
/-
**KuratowskiEmbedding.embeddingOfSubset_coe** 是 Mathlib 中的一个定理，位于命名空间 `Kuratowsk
iEmbedding`。
形式化陈述：embeddingOfSubset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0
) (x n)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embeddingOfSubset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/-- The embedding map is always a semi-contraction. -/
/-
**KuratowskiEmbedding.embeddingOfSubset_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `Kurat
owskiEmbedding`。
形式化陈述：embeddingOfSubset_dist_le (a b : α) : dist (embeddingOfSubset x a) (embedd
ingOfSubset x b) <= dist a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `lp.norm_le_of_forall_le`：norm_le_of_forall_le {f : lp E ∞} {C : Real} (h
C : 0 <= C) (hCf : forall i, ‖f i‖ <= C) : ‖f‖ <= C
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `abs_dist_sub_le`：abs_dist_sub_le (x y z : α) : |dist x z - dist y z| <= 
dist x y

--- 原说明 ---
The embedding map is always a semi-contraction.
-/
theorem embeddingOfSubset_dist_le (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b := by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le dist_nonneg fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe]
  convert! abs_dist_sub_le a b (x n) using 2
  ring

/-- When the reference set is dense, the embedding map is an isometry on its image. -/
/-
**KuratowskiEmbedding.embeddingOfSubset_isometry** 是 Mathlib 中的一个定理，位于命名空间 `Kura
towskiEmbedding`。
形式化陈述：embeddingOfSubset_isometry (H : DenseRange x) : Isometry (embeddingOfSubse
t x)
参数：H : DenseRange x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `KuratowskiEmbedding.embeddingOfSubset_dist_le`：embeddingOfSubset_dist_le
 (a b : α) : dist (embeddingOfSubset x a) (embeddingOfSubset x b) <= dist a b
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closure_range_iff`：mem_closure_range_iff {e : β -> α} {a : α}
 : a in closure (range e) ↔ forall ε > 0, exists k : β, dist a (e k) < ε
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
When the reference set is dense, the embedding map is an isometry on its image.
-/
theorem embeddingOfSubset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) := by
  refine Isometry.of_dist_eq fun a b => ?_
  refine (embeddingOfSubset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => ?_)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm control at index n to conclude
  have C : dist b (x n) - dist a (x n) = embeddingOfSubset x b n - embeddingOfSubset x a n := by
    simp only [embeddingOfSubset_coe, sub_sub_sub_cancel_right]
  have :=
    calc
      dist a b ≤ dist a (x n) + dist (x n) b := dist_triangle _ _ _
      _ = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) := by simp [dist_comm]; ring
      _ ≤ 2 * dist a (x n) + |dist b (x n) - dist a (x n)| := by grw [← le_abs_self]
      _ ≤ 2 * (e / 2) + |embeddingOfSubset x b n - embeddingOfSubset x a n| := by
        rw [C]
        gcongr
      _ ≤ 2 * (e / 2) + dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
        gcongr
        simp only [dist_eq_norm]
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero
          (embeddingOfSubset x b - embeddingOfSubset x a) n
      _ = dist (embeddingOfSubset x b) (embeddingOfSubset x a) + e := by ring
  simpa [dist_comm] using this

/-- Every separable metric space embeds isometrically in `ℓ^∞(ℕ)`. -/
/-
**KuratowskiEmbedding.exists_isometric_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Kura
towskiEmbedding`。
形式化陈述：exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α]
 : exists f : α -> ℓ^∞(Nat, Real), Isometry f
参数：α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.countable_iff_exists_subset_range`：countable_iff_exists_subset_range
 [Nonempty α] {s : Set α} : s.Countable ↔ exists f : Nat -> α, s subseteq range 
f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `KuratowskiEmbedding.embeddingOfSubset_isometry`：embeddingOfSubset_isomet
ry (H : DenseRange x) : Isometry (embeddingOfSubset x)
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂

--- 原说明 ---
Every separable metric space embeds isometrically in `ℓ^∞(ℕ)`.
-/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α] :
    ∃ f : α → ℓ^∞(ℕ, ℝ), Isometry f := by
  rcases (univ : Set α).eq_empty_or_nonempty with h | h
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    have : Inhabited α := ⟨basepoint⟩
    have : ∃ s : Set α, s.Countable ∧ Dense s := exists_countable_dense α
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    rcases Set.countable_iff_exists_subset_range.1 S_countable with ⟨x, x_range⟩
    -- Use embeddingOfSubset to construct the desired isometry
    exact ⟨embeddingOfSubset x, embeddingOfSubset_isometry x (S_dense.mono x_range)⟩

end KuratowskiEmbedding

open KuratowskiEmbedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℕ, ℝ)`.
-/
/-
**kuratowskiEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α ->
 ℓ^∞(Nat, Real)
参数：α : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `KuratowskiEmbedding.exists_isometric_embedding`：exists_isometric_embeddi
ng (α : Type u) [MetricSpace α] [SeparableSpace α] : exists f : α -> ℓ^∞(Nat, Re
al), Isometry f

--- 原说明 ---
The Kuratowski embedding is an isometric embedding of a separable metric space i
n `ℓ^∞(ℕ, ℝ)`.
-/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α → ℓ^∞(ℕ, ℝ) :=
  Classical.choose (KuratowskiEmbedding.exists_isometric_embedding α)

/--
The Kuratowski embedding is an isometry.
Theorem 2.1 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]. -/
/-
**kuratowskiEmbedding.isometry** 是 Mathlib 中的一个定理，位于命名空间 `kuratowskiEmbedding`。
形式化陈述：∀ (α : Type u) [inst : MetricSpace α] [inst_1 : TopologicalSpace.Separable
Space α], Isometry (kuratowskiEmbedding α)
参数：α : Type u；kuratowskiEmbedding α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `KuratowskiEmbedding.exists_isometric_embedding`：exists_isometric_embeddi
ng (α : Type u) [MetricSpace α] [SeparableSpace α] : exists f : α -> ℓ^∞(Nat, Re
al), Isometry f

--- 原说明 ---
The Kuratowski embedding is an isometry.
Theorem 2.1 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2
015].
-/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.choose_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
nonrec def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α]
    [Nonempty α] : NonemptyCompacts ℓ^∞(ℕ, ℝ) where
  carrier := range (kuratowskiEmbedding α)
  isCompact' := isCompact_range (kuratowskiEmbedding.isometry α).continuous
  nonempty' := range_nonempty _

/--
A function `f : α → ℓ^∞(ι, ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.

Theorem 2.2 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]

The same result for the case of a finite type `ι` is implemented in
`LipschitzOnWith.extend_pi`.
-/
/-
**LipschitzOnWith.extend_lp_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.extend_lp_infty [PseudoMetricSpace α] {s : Set α} {ι : Typ
e*} {f : α -> ℓ^∞(ι, Real)} {K : Real>=0} (hfl : LipschitzOnWith K f s) : exists
 g : α -> ℓ^∞(ι, Real), LipschitzWith K g ∧ EqOn f g s
参数：ι, Real；hfl : LipschitzOnWith K f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `LipschitzOnWith.extend_real`：LipschitzOnWith.extend_real {f : α -> Real}
 {s : Set α} {K : Real>=0} (hf : LipschitzOnWith K f s) : exists g : α -> Real, 
LipschitzWith K g…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LipschitzOnWith.coordinate`：LipschitzOnWith.coordinate [PseudoMetricSpac
e α] (f : α -> ℓ^∞(ι, Real)) (s : Set α) (K : Real>=0) : LipschitzOnWith K f s ↔
 forall i : ι, L…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `LipschitzWith.const'`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] (b : β) {K : NNReal},   LipschitzWith K 
fun x => b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `LipschitzWith.uniformly_bounded`：LipschitzWith.uniformly_bounded [Pseudo
MetricSpace α] (g : α -> ι -> Real) {K : Real>=0} (hg : forall i, LipschitzWith 
K (g · i)) (a₀ : α) (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lp.norm_apply_le_norm`：norm_apply_le_norm (hp : p != 0) (f : lp E p) (i 
: α) : ‖f i‖ <= ‖f‖
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
· 使用定理 `LipschitzWith.coordinate`：LipschitzWith.coordinate [PseudoMetricSpace α]
 {f : α -> ℓ^∞(ι, Real)} (K : Real>=0) : LipschitzWith K f ↔ forall i : ι, Lipsc
hitzWith K (fu…
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A function `f : α → ℓ^∞(ι, ℝ)` which is `K`-Lipschitz on a subset `s` admits a `
K`-Lipschitz
extension to the whole space.

Theorem 2.2 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2
015]

The same result for the case of a finite type `ι` is implemented in
`LipschitzOnWith.extend_pi`.
-/
theorem LipschitzOnWith.extend_lp_infty [PseudoMetricSpace α] {s : Set α} {ι : Type*}
    {f : α → ℓ^∞(ι, ℝ)} {K : ℝ≥0} (hfl : LipschitzOnWith K f s) :
    ∃ g : α → ℓ^∞(ι, ℝ), LipschitzWith K g ∧ EqOn f g s := by
  -- Construct the coordinate-wise extensions
  rw [LipschitzOnWith.coordinate] at hfl
  have (i : ι) : ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s :=
    LipschitzOnWith.extend_real (hfl i) -- use the nonlinear Hahn-Banach theorem here!
  choose g hgl hgeq using this
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀_in_s⟩
  · exact ⟨0, LipschitzWith.const' 0, by simp⟩
  · -- Show that the extensions are uniformly bounded
    have hf_extb : ∀ a : α, Memℓp (swap g a) ∞ := by
      apply LipschitzWith.uniformly_bounded (swap g) hgl a₀
      use ‖f a₀‖
      rintro - ⟨i, rfl⟩
      simp_rw [← hgeq i ha₀_in_s]
      exact lp.norm_apply_le_norm top_ne_zero (f a₀) i
    -- Construct witness by bundling the function with its certificate of membership in ℓ^∞
    let f_ext' : α → ℓ^∞(ι, ℝ) := fun i ↦ ⟨swap g i, hf_extb i⟩
    refine ⟨f_ext', ?_, ?_⟩
    · rw [LipschitzWith.coordinate]
      exact hgl
    · intro a hyp
      ext i
      exact (hgeq i) hyp
