/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Bases

/-!
# Hilbert sum of a family of inner product spaces

Given a family `(G : ι → Type*) [Π i, InnerProductSpace 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ‖f i‖ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the *Hilbert sum* of the family `G`.  By choosing
`G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this construction.

We also define a *predicate* `IsHilbertSum 𝕜 G V`, where `V : Π i, G i →ₗᵢ[𝕜] E`, expressing that
`V` is an `OrthogonalFamily` and that the associated map `lp G 2 →ₗᵢ[𝕜] E` is surjective.

## Main definitions

* `OrthogonalFamily.linearIsometry`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with
  mutually-orthogonal images, there is an induced isometric embedding of the Hilbert sum of `G`
  into `E`.

* `IsHilbertSum`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E`,
  `IsHilbertSum 𝕜 G V` means that `V` is an `OrthogonalFamily` and that the above
  linear isometry is surjective.

* `IsHilbertSum.linearIsometryEquiv`: If a Hilbert space `E` is a Hilbert sum of the
  inner product spaces `G i` with respect to the family `V : Π i, G i →ₗᵢ[𝕜] E`, then the
  corresponding `OrthogonalFamily.linearIsometry` can be upgraded to a `LinearIsometryEquiv`.

* `HilbertBasis`: We define a *Hilbert basis* of a Hilbert space `E` to be a structure whose single
  field `HilbertBasis.repr` is an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)` (i.e., the Hilbert
  sum of `ι` copies of `𝕜`).  This parallels the definition of `Basis`, in `LinearAlgebra.Basis`,
  as an isomorphism of an `R`-module with `ι →₀ R`.

* `HilbertBasis.instCoeFun`: More conventionally a Hilbert basis is thought of as a family
  `ι → E` of vectors in `E` satisfying certain properties (orthonormality, completeness).  We obtain
  this interpretation of a Hilbert basis `b` by defining `⇑b`, of type `ι → E`, to be the image
  under `b.repr` of `lp.single 2 i (1:𝕜)`.  This parallels the definition `Basis.coeFun` in
  `LinearAlgebra.Basis`.

* `HilbertBasis.mk`: Make a Hilbert basis of `E` from an orthonormal family `v : ι → E` of vectors
  in `E` whose span is dense.  This parallels the definition `Basis.mk` in `LinearAlgebra.Basis`.

* `HilbertBasis.mkOfOrthogonalEqBot`: Make a Hilbert basis of `E` from an orthonormal family
  `v : ι → E` of vectors in `E` whose span has trivial orthogonal complement.

* `HilbertBasis.toUnconditionalSchauderBasis`: Convert a Hilbert basis of `E` into an unconditional
  Schauder basis (`UnconditionalSchauderBasis`), with coordinate functionals `x ↦ ⟪b i, x⟫`.

* `HilbertBasis.toSchauderBasis`: Convert a Hilbert basis of `E` indexed by `ℕ` into a classical
  Schauder basis (`SchauderBasis`).

## Main results

* `lp.instInnerProductSpace`: Construction of the inner product space instance on the Hilbert sum
  `lp G 2`. Note that from the file `Mathlib/Analysis/Normed/Lp/lpSpace.lean`, the space `lp G 2`
  already held a normed space instance (`lp.normedSpace`), and if each `G i` is a Hilbert space
  (i.e., complete), then `lp G 2` was already known to be complete (`lp.completeSpace`). So the work
  here is to define the inner product and show it is compatible.

* `OrthogonalFamily.range_linearIsometry`: Given a family `G` of inner product spaces and a family
  `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with mutually-orthogonal
  images, the image of the embedding `OrthogonalFamily.linearIsometry` of the Hilbert sum of `G`
  into `E` is the closure of the span of the images of the `G i`.

* `HilbertBasis.repr_apply_apply`: Given a Hilbert basis `b` of `E`, the entry `b.repr x i` of
  `x`'s representation in `ℓ²(ι, 𝕜)` is the inner product `⟪b i, x⟫`.

* `HilbertBasis.hasSum_repr`: Given a Hilbert basis `b` of `E`, a vector `x` in `E` can be
  expressed as the "infinite linear combination" `∑' i, b.repr x i • b i` of the basis vectors
  `b i`, with coefficients given by the entries `b.repr x i` of `x`'s representation in `ℓ²(ι, 𝕜)`.

* `exists_hilbertBasis`: A Hilbert space admits a Hilbert basis.

## Keywords

Hilbert space, Hilbert sum, l2, Hilbert basis, unitary equivalence, isometric isomorphism
-/

@[expose] public section

open RCLike Submodule Filter
open scoped NNReal ENNReal ComplexConjugate Topology lp

noncomputable section

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Inner product space structure on `lp G 2` -/


namespace lp

/-
**lp.summable_inner** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：summable_inner (f g : lp G 2) : Summable fun i => ⟪f i, g i⟫
参数：f g : lp G 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `lp.summable_mul`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → N
ormedAddCommGroup (E i)] {p q : ENNReal},   p.toReal.HolderConjugate q.toReal → 
∀ (f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.holderConjugate_iff`：∀ {p q : ℝ}, p.HolderConjugate q ↔ 1 < p ∧ p⁻¹
 + q⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
-/
theorem summable_inner (f g : lp G 2) : Summable fun i => ⟪f i, g i⟫ := by
  -- Apply the Direct Comparison Test, comparing with ∑' i, ‖f i‖ * ‖g i‖ (summable by Hölder)
  refine .of_norm_bounded (lp.summable_mul ?_ f g) ?_
  · rw [Real.holderConjugate_iff]; norm_num
  intro i
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm (𝕜 := 𝕜) _ _
/-
**lp.instInnerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：instInnerProductSpace : InnerProductSpace 𝕜 (lp G 2)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instInnerProductSpace : InnerProductSpace 𝕜 (lp G 2) :=
  { lp.normedAddCommGroup (E := G) (p := 2) with
    inner := fun f g => ∑' i, ⟪f i, g i⟫
    norm_sq_eq_re_inner := fun f => by
      calc
        ‖f‖ ^ 2 = ‖f‖ ^ (2 : ℝ≥0∞).toReal := by norm_cast
        _ = ∑' i, ‖f i‖ ^ (2 : ℝ≥0∞).toReal := lp.norm_rpow_eq_tsum ?_ f
        _ = ∑' i, ‖f i‖ ^ (2 : ℕ) := by norm_cast
        _ = ∑' i, re ⟪f i, f i⟫ := by simp
        _ = re (∑' i, ⟪f i, f i⟫) := (RCLike.reCLM.map_tsum ?_).symm
      · norm_num
      · exact summable_inner f f
    conj_inner_symm := fun f g => by
      calc
        conj _ = conj (∑' i, ⟪g i, f i⟫) := by congr
        _ = ∑' i, conj ⟪g i, f i⟫ := RCLike.conjCLE.map_tsum
        _ = ∑' i, ⟪f i, g i⟫ := by simp only [inner_conj_symm]
        _ = _ := by congr
    add_left := fun f₁ f₂ g => by
      calc
        _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ := ?_
        _ = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) := by
          simp only [inner_add_left, Pi.add_apply, coeFn_add]
        _ = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ := Summable.tsum_add ?_ ?_
        _ = _ := by congr
      · congr
      · exact summable_inner f₁ g
      · exact summable_inner f₂ g
    smul_left := fun f g c => by
      calc
        _ = ∑' i, ⟪c • f i, g i⟫ := ?_
        _ = ∑' i, conj c * ⟪f i, g i⟫ := by simp only [inner_smul_left]
        _ = conj c * ∑' i, ⟪f i, g i⟫ := tsum_mul_left
        _ = _ := ?_
      · simp only [coeFn_smul, Pi.smul_apply]
      · congr }
/-
**lp.inner_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫
参数：f g : lp G 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ :=
  rfl
/-
**lp.hasSum_inner** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫
参数：f g : lp G 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `lp.summable_inner`：summable_inner (f g : lp G 2) : Summable fun i => ⟪f 
i, g i⟫
-/
theorem hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫ :=
  (summable_inner f g).hasSum
/-
**lp.inner_single_left** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：inner_single_left [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) : ⟪lp.sin
gle 2 i a, f⟫ = ⟪a, f i⟫
参数：i : ι；a : G i；f : lp G 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `lp.hasSum_inner`：hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g 
i⟫) ⟪f, g⟫
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasSum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] 
(a …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem inner_single_left [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫ := by
  refine (hasSum_inner (lp.single 2 i a) f).unique ?_
  simp_rw [lp.coeFn_single]
  convert! hasSum_ite_eq i ⟪a, f i⟫ using 1
  ext j
  split_ifs with h
  · subst h; rw [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]
/-
**lp.inner_single_right** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：inner_single_right [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) : ⟪f, lp
.single 2 i a⟫ = ⟪f i, a⟫
参数：i : ι；a : G i；f : lp G 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `lp.inner_single_left`：inner_single_left [DecidableEq ι] (i : ι) (a : G i
) (f : lp G 2) : ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫
-/
theorem inner_single_right [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪f, lp.single 2 i a⟫ = ⟪f i, a⟫ := by
  simpa [inner_conj_symm] using congr_arg conj (inner_single_left (𝕜 := 𝕜) i a f)

end lp

/-! ### Identification of a general Hilbert space `E` with a Hilbert sum -/


namespace OrthogonalFamily

variable [CompleteSpace E] {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 G V)
include hV

/-
**OrthogonalFamily.summable_of_lp** 是 Mathlib 中的一个定理，位于命名空间 `OrthogonalFamily`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E},   OrthogonalFamily 𝕜
 G V → ∀ (f : ↥(lp G 2)), Summable fun i => (V i) (↑f i)
参数：i : ι；G i；i : ι；G i；i : ι；f : ↥(lp G 2)；V i；↑f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthogonalFamily.summable_iff_norm_sq_summable`：OrthogonalFamily.summabl
e_iff_norm_sq_summable [CompleteSpace E] (f : forall i, G i) : (Summable fun i =
> V i (f i)) ↔ Summable fun i => ‖f …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
-/
protected theorem summable_of_lp (f : lp G 2) :
    Summable fun i => V i (f i) := by
  rw [hV.summable_iff_norm_sq_summable]
  convert! (lp.memℓp f).summable _
  · norm_cast
  · norm_num

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
/-
**OrthogonalFamily.linearIsometry** 是 Mathlib 中的一个定义，位于命名空间 `OrthogonalFamily`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_2} →     [inst : RCLike 𝕜] →       {E : Typ
e u_3} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             {G : ι → Type u_4} →               [inst_3 : (i : ι)
 → NormedAddCommGroup (G i)] →                 [inst_4 : (i : ι) → InnerProductS
pace 𝕜 (G i)] →                   [CompleteSpace E] → {V : (i : ι) → G i →ₗᵢ[𝕜] 
E} → OrthogonalFamily 𝕜 G V → ↥(lp G 2) →ₗᵢ[𝕜] E
参数：i : ι；G i；i : ι；G i；i : ι；lp G 2。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
A mutually orthogonal family of subspaces of `E` induce a linear isometry from `
lp 2` of the
subspaces into `E`.
-/
protected def linearIsometry (hV : OrthogonalFamily 𝕜 G V) : lp G 2 →ₗᵢ[𝕜] E where
  toFun f := ∑' i, V i (f i)
  map_add' f g := by
    simp only [(hV.summable_of_lp f).tsum_add (hV.summable_of_lp g), lp.coeFn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coeFn_smul] using!
      (hV.summable_of_lp f).tsum_const_smul c
  norm_map' f := by
    -- needed for lattice instance on `Finset ι`, for `Filter.atTop_neBot`
    have H : 0 < (2 : ℝ≥0∞).toReal := by simp
    suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : ℝ≥0∞).toReal = ‖f‖ ^ (2 : ℝ≥0∞).toReal by
      exact Real.rpow_left_injOn H.ne' (norm_nonneg _) (norm_nonneg _) this
    refine tendsto_nhds_unique ?_ (lp.hasSum_norm H f)
    convert! (hV.summable_of_lp f).hasSum.norm.rpow_const (Or.inr H.le) using 1
    ext s
    exact mod_cast (hV.norm_sum f s).symm
/-
**OrthogonalFamily.linearIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrthogonalFam
ily`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   (hV : Orth
ogonalFamily 𝕜 G V) (f : ↥(lp G 2)), hV.linearIsometry f = ∑' (i : ι), (V i) (↑f
 i)
参数：i : ι；G i；i : ι；G i；i : ι；hV : OrthogonalFamily 𝕜 G V；f : ↥(lp G 2)；i : ι；V i
；↑f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
protected theorem linearIsometry_apply (f : lp G 2) : hV.linearIsometry f = ∑' i, V i (f i) :=
  rfl
/-
**OrthogonalFamily.hasSum_linearIsometry** 是 Mathlib 中的一个定理，位于命名空间 `OrthogonalFa
mily`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   (hV : Orth
ogonalFamily 𝕜 G V) (f : ↥(lp G 2)), HasSum (fun i => (V i) (↑f i)) (hV.linearIs
ometry f)
参数：i : ι；G i；i : ι；G i；i : ι；hV : OrthogonalFamily 𝕜 G V；f : ↥(lp G 2)；fun i => 
(V i) (↑f i)；hV.linearIsometry f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `OrthogonalFamily.summable_of_lp`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst :
 RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProdu
ctSpace 𝕜 E] {G : ι →…
-/
protected theorem hasSum_linearIsometry (f : lp G 2) :
    HasSum (fun i => V i (f i)) (hV.linearIsometry f) :=
  (hV.summable_of_lp f).hasSum

@[simp]
/-
**OrthogonalFamily.linearIsometry_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `Orthog
onalFamily`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   (hV : Orth
ogonalFamily 𝕜 G V) [inst_6 : DecidableEq ι] {i : ι} (x : G i),   hV.linearIsome
try (lp.single 2 i x) = (V i) x
参数：i : ι；G i；i : ι；G i；i : ι；hV : OrthogonalFamily 𝕜 G V；x : G i；lp.single 2 i x
；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthogonalFamily.linearIsometry_apply`：∀ {ι : Type u_1} {𝕜 : Type u_2} [
inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : Inne
rProductSpace 𝕜 E] {G : ι →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] (a
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lp.single_apply`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → N
ormedAddCommGroup (E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E
 i) (…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
-/
protected theorem linearIsometry_apply_single [DecidableEq ι] {i : ι} (x : G i) :
    hV.linearIsometry (lp.single 2 i x) = V i x := by
  rw [hV.linearIsometry_apply, ← tsum_ite_eq i (fun _ ↦ V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [h]
/-
**OrthogonalFamily.linearIsometry_apply_dfinsupp_sum_single** 是 Mathlib 中的一个定理，位
于命名空间 `OrthogonalFamily`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   (hV : Orth
ogonalFamily 𝕜 G V) [inst_6 : DecidableEq ι] [inst_7 : (i : ι) → DecidableEq (G 
i)] (W₀ : Π₀ (i : ι), G i),   hV.linearIsometry (W₀.sum (lp.single 2)) = W₀.sum 
fun i => ⇑(V i)
参数：i : ι；G i；i : ι；G i；i : ι；hV : OrthogonalFamily 𝕜 G V；i : ι；G i；W₀ : Π₀ (i : 
ι), G i；W₀.sum (lp.single 2)；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_dfinsuppSum`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι] 
{R : Type u_1} {S : Type u_2} {H : Type u_3}   [inst_1 : (i : ι) → Zero (β i)] [
inst_…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `DFinsupp.sum.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {i
nst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)] 
{inst_3 : (i …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrthogonalFamily.linearIsometry_apply_single`：∀ {ι : Type u_1} {𝕜 : Type
 u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpace 𝕜 E] {G : ι →…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem linearIsometry_apply_dfinsupp_sum_single [DecidableEq ι] [∀ i, DecidableEq (G i)]
    (W₀ : Π₀ i : ι, G i) : hV.linearIsometry (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
/-
**OrthogonalFamily.range_linearIsometry** 是 Mathlib 中的一个定理，位于命名空间 `OrthogonalFam
ily`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   (hV : Orth
ogonalFamily 𝕜 G V) [∀ (i : ι), CompleteSpace (G i)],   hV.linearIsometry.range 
= (⨆ i, (V i).range).topologicalClosure
参数：i : ι；G i；i : ι；G i；i : ι；hV : OrthogonalFamily 𝕜 G V；i : ι；G i；⨆ i, (V i).ra
nge。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
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
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `OrthogonalFamily.hasSum_linearIsometry`：∀ {ι : Type u_1} {𝕜 : Type u_2} 
[inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : Inn
erProductSpace 𝕜 E] {G : ι →…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `Submodule.topologicalClosure_minimal`：Submodule.topologicalClosure_minim
al (s : Submodule R M) {t : Submodule R M} (h : s <= t) (ht : IsClosed (t : Set 
M)) : s.topologicalClosure…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `OrthogonalFamily.linearIsometry_apply_single`：∀ {ι : Type u_1} {𝕜 : Type
 u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpace 𝕜 E] {G : ι →…
· 使用定理 `IsComplete.isClosed`：IsComplete.isClosed [UniformSpace α] [T0Space α] {s
 : Set α} (h : IsComplete s) : IsClosed s
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The canonical linear isometry from the `lp 2` of a mutually orthogonal family of
 subspaces of
`E` into E, has range the closure of the span of the subspaces.
-/
protected theorem range_linearIsometry [∀ i, CompleteSpace (G i)] :
    LinearMap.range hV.linearIsometry.toLinearMap =
      (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure := by
  classical
  refine le_antisymm ?_ ?_
  · rintro x ⟨f, rfl⟩
    refine mem_closure_of_tendsto (hV.hasSum_linearIsometry f) (Eventually.of_forall ?_)
    intro s
    rw [SetLike.mem_coe]
    refine sum_mem ?_
    intro i _
    refine mem_iSup_of_mem i ?_
    exact LinearMap.mem_range_self _ (f i)
  · apply topologicalClosure_minimal
    · refine iSup_le ?_
      rintro i x ⟨x, rfl⟩
      use lp.single 2 i x
      exact hV.linearIsometry_apply_single x
    exact hV.linearIsometry.isometry.isUniformInducing.isComplete_range.isClosed

end OrthogonalFamily

section IsHilbertSum

variable (𝕜 G)
variable [CompleteSpace E] (V : ∀ i, G i →ₗᵢ[𝕜] E) (F : ι → Submodule 𝕜 E)

/-- Given a family of Hilbert spaces `G : ι → Type*`, a Hilbert sum of `G` consists of a Hilbert
space `E` and an orthogonal family `V : Π i, G i →ₗᵢ[𝕜] E` such that the induced isometry
`Φ : lp G 2 → E` is surjective.

Keeping in mind that `lp G 2` is "the" external Hilbert sum of `G : ι → Type*`, this is analogous
to `DirectSum.IsInternal`, except that we don't express it in terms of actual submodules. -/
/-
**IsHilbertSum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   (𝕜 : Type u_2) →     [inst : RCLike 𝕜] →       {E : Typ
e u_3} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             (G : ι → Type u_4) →               [inst_3 : (i : ι)
 → NormedAddCommGroup (G i)] →                 [inst_4 : (i : ι) → InnerProductS
pace 𝕜 (G i)] → [CompleteSpace E] → ((i : ι) → G i →ₗᵢ[𝕜] E) → Prop
参数：𝕜 : Type u_2；G : ι → Type u_4；i : ι；G i；i : ι；G i；(i : ι) → G i →ₗᵢ[𝕜] E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of Hilbert spaces `G : ι → Type*`, a Hilbert sum of `G` consists 
of a Hilbert
space `E` and an orthogonal family `V : Π i, G i →ₗᵢ[𝕜] E` such that the induced
 isometry
`Φ : lp G 2 → E` is surjective.

Keeping in mind that `lp G 2` is "the" external Hilbert sum of `G : ι → Type*`, 
this is analogous
to `DirectSum.IsInternal`, except that we don't express it in terms of actual su
bmodules.
-/
structure IsHilbertSum : Prop where
  ofSurjective ::
  /-- The orthogonal family constituting the summands in the Hilbert sum. -/
  protected OrthogonalFamily : OrthogonalFamily 𝕜 G V
  /-- The isometry `lp G 2 → E` induced by the orthogonal family is surjective. -/
  protected surjective_isometry : Function.Surjective OrthogonalFamily.linearIsometry

variable {𝕜 G V}

/-- If `V : Π i, G i →ₗᵢ[𝕜] E` is an orthogonal family such that the supremum of the ranges of
`V i` is dense, then `(E, V)` is a Hilbert sum of `G`. -/
/-
**IsHilbertSum.mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHilbertSum.mk [forall i, CompleteSpace <| G i] (hVortho : OrthogonalFami
ly 𝕜 G V) (hVtotal : ⊤ <= (⨆ i, LinearMap.range (V i).toLinearMap).topologicalCl
osure) : IsHilbertSum 𝕜 G V
参数：hVortho : OrthogonalFamily 𝕜 G V；hVtotal : ⊤ <= (⨆ i, LinearMap.range (V i).t
oLinearMap).topologicalClosure。
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometry.coe_toLinearMap`：coe_toLinearMap : ⇑f.toLinearMap = f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `OrthogonalFamily.range_linearIsometry`：∀ {ι : Type u_1} {𝕜 : Type u_2} [
inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : Inne
rProductSpace 𝕜 E] {G : ι →…

--- 原说明 ---
If `V : Π i, G i →ₗᵢ[𝕜] E` is an orthogonal family such that the supremum of the
 ranges of
`V i` is dense, then `(E, V)` is a Hilbert sum of `G`.
-/
theorem IsHilbertSum.mk [∀ i, CompleteSpace <| G i] (hVortho : OrthogonalFamily 𝕜 G V)
    (hVtotal : ⊤ ≤ (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure) :
    IsHilbertSum 𝕜 G V :=
  { OrthogonalFamily := hVortho
    surjective_isometry := by
      rw [← LinearIsometry.coe_toLinearMap]
      exact LinearMap.range_eq_top.mp
        (eq_top_iff.mpr <| hVtotal.trans_eq hVortho.range_linearIsometry.symm) }

/-- This is `Orthonormal.isHilbertSum` in the case of actual inclusions from subspaces. -/
/-
**IsHilbertSum.mkInternal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHilbertSum.mkInternal [forall i, CompleteSpace <| F i] (hFortho : Orthog
onalFamily 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ) (hFtotal : ⊤ <= (⨆ i, F i)
.topologicalClosure) : IsHilbertSum 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ
参数：hFortho : OrthogonalFamily 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ；hFtotal 
: ⊤ <= (⨆ i, F i).topologicalClosure。
该定理/引理给出了一组等式。
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
· 使用定理 `IsHilbertSum.mk`：IsHilbertSum.mk [forall i, CompleteSpace <| G i] (hVort
ho : OrthogonalFamily 𝕜 G V) (hVtotal : ⊤ <= (⨆ i, LinearMap.range (V i).toLinea
rMap)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.topologicalClosure.congr_simp`：∀ {R : Type u} {M : Type v} [in
st : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMonoid M]   [ins
t_3 : _root_.Module R M] [ins…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p

--- 原说明 ---
This is `Orthonormal.isHilbertSum` in the case of actual inclusions from subspac
es.
-/
theorem IsHilbertSum.mkInternal [∀ i, CompleteSpace <| F i]
    (hFortho : OrthogonalFamily 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ)
    (hFtotal : ⊤ ≤ (⨆ i, F i).topologicalClosure) :
    IsHilbertSum 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ :=
  IsHilbertSum.mk hFortho (by simpa [subtypeₗᵢ_toLinearMap, range_subtype] using hFtotal)

/-- *A* Hilbert sum `(E, V)` of `G` is canonically isomorphic to *the* Hilbert sum of `G`,
i.e `lp G 2`.

Note that this goes in the opposite direction from `OrthogonalFamily.linearIsometry`. -/
/-
**IsHilbertSum.linearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsHilbertSum.linearIsometryEquiv (hV : IsHilbertSum 𝕜 G V) : E ≃ₗᵢ[𝕜] lp G
 2
参数：hV : IsHilbertSum 𝕜 G V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsHilbertSum.OrthogonalFamily`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] {G : ι →…
· 使用定理 `IsHilbertSum.surjective_isometry`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst 
: RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProd
uctSpace 𝕜 E] {G : ι →…

--- 原说明 ---
*A* Hilbert sum `(E, V)` of `G` is canonically isomorphic to *the* Hilbert sum o
f `G`,
i.e `lp G 2`.

Note that this goes in the opposite direction from `OrthogonalFamily.linearIsome
try`.
-/
noncomputable def IsHilbertSum.linearIsometryEquiv (hV : IsHilbertSum 𝕜 G V) : E ≃ₗᵢ[𝕜] lp G 2 :=
  LinearIsometryEquiv.symm <|
    LinearIsometryEquiv.ofSurjective hV.OrthogonalFamily.linearIsometry hV.surjective_isometry

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`. -/
/-
**IsHilbertSum.linearIsometryEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsHilbe
rtSum`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   (hV : IsHi
lbertSum 𝕜 G V) (w : ↥(lp G 2)), hV.linearIsometryEquiv.symm w = ∑' (i : ι), (V 
i) (↑w i)
参数：i : ι；G i；i : ι；G i；i : ι；hV : IsHilbertSum 𝕜 G V；w : ↥(lp G 2)；i : ι；V i；↑w 
i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsHilbertSum.OrthogonalFamily`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] {G : ι →…
· 使用定理 `IsHilbertSum.surjective_isometry`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst 
: RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProd
uctSpace 𝕜 E] {G : ι →…
· 使用定理 `LinearIsometryEquiv.coe_ofSurjective`：coe_ofSurjective (f : F ->ₛₗᵢ[σ₁₂]
 E₂) (hfr : Function.Surjective f) : ⇑(LinearIsometryEquiv.ofSurjective f hfr) =
 f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp 
G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated element
s in `E`.
-/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : hV.linearIsometryEquiv.symm w = ∑' i, V i (w i) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`, and this
sum indeed converges. -/
/-
**IsHilbertSum.hasSum_linearIsometryEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsHilb
ertSum`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   (hV : IsHi
lbertSum 𝕜 G V) (w : ↥(lp G 2)), HasSum (fun i => (V i) (↑w i)) (hV.linearIsomet
ryEquiv.symm w)
参数：i : ι；G i；i : ι；G i；i : ι；hV : IsHilbertSum 𝕜 G V；w : ↥(lp G 2)；fun i => (V i
) (↑w i)；hV.linearIsometryEquiv.symm w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsHilbertSum.OrthogonalFamily`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] {G : ι →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsHilbertSum.surjective_isometry`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst 
: RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProd
uctSpace 𝕜 E] {G : ι →…
· 使用定理 `LinearIsometryEquiv.coe_ofSurjective`：coe_ofSurjective (f : F ->ₛₗᵢ[σ₁₂]
 E₂) (hfr : Function.Surjective f) : ⇑(LinearIsometryEquiv.ofSurjective f hfr) =
 f

--- 原说明 ---
In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp 
G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated element
s in `E`, and this
sum indeed converges.
-/
protected theorem IsHilbertSum.hasSum_linearIsometryEquiv_symm (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : HasSum (fun i => V i (w i)) (hV.linearIsometryEquiv.symm w) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.hasSum_linearIsometry]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, an "elementary basis vector" in `lp G 2` supported at `i : ι` is the image of the
associated element in `E`. -/
@[simp]
/-
**IsHilbertSum.linearIsometryEquiv_symm_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `
IsHilbertSum`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   [inst_6 : 
DecidableEq ι] (hV : IsHilbertSum 𝕜 G V) {i : ι} (x : G i),   hV.linearIsometryE
quiv.symm (lp.single 2 i x) = (V i) x
参数：i : ι；G i；i : ι；G i；i : ι；hV : IsHilbertSum 𝕜 G V；x : G i；lp.single 2 i x；V i
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsHilbertSum.OrthogonalFamily`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] {G : ι →…
· 使用定理 `IsHilbertSum.surjective_isometry`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst 
: RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProd
uctSpace 𝕜 E] {G : ι →…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearIsometryEquiv.coe_ofSurjective`：coe_ofSurjective (f : F ->ₛₗᵢ[σ₁₂]
 E₂) (hfr : Function.Surjective f) : ⇑(LinearIsometryEquiv.ofSurjective f hfr) =
 f
· 使用定理 `OrthogonalFamily.linearIsometry_apply_single`：∀ {ι : Type u_1} {𝕜 : Type
 u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpace 𝕜 E] {G : ι →…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Typ
e*` and
`lp G 2`, an "elementary basis vector" in `lp G 2` supported at `i : ι` is the i
mage of the
associated element in `E`.
-/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_single
    [DecidableEq ι] (hV : IsHilbertSum 𝕜 G V) {i : ι} (x : G i) :
    hV.linearIsometryEquiv.symm (lp.single 2 i x) = V i x := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply_single]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
/-
**IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single** 是 Mathlib 中的
一个定理，位于命名空间 `IsHilbertSum`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   [inst_6 : 
DecidableEq ι] [inst_7 : (i : ι) → DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) 
(W₀ : Π₀ (i : ι), G i),   hV.linearIsometryEquiv.symm (W₀.sum (lp.single 2)) = W
₀.sum fun i => ⇑(V i)
参数：i : ι；G i；i : ι；G i；i : ι；i : ι；G i；hV : IsHilbertSum 𝕜 G V；W₀ : Π₀ (i : ι), 
G i；W₀.sum (lp.single 2)；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_dfinsuppSum`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι] 
{R : Type u_1} {S : Type u_2} {H : Type u_3}   [inst_1 : (i : ι) → Zero (β i)] [
inst_…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `DFinsupp.sum.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {i
nst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)] 
{inst_3 : (i …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsHilbertSum.linearIsometryEquiv_symm_apply_single`：∀ {ι : Type u_1} {𝕜 
: Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [
inst_2 : InnerProductSpace 𝕜 E] {G : ι →…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Typ
e*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated
 finite sum of
elements of `E`.
-/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single
    [DecidableEq ι] [∀ i, DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    hV.linearIsometryEquiv.symm (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp only [map_dfinsuppSum, IsHilbertSum.linearIsometryEquiv_symm_apply_single]

set_option backward.isDefEq.respectTransparency false in
/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp]
/-
**IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single** 是 Mathlib 中的一个定理，
位于命名空间 `IsHilbertSum`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι → Type u_4} [in
st_3 : (i : ι) → NormedAddCommGroup (G i)]   [inst_4 : (i : ι) → InnerProductSpa
ce 𝕜 (G i)] [inst_5 : CompleteSpace E] {V : (i : ι) → G i →ₗᵢ[𝕜] E}   [inst_6 : 
DecidableEq ι] [inst_7 : (i : ι) → DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) 
(W₀ : Π₀ (i : ι), G i),   ↑(W₀.sum fun a b => hV.linearIsometryEquiv ((V a) b)) 
= ⇑W₀
参数：i : ι；G i；i : ι；G i；i : ι；i : ι；G i；hV : IsHilbertSum 𝕜 G V；W₀ : Π₀ (i : ι), 
G i；W₀.sum fun a b => hV.linearIsometryEquiv ((V a) b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_dfinsuppSum`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι] 
{R : Type u_1} {S : Type u_2} {H : Type u_3}   [inst_1 : (i : ι) → Zero (β i)] [
inst_…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single`：∀ {ι : 
Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCom
mGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {G : ι →…
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddSubgroup.val_finsetSum`：∀ {ι : Type u_3} {G : Type u_4} [inst : AddCo
mmGroup G] (H : AddSubgroup G) (f : ι → ↥H) (s : Finset ι),   ↑(∑ i ∈ s, f i) = 
∑ i ∈ s, ↑(f i)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_pi_single`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : Decida
bleEq ι] [inst_1 : (a : ι) → AddCommMonoid (M a)] (a : ι)   (f : (a : ι) → M a) 
(s : Finse…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Typ
e*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated
 finite sum of
elements of `E`.
-/
protected theorem IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single
    [DecidableEq ι] [∀ i, DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    ((W₀.sum (γ := lp G 2) fun a b ↦ hV.linearIsometryEquiv (V a b)) : ∀ i, G i) = W₀ := by
  rw [← map_dfinsuppSum]
  rw [← hV.linearIsometryEquiv_symm_apply_dfinsupp_sum_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp +contextual [DFinsupp.sum, lp.single_apply]

/-- Given a total orthonormal family `v : ι → E`, `E` is a Hilbert sum of `fun i : ι => 𝕜`
relative to the family of linear isometries `fun i k => k • v i`. -/
/-
**Orthonormal.isHilbertSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.isHilbertSum {v : ι -> E} (hv : Orthonormal 𝕜 v) (hsp : ⊤ <= (
span 𝕜 (Set.range v)).topologicalClosure) : IsHilbertSum 𝕜 (fun _ : ι => 𝕜) fun 
i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i)
参数：hv : Orthonormal 𝕜 v；hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure。
该定理/引理给出了一组等式。
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
· 使用定理 `IsHilbertSum.mk`：IsHilbertSum.mk [forall i, CompleteSpace <| G i] (hVort
ho : OrthogonalFamily 𝕜 G V) (hVtotal : ⊤ <= (⨆ i, LinearMap.range (V i).toLinea
rMap)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `Orthonormal.orthogonalFamily`：Orthonormal.orthogonalFamily {v : ι -> E} 
(hv : Orthonormal 𝕜 v) : OrthogonalFamily 𝕜 (fun _i : ι => 𝕜) fun i => LinearIso
metry.toSpanSingle…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a total orthonormal family `v : ι → E`, `E` is a Hilbert sum of `fun i : ι
 => 𝕜`
relative to the family of linear isometries `fun i k => k • v i`.
-/
theorem Orthonormal.isHilbertSum {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    IsHilbertSum 𝕜 (fun _ : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  IsHilbertSum.mk hv.orthogonalFamily (by
    convert! hsp
    simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion])
/-
**Submodule.isHilbertSumOrthogonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isHilbertSumOrthogonal (K : Submodule 𝕜 E) [hK : CompleteSpace K
] : IsHilbertSum 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ
参数：K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsHilbertSum.mkInternal`：IsHilbertSum.mkInternal [forall i, CompleteSpac
e <| F i] (hFortho : OrthogonalFamily 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ)
 (hFtotal : ⊤…
· 使用定理 `Submodule.orthogonalFamily_self`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst :
 RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (K
 : Submodule 𝕜 E), Or…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
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
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `cond.eq_2`：∀ {α : Sort u} (x y : α), (bif false then x else y) = y
· 使用定理 `Codisjoint.top_le`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → ⊤ ≤ a ⊔ b
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `Submodule.le_topologicalClosure`：Submodule.le_topologicalClosure (s : Su
bmodule R M) : s <= s.topologicalClosure
-/
theorem Submodule.isHilbertSumOrthogonal (K : Submodule 𝕜 E) [hK : CompleteSpace K] :
    IsHilbertSum 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ := by
  have : ∀ b, CompleteSpace (↥(cond b K Kᗮ)) := by
    intro b
    cases b <;> first | exact instOrthogonalCompleteSpace K | assumption
  refine IsHilbertSum.mkInternal _ K.orthogonalFamily_self ?_
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  rw [iSup_bool_eq, cond, cond]
  refine Codisjoint.top_le ?_
  exact K.isCompl_orthogonal.codisjoint

end IsHilbertSum

/-! ### Hilbert bases -/


section

variable (ι) (𝕜) (E)

/-- A Hilbert basis on `ι` for an inner product space `E` is an identification of `E` with the `lp`
space `ℓ²(ι, 𝕜)`. -/
/-
**HilbertBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 →   (𝕜 : Type u_2) →     [inst : RCLike 𝕜] →       (E : Type u_3)
 → [inst_1 : NormedAddCommGroup E] → [InnerProductSpace 𝕜 E] → Type (max (max u_
1 u_2) u_3)
参数：𝕜 : Type u_2；E : Type u_3；max (max u_1 u_2) u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hilbert basis on `ι` for an inner product space `E` is an identification of `E
` with the `lp`
space `ℓ²(ι, 𝕜)`.
-/
structure HilbertBasis where ofRepr ::
  /-- The linear isometric equivalence implementing identifying the Hilbert space with `ℓ²`. -/
  repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)

end

namespace HilbertBasis

/-
**HilbertBasis.** 是 Mathlib 中的一个实例，位于命名空间 `HilbertBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} : Inhabited (HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) :=
  ⟨ofRepr (LinearIsometryEquiv.refl 𝕜 _)⟩

open scoped Classical in
/-- `b i` is the `i`th basis vector. -/
/-
**HilbertBasis.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `HilbertBasis`。
形式化陈述：instFunLike : FunLike (HilbertBasis ι 𝕜 E) ι E where coe b i
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
`b i` is the `i`th basis vector.
-/
instance instFunLike : FunLike (HilbertBasis ι 𝕜 E) ι E where
  coe b i := b.repr.symm (lp.single 2 i (1 : 𝕜))
  coe_injective
  | ⟨b₁⟩, ⟨b₂⟩, h => by
    congr
    apply LinearIsometryEquiv.symm_bijective.injective
    apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
    apply ContinuousLinearEquiv.coe_injective
    refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun i => ?_
    ext
    exact congr_fun h i

@[simp]
/-
**HilbertBasis.repr_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : DecidableEq 
ι] (b : HilbertBasis ι 𝕜 E) (i : ι),   b.repr.symm (lp.single 2 i 1) = b i
参数：b : HilbertBasis ι 𝕜 E；i : ι；lp.single 2 i 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
protected theorem repr_symm_single [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (lp.single 2 i (1 : 𝕜)) = b i := by
  dsimp +instances [instFunLike]
  convert! rfl
/-
**HilbertBasis.repr_self** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : DecidableEq 
ι] (b : HilbertBasis ι 𝕜 E) (i : ι),   b.repr (b i) = lp.single 2 i 1
参数：b : HilbertBasis ι 𝕜 E；i : ι；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HilbertBasis.repr_symm_single`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] [inst_3 …
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem repr_self [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = lp.single 2 i (1 : 𝕜) := by
  simp only [LinearIsometryEquiv.apply_symm_apply, ← b.repr_symm_single]
/-
**HilbertBasis.repr_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E) (v : E) (i : ι), ↑(b.repr v) i = inner 𝕜 (b i) v
参数：b : HilbertBasis ι 𝕜 E；v : E；i : ι；b.repr v；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `HilbertBasis.repr_self`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜
] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜
 E] [inst_3 …
· 使用定理 `lp.inner_single_left`：inner_single_left [DecidableEq ι] (i : ι) (a : G i
) (f : lp G 2) : ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem repr_apply_apply (b : HilbertBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  classical
  rw [← b.repr.inner_map_map (b i) v, b.repr_self, lp.inner_single_left]
  simp

@[simp]
/-
**HilbertBasis.orthonormal** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E), Orthonormal 𝕜 ⇑b
参数：b : HilbertBasis ι 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `HilbertBasis.repr_self`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜
] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜
 E] [inst_3 …
· 使用定理 `lp.inner_single_left`：inner_single_left [DecidableEq ι] (i : ι) (a : G i
) (f : lp G 2) : ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫
· 使用定理 `lp.single_apply`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → N
ormedAddCommGroup (E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E
 i) (…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem orthonormal (b : HilbertBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self, b.repr_self, lp.inner_single_left,
    lp.single_apply, Pi.single_apply]
  simp
/-
**HilbertBasis.hasSum_repr_symm** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E) (f : ↥(lp (fun x => 𝕜) 2)),   HasSum (fun i => ↑f i • b i) (b.repr.symm f)
参数：b : HilbertBasis ι 𝕜 E；f : ↥(lp (fun x => 𝕜) 2)；fun i => ↑f i • b i；b.repr.sy
mm f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `lp.single_smul`：∀ {𝕜 : Type u_1} {α : Type u_3} {E : α → Type u_4} [inst
 : (i : α) → NormedAddCommGroup (E i)] [inst_1 : NormedRing 𝕜]   [inst_2 : (i : 
α) →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `HilbertBasis.repr_self`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜
] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜
 E] [inst_3 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearIsometryEquiv.coe_toContinuousLinearEquiv`：coe_toContinuousLinearE
quiv : ⇑e.toContinuousLinearEquiv = e
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `lp.hasSum_single`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [ins
t : (i : α) → NormedAddCommGroup (E i)] [inst_1 : DecidableEq α]   [inst_2 : Fac
t (1 ≤…
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
-/
protected theorem hasSum_repr_symm (b : HilbertBasis ι 𝕜 E) (f : ℓ²(ι, 𝕜)) :
    HasSum (fun i => f i • b i) (b.repr.symm f) := by
  classical
  suffices H : (fun i : ι => f i • b i) = fun b_1 : ι => b.repr.symm.toContinuousLinearEquiv <|
      (fun i : ι => lp.single 2 i (f i) (E := (fun _ : ι => 𝕜))) b_1 by
    rw [H]
    have : HasSum (fun i : ι => lp.single 2 i (f i)) f := lp.hasSum_single ENNReal.ofNat_ne_top f
    exact (↑b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, 𝕜) →L[𝕜] E).hasSum this
  ext i
  apply b.repr.injective
  let : NormedSpace 𝕜 (lp (fun _i : ι => 𝕜) 2) := by infer_instance
  have : lp.single (E := (fun _ : ι => 𝕜)) 2 i (f i * 1) = f i • lp.single 2 i 1 :=
    lp.single_smul (E := (fun _ : ι => 𝕜)) 2 i (f i) (1 : 𝕜)
  rw [mul_one] at this
  rw [map_smul, b.repr_self, ← this, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm
/-
**HilbertBasis.hasSum_repr** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E) (x : E), HasSum (fun i => ↑(b.repr x) i • b i) x
参数：b : HilbertBasis ι 𝕜 E；x : E；fun i => ↑(b.repr x) i • b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `HilbertBasis.hasSum_repr_symm`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] (b : Hil…
-/
protected theorem hasSum_repr (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => b.repr x i • b i) x := by simpa using b.hasSum_repr_symm (b.repr x)

@[simp]
/-
**HilbertBasis.dense_span** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E), (Submodule.span 𝕜 (Set.range ⇑b)).topologicalClosure = ⊤
参数：b : HilbertBasis ι 𝕜 E；Submodule.span 𝕜 (Set.range ⇑b)。
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
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HilbertBasis.hasSum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] (b : Hil…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
protected theorem dense_span (b : HilbertBasis ι 𝕜 E) :
    (span 𝕜 (Set.range b)).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  refine mem_closure_of_tendsto (b.hasSum_repr x) (Eventually.of_forall ?_)
  intro s
  simp only [SetLike.mem_coe]
  refine sum_mem ?_
  rintro i -
  refine smul_mem _ _ ?_
  exact subset_span ⟨i, rfl⟩
/-
**HilbertBasis.hasSum_inner_mul_inner** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E) (x y : E),   HasSum (fun i => inner 𝕜 x (b i) * inner 𝕜 (b i) y) (inner 𝕜 x y
)
参数：b : HilbertBasis ι 𝕜 E；x y : E；fun i => inner 𝕜 x (b i) * inner 𝕜 (b i) y；inn
er 𝕜 x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `innerSL_apply_apply`：innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v,
 w⟫
· 使用定理 `HilbertBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] (b : Hil…
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasSum.mapL`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u
_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddC
o…
· 使用定理 `HilbertBasis.hasSum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] (b : Hil…
-/
protected theorem hasSum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    HasSum (fun i => ⟪x, b i⟫ * ⟪b i, y⟫) ⟪x, y⟫ := by
  convert! (b.hasSum_repr y).mapL (innerSL 𝕜 x) using 1
  ext i
  rw [innerSL_apply_apply, b.repr_apply_apply, inner_smul_right, mul_comm]
/-
**HilbertBasis.summable_inner_mul_inner** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`
。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E) (x y : E),   Summable fun i => inner 𝕜 x (b i) * inner 𝕜 (b i) y
参数：b : HilbertBasis ι 𝕜 E；x y : E；b i；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HilbertBasis.hasSum_inner_mul_inner`：∀ {ι : Type u_1} {𝕜 : Type u_2} [in
st : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] (b : Hil…
-/
protected theorem summable_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    Summable fun i => ⟪x, b i⟫ * ⟪b i, y⟫ :=
  (b.hasSum_inner_mul_inner x y).summable
/-
**HilbertBasis.tsum_inner_mul_inner** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 
E) (x y : E),   ∑' (i : ι), inner 𝕜 x (b i) * inner 𝕜 (b i) y = inner 𝕜 x y
参数：b : HilbertBasis ι 𝕜 E；x y : E；i : ι；b i；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HilbertBasis.hasSum_inner_mul_inner`：∀ {ι : Type u_1} {𝕜 : Type u_2} [in
st : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] (b : Hil…
-/
protected theorem tsum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    ∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ :=
  (b.hasSum_inner_mul_inner x y).tsum_eq

-- Note: this should be `b.repr` composed with an identification of `lp (fun i : ι => 𝕜) p` with
-- `PiLp p (fun i : ι => 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- A finite Hilbert basis is an orthonormal basis. -/
/-
**HilbertBasis.toOrthonormalBasis** 是 Mathlib 中的一个定义，位于命名空间 `HilbertBasis`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_2} →     [inst : RCLike 𝕜] →       {E : Typ
e u_3} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] → [inst_3 : Fintype ι] → HilbertBasis ι 𝕜 E → OrthonormalBasis ι 𝕜
 E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HilbertBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] (b : Hil…

--- 原说明 ---
A finite Hilbert basis is an orthonormal basis.
-/
protected def toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk b.orthonormal
    (by
      refine Eq.ge ?_
      classical
      have := (span 𝕜 (Finset.univ.image b : Set E)).closed_of_finiteDimensional
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, HilbertBasis.dense_span] using
        this.submodule_topologicalClosure_eq.symm)

@[simp]
/-
**HilbertBasis.coe_toOrthonormalBasis** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：coe_toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) : (b.toOrthono
rmalBasis : ι -> E) = b
参数：b : HilbertBasis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthonormalBasis.coe_mk`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 
𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 
𝕜 E] [inst_3 …
· 使用定理 `HilbertBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] (b : Hil…
-/
theorem coe_toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    (b.toOrthonormalBasis : ι → E) = b :=
  OrthonormalBasis.coe_mk _ _

/-- A Hilbert basis of is an unconditional Schauder basis (`UnconditionalSchauderBasis`),
with coordinate functionals `x ↦ ⟪b i, x⟫`. The basis expansion `x = ∑' i, ⟪b i, x⟫ • b i`
converges unconditionally. -/
@[simps]
/-
**HilbertBasis.toUnconditionalSchauderBasis** 是 Mathlib 中的一个定义，位于命名空间 `HilbertBa
sis`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_2} →     [inst : RCLike 𝕜] →       {E : Typ
e u_3} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] → HilbertBasis ι 𝕜 E → UnconditionalSchauderBasis ι 𝕜 E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hilbert basis of is an unconditional Schauder basis (`UnconditionalSchauderBas
is`),
with coordinate functionals `x ↦ ⟪b i, x⟫`. The basis expansion `x = ∑' i, ⟪b i,
 x⟫ • b i`
converges unconditionally.
-/
protected def toUnconditionalSchauderBasis (b : HilbertBasis ι 𝕜 E) :
    UnconditionalSchauderBasis ι 𝕜 E where
  basis := b
  coord i := innerSL 𝕜 (b i)
  ortho i j := by
    classical
    simpa [innerSL_apply_apply, Pi.single_apply] using orthonormal_iff_ite.mp b.orthonormal i j
  expansion x := by
    simpa only [innerSL_apply_apply, ← b.repr_apply_apply] using b.hasSum_repr x

/-- Every Hilbert basis indexed by `ℕ` is a Schauder basis (`SchauderBasis`) with
coordinate functionals `x ↦ ⟪b i, x⟫`. The expansion `x = ∑ i, ⟪b i, x⟫ • b i` converges. -/
@[simps]
/-
**HilbertBasis.toSchauderBasis** 是 Mathlib 中的一个定义，位于命名空间 `HilbertBasis`。
形式化陈述：{𝕜 : Type u_2} →   [inst : RCLike 𝕜] →     {E : Type u_3} →       [inst_1 
: NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → HilbertBasis ℕ 𝕜 E 
→ SchauderBasis 𝕜 E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Hilbert basis indexed by `ℕ` is a Schauder basis (`SchauderBasis`) with
coordinate functionals `x ↦ ⟪b i, x⟫`. The expansion `x = ∑ i, ⟪b i, x⟫ • b i` c
onverges.
-/
protected def toSchauderBasis (b : HilbertBasis ℕ 𝕜 E) : SchauderBasis 𝕜 E where
  basis := ⇑b
  coord i := innerSL 𝕜 (b i)
  ortho := b.toUnconditionalSchauderBasis.ortho
  expansion x := (b.toUnconditionalSchauderBasis.expansion x).mono_left SummationFilter.le_atTop
/-
**HilbertBasis.hasSum_orthogonalProjectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Hilber
tBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {U : Submodule 𝕜 E} [i
nst_3 : CompleteSpace ↥U] (b : HilbertBasis ι 𝕜 ↥U) (x : E),   HasSum (fun i => 
inner 𝕜 (↑(b i)) x • b i) (U.orthogonalProjectionOnto x)
参数：b : HilbertBasis ι 𝕜 ↥U；x : E；fun i => inner 𝕜 (↑(b i)) x • b i；U.orthogonalP
rojectionOnto x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HilbertBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] (b : Hil…
· 使用定理 `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left`：inner_orthogona
lProjectionOnto_eq_of_mem_left [K.HasOrthogonalProjection] (u : K) (v : E) : ⟪u,
 K.orthogonalProjectionOnto v⟫ = ⟪(u : E), v⟫
· 使用定理 `HilbertBasis.hasSum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] (b : Hil…
-/
protected theorem hasSum_orthogonalProjectionOnto {U : Submodule 𝕜 E} [CompleteSpace U]
    (b : HilbertBasis ι 𝕜 U) (x : E) :
    HasSum (fun i => ⟪(b i : E), x⟫ • b i) (U.orthogonalProjectionOnto x) := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    b.hasSum_repr (U.orthogonalProjectionOnto x)

@[deprecated (since := "2026-05-05")] alias hasSum_orthogonalProjection :=
  HilbertBasis.hasSum_orthogonalProjectionOnto
/-
**HilbertBasis.finite_spans_dense** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：finite_spans_dense [DecidableEq E] (b : HilbertBasis ι 𝕜 E) : (⨆ J : Finse
t ι, span 𝕜 (J.image b : Set E)).topologicalClosure = ⊤
参数：b : HilbertBasis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `HilbertBasis.dense_span`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 
𝕜 E] (b : Hil…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.topologicalClosure.congr_simp`：∀ {R : Type u} {M : Type v} [in
st : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMonoid M]   [ins
t_3 : _root_.Module R M] [ins…
· 使用定理 `Submodule.topologicalClosure_mono`：Submodule.topologicalClosure_mono {s 
: Submodule R M} {t : Submodule R M} (h : s <= t) : s.topologicalClosure <= t.to
pologicalClosure
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem finite_spans_dense [DecidableEq E] (b : HilbertBasis ι 𝕜 E) :
    (⨆ J : Finset ι, span 𝕜 (J.image b : Set E)).topologicalClosure = ⊤ :=
  eq_top_iff.mpr <| b.dense_span.ge.trans (by
    simp_rw [← Submodule.span_iUnion]
    exact topologicalClosure_mono (span_mono <| Set.range_subset_iff.mpr fun i =>
      Set.mem_iUnion_of_mem {i} <| Finset.mem_coe.mpr <| Finset.mem_image_of_mem _ <|
      Finset.mem_singleton_self i))

variable [CompleteSpace E]

section
variable {v : ι → E} (hv : Orthonormal 𝕜 v)
include hv

/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
/-
**HilbertBasis.mk** 是 Mathlib 中的一个定义，位于命名空间 `HilbertBasis`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_2} →     [inst : RCLike 𝕜] →       {E : Typ
e u_3} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             [CompleteSpace E] →               {v : ι → E} →     
            Orthonormal 𝕜 v → ⊤ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalCl
osure → HilbertBasis ι 𝕜 E
参数：Submodule.span 𝕜 (Set.range v)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.isHilbertSum`：Orthonormal.isHilbertSum {v : ι -> E} (hv : Or
thonormal 𝕜 v) (hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure) : IsHilber
tSum 𝕜 (fun _ …

--- 原说明 ---
An orthonormal family of vectors whose span is dense in the whole module is a Hi
lbert basis.
-/
protected def mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.ofRepr <| (hv.isHilbertSum hsp).linearIsometryEquiv
/-
**HilbertBasis._root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one** 是 
Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one [DecidableEq ι] (h i) :
    (hv.isHilbertSum h).linearIsometryEquiv.symm (lp.single 2 i 1) = v i := by
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single, LinearIsometry.toSpanSingleton_apply,
    one_smul]

@[simp]
/-
**HilbertBasis.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpac
e E] {v : ι → E} (hv : Orthonormal 𝕜 v)   (hsp : ⊤ ≤ (Submodule.span 𝕜 (Set.rang
e v)).topologicalClosure), ⇑(HilbertBasis.mk hv hsp) = v
参数：hv : Orthonormal 𝕜 v；hsp : ⊤ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalCl
osure；HilbertBasis.mk hv hsp。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Orthonormal.isHilbertSum`：Orthonormal.isHilbertSum {v : ι -> E} (hv : Or
thonormal 𝕜 v) (hsp : ⊤ <= (span 𝕜 (Set.range v)).topologicalClosure) : IsHilber
tSum 𝕜 (fun _ …
· 使用定理 `Orthonormal.linearIsometryEquiv_symm_apply_single_one`：∀ {ι : Type u_1} 
{𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E] 
  [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
-/
protected theorem coe_mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    ⇑(HilbertBasis.mk hv hsp) = v := by
  classical
  apply funext <| Orthonormal.linearIsometryEquiv_symm_apply_single_one hv hsp

/-- An orthonormal family of vectors whose span has trivial orthogonal complement is a Hilbert
basis. -/
/-
**HilbertBasis.mkOfOrthogonalEqBot** 是 Mathlib 中的一个定义，位于命名空间 `HilbertBasis`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_2} →     [inst : RCLike 𝕜] →       {E : Typ
e u_3} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             [CompleteSpace E] →               {v : ι → E} → Orth
onormal 𝕜 v → (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ → HilbertBasis ι 𝕜 E
参数：Submodule.span 𝕜 (Set.range v)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orthonormal family of vectors whose span has trivial orthogonal complement is
 a Hilbert
basis.
-/
protected def mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk hv
    (by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])

@[simp]
/-
**HilbertBasis.coe_mkOfOrthogonalEqBot** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpac
e E] {v : ι → E} (hv : Orthonormal 𝕜 v)   (hsp : (Submodule.span 𝕜 (Set.range v)
)ᗮ = ⊥), ⇑(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v
参数：hv : Orthonormal 𝕜 v；hsp : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥；HilbertBasis
.mkOfOrthogonalEqBot hv hsp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HilbertBasis.coe_mk`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E]
 [inst_3 …
-/
protected theorem coe_mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    ⇑(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v :=
  HilbertBasis.coe_mk hv _

-- Note : this should be `b.repr` composed with an identification of `lp (fun i : ι => 𝕜) p` with
-- `PiLp p (fun i : ι => 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- An orthonormal basis is a Hilbert basis. -/
/-
**HilbertBasis._root_.OrthonormalBasis.toHilbertBasis** 是 Mathlib 中的一个定义，位于命名空间 
`HilbertBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orthonormal basis is a Hilbert basis.
-/
protected def _root_.OrthonormalBasis.toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk b.orthonormal <| by
    simpa only [← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq, eq_top_iff] using!
      @subset_closure E _ _

end

@[simp]
/-
**HilbertBasis._root_.OrthonormalBasis.coe_toHilbertBasis** 是 Mathlib 中的一个定理，位于命
名空间 `HilbertBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrthonormalBasis.coe_toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    (b.toHilbertBasis : ι → E) = b :=
  HilbertBasis.coe_mk _ _

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
/-
**HilbertBasis._root_.Orthonormal.exists_hilbertBasis_extension** 是 Mathlib 中的一个
定理，位于命名空间 `HilbertBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hilbert space admits a Hilbert basis extending a given orthonormal subset.
-/
theorem _root_.Orthonormal.exists_hilbertBasis_extension {s : Set E}
    (hs : Orthonormal 𝕜 ((↑) : s → E)) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), s ⊆ w ∧ ⇑b = ((↑) : w → E) :=
  let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs
  ⟨w, HilbertBasis.mkOfOrthogonalEqBot hw_ortho
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq,
      maximal_orthonormal_iff_orthogonalComplement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_mkOfOrthogonalEqBot _ _⟩

variable (𝕜 E)

/-- A Hilbert space admits a Hilbert basis. -/
/-
**HilbertBasis._root_.exists_hilbertBasis** 是 Mathlib 中的一个定理，位于命名空间 `HilbertBasi
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hilbert space admits a Hilbert basis.
-/
theorem _root_.exists_hilbertBasis : ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbertBasis_extension
  ⟨w, hw, hw''⟩

end HilbertBasis

