/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of degree `n` is the ring homomorphism
`K →+* ℂ^n` that sends `x ∈ K` to `(φ_₁(x),...,φ_n(x))` where the `φ_i`'s are the complex
embeddings of `K`. Note that we do not choose an ordering of the embeddings, but instead map `K`
into the type `(K →+* ℂ) → ℂ` of `ℂ`-vectors indexed by the complex embeddings.

## Main definitions and results

* `NumberField.canonicalEmbedding`: the ring homomorphism `K →+* ((K →+* ℂ) → ℂ)` defined by
  sending `x : K` to the vector `(φ x)` indexed by `φ : K →+* ℂ`.

* `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`: the intersection of the
  image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
  radius is finite.

* `NumberField.mixedEmbedding`: the ring homomorphism from `K` to the mixed space
  `K →+* ({ w // IsReal w } → ℝ) × ({ w // IsComplex w } → ℂ)` that sends `x ∈ K` to `(φ_w x)_w`
  where `φ_w` is the embedding associated to the infinite place `w`. In particular, if `w` is real
  then `φ_w : K →+* ℝ` and, if `w` is complex, `φ_w` is an arbitrary choice between the two complex
  embeddings defining the place `w`.

## Tags

number field, infinite places
-/

@[expose] public section

open Module

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

/-- The canonical embedding of a number field `K` of degree `n` into `ℂ^n`. -/
/-
**NumberField.canonicalEmbedding._root_.NumberField.canonicalEmbedding** 是 Mathl
ib 中的一个定义，位于命名空间 `NumberField.canonicalEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical embedding of a number field `K` of degree `n` into `ℂ^n`.
-/
def _root_.NumberField.canonicalEmbedding : K →+* ((K →+* ℂ) → ℂ) := RingHom.pi fun φ => φ
/-
**NumberField.canonicalEmbedding._root_.NumberField.canonicalEmbedding_injective
** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.canonicalEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NumberField.canonicalEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.canonicalEmbedding K) := RingHom.injective _

variable {K}

@[simp]
/-
**NumberField.canonicalEmbedding.apply_at** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.canonicalEmbedding`。
形式化陈述：apply_at (φ : K ->+* Complex) (x : K) : (NumberField.canonicalEmbedding K 
x) φ = φ x
参数：φ : K ->+* Complex；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_at (φ : K →+* ℂ) (x : K) : (NumberField.canonicalEmbedding K x) φ = φ x := rfl

open scoped ComplexConjugate

/-- The image of `canonicalEmbedding` lives in the `ℝ`-submodule of the `x ∈ ((K →+* ℂ) → ℂ)` such
that `conj x_φ = x_(conj φ)` for all `φ : K →+* ℂ`. -/
/-
**NumberField.canonicalEmbedding.conj_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.canonicalEmbedding`。
形式化陈述：conj_apply {x : ((K ->+* Complex) -> Complex)} (φ : K ->+* Complex) (hx : 
x in Submodule.span Real (Set.range (canonicalEmbedding K))) : conj (x φ) = x (C
omplexEmbedding.conjugate φ)
参数：(K ->+* Complex) -> Complex；φ : K ->+* Complex；hx : x in Submodule.span Real 
(Set.range (canonicalEmbedding K))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.canonicalEmbedding.apply_at`：apply_at (φ : K ->+* Complex) (
x : K) : (NumberField.canonicalEmbedding K x) φ = φ x
· 使用定理 `NumberField.ComplexEmbedding.conjugate_coe_eq`：conjugate_coe_eq (φ : K -
>+* Complex) (x : K) : (conjugate φ) x = conj (φ x)
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `Complex.real_smul`：real_smul {x : Real} {z : Complex} : x • z = x * z
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r

--- 原说明 ---
The image of `canonicalEmbedding` lives in the `ℝ`-submodule of the `x ∈ ((K →+*
 ℂ) → ℂ)` such
that `conj x_φ = x_(conj φ)` for all `φ : K →+* ℂ`.
-/
theorem conj_apply {x : ((K →+* ℂ) → ℂ)} (φ : K →+* ℂ)
    (hx : x ∈ Submodule.span ℝ (Set.range (canonicalEmbedding K))) :
    conj (x φ) = x (ComplexEmbedding.conjugate φ) := by
  refine Submodule.span_induction ?_ ?_ (fun _ _ _ _ hx hy => ?_) (fun a _ _ hx => ?_) hx
  · rintro _ ⟨x, rfl⟩
    rw [apply_at, apply_at, ComplexEmbedding.conjugate_coe_eq]
  · rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [Pi.add_apply, Pi.add_apply, map_add, hx, hy]
  · rw [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    exact congrArg ((a : ℂ) * ·) hx
/-
**NumberField.canonicalEmbedding.nnnorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.canonicalEmbedding`。
形式化陈述：nnnorm_eq [NumberField K] (x : K) : ‖canonicalEmbedding K x‖₊ = Finset.uni
v.sup (fun φ : K ->+* Complex => ‖φ x‖₊)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_eq [NumberField K] (x : K) :
    ‖canonicalEmbedding K x‖₊ = Finset.univ.sup (fun φ : K →+* ℂ => ‖φ x‖₊) := by
  simp_rw [Pi.nnnorm_def, apply_at]
/-
**NumberField.canonicalEmbedding.norm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.canonicalEmbedding`。
形式化陈述：norm_le_iff [NumberField K] (x : K) (r : Real) : ‖canonicalEmbedding K x‖ 
<= r ↔ forall φ : K ->+* Complex, ‖φ x‖ <= r
参数：x : K；r : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.canonicalEmbedding.nnnorm_eq`：nnnorm_eq [NumberField K] (x :
 K) : ‖canonicalEmbedding K x‖₊ = Finset.univ.sup (fun φ : K ->+* Complex => ‖φ 
x‖₊)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem norm_le_iff [NumberField K] (x : K) (r : ℝ) :
    ‖canonicalEmbedding K x‖ ≤ r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
  obtain hr | hr := lt_or_ge r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    refine iff_of_false ?_ ?_
    · exact (hr.trans_le (norm_nonneg _)).not_ge
    · exact fun h => hr.not_ge (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left]

variable (K)

/-- The image of `𝓞 K` as a subring of `ℂ^n`. -/
/-
**NumberField.canonicalEmbedding.integerLattice** 是 Mathlib 中的一个定义，位于命名空间 `Numbe
rField.canonicalEmbedding`。
形式化陈述：integerLattice : Subring ((K ->+* Complex) -> Complex)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `𝓞 K` as a subring of `ℂ^n`.
-/
def integerLattice : Subring ((K →+* ℂ) → ℂ) :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)
/-
**NumberField.canonicalEmbedding.integerLattice.inter_ball_finite** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.canonicalEmbedding.integerLattice`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (r : ℝ),   (↑(N
umberField.canonicalEmbedding.integerLattice K) ∩ Metric.closedBall 0 r).Finite
参数：K : Type u_1；r : ℝ；↑(NumberField.canonicalEmbedding.integerLattice K) ∩ Metri
c.closedBall 0 r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.canonicalEmbedding.norm_le_iff`：norm_le_iff [NumberField K] 
(x : K) (r : Real) : ‖canonicalEmbedding K x‖ <= r ↔ forall φ : K ->+* Complex, 
‖φ x‖ <= r
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `NumberField.Embeddings.finite_of_norm_le`：finite_of_norm_le (B : Real) :
 {x : K | IsIntegral Int x ∧ forall φ : K ->+* A, ‖φ x‖ <= B}.Finite
-/
theorem integerLattice.inter_ball_finite [NumberField K] (r : ℝ) :
    ((integerLattice K : Set ((K →+* ℂ) → ℂ)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | _ := lt_or_ge r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : ∀ x, canonicalEmbedding K x ∈ Metric.closedBall 0 r ↔
        ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert! (Embeddings.finite_of_norm_le K ℂ r).image (canonicalEmbedding K)
    ext; constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx⟩
      exact ⟨x, ⟨SetLike.coe_mem x, fun φ => (heq _).mp hx φ⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩

/-- A `ℂ`-basis of `ℂ^n` that is also a `ℤ`-basis of the `integerLattice`. -/
/-
**NumberField.canonicalEmbedding.latticeBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberF
ield.canonicalEmbedding`。
形式化陈述：latticeBasis [NumberField K] : Basis (Free.ChooseBasisIndex Int (𝓞 K)) Com
plex ((K ->+* Complex) -> Complex)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K

--- 原说明 ---
A `ℂ`-basis of `ℂ^n` that is also a `ℤ`-basis of the `integerLattice`.
-/
noncomputable def latticeBasis [NumberField K] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ ((K →+* ℂ) → ℂ) := by
  classical
  -- Let `B` be the canonical basis of `(K →+* ℂ) → ℂ`. We prove that the determinant of
  -- the image by `canonicalEmbedding` of the integral basis of `K` is nonzero. This
  -- will imply the result.
    let B := Pi.basisFun ℂ (K →+* ℂ)
    let e : (K →+* ℂ) ≃ Free.ChooseBasisIndex ℤ (𝓞 K) :=
      Fintype.equivOfCardEq ((Embeddings.card K ℂ).trans (finrank_eq_card_basis (integralBasis K)))
    let M := B.toMatrix (fun i => canonicalEmbedding K (integralBasis K (e i)))
    suffices M.det ≠ 0 by
      rw [← isUnit_iff_ne_zero, ← Basis.det_apply, ← Basis.is_basis_iff_det] at this
      exact (basisOfPiSpaceOfLinearIndependent this.1).reindex e
  -- In order to prove that the determinant is nonzero, we show that it is equal to the
  -- square of the discriminant of the integral basis and thus it is not zero
    let N := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => integralBasis K (e i))
      (RingHom.equivRatAlgHom K ℂ)
    rw [show M = N.transpose by { ext : 2; rfl }]
    rw [Matrix.det_transpose, ← pow_ne_zero_iff two_ne_zero]
    convert!
      (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
        (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
    rw [← Algebra.discr_reindex ℚ (integralBasis K) e.symm]
    exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (fun i => integralBasis K (e i)) (RingHom.equivRatAlgHom K ℂ)).symm

@[simp]
/-
**NumberField.canonicalEmbedding.latticeBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.canonicalEmbedding`。
形式化陈述：latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) :
 latticeBasis K i = (canonicalEmbedding K) (integralBasis K i)
参数：i : Free.ChooseBasisIndex Int (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.integralBasis_apply`：integralBasis_apply (i : Free.ChooseBas
isIndex Int (𝓞 K)) : integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basi
s K i)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `basisOfPiSpaceOfLinearIndependent.congr_simp`：∀ {K : Type u} [inst : Div
isionRing K] {ι : Type u_1} [inst_1 : Fintype ι] [inst_2 : Decidable (Nonempty ι
)]   {b b_1 : ι → ι → K} (e_b : b …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `coe_basisOfPiSpaceOfLinearIndependent`：coe_basisOfPiSpaceOfLinearIndepen
dent {b : ι -> (ι -> K)} (hb : LinearIndependent K b) : ⇑(basisOfPiSpaceOfLinear
Independent hb) = b
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (canonicalEmbedding K) (integralBasis K i) := by
  simp [latticeBasis, integralBasis_apply, coe_basisOfPiSpaceOfLinearIndependent,
    Function.comp_apply, Equiv.apply_symm_apply]
/-
**NumberField.canonicalEmbedding.mem_span_latticeBasis** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.canonicalEmbedding`。
形式化陈述：mem_span_latticeBasis [NumberField K] {x : (K ->+* Complex) -> Complex} : 
x in Submodule.span Int (Set.range (latticeBasis K)) ↔ x in ((canonicalEmbedding
 K).comp (algebraMap (𝓞 K) K)).range
参数：K ->+* Complex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.canonicalEmbedding.latticeBasis_apply`：latticeBasis_apply [N
umberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (canoni
calEmbedding K) (integralBasis K i)
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `RingHom.map_range`：map_range : f.range.map g = (g.comp f).range
· 使用定理 `Subring.mem_map`：mem_map {f : R ->+* S} {s : Subring R} {y : S} : y in s
.map f ↔ exists x in s, f x = y
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.mem_span_integralBasis`：mem_span_integralBasis {x : K} : x i
n Submodule.span Int (Set.range (integralBasis K)) ↔ x in (algebraMap (𝓞 K) K).r
ange
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_span_latticeBasis [NumberField K] {x : (K →+* ℂ) → ℂ} :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔
      x ∈ ((canonicalEmbedding K).comp (algebraMap (𝓞 K) K)).range := by
  rw [show Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [← RingHom.map_range, Subring.mem_map, Set.mem_image]
  simp only [SetLike.mem_coe, mem_span_integralBasis K]
  rfl
/-
**NumberField.canonicalEmbedding.mem_rat_span_latticeBasis** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.canonicalEmbedding`。
形式化陈述：mem_rat_span_latticeBasis [NumberField K] (x : K) : canonicalEmbedding K x
 in Submodule.span Rat (Set.range (latticeBasis K))
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `Submodule.sum_smul_mem`：sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι 
-> R) (hyp : forall c in t, f c in p) : (∑ i in t, r i • f i) in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `NumberField.canonicalEmbedding.latticeBasis_apply`：latticeBasis_apply [N
umberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (canoni
calEmbedding K) (integralBasis K i)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem mem_rat_span_latticeBasis [NumberField K] (x : K) :
    canonicalEmbedding K x ∈ Submodule.span ℚ (Set.range (latticeBasis K)) := by
  rw [← Basis.sum_repr (integralBasis K) x, map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ ↦ Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

set_option backward.isDefEq.respectTransparency.types false in
/-
**NumberField.canonicalEmbedding.integralBasis_repr_apply** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.canonicalEmbedding`。
形式化陈述：integralBasis_repr_apply [NumberField K] (x : K) (i : Free.ChooseBasisInde
x Int (𝓞 K)) : (latticeBasis K).repr (canonicalEmbedding K x) i = (integralBasis
 K).repr x i
参数：x : K；i : Free.ChooseBasisIndex Int (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `NumberField.canonicalEmbedding.mem_rat_span_latticeBasis`：mem_rat_span_l
atticeBasis [NumberField K] (x : K) : canonicalEmbedding K x in Submodule.span R
at (Set.range (latticeBasis K))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.restrictScalars_repr_apply`：∀ {ι : Type u_1} (R : Type u_3)
 {M : Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst
_2 : Ring S] [inst_3 : Nontri…
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `Rat.cast_inj`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] {p q
 : ℚ}, ↑p = ↑q ↔ p = q
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `LinearMap.codRestrict_apply`：codRestrict_apply (p : Submodule R₂ M₂) (f 
: M ->ₛₗ[σ₁₂] M₂) {h} (x : M) : (codRestrict p f h x : M₂) = f x
· 使用定理 `AlgHom.toLinearMap_apply`：toLinearMap_apply (p : A) : φ.toLinearMap p = 
φ p
· 使用定理 `Module.Basis.restrictScalars_apply`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst_2 : 
Ring S] [inst_3 : Nontri…
· 使用定理 `NumberField.canonicalEmbedding.latticeBasis_apply`：latticeBasis_apply [N
umberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (canoni
calEmbedding K) (integralBasis K i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem integralBasis_repr_apply [NumberField K] (x : K) (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (latticeBasis K).repr (canonicalEmbedding K x) i = (integralBasis K).repr x i := by
  rw [← Basis.restrictScalars_repr_apply ℚ _ ⟨_, mem_rat_span_latticeBasis K x⟩, eq_ratCast,
    Rat.cast_inj]
  let f := (canonicalEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x ↦ mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars ℚ).repr.toLinearMap ∘ₗ f =
    (integralBasis K).repr.toLinearMap from DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext (integralBasis K) (fun i ↦ ?_)
  have : f (integralBasis K i) = ((latticeBasis K).restrictScalars ℚ) i := by
    apply Subtype.val_injective
    rw [LinearMap.codRestrict_apply, AlgHom.toLinearMap_apply, Basis.restrictScalars_apply,
      latticeBasis_apply]
    rfl
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

end NumberField.canonicalEmbedding

namespace NumberField.mixedEmbedding

open NumberField.InfinitePlace Module Finset

/-- The mixed space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
/-
**NumberField.mixedEmbedding.mixedSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField
.mixedEmbedding`。
形式化陈述：mixedSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mixed space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`.
-/
abbrev mixedSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The mixed embedding of a number field `K` into the mixed space of `K`. -/
/-
**NumberField.mixedEmbedding._root_.NumberField.mixedEmbedding** 是 Mathlib 中的一个定
义，位于命名空间 `NumberField.mixedEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mixed embedding of a number field `K` into the mixed space of `K`.
-/
noncomputable def _root_.NumberField.mixedEmbedding : K →+* (mixedSpace K) :=
  RingHom.prod (RingHom.pi fun w => embedding_of_isReal w.prop)
    (RingHom.pi fun w => w.val.embedding)

@[simp]
/-
**NumberField.mixedEmbedding.mixedEmbedding_apply_isReal** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：mixedEmbedding_apply_isReal (x : K) (w : {w // IsReal w}) : (mixedEmbeddin
g K x).1 w = embedding_of_isReal w.prop x
参数：x : K；w : {w // IsReal w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mixedEmbedding_apply_isReal (x : K) (w : {w // IsReal w}) :
    (mixedEmbedding K x).1 w = embedding_of_isReal w.prop x := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]

@[simp]
/-
**NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：mixedEmbedding_apply_isComplex (x : K) (w : {w // IsComplex w}) : (mixedEm
bedding K x).2 w = w.val.embedding x
参数：x : K；w : {w // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mixedEmbedding_apply_isComplex (x : K) (w : {w // IsComplex w}) :
    (mixedEmbedding K x).2 w = w.val.embedding x := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, RingHom.pi_apply]
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField K] : Nontrivial (mixedSpace K) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain hw | hw := w.isReal_or_isComplex
  · have : Nonempty {w : InfinitePlace K // IsReal w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · have : Nonempty {w : InfinitePlace K // IsComplex w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_right
/-
**NumberField.mixedEmbedding.finrank** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixe
dEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Module.finra
nk ℝ (NumberField.mixedEmbedding.mixedSpace K) = Module.finrank ℚ K
参数：K : Type u_1；NumberField.mixedEmbedding.mixedSpace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_prod`：Module.finrank_prod [Module.Finite R M] [Module.Fin
ite R M'] : finrank R (M × M') = finrank R M + finrank R M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Module.finrank_pi`：Module.finrank_pi {ι : Type v} [Fintype ι] : finrank 
R (ι -> R) = Fintype.card ι
· 使用定理 `Module.finrank_pi_fintype`：Module.finrank_pi_fintype {ι : Type v} [Finty
pe ι] {M : ι -> Type w} [forall i : ι, AddCommMonoid (M i)] [forall i : ι, Modul
e R (M i)] [for…
· 使用定理 `Complex.finrank_real_complex`：finrank_real_complex : finrank Real Comple
x = 2
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.nrRealPlaces.eq_1`：∀ (K : Type u_1) [inst : Fi
eld K] [inst_1 : NumberField K],   NumberField.InfinitePlace.nrRealPlaces K = Fi
ntype.card { w // w.IsReal }
· 使用定理 `NumberField.InfinitePlace.nrComplexPlaces.eq_1`：∀ (K : Type u_1) [inst :
 Field K] [inst_1 : NumberField K],   NumberField.InfinitePlace.nrComplexPlaces 
K = Fintype.card { w // w.IsComplex …
· 使用定理 `NumberField.InfinitePlace.card_real_embeddings`：card_real_embeddings : c
ard { φ : K ->+* Complex // ComplexEmbedding.IsReal φ } = nrRealPlaces K
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NumberField.InfinitePlace.card_complex_embeddings`：card_complex_embeddin
gs : card { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPl
aces K
· 使用定理 `NumberField.Embeddings.card`：card : Fintype.card (K ->+* A) = finrank Ra
t K
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `Fintype.card_subtype_le`：Fintype.card_subtype_le [Fintype α] (p : α -> P
rop) [Fintype {a // p a}] : Fintype.card { x // p x } <= Fintype.card α
-/
protected theorem finrank [NumberField K] : finrank ℝ (mixedSpace K) = finrank ℚ K := by
  classical
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, Complex.finrank_real_complex, sum_const,
    card_univ, ← nrRealPlaces, ← nrComplexPlaces, ← card_real_embeddings, smul_eq_mul,
    mul_comm, ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ,
    Fintype.card_subtype_compl, Nat.add_sub_of_le (Fintype.card_subtype_le _)]
/-
**NumberField.mixedEmbedding._root_.NumberField.mixedEmbedding_injective** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NumberField.mixedEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.mixedEmbedding K) := by
  exact RingHom.injective _

section Measure

open MeasureTheory.Measure MeasureTheory

variable [NumberField K]

open scoped Classical in
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddHaarMeasure (volume : Measure (mixedSpace K)) :=
  prod.instIsAddHaarMeasure volume volume

open scoped Classical in
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NullSingletonClass (volume : Measure (mixedSpace K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw : IsReal w
  · have : NullSingletonClass (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ)) :=
      pi_nullSingletonClass ⟨w, hw⟩
    exact prod.instNullSingletonClass_fst
  · have : NullSingletonClass (volume : Measure ({w : InfinitePlace K // IsComplex w} → ℂ)) :=
      pi_nullSingletonClass ⟨w, not_isReal_iff_isComplex.mp hw⟩
    exact prod.instNullSingletonClass_snd

set_option backward.isDefEq.respectTransparency.types false in
variable {K} in
open scoped Classical in
/-- The set of points in the mixedSpace that are equal to `0` at a fixed (real) place has
volume zero. -/
/-
**NumberField.mixedEmbedding.volume_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：volume_eq_zero (w : {w // IsReal w}) : volume ({x : mixedSpace K | x.1 w =
 0}) = 0
参数：w : {w // IsReal w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.addHaar_affineSubspace`：addHaar_affineSubspace {E 
: Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelS
pace E] [FiniteDimensional Real E]…
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The set of points in the mixedSpace that are equal to `0` at a fixed (real) plac
e has
volume zero.
-/
theorem volume_eq_zero (w : {w // IsReal w}) :
    volume ({x : mixedSpace K | x.1 w = 0}) = 0 := by
  let A : AffineSubspace ℝ (mixedSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x.1 w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 ∈ A)

end Measure

section commMap

/-- The linear map that makes `canonicalEmbedding` and `mixedEmbedding` commute, see
`commMap_canonical_eq_mixed`. -/
/-
**NumberField.mixedEmbedding.commMap** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.mixe
dEmbedding`。
形式化陈述：commMap : ((K ->+* Complex) -> Complex) ->ₗ[Real] (mixedSpace K) where toF
un
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map that makes `canonicalEmbedding` and `mixedEmbedding` commute, see
`commMap_canonical_eq_mixed`.
-/
noncomputable def commMap : ((K →+* ℂ) → ℂ) →ₗ[ℝ] (mixedSpace K) where
  toFun := fun x => ⟨fun w => (x w.val.embedding).re, fun w => x w.val.embedding⟩
  map_add' := by
    simp only [Pi.add_apply, Complex.add_re, Prod.mk_add_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩
  map_smul' := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩
/-
**NumberField.mixedEmbedding.commMap_apply_of_isReal** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：commMap_apply_of_isReal (x : (K ->+* Complex) -> Complex) {w : InfinitePla
ce K} (hw : IsReal w) : (commMap K x).1 ⟨w, hw⟩ = (x w.embedding).re
参数：x : (K ->+* Complex) -> Complex；hw : IsReal w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commMap_apply_of_isReal (x : (K →+* ℂ) → ℂ) {w : InfinitePlace K} (hw : IsReal w) :
    (commMap K x).1 ⟨w, hw⟩ = (x w.embedding).re := rfl
/-
**NumberField.mixedEmbedding.commMap_apply_of_isComplex** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：commMap_apply_of_isComplex (x : (K ->+* Complex) -> Complex) {w : Infinite
Place K} (hw : IsComplex w) : (commMap K x).2 ⟨w, hw⟩ = x w.embedding
参数：x : (K ->+* Complex) -> Complex；hw : IsComplex w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commMap_apply_of_isComplex (x : (K →+* ℂ) → ℂ) {w : InfinitePlace K} (hw : IsComplex w) :
    (commMap K x).2 ⟨w, hw⟩ = x w.embedding := rfl

@[simp]
/-
**NumberField.mixedEmbedding.commMap_canonical_eq_mixed** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：commMap_canonical_eq_mixed (x : K) : commMap K (canonicalEmbedding K x) = 
mixedEmbedding K x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
theorem commMap_canonical_eq_mixed (x : K) :
    commMap K (canonicalEmbedding K x) = mixedEmbedding K x := by
  simp only [canonicalEmbedding, commMap, LinearMap.coe_mk, AddHom.coe_mk, RingHom.pi_apply,
    mixedEmbedding, RingHom.prod_apply, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

/-- This is a technical result to ensure that the image of the `ℂ`-basis of `ℂ^n` defined in
`canonicalEmbedding.latticeBasis` is a `ℝ`-basis of the mixed space `ℝ^r₁ × ℂ^r₂`,
see `mixedEmbedding.latticeBasis`. -/
/-
**NumberField.mixedEmbedding.disjoint_span_commMap_ker** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.mixedEmbedding`。
形式化陈述：disjoint_span_commMap_ker [NumberField K] : Disjoint (Submodule.span Real 
(Set.range (canonicalEmbedding.latticeBasis K))) (LinearMap.ker (commMap K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `LinearMap.disjoint_ker`：disjoint_ker {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule
 R M} : Disjoint p (ker f) ↔ forall x in p, f x = 0 -> x = 0
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.canonicalEmbedding.latticeBasis_apply`：latticeBasis_apply [N
umberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (canoni
calEmbedding K) (integralBasis K i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq_of_isReal`：embedding_mk_eq_of_
isReal {φ : K ->+* Complex} (h : ComplexEmbedding.IsReal φ) : embedding (mk φ) =
 φ
· 使用定理 `NumberField.mixedEmbedding.commMap_apply_of_isReal`：commMap_apply_of_isR
eal (x : (K ->+* Complex) -> Complex) {w : InfinitePlace K} (hw : IsReal w) : (c
ommMap K x).1 ⟨w, hw⟩ = (x w.embedding).…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.zero_im`：zero_im : (0 : Complex).im = 0
· 使用定理 `Complex.conj_eq_iff_im`：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im
 = 0
· 使用定理 `NumberField.canonicalEmbedding.conj_apply`：conj_apply {x : ((K ->+* Comp
lex) -> Complex)} (φ : K ->+* Complex) (hx : x in Submodule.span Real (Set.range
 (canonicalEmbedding K))) : con…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq`：embedding_mk_eq (φ : K ->+* C
omplex) : embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ
· 使用定理 `NumberField.mixedEmbedding.commMap_apply_of_isComplex`：commMap_apply_of_
isComplex (x : (K ->+* Complex) -> Complex) {w : InfinitePlace K} (hw : IsComple
x w) : (commMap K x).2 ⟨w, hw⟩ = x w.embedd…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
This is a technical result to ensure that the image of the `ℂ`-basis of `ℂ^n` de
fined in
`canonicalEmbedding.latticeBasis` is a `ℝ`-basis of the mixed space `ℝ^r₁ × ℂ^r₂
`,
see `mixedEmbedding.latticeBasis`.
-/
theorem disjoint_span_commMap_ker [NumberField K] :
    Disjoint (Submodule.span ℝ (Set.range (canonicalEmbedding.latticeBasis K)))
      (LinearMap.ker (commMap K)) := by
  refine LinearMap.disjoint_ker.mpr (fun x h_mem h_zero => ?_)
  replace h_mem : x ∈ Submodule.span ℝ (Set.range (canonicalEmbedding K)) := by
    refine (Submodule.span_mono ?_) h_mem
    rintro _ ⟨i, rfl⟩
    exact ⟨integralBasis K i, (canonicalEmbedding.latticeBasis_apply K i).symm⟩
  ext1 φ
  rw [Pi.zero_apply]
  by_cases hφ : ComplexEmbedding.IsReal φ
  · apply Complex.ext
    · rw [← embedding_mk_eq_of_isReal hφ, ← commMap_apply_of_isReal K x ⟨φ, hφ, rfl⟩]
      exact congrFun (congrArg (fun x => x.1) h_zero) ⟨InfinitePlace.mk φ, _⟩
    · rw [Complex.zero_im, ← Complex.conj_eq_iff_im, canonicalEmbedding.conj_apply _ h_mem,
        ComplexEmbedding.isReal_iff.mp hφ]
  · have := congrFun (congrArg (fun x => x.2) h_zero) ⟨InfinitePlace.mk φ, ⟨φ, hφ, rfl⟩⟩
    cases embedding_mk_eq φ with
    | inl h => rwa [← h, ← commMap_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]
    | inr h =>
        apply RingHom.injective (starRingEnd ℂ)
        rwa [canonicalEmbedding.conj_apply _ h_mem, ← h, map_zero,
          ← commMap_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]

end commMap

noncomputable section norm

variable {K}

open scoped Classical in
/-- The norm at the infinite place `w` of an element of the mixed space -/
/-
**NumberField.mixedEmbedding.normAtPlace** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.
mixedEmbedding`。
形式化陈述：normAtPlace (w : InfinitePlace K) : (mixedSpace K) ->*₀ Real where toFun x
参数：w : InfinitePlace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm at the infinite place `w` of an element of the mixed space
-/
def normAtPlace (w : InfinitePlace K) : (mixedSpace K) →*₀ ℝ where
  toFun x := if hw : IsReal w then ‖x.1 ⟨w, hw⟩‖ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by split_ifs <;> simp
/-
**NumberField.mixedEmbedding.normAtPlace_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.mixedEmbedding`。
形式化陈述：normAtPlace_nonneg (w : InfinitePlace K) (x : mixedSpace K) : 0 <= normAtP
lace w x
参数：w : InfinitePlace K；x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (w : NumberField.InfinitePlace K),   NumberField.mixedEmbedding.normAtPla
ce w =     { toFun := fun x => if…
· 使用定理 `MonoidWithZeroHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZer
oOneClass α] [inst_1 : MulZeroOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 
1) (hmul : ∀ (…
· 使用定理 `ZeroHom.coe_mk`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 
: Zero N] (f : M → N) (h1 : f 0 = 0),   ⇑{ toFun := f, map_zero' := h1 } = f
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem normAtPlace_nonneg (w : InfinitePlace K) (x : mixedSpace K) :
    0 ≤ normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> exact norm_nonneg _
/-
**NumberField.mixedEmbedding.normAtPlace_neg** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.mixedEmbedding`。
形式化陈述：normAtPlace_neg (w : InfinitePlace K) (x : mixedSpace K) : normAtPlace w (
-x) = normAtPlace w x
参数：w : InfinitePlace K；x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (w : NumberField.InfinitePlace K),   NumberField.mixedEmbedding.normAtPla
ce w =     { toFun := fun x => if…
· 使用定理 `MonoidWithZeroHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZer
oOneClass α] [inst_1 : MulZeroOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 
1) (hmul : ∀ (…
· 使用定理 `ZeroHom.coe_mk`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 
: Zero N] (f : M → N) (h1 : f 0 = 0),   ⇑{ toFun := f, map_zero' := h1 } = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem normAtPlace_neg (w : InfinitePlace K) (x : mixedSpace K) :
    normAtPlace w (-x) = normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> simp
/-
**NumberField.mixedEmbedding.normAtPlace_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.mixedEmbedding`。
形式化陈述：normAtPlace_add_le (w : InfinitePlace K) (x y : mixedSpace K) : normAtPlac
e w (x + y) <= normAtPlace w x + normAtPlace w y
参数：w : InfinitePlace K；x y : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (w : NumberField.InfinitePlace K),   NumberField.mixedEmbedding.normAtPla
ce w =     { toFun := fun x => if…
· 使用定理 `MonoidWithZeroHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZer
oOneClass α] [inst_1 : MulZeroOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 
1) (hmul : ∀ (…
· 使用定理 `ZeroHom.coe_mk`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 
: Zero N] (f : M → N) (h1 : f 0 = 0),   ⇑{ toFun := f, map_zero' := h1 } = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem normAtPlace_add_le (w : InfinitePlace K) (x y : mixedSpace K) :
    normAtPlace w (x + y) ≤ normAtPlace w x + normAtPlace w y := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> exact norm_add_le _ _
/-
**NumberField.mixedEmbedding.normAtPlace_smul** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：normAtPlace_smul (w : InfinitePlace K) (x : mixedSpace K) (c : Real) : nor
mAtPlace w (c • x) = |c| * normAtPlace w x
参数：w : InfinitePlace K；x : mixedSpace K；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (w : NumberField.InfinitePlace K),   NumberField.mixedEmbedding.normAtPla
ce w =     { toFun := fun x => if…
· 使用定理 `MonoidWithZeroHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZer
oOneClass α] [inst_1 : MulZeroOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 
1) (hmul : ∀ (…
· 使用定理 `ZeroHom.coe_mk`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 
: Zero N] (f : M → N) (h1 : f 0 = 0),   ⇑{ toFun := f, map_zero' := h1 } = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
-/
theorem normAtPlace_smul (w : InfinitePlace K) (x : mixedSpace K) (c : ℝ) :
    normAtPlace w (c • x) = |c| * normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> simp
/-
**NumberField.mixedEmbedding.normAtPlace_real** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：normAtPlace_real (w : InfinitePlace K) (c : Real) : normAtPlace w ((fun _ 
=> c, fun _ => c) : (mixedSpace K)) = |c|
参数：w : InfinitePlace K；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_smul`：normAtPlace_smul (w : Infin
itePlace K) (x : mixedSpace K) (c : Real) : normAtPlace w (c • x) = |c| * normAt
Place w x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem normAtPlace_real (w : InfinitePlace K) (c : ℝ) :
    normAtPlace w ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = |c| := by
  rw [show ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = c • 1 by ext <;> simp, normAtPlace_smul,
    map_one, mul_one]
/-
**NumberField.mixedEmbedding.normAtPlace_apply_of_isReal** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtPlace_apply_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mix
edSpace K) : normAtPlace w x = ‖x.1 ⟨w, hw⟩‖
参数：hw : IsReal w；x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (w : NumberField.InfinitePlace K),   NumberField.mixedEmbedding.normAtPla
ce w =     { toFun := fun x => if…
· 使用定理 `MonoidWithZeroHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZer
oOneClass α] [inst_1 : MulZeroOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 
1) (hmul : ∀ (…
· 使用定理 `ZeroHom.coe_mk`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 
: Zero N] (f : M → N) (h1 : f 0 = 0),   ⇑{ toFun := f, map_zero' := h1 } = f
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem normAtPlace_apply_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) :
    normAtPlace w x = ‖x.1 ⟨w, hw⟩‖ := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_pos]
/-
**NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtPlace_apply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x
 : mixedSpace K) : normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
参数：hw : IsComplex w；x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (w : NumberField.InfinitePlace K),   NumberField.mixedEmbedding.normAtPla
ce w =     { toFun := fun x => if…
· 使用定理 `MonoidWithZeroHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZer
oOneClass α] [inst_1 : MulZeroOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 
1) (hmul : ∀ (…
· 使用定理 `ZeroHom.coe_mk`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 
: Zero N] (f : M → N) (h1 : f 0 = 0),   ⇑{ toFun := f, map_zero' := h1 } = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem normAtPlace_apply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) :
    normAtPlace w x = ‖x.2 ⟨w, hw⟩‖ := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    dif_neg (not_isReal_iff_isComplex.mpr hw)]

@[simp]
/-
**NumberField.mixedEmbedding.normAtPlace_apply** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：normAtPlace_apply (w : InfinitePlace K) (x : K) : normAtPlace w (mixedEmbe
dding K x) = w x
参数：w : InfinitePlace K；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `NumberField.InfinitePlace.norm_embedding_of_isReal`：norm_embedding_of_is
Real {w : InfinitePlace K} (hw : IsReal w) (x : K) : ‖embedding_of_isReal hw x‖ 
= w x
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_id`：∀ {c : Prop} [inst : Decidable c] {α : Sort u_1} (t : α), (if c 
then t else t) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normAtPlace_apply (w : InfinitePlace K) (x : K) :
    normAtPlace w (mixedEmbedding K x) = w x := by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mixedEmbedding,
    RingHom.prod_apply, RingHom.pi_apply, norm_embedding_of_isReal, norm_embedding_eq, dite_eq_ite,
    ite_id]
/-
**NumberField.mixedEmbedding.forall_normAtPlace_eq_zero_iff** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：forall_normAtPlace_eq_zero_iff {x : mixedSpace K} : (forall w, normAtPlace
 w x = 0) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem forall_normAtPlace_eq_zero_iff {x : mixedSpace K} :
    (∀ w, normAtPlace w x = 0) ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isReal w.prop _ ▸ h w.1)
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isComplex w.prop _ ▸ h w.1)
  · simp_rw [h, map_zero, implies_true]

@[simp]
/-
**NumberField.mixedEmbedding.exists_normAtPlace_ne_zero_iff** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_normAtPlace_ne_zero_iff {x : mixedSpace K} : (exists w, normAtPlace
 w x != 0) ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.forall_normAtPlace_eq_zero_iff`：forall_normAt
Place_eq_zero_iff {x : mixedSpace K} : (forall w, normAtPlace w x = 0) ↔ x = 0
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exists_normAtPlace_ne_zero_iff {x : mixedSpace K} :
    (∃ w, normAtPlace w x ≠ 0) ↔ x ≠ 0 := by
  rw [ne_eq, ← forall_normAtPlace_eq_zero_iff, not_forall]

@[fun_prop]
/-
**NumberField.mixedEmbedding.continuous_normAtPlace** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.mixedEmbedding`。
形式化陈述：continuous_normAtPlace (w : InfinitePlace K) : Continuous (normAtPlace w)
参数：w : InfinitePlace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
theorem continuous_normAtPlace (w : InfinitePlace K) :
    Continuous (normAtPlace w) := by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> fun_prop

variable [NumberField K]

open scoped Classical in
/-
**NumberField.mixedEmbedding.nnnorm_eq_sup_normAtPlace** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.mixedEmbedding`。
形式化陈述：nnnorm_eq_sup_normAtPlace (x : mixedSpace K) : ‖x‖₊ = univ.sup fun w => .m
k (normAtPlace w x) (normAtPlace_nonneg w x)
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Prod.nnnorm_def`：∀ {E : Type u_2} {F : Type u_3} [inst : SeminormedAddGr
oup E] [inst_1 : SeminormedAddGroup F] (x : E × F),   ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
-/
theorem nnnorm_eq_sup_normAtPlace (x : mixedSpace K) :
    ‖x‖₊ = univ.sup fun w ↦ .mk (normAtPlace w x) (normAtPlace_nonneg w x) := by
  have :
      (univ : Finset (InfinitePlace K)) =
      (univ.image (fun w : {w : InfinitePlace K // IsReal w} ↦ w.1)) ∪
      (univ.image (fun w : {w : InfinitePlace K // IsComplex w} ↦ w.1)) := by
    ext; simp [isReal_or_isComplex]
  rw [this, sup_union, univ.sup_image, univ.sup_image,
    Prod.nnnorm_def, Pi.nnnorm_def, Pi.nnnorm_def]
  congr
  · ext w
    simp [normAtPlace_apply_of_isReal w.prop]
  · ext w
    simp [normAtPlace_apply_of_isComplex w.prop]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-
**NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.mixedEmbedding`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (x : NumberFiel
d.mixedEmbedding.mixedSpace K),   ‖x‖ = Finset.univ.sup' ⋯ fun w => (NumberField
.mixedEmbedding.normAtPlace w) x
参数：x : NumberField.mixedEmbedding.mixedSpace K；NumberField.mixedEmbedding.normAt
Place w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `NumberField.instNonemptyInfinitePlaceOfRingHomComplex`：∀ (K : Type u_1) 
[inst : Field K] [Nonempty (K →+* ℂ)], Nonempty (NumberField.InfinitePlace K)
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
· 使用定理 `NumberField.mixedEmbedding.nnnorm_eq_sup_normAtPlace`：nnnorm_eq_sup_norm
AtPlace (x : mixedSpace K) : ‖x‖₊ = univ.sup fun w => .mk (normAtPlace w x) (nor
mAtPlace_nonneg w x)
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `NNReal.val_eq_coe`：val_eq_coe (n : Real>=0) : n.val = n
· 使用定理 `OrderHom.Subtype.val_coe`：∀ {α : Type u_2} [inst : Preorder α] (p : α → 
Prop), ⇑(OrderHom.Subtype.val p) = Subtype.val
· 使用定理 `map_finset_sup'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   [inst_2 : FunLike
 F α …
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderHomClass.toLatticeHomClass`：∀ {F : Type u_1} (α : Type u_2) (β : Ty
pe u_3) [inst : FunLike F α β] [inst_1 : LinearOrder α] [inst_2 : Lattice β]   [
OrderHomClass F α β],…
· 使用定理 `OrderHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β], OrderHomClass (α →o β) α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_eq_sup'_normAtPlace (x : mixedSpace K) :
    ‖x‖ = univ.sup' univ_nonempty fun w ↦ normAtPlace w x := by
  rw [← coe_nnnorm, nnnorm_eq_sup_normAtPlace, ← sup'_eq_sup univ_nonempty, ← NNReal.val_eq_coe,
    ← OrderHom.Subtype.val_coe, map_finset_sup', OrderHom.Subtype.val_coe]
  simp

/-- The norm of `x` is `∏ w, (normAtPlace x) ^ mult w`. It is defined such that the norm of
`mixedEmbedding K a` for `a : K` is equal to the absolute value of the norm of `a` over `ℚ`,
see `norm_eq_norm`. -/
/-
**NumberField.mixedEmbedding.norm** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.mixedEm
bedding`。
形式化陈述：{K : Type u_1} → [inst : Field K] → [NumberField K] → NumberField.mixedEmb
edding.mixedSpace K →*₀ ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of `x` is `∏ w, (normAtPlace x) ^ mult w`. It is defined such that the 
norm of
`mixedEmbedding K a` for `a : K` is equal to the absolute value of the norm of `
a` over `ℚ`,
see `norm_eq_norm`.
-/
protected def norm : (mixedSpace K) →*₀ ℝ where
  toFun x := ∏ w, (normAtPlace w x) ^ (mult w)
  map_one' := by simp only [map_one, one_pow, prod_const_one]
  map_zero' := by simp [mult]
  map_mul' _ _ := by simp only [map_mul, mul_pow, prod_mul_distrib]
/-
**NumberField.mixedEmbedding.norm_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (x : NumberFiel
d.mixedEmbedding.mixedSpace K),   NumberField.mixedEmbedding.norm x = ∏ w, (Numb
erField.mixedEmbedding.normAtPlace w) x ^ w.mult
参数：x : NumberField.mixedEmbedding.mixedSpace K；NumberField.mixedEmbedding.normAt
Place w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem norm_apply (x : mixedSpace K) :
    mixedEmbedding.norm x = ∏ w, (normAtPlace w x) ^ (mult w) := rfl
/-
**NumberField.mixedEmbedding.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
mixedEmbedding`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (x : NumberFiel
d.mixedEmbedding.mixedSpace K),   0 ≤ NumberField.mixedEmbedding.norm x
参数：x : NumberField.mixedEmbedding.mixedSpace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
-/
protected theorem norm_nonneg (x : mixedSpace K) :
    0 ≤ mixedEmbedding.norm x := univ.prod_nonneg fun _ _ ↦ pow_nonneg (normAtPlace_nonneg _ _) _
/-
**NumberField.mixedEmbedding.norm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {x : NumberFiel
d.mixedEmbedding.mixedSpace K},   NumberField.mixedEmbedding.norm x = 0 ↔ ∃ w, (
NumberField.mixedEmbedding.normAtPlace w) x = 0
参数：NumberField.mixedEmbedding.normAtPlace w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
· 使用定理 `NumberField.InfinitePlace.mult_ne_zero`：mult_ne_zero {w : InfinitePlace 
K} : mult w != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem norm_eq_zero_iff {x : mixedSpace K} :
    mixedEmbedding.norm x = 0 ↔ ∃ w, normAtPlace w x = 0 := by
  simp_rw [mixedEmbedding.norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, prod_eq_zero_iff,
    mem_univ, true_and, pow_eq_zero_iff mult_ne_zero]
/-
**NumberField.mixedEmbedding.norm_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {x : NumberFiel
d.mixedEmbedding.mixedSpace K},   NumberField.mixedEmbedding.norm x ≠ 0 ↔     ∀ 
(w : NumberField.InfinitePlace K), (NumberField.mixedEmbedding.normAtPlace w) x 
≠ 0
参数：w : NumberField.InfinitePlace K；NumberField.mixedEmbedding.normAtPlace w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem norm_ne_zero_iff {x : mixedSpace K} :
    mixedEmbedding.norm x ≠ 0 ↔ ∀ w, normAtPlace w x ≠ 0 := by
  rw [← not_iff_not]
  simp_rw [ne_eq, mixedEmbedding.norm_eq_zero_iff, not_not, not_forall, not_not]
/-
**NumberField.mixedEmbedding.norm_eq_of_normAtPlace_eq** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.mixedEmbedding`。
形式化陈述：norm_eq_of_normAtPlace_eq {x y : mixedSpace K} (h : forall w, normAtPlace 
w x = normAtPlace w y) : mixedEmbedding.norm x = mixedEmbedding.norm y
参数：h : forall w, normAtPlace w x = normAtPlace w y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_eq_of_normAtPlace_eq {x y : mixedSpace K}
    (h : ∀ w, normAtPlace w x = normAtPlace w y) :
    mixedEmbedding.norm x = mixedEmbedding.norm y := by
  simp_rw [mixedEmbedding.norm_apply, h]
/-
**NumberField.mixedEmbedding.norm_smul** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mi
xedEmbedding`。
形式化陈述：norm_smul (c : Real) (x : mixedSpace K) : mixedEmbedding.norm (c • x) = |c
| ^ finrank Rat K * (mixedEmbedding.norm x)
参数：c : Real；x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_smul`：normAtPlace_smul (w : Infin
itePlace K) (x : mixedSpace K) (c : Real) : normAtPlace w (c • x) = |c| * normAt
Place w x
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.InfinitePlace.sum_mult_eq`：sum_mult_eq [NumberField K] : ∑ w
 : InfinitePlace K, mult w = Module.finrank Rat K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_smul (c : ℝ) (x : mixedSpace K) :
    mixedEmbedding.norm (c • x) = |c| ^ finrank ℚ K * (mixedEmbedding.norm x) := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_smul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq]
/-
**NumberField.mixedEmbedding.norm_real** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mi
xedEmbedding`。
形式化陈述：norm_real (c : Real) : mixedEmbedding.norm ((fun _ => c, fun _ => c) : (mi
xedSpace K)) = |c| ^ finrank Rat K
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.norm_smul`：norm_smul (c : Real) (x : mixedSpa
ce K) : mixedEmbedding.norm (c • x) = |c| ^ finrank Rat K * (mixedEmbedding.norm
 x)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem norm_real (c : ℝ) :
    mixedEmbedding.norm ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = |c| ^ finrank ℚ K := by
  rw [show ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = c • 1 by ext <;> simp, norm_smul, map_one,
    mul_one]

@[simp]
/-
**NumberField.mixedEmbedding.norm_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.mixedEmbedding`。
形式化陈述：norm_eq_norm (x : K) : mixedEmbedding.norm (mixedEmbedding K x) = |Algebra
.norm Rat x|
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.InfinitePlace.prod_eq_abs_norm`：prod_eq_abs_norm (x : K) : ∏
 w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm Rat x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_eq_norm (x : K) :
    mixedEmbedding.norm (mixedEmbedding K x) = |Algebra.norm ℚ x| := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_apply, prod_eq_abs_norm]
/-
**NumberField.mixedEmbedding.norm_unit** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mi
xedEmbedding`。
形式化陈述：norm_unit (u : (𝓞 K)ˣ) : mixedEmbedding.norm (mixedEmbedding K u) = 1
参数：u : (𝓞 K)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.norm_eq_norm`：norm_eq_norm (x : K) : mixedEmb
edding.norm (mixedEmbedding K x) = |Algebra.norm Rat x|
· 使用定理 `NumberField.Units.norm`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Numb
erField K] (x : (NumberField.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraM
ap (NumberFi…
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
-/
theorem norm_unit (u : (𝓞 K)ˣ) :
    mixedEmbedding.norm (mixedEmbedding K u) = 1 := by
  rw [norm_eq_norm, Units.norm, Rat.cast_one]
/-
**NumberField.mixedEmbedding.norm_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：norm_eq_zero_iff' {x : mixedSpace K} (hx : x in Set.range (mixedEmbedding 
K)) : mixedEmbedding.norm x = 0 ↔ x = 0
参数：hx : x in Set.range (mixedEmbedding K)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.norm_eq_norm`：norm_eq_norm (x : K) : mixedEmb
edding.norm (mixedEmbedding K x) = |Algebra.norm Rat x|
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `abs_eq_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| = 0 ↔ a = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Rat.cast_eq_zero`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] 
{p : ℚ}, ↑p = 0 ↔ p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Algebra.norm_eq_zero_iff`：norm_eq_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x = 0 ↔ x = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `map_eq_zero`：map_eq_zero : f a = 0 ↔ a = 0
· 使用定理 `NumberField.mixedEmbedding.instNontrivialMixedSpace`：∀ (K : Type u_1) [i
nst : Field K] [NumberField K], Nontrivial (NumberField.mixedEmbedding.mixedSpac
e K)
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_eq_zero_iff' {x : mixedSpace K} (hx : x ∈ Set.range (mixedEmbedding K)) :
    mixedEmbedding.norm x = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [norm_eq_norm, Rat.cast_abs, abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff,
    map_eq_zero]

variable (K) in
@[fun_prop]
/-
**NumberField.mixedEmbedding.continuous_norm** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K], Continuous ⇑Nu
mberField.mixedEmbedding.norm
参数：K : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_finsetProd`：continuous_finsetProd {f : ι -> X -> M} (s : Fins
et ι) : (forall i in s, Continuous (f i)) -> Continuous fun a => ∏ i in s, f i a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `dite_pow`：dite_pow (p : Prop) [Decidable p] (a : p -> α) (b : ¬ p -> α) 
(c : β) : (if h : p then a h else b h) ^ c = if h : p then a h ^ c else b h ^ …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
protected theorem continuous_norm : Continuous (mixedEmbedding.norm : (mixedSpace K) → ℝ) := by
  refine continuous_finsetProd Finset.univ fun _ _ ↦ ?_
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_pow]
  split_ifs <;> fun_prop

end norm

noncomputable section stdBasis

open Complex MeasureTheory MeasureTheory.Measure ZSpan Matrix ComplexConjugate

variable [NumberField K]

/-- The type indexing the basis `stdBasis`. -/
/-
**NumberField.mixedEmbedding.index** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.mixe
dEmbedding`。
形式化陈述：index
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type indexing the basis `stdBasis`.
-/
abbrev index := {w : InfinitePlace K // IsReal w} ⊕ ({w : InfinitePlace K // IsComplex w}) × (Fin 2)

open scoped Classical in
/-- The `ℝ`-basis of the mixed space of `K` formed by the vector equal to `1` at `w` and `0`
elsewhere for `IsReal w` and by the couple of vectors equal to `1` (resp. `I`) at `w` and `0`
elsewhere for `IsComplex w`. -/
/-
**NumberField.mixedEmbedding.stdBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.mix
edEmbedding`。
形式化陈述：stdBasis : Basis (index K) Real (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℝ`-basis of the mixed space of `K` formed by the vector equal to `1` at `w`
 and `0`
elsewhere for `IsReal w` and by the couple of vectors equal to `1` (resp. `I`) a
t `w` and `0`
elsewhere for `IsComplex w`.
-/
def stdBasis : Basis (index K) ℝ (mixedSpace K) :=
  Basis.prod (Pi.basisFun ℝ _)
    (Basis.reindex (Pi.basis fun _ => basisOneI) (Equiv.sigmaEquivProd _ _))

variable {K}

@[simp]
/-
**NumberField.mixedEmbedding.stdBasis_apply_isReal** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：stdBasis_apply_isReal (x : mixedSpace K) (w : {w : InfinitePlace K // IsRe
al w}) : (stdBasis K).repr x (Sum.inl w) = x.1 w
参数：x : mixedSpace K；w : {w : InfinitePlace K // IsReal w}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stdBasis_apply_isReal (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (stdBasis K).repr x (Sum.inl w) = x.1 w := rfl

@[simp]
/-
**NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding`。
形式化陈述：stdBasis_apply_isComplex_fst (x : mixedSpace K) (w : {w : InfinitePlace K 
// IsComplex w}) : (stdBasis K).repr x (Sum.inr ⟨w, 0⟩) = (x.2 w).re
参数：x : mixedSpace K；w : {w : InfinitePlace K // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem stdBasis_apply_isComplex_fst (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 0⟩) = (x.2 w).re := rfl

@[simp]
/-
**NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding`。
形式化陈述：stdBasis_apply_isComplex_snd (x : mixedSpace K) (w : {w : InfinitePlace K 
// IsComplex w}) : (stdBasis K).repr x (Sum.inr ⟨w, 1⟩) = (x.2 w).im
参数：x : mixedSpace K；w : {w : InfinitePlace K // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem stdBasis_apply_isComplex_snd (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 1⟩) = (x.2 w).im := rfl

variable (K)

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalDomain_stdBasis** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：fundamentalDomain_stdBasis : fundamentalDomain (stdBasis K) = (Set.univ.pi
 fun _ => Set.Ico 0 1) ×ˢ (Set.univ.pi fun _ => Complex.measurableEquivPi ⁻¹' (S
et.univ.pi fun _ => Set.Ico 0 1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Pi.basisFun_repr`：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η)
.repr x i = x i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fundamentalDomain_stdBasis :
    fundamentalDomain (stdBasis K) =
      (Set.univ.pi fun _ => Set.Ico 0 1) ×ˢ
      (Set.univ.pi fun _ => Complex.measurableEquivPi ⁻¹' (Set.univ.pi fun _ => Set.Ico 0 1)) := by
  ext
  simp [stdBasis, mem_fundamentalDomain, Complex.measurableEquivPi]

open scoped Classical in
/-
**NumberField.mixedEmbedding.volume_fundamentalDomain_stdBasis** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：volume_fundamentalDomain_stdBasis : volume (fundamentalDomain (stdBasis K)
) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalDomain_stdBasis`：fundamentalDomain
_stdBasis : fundamentalDomain (stdBasis K) = (Set.univ.pi fun _ => Set.Ico 0 1) 
×ˢ (Set.univ.pi fun _ => Complex.measurable…
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.volume_pi`：volume_pi [forall i, MeasureSpace (α i)] : (vol
ume : Measure (forall i, α i)) = Measure.pi fun _ => volume
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `Complex.volume_preserving_equiv_pi`：volume_preserving_equiv_pi : Measure
Preserving measurableEquivPi
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Set.countable_univ`：countable_univ [Countable α] : (univ : Set α).Counta
ble
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
（共 37 条，此处仅展示前 30 条）
-/
theorem volume_fundamentalDomain_stdBasis :
    volume (fundamentalDomain (stdBasis K)) = 1 := by
  rw [fundamentalDomain_stdBasis, volume_eq_prod, prod_prod, volume_pi, volume_pi, pi_pi, pi_pi,
    Complex.volume_preserving_equiv_pi.measure_preimage ?_, volume_pi, pi_pi, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one, prod_const_one, prod_const_one, prod_const_one, one_mul]
  exact (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).nullMeasurableSet

open scoped Classical in
/-- The `Equiv` between `index K` and `K →+* ℂ` defined by sending a real infinite place `w` to
the unique corresponding embedding `w.embedding`, and the pair `⟨w, 0⟩` (resp. `⟨w, 1⟩`) for a
complex infinite place `w` to `w.embedding` (resp. `conjugate w.embedding`). -/
/-
**NumberField.mixedEmbedding.indexEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：indexEquiv : (index K) ≃ (K ->+* Complex)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Equiv` between `index K` and `K →+* ℂ` defined by sending a real infinite p
lace `w` to
the unique corresponding embedding `w.embedding`, and the pair `⟨w, 0⟩` (resp. `
⟨w, 1⟩`) for a
complex infinite place `w` to `w.embedding` (resp. `conjugate w.embedding`).
-/
def indexEquiv : (index K) ≃ (K →+* ℂ) := by
  refine Equiv.ofBijective (fun c => ?_)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩)
  · cases c with
    | inl w => exact w.val.embedding
    | inr wj => rcases wj with ⟨w, j⟩
                exact if j = 0 then w.val.embedding else ComplexEmbedding.conjugate w.val.embedding
  · intro φ
    by_cases hφ : ComplexEmbedding.IsReal φ
    · exact ⟨Sum.inl (InfinitePlace.mkReal ⟨φ, hφ⟩), by simp [embedding_mk_eq_of_isReal hφ]⟩
    · by_cases hw : (InfinitePlace.mk φ).embedding = φ
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 0⟩, by simp [hw]⟩
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 1⟩,
          by simp [(embedding_mk_eq φ).resolve_left hw]⟩
  · rw [Embeddings.card, ← mixedEmbedding.finrank K,
      ← Module.finrank_eq_card_basis (stdBasis K)]

variable {K}

@[simp]
/-
**NumberField.mixedEmbedding.indexEquiv_apply_isReal** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：indexEquiv_apply_isReal (w : {w : InfinitePlace K // IsReal w}) : (indexEq
uiv K) (Sum.inl w) = w.val.embedding
参数：w : {w : InfinitePlace K // IsReal w}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem indexEquiv_apply_isReal (w : {w : InfinitePlace K // IsReal w}) :
    (indexEquiv K) (Sum.inl w) = w.val.embedding := rfl

@[simp]
/-
**NumberField.mixedEmbedding.indexEquiv_apply_isComplex_fst** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：indexEquiv_apply_isComplex_fst (w : {w : InfinitePlace K // IsComplex w}) 
: (indexEquiv K) (Sum.inr ⟨w, 0⟩) = w.val.embedding
参数：w : {w : InfinitePlace K // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem indexEquiv_apply_isComplex_fst (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 0⟩) = w.val.embedding := rfl

@[simp]
/-
**NumberField.mixedEmbedding.indexEquiv_apply_isComplex_snd** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：indexEquiv_apply_isComplex_snd (w : {w : InfinitePlace K // IsComplex w}) 
: (indexEquiv K) (Sum.inr ⟨w, 1⟩) = ComplexEmbedding.conjugate w.val.embedding
参数：w : {w : InfinitePlace K // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem indexEquiv_apply_isComplex_snd (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 1⟩) = ComplexEmbedding.conjugate w.val.embedding := rfl

variable (K)

open scoped Classical in
/-- The matrix that gives the representation on `stdBasis` of the image by `commMap` of an
element `x` of `(K →+* ℂ) → ℂ` fixed by the map `x_φ ↦ conj x_(conjugate φ)`,
see `stdBasis_repr_eq_matrixToStdBasis_mul`. -/
/-
**NumberField.mixedEmbedding.matrixToStdBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：matrixToStdBasis : Matrix (index K) (index K) Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix that gives the representation on `stdBasis` of the image by `commMap`
 of an
element `x` of `(K →+* ℂ) → ℂ` fixed by the map `x_φ ↦ conj x_(conjugate φ)`,
see `stdBasis_repr_eq_matrixToStdBasis_mul`.
-/
def matrixToStdBasis : Matrix (index K) (index K) ℂ :=
  fromBlocks (diagonal fun _ => 1) 0 0 <| reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (blockDiagonal (fun _ => (2 : ℂ)⁻¹ • !![1, 1; -I, I]))

open scoped Classical in
/-
**NumberField.mixedEmbedding.det_matrixToStdBasis** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：det_matrixToStdBasis : (matrixToStdBasis K).det = (2⁻¹ * I) ^ nrComplexPla
ces K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.matrixToStdBasis.eq_1`：∀ (K : Type u_1) [inst
 : Field K],   NumberField.mixedEmbedding.matrixToStdBasis K =     Matrix.fromBl
ocks (Matrix.diagonal fun x => 1) 0 0 …
· 使用定理 `Matrix.det_fromBlocks_zero₂₁`：det_fromBlocks_zero₂₁ (A : Matrix m m R) (
B : Matrix m n R) (D : Matrix n n R) : (Matrix.fromBlocks A B 0 D).det = A.det *
 D.det
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `Matrix.det_blockDiagonal`：det_blockDiagonal {o : Type*} [Fintype o] [Dec
idableEq o] (M : o -> Matrix n n R) : (blockDiagonal M).det = ∏ k, (M k).det
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.smul_cons`：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M
 α] (x : M) (y : α) (v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (
x • y)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.smul_empty`：∀ {α : Type u_1} {M : Type u_2} [inst : SMul M α] (x 
: M) (v : Fin 0 → α), x • v = ![]
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
（共 62 条，此处仅展示前 30 条）
-/
theorem det_matrixToStdBasis :
    (matrixToStdBasis K).det = (2⁻¹ * I) ^ nrComplexPlaces K :=
  calc
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, det ((2 : ℂ)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrixToStdBasis, det_fromBlocks_zero₂₁, det_diagonal, prod_const_one, one_mul,
          det_reindex_self, det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, (2⁻¹ * Complex.I) := by
      refine prod_congr (Eq.refl _) (fun _ _ => ?_)
      simp [field]; ring
  _ = (2⁻¹ * Complex.I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} := by
      rw [prod_const, Fintype.card]

open scoped Classical in
/-- Let `x : (K →+* ℂ) → ℂ` such that `x_φ = conj x_(conj φ)` for all `φ : K →+* ℂ`, then the
representation of `commMap K x` on `stdBasis` is given (up to reindexing) by the product of
`matrixToStdBasis` by `x`. -/
/-
**NumberField.mixedEmbedding.stdBasis_repr_eq_matrixToStdBasis_mul** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：stdBasis_repr_eq_matrixToStdBasis_mul (x : (K ->+* Complex) -> Complex) (h
x : forall φ, conj (x φ) = x (ComplexEmbedding.conjugate φ)) (c : index K) : ((s
tdBasis K).repr (commMap K x) c : Complex) = (matrixToStdBasis K *ᵥ (x ∘ (indexE
quiv K))) c
参数：x : (K ->+* Complex) -> Complex；hx : forall φ, conj (x φ) = x (ComplexEmbeddi
ng.conjugate φ)；c : index K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.smul_cons`：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M
 α] (x : M) (y : α) (v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (
x • y)…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.smul_empty`：∀ {α : Type u_1} {M : Type u_2} [inst : SMul M α] (x 
: M) (v : Fin 0 → α), x • v = ![]
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NumberField.InfinitePlace.conjugate_embedding_eq_of_isReal`：conjugate_em
bedding_eq_of_isReal {w : InfinitePlace K} (h : IsReal w) : ComplexEmbedding.con
jugate (embedding w) = embedding w
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
（共 129 条，此处仅展示前 30 条）

--- 原说明 ---
Let `x : (K →+* ℂ) → ℂ` such that `x_φ = conj x_(conj φ)` for all `φ : K →+* ℂ`,
 then the
representation of `commMap K x` on `stdBasis` is given (up to reindexing) by the
 product of
`matrixToStdBasis` by `x`.
-/
theorem stdBasis_repr_eq_matrixToStdBasis_mul (x : (K →+* ℂ) → ℂ)
    (hx : ∀ φ, conj (x φ) = x (ComplexEmbedding.conjugate φ)) (c : index K) :
    ((stdBasis K).repr (commMap K x) c : ℂ) =
      (matrixToStdBasis K *ᵥ (x ∘ (indexEquiv K))) c := by
  simp_rw [commMap, matrixToStdBasis, LinearMap.coe_mk, AddHom.coe_mk,
    mulVec, dotProduct, Function.comp_apply, index, Fintype.sum_sum_type,
    diagonal_one, reindex_apply, ← univ_product_univ, sum_product,
    indexEquiv_apply_isReal, Fin.sum_univ_two, indexEquiv_apply_isComplex_fst,
    indexEquiv_apply_isComplex_snd, smul_of, smul_cons, smul_eq_mul,
    mul_one, Matrix.smul_empty, Equiv.prodComm_symm, Equiv.coe_prodComm]
  cases c with
  | inl w =>
      simp_rw [stdBasis_apply_isReal, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
        add_zero, sum_const_zero, add_zero, ← conj_eq_iff_re, hx (embedding w.val),
        conjugate_embedding_eq_of_isReal w.prop]
  | inr c =>
    rcases c with ⟨w, j⟩
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, stdBasis_apply_isComplex_fst, re_eq_add_conj,
        mul_neg, fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul, sum_const_zero,
        fromBlocks_apply₂₂, submatrix_apply, Prod.swap_prod_mk, blockDiagonal_apply, of_apply,
        cons_val', cons_val_zero, empty_val', cons_val_fin_one, ite_mul, cons_val_one,
        sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← hx (embedding w), zero_add]
      ring
    · simp only [Fin.mk_one, Fin.isValue, stdBasis_apply_isComplex_snd, im_eq_sub_conj,
        mul_neg, fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul, sum_const_zero,
        fromBlocks_apply₂₂, submatrix_apply, Prod.swap_prod_mk, blockDiagonal_apply, of_apply,
        cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, ite_mul, neg_mul,
        sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← hx (embedding w), zero_add]
      ring_nf; simp [field]

end stdBasis

noncomputable section integerLattice

variable [NumberField K]

open Module.Free

open scoped nonZeroDivisors

/-- The image of the ring of integers of `K` in the mixed space. -/
/-
**NumberField.mixedEmbedding.integerLattice** 是 Mathlib 中的一个定义，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：(K : Type u_1) → [inst : Field K] → Submodule ℤ (NumberField.mixedEmbeddin
g.mixedSpace K)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of the ring of integers of `K` in the mixed space.
-/
protected abbrev integerLattice : Submodule ℤ (mixedSpace K) :=
  LinearMap.range ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap

/-- A `ℝ`-basis of the mixed space that is also a `ℤ`-basis of the image of `𝓞 K`. -/
/-
**NumberField.mixedEmbedding.latticeBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberField
.mixedEmbedding`。
形式化陈述：latticeBasis : Basis (ChooseBasisIndex Int (𝓞 K)) Real (mixedSpace K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
A `ℝ`-basis of the mixed space that is also a `ℤ`-basis of the image of `𝓞 K`.
-/
def latticeBasis :
    Basis (ChooseBasisIndex ℤ (𝓞 K)) ℝ (mixedSpace K) := by
  classical
    -- We construct an `ℝ`-linear independent family from the image of
    -- `canonicalEmbedding.lattice_basis` by `commMap`
    have := LinearIndependent.map (LinearIndependent.restrict_scalars
      (by { simpa only [Complex.real_smul, mul_one] using Complex.ofReal_injective })
      (canonicalEmbedding.latticeBasis K).linearIndependent)
      (disjoint_span_commMap_ker K)
    -- and it's a basis since it has the right cardinality
    refine basisOfLinearIndependentOfCardEqFinrank this ?_
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_prod, finrank_pi,
      finrank_pi_fintype, Complex.finrank_real_complex, sum_const, card_univ, ← nrRealPlaces,
      ← nrComplexPlaces, ← card_real_embeddings, smul_eq_mul, mul_comm,
      ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
      Nat.add_sub_of_le (Fintype.card_subtype_le _)]

@[simp]
/-
**NumberField.mixedEmbedding.latticeBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.mixedEmbedding`。
形式化陈述：latticeBasis_apply (i : ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (
mixedEmbedding K) (integralBasis K i)
参数：i : ChooseBasisIndex Int (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `NumberField.canonicalEmbedding.latticeBasis_apply`：latticeBasis_apply [N
umberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (canoni
calEmbedding K) (integralBasis K i)
· 使用定理 `NumberField.integralBasis_apply`：integralBasis_apply (i : Free.ChooseBas
isIndex Int (𝓞 K)) : integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basi
s K i)
· 使用定理 `NumberField.mixedEmbedding.commMap_canonical_eq_mixed`：commMap_canonical
_eq_mixed (x : K) : commMap K (canonicalEmbedding K x) = mixedEmbedding K x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem latticeBasis_apply (i : ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (mixedEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, commMap_canonical_eq_mixed]
/-
**NumberField.mixedEmbedding.mem_span_latticeBasis** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：mem_span_latticeBasis {x : (mixedSpace K)} : x in Submodule.span Int (Set.
range (latticeBasis K)) ↔ x in mixedEmbedding.integerLattice K
参数：mixedSpace K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.latticeBasis_apply`：latticeBasis_apply (i : C
hooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (mixedEmbedding K) (integralBasi
s K i)
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.mem_span_integralBasis`：mem_span_integralBasis {x : K} : x i
n Submodule.span Int (Set.range (integralBasis K)) ↔ x in (algebraMap (𝓞 K) K).r
ange
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_span_latticeBasis {x : (mixedSpace K)} :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔
      x ∈ mixedEmbedding.integerLattice K := by
  rw [show Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  simp only [Set.mem_image, SetLike.mem_coe, mem_span_integralBasis K,
    RingHom.mem_range, exists_exists_eq_and]
  rfl
/-
**NumberField.mixedEmbedding.span_latticeBasis** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：span_latticeBasis : Submodule.span Int (Set.range (latticeBasis K)) = mixe
dEmbedding.integerLattice K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Submodule.ext_iff`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p q : Submodule R M}, p = 
q ↔ ∀ (…
· 使用定理 `NumberField.mixedEmbedding.mem_span_latticeBasis`：mem_span_latticeBasis 
{x : (mixedSpace K)} : x in Submodule.span Int (Set.range (latticeBasis K)) ↔ x 
in mixedEmbedding.integerLattice K
-/
theorem span_latticeBasis :
    Submodule.span ℤ (Set.range (latticeBasis K)) = mixedEmbedding.integerLattice K :=
  Submodule.ext_iff.mpr fun _ ↦ mem_span_latticeBasis K
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology (mixedEmbedding.integerLattice K) := by
  classical
  rw [← span_latticeBasis]
  infer_instance

open scoped Classical in
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZLattice ℝ (mixedEmbedding.integerLattice K) := by
  simp_rw [← span_latticeBasis]
  infer_instance

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalDomain_integerLattice** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：fundamentalDomain_integerLattice : MeasureTheory.IsAddFundamentalDomain (m
ixedEmbedding.integerLattice K) (ZSpan.fundamentalDomain (latticeBasis K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.span_latticeBasis`：span_latticeBasis : Submod
ule.span Int (Set.range (latticeBasis K)) = mixedEmbedding.integerLattice K
· 使用定理 `ZSpan.isAddFundamentalDomain`：∀ {E : Type u_1} {ι : Type u_2} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finit
e ι] [inst_3 : Mea…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
-/
theorem fundamentalDomain_integerLattice :
    MeasureTheory.IsAddFundamentalDomain (mixedEmbedding.integerLattice K)
      (ZSpan.fundamentalDomain (latticeBasis K)) := by
  rw [← span_latticeBasis]
  exact ZSpan.isAddFundamentalDomain (latticeBasis K) _
/-
**NumberField.mixedEmbedding.mem_rat_span_latticeBasis** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.mixedEmbedding`。
形式化陈述：mem_rat_span_latticeBasis (x : K) : mixedEmbedding K x in Submodule.span R
at (Set.range (latticeBasis K))
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `Submodule.sum_smul_mem`：sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι 
-> R) (hyp : forall c in t, f c in p) : (∑ i in t, r i • f i) in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `NumberField.mixedEmbedding.latticeBasis_apply`：latticeBasis_apply (i : C
hooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (mixedEmbedding K) (integralBasi
s K i)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem mem_rat_span_latticeBasis (x : K) :
    mixedEmbedding K x ∈ Submodule.span ℚ (Set.range (latticeBasis K)) := by
  rw [← Basis.sum_repr (integralBasis K) x, map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ ↦ Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

set_option backward.isDefEq.respectTransparency.types false in
/-
**NumberField.mixedEmbedding.latticeBasis_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：latticeBasis_repr_apply (x : K) (i : ChooseBasisIndex Int (𝓞 K)) : (lattic
eBasis K).repr (mixedEmbedding K x) i = (integralBasis K).repr x i
参数：x : K；i : ChooseBasisIndex Int (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `NumberField.mixedEmbedding.mem_rat_span_latticeBasis`：mem_rat_span_latti
ceBasis (x : K) : mixedEmbedding K x in Submodule.span Rat (Set.range (latticeBa
sis K))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.restrictScalars_repr_apply`：∀ {ι : Type u_1} (R : Type u_3)
 {M : Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst
_2 : Ring S] [inst_3 : Nontri…
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `Rat.cast_inj`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] {p q
 : ℚ}, ↑p = ↑q ↔ p = q
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `LinearMap.codRestrict_apply`：codRestrict_apply (p : Submodule R₂ M₂) (f 
: M ->ₛₗ[σ₁₂] M₂) {h} (x : M) : (codRestrict p f h x : M₂) = f x
· 使用定理 `AlgHom.toLinearMap_apply`：toLinearMap_apply (p : A) : φ.toLinearMap p = 
φ p
· 使用定理 `Module.Basis.restrictScalars_apply`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst_2 : 
Ring S] [inst_3 : Nontri…
· 使用定理 `NumberField.mixedEmbedding.latticeBasis_apply`：latticeBasis_apply (i : C
hooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (mixedEmbedding K) (integralBasi
s K i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem latticeBasis_repr_apply (x : K) (i : ChooseBasisIndex ℤ (𝓞 K)) :
    (latticeBasis K).repr (mixedEmbedding K x) i = (integralBasis K).repr x i := by
  rw [← Basis.restrictScalars_repr_apply ℚ _ ⟨_, mem_rat_span_latticeBasis K x⟩, eq_ratCast,
    Rat.cast_inj]
  let f := (mixedEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x ↦ mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars ℚ).repr.toLinearMap ∘ₗ f =
    (integralBasis K).repr.toLinearMap from DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext (integralBasis K) (fun i ↦ ?_)
  have : f (integralBasis K i) = ((latticeBasis K).restrictScalars ℚ) i := by
    apply Subtype.val_injective
    rw [LinearMap.codRestrict_apply, AlgHom.toLinearMap_apply, Basis.restrictScalars_apply,
      latticeBasis_apply]
    rfl
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The image of the fractional ideal `I` in the mixed space. -/
/-
**NumberField.mixedEmbedding.idealLattice** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：idealLattice (K : Type*) [Field K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Sub
module Int (mixedSpace K)
参数：K : Type*；I : (FractionalIdeal (𝓞 K)⁰ K)ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of the fractional ideal `I` in the mixed space.
-/
abbrev idealLattice (K : Type*) [Field K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedSpace K) := LinearMap.range <|
  (mixedEmbedding K).toIntAlgHom.toLinearMap ∘ₗ ((I : Submodule (𝓞 K) K).subtype.restrictScalars ℤ)
/-
**NumberField.mixedEmbedding.mem_idealLattice** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：mem_idealLattice (K : Type*) [Field K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {
x : mixedSpace K} : x in idealLattice K I ↔ exists y, y in (I : Set K) ∧ mixedEm
bedding K y = x
参数：K : Type*；I : (FractionalIdeal (𝓞 K)⁰ K)ˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_idealLattice (K : Type*) [Field K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : mixedSpace K} :
    x ∈ idealLattice K I ↔ ∃ y, y ∈ (I : Set K) ∧ mixedEmbedding K y = x := by
  simp [idealLattice]

/-- The generalized index of the lattice generated by `I` in the lattice generated by
`𝓞 K` is equal to the norm of the ideal `I`. The result is stated in terms of base change
determinant and is the translation of `NumberField.det_basisOfFractionalIdeal_eq_absNorm` in
the mixed space. This is useful, in particular, to prove that the family obtained from
the `ℤ`-basis of `I` is actually an `ℝ`-basis of the mixed space, see
`fractionalIdealLatticeBasis`. -/
/-
**NumberField.mixedEmbedding.det_basisOfFractionalIdeal_eq_norm** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：det_basisOfFractionalIdeal_eq_norm (e : (ChooseBasisIndex Int (𝓞 K)) ≃ (Ch
ooseBasisIndex Int I)) : |Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basis
OfFractionalIdeal K I) ∘ e))| = FractionalIdeal.absNorm I.1
参数：e : (ChooseBasisIndex Int (𝓞 K)) ≃ (ChooseBasisIndex Int I)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `NumberField.mixedEmbedding.latticeBasis_repr_apply`：latticeBasis_repr_ap
ply (x : K) (i : ChooseBasisIndex Int (𝓞 K)) : (latticeBasis K).repr (mixedEmbed
ding K x) i = (integralBasis K).repr x i
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `NumberField.det_basisOfFractionalIdeal_eq_absNorm`：det_basisOfFractional
Ideal_eq_absNorm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (e : (Free.ChooseBasisIndex I
nt (𝓞 K)) ≃ (Free.ChooseBasisIndex Int …

--- 原说明 ---
The generalized index of the lattice generated by `I` in the lattice generated b
y
`𝓞 K` is equal to the norm of the ideal `I`. The result is stated in terms of ba
se change
determinant and is the translation of `NumberField.det_basisOfFractionalIdeal_eq
_absNorm` in
the mixed space. This is useful, in particular, to prove that the family obtaine
d from
the `ℤ`-basis of `I` is actually an `ℝ`-basis of the mixed space, see
`fractionalIdealLatticeBasis`.
-/
theorem det_basisOfFractionalIdeal_eq_norm
    (e : (ChooseBasisIndex ℤ (𝓞 K)) ≃ (ChooseBasisIndex ℤ I)) :
    |Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e))| =
      FractionalIdeal.absNorm I.1 := by
  suffices Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e)) =
      (algebraMap ℚ ℝ) ((Basis.det (integralBasis K)) ((basisOfFractionalIdeal K I) ∘ e)) by
    rw [this, eq_ratCast, ← Rat.cast_abs, ← Equiv.symm_symm e, ← Basis.coe_reindex,
      det_basisOfFractionalIdeal_eq_absNorm K I e]
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr
  ext i j
  simp_rw [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, Function.comp_apply]
  exact latticeBasis_repr_apply K _ i

/-- A `ℝ`-basis of the mixed space of `K` that is also a `ℤ`-basis of the image of the fractional
ideal `I`. -/
/-
**NumberField.mixedEmbedding.fractionalIdealLatticeBasis** 是 Mathlib 中的一个定义，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：fractionalIdealLatticeBasis : Basis (ChooseBasisIndex Int I) Real (mixedSp
ace K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K

--- 原说明 ---
A `ℝ`-basis of the mixed space of `K` that is also a `ℤ`-basis of the image of t
he fractional
ideal `I`.
-/
def fractionalIdealLatticeBasis :
    Basis (ChooseBasisIndex ℤ I) ℝ (mixedSpace K) := by
  let e : (ChooseBasisIndex ℤ (𝓞 K)) ≃ (ChooseBasisIndex ℤ I) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      fractionalIdeal_rank]
  refine Basis.reindex ?_ e
  suffices IsUnit ((latticeBasis K).det ((mixedEmbedding K) ∘ (basisOfFractionalIdeal K I) ∘ e)) by
    rw [← Basis.is_basis_iff_det] at this
    exact Basis.mk this.1 (by rw [this.2])
  rw [isUnit_iff_ne_zero, ne_eq, ← abs_eq_zero.not, det_basisOfFractionalIdeal_eq_norm,
    Rat.cast_eq_zero, FractionalIdeal.absNorm_eq_zero_iff]
  exact Units.ne_zero I

@[simp]
/-
**NumberField.mixedEmbedding.fractionalIdealLatticeBasis_apply** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：fractionalIdealLatticeBasis_apply (i : ChooseBasisIndex Int I) : fractiona
lIdealLatticeBasis K I i = (mixedEmbedding K) (basisOfFractionalIdeal K I i)
参数：i : ChooseBasisIndex Int I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fractionalIdealLatticeBasis_apply (i : ChooseBasisIndex ℤ I) :
    fractionalIdealLatticeBasis K I i = (mixedEmbedding K) (basisOfFractionalIdeal K I i) := by
  simp only [fractionalIdealLatticeBasis, Basis.coe_reindex, Basis.coe_mk, Function.comp_apply,
    Equiv.apply_symm_apply]
/-
**NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：mem_span_fractionalIdealLatticeBasis {x : (mixedSpace K)} : x in Submodule
.span Int (Set.range (fractionalIdealLatticeBasis K I)) ↔ x in mixedEmbedding K 
'' I
参数：mixedSpace K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.fractionalIdealLatticeBasis_apply`：fractional
IdealLatticeBasis_apply (i : ChooseBasisIndex Int I) : fractionalIdealLatticeBas
is K I i = (mixedEmbedding K) (basisOfFractionalId…
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_span_fractionalIdealLatticeBasis {x : (mixedSpace K)} :
    x ∈ Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I)) ↔
      x ∈ mixedEmbedding K '' I := by
  rw [show Set.range (fractionalIdealLatticeBasis K I) =
        (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (basisOfFractionalIdeal K I)) by
      rw [← Set.range_comp]
      exact congr_arg Set.range (funext (fun i ↦ fractionalIdealLatticeBasis_apply K I i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [show Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) = (I : Set K) by
        ext; simp [mem_span_basisOfFractionalIdeal]]
  rfl
/-
**NumberField.mixedEmbedding.span_idealLatticeBasis** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.mixedEmbedding`。
形式化陈述：span_idealLatticeBasis : (Submodule.span Int (Set.range (fractionalIdealLa
tticeBasis K I))) = (mixedEmbedding.idealLattice K I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem span_idealLatticeBasis :
    (Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I))) =
      (mixedEmbedding.idealLattice K I) := by
  ext x
  simp [mem_span_fractionalIdealLatticeBasis]
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology (mixedEmbedding.idealLattice K I) := by
  classical
  rw [← span_idealLatticeBasis]
  infer_instance

open scoped Classical in
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZLattice ℝ (mixedEmbedding.idealLattice K I) := by
  simp_rw [← span_idealLatticeBasis]
  infer_instance

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalDomain_idealLattice** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：fundamentalDomain_idealLattice : MeasureTheory.IsAddFundamentalDomain (mix
edEmbedding.idealLattice K I) (ZSpan.fundamentalDomain (fractionalIdealLatticeBa
sis K I))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.span_idealLatticeBasis`：span_idealLatticeBasi
s : (Submodule.span Int (Set.range (fractionalIdealLatticeBasis K I))) = (mixedE
mbedding.idealLattice K I)
· 使用定理 `ZSpan.isAddFundamentalDomain`：∀ {E : Type u_1} {ι : Type u_2} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finit
e ι] [inst_3 : Mea…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
-/
theorem fundamentalDomain_idealLattice :
    MeasureTheory.IsAddFundamentalDomain (mixedEmbedding.idealLattice K I)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) := by
  rw [← span_idealLatticeBasis]
  exact ZSpan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) _

end integerLattice

noncomputable section

namespace euclidean

open MeasureTheory NumberField Submodule

/-- The mixed space `ℝ^r₁ × ℂ^r₂`, with `(r₁, r₂)` the signature of `K`, as a Euclidean space. -/
/-
**NumberField.mixedEmbedding.euclidean.mixedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Num
berField.mixedEmbedding.euclidean`。
形式化陈述：(K : Type u_1) → [Field K] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mixed space `ℝ^r₁ × ℂ^r₂`, with `(r₁, r₂)` the signature of `K`, as a Euclid
ean space.
-/
protected abbrev mixedSpace :=
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))
/-
**NumberField.mixedEmbedding.euclidean.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.m
ixedEmbedding.euclidean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring (euclidean.mixedSpace K) :=
  have : Ring (EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) := (WithLp.equiv 2 _).ring
  have : Ring (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w}) := (WithLp.equiv 2 _).ring
  (WithLp.equiv 2 _).ring

variable [NumberField K]

open scoped Classical in
/-- The continuous linear equivalence between the Euclidean mixed space and the mixed space. -/
/-
**NumberField.mixedEmbedding.euclidean.toMixed** 是 Mathlib 中的一个定义，位于命名空间 `Number
Field.mixedEmbedding.euclidean`。
形式化陈述：toMixed : (euclidean.mixedSpace K) ≃L[Real] (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous linear equivalence between the Euclidean mixed space and the mixe
d space.
-/
def toMixed : (euclidean.mixedSpace K) ≃L[ℝ] (mixedSpace K) :=
  (WithLp.linearEquiv _ _ _).trans
    ((WithLp.linearEquiv _ _ _).prodCongr (WithLp.linearEquiv _ _ _)) |>.toContinuousLinearEquiv
/-
**NumberField.mixedEmbedding.euclidean.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.m
ixedEmbedding.euclidean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (euclidean.mixedSpace K) := (toMixed K).toEquiv.nontrivial
/-
**NumberField.mixedEmbedding.euclidean.finrank** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding.euclidean`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Module.finra
nk ℝ (NumberField.mixedEmbedding.euclidean.mixedSpace K) = Module.finrank ℚ K
参数：K : Type u_1；NumberField.mixedEmbedding.euclidean.mixedSpace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `NumberField.mixedEmbedding.finrank`：∀ (K : Type u_1) [inst : Field K] [i
nst_1 : NumberField K],   Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpac
e K) = Module.finrank ℚ …
-/
protected theorem finrank :
    finrank ℝ (euclidean.mixedSpace K) = finrank ℚ K := by
  rw [LinearEquiv.finrank_eq (toMixed K).toLinearEquiv, mixedEmbedding.finrank]

open scoped Classical in
/-- An orthonormal basis of the Euclidean mixed space. -/
/-
**NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis** 是 Mathlib 中的一个定义，位于
命名空间 `NumberField.mixedEmbedding.euclidean`。
形式化陈述：stdOrthonormalBasis : OrthonormalBasis (index K) Real (euclidean.mixedSpac
e K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
An orthonormal basis of the Euclidean mixed space.
-/
def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (euclidean.mixedSpace K) :=
  OrthonormalBasis.prod (EuclideanSpace.basisFun _ ℝ)
    ((Pi.orthonormalBasis fun _ ↦ Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

open scoped Classical in
/-
**NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.mixedEmbedding.euclidean`。
形式化陈述：stdOrthonormalBasis_map_eq : (euclidean.stdOrthonormalBasis K).toBasis.map
 (toMixed K).toLinearEquiv = mixedEmbedding.stdBasis K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem stdOrthonormalBasis_map_eq :
    (euclidean.stdOrthonormalBasis K).toBasis.map (toMixed K).toLinearEquiv =
      mixedEmbedding.stdBasis K := by
  ext <;> rfl

open scoped Classical in
/-
**NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.euclidean`。
形式化陈述：volumePreserving_toMixed : MeasurePreserving (toMixed K) where measurable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.addHaar_eq_volume`：OrthonormalBasis.addHaar_eq_volume {
ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace Real F] [Fini
teDimensional Real F] [M…
· 使用定理 `Module.Basis.map_addHaar`：map_addHaar {ι E F : Type*} [Fintype ι] [Norme
dAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F
] [MeasurableS…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `instSigmaCompactSpaceProd`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y] [SigmaCompactSpace X]   [SigmaCompa
ctSpace Y], Sig…
· 使用定理 `instSigmaCompactSpaceForallOfFinite`：∀ {ι : Type u_3} [Finite ι] {X : ι 
→ Type u_4} [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), SigmaCompact
Space (X i)], SigmaCompac…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
（共 49 条，此处仅展示前 30 条）
-/
theorem volumePreserving_toMixed :
    MeasurePreserving (toMixed K) where
  measurable := (toMixed K).continuous.measurable
  map_eq := by
    rw [← (OrthonormalBasis.addHaar_eq_volume (euclidean.stdOrthonormalBasis K)), Basis.map_addHaar,
      stdOrthonormalBasis_map_eq, Basis.addHaar_eq_iff, Basis.coe_parallelepiped,
      ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (stdBasis K) volume),
      volume_fundamentalDomain_stdBasis K]

open scoped Classical in
/-
**NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed_symm** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.euclidean`。
形式化陈述：volumePreserving_toMixed_symm : MeasurePreserving (toMixed K).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed`：volumePre
serving_toMixed : MeasurePreserving (toMixed K) where measurable
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
-/
theorem volumePreserving_toMixed_symm :
    MeasurePreserving (toMixed K).symm := by
  have : MeasurePreserving (toMixed K).toHomeomorph.toMeasurableEquiv := volumePreserving_toMixed K
  exact this.symm

open scoped Classical in
/-- The image of ring of integers `𝓞 K` in the Euclidean mixed space. -/
/-
**NumberField.mixedEmbedding.euclidean.integerLattice** 是 Mathlib 中的一个定义，位于命名空间 
`NumberField.mixedEmbedding.euclidean`。
形式化陈述：(K : Type u_1) → [inst : Field K] → [NumberField K] → Submodule ℤ (NumberF
ield.mixedEmbedding.euclidean.mixedSpace K)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The image of ring of integers `𝓞 K` in the Euclidean mixed space.
-/
protected def integerLattice : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.integerLattice K) (toMixed K).toLinearMap
/-
**NumberField.mixedEmbedding.euclidean.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.m
ixedEmbedding.euclidean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology (euclidean.integerLattice K) := by
  rw [euclidean.integerLattice]
  infer_instance

open scoped Classical in
/-
**NumberField.mixedEmbedding.euclidean.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.m
ixedEmbedding.euclidean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZLattice ℝ (euclidean.integerLattice K) := by
  simp_rw [euclidean.integerLattice]
  infer_instance

end euclidean

end

noncomputable section plusPart

open ContinuousLinearEquiv

variable {K} (s : Set {w : InfinitePlace K // IsReal w})

open scoped Classical in
/-- Let `s` be a set of real places, define the continuous linear equiv of the mixed space that
swaps sign at places in `s` and leaves the rest unchanged. -/
/-
**NumberField.mixedEmbedding.negAt** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.mixedE
mbedding`。
形式化陈述：negAt : mixedSpace K ≃L[Real] mixedSpace K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `s` be a set of real places, define the continuous linear equiv of the mixed
 space that
swaps sign at places in `s` and leaves the rest unchanged.
-/
def negAt :
    mixedSpace K ≃L[ℝ] mixedSpace K :=
  (piCongrRight fun w ↦ if w ∈ s then neg ℝ else ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.refl ℝ _)

variable {s}

@[simp]
/-
**NumberField.mixedEmbedding.negAt_apply_isReal_and_mem** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：negAt_apply_isReal_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : 
w in s) : (negAt s x).1 w = -x.1 w
参数：x : mixedSpace K；hw : w in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearEquiv.neg_apply`：neg_apply [ContinuousNeg M] (x : M) : n
eg R x = -x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem negAt_apply_isReal_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∈ s) :
    (negAt s x).1 w = -x.1 w := by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_pos hw,
    ContinuousLinearEquiv.neg_apply]

@[simp]
/-
**NumberField.mixedEmbedding.negAt_apply_isReal_and_notMem** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding`。
形式化陈述：negAt_apply_isReal_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw
 : w ∉ s) : (negAt s x).1 w = x.1 w
参数：x : mixedSpace K；hw : w ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem negAt_apply_isReal_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) :
    (negAt s x).1 w = x.1 w := by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_neg hw,
    ContinuousLinearEquiv.refl_apply]

@[simp]
/-
**NumberField.mixedEmbedding.negAt_apply_isComplex** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：negAt_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) : (negAt
 s x).2 w = x.2 w
参数：x : mixedSpace K；w : {w // IsComplex w}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem negAt_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    (negAt s x).2 w = x.2 w := rfl

@[simp]
/-
**NumberField.mixedEmbedding.negAt_apply_snd** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.mixedEmbedding`。
形式化陈述：negAt_apply_snd (x : mixedSpace K) : (negAt s x).2 = x.2
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem negAt_apply_snd (x : mixedSpace K) :
    (negAt s x).2 = x.2 := rfl
/-
**NumberField.mixedEmbedding.negAt_apply_norm_isReal** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：negAt_apply_norm_isReal (x : mixedSpace K) (w : {w // IsReal w}) : ‖(negAt
 s x).1 w‖ = ‖x.1 w‖
参数：x : mixedSpace K；w : {w // IsReal w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_mem`：negAt_apply_isRea
l_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w in s) : (negAt s x).1
 w = -x.1 w
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_notMem`：negAt_apply_is
Real_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) : (negAt s
 x).1 w = x.1 w
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem negAt_apply_norm_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    ‖(negAt s x).1 w‖ = ‖x.1 w‖ := by
  by_cases hw : w ∈ s <;> simp [hw]

open MeasureTheory Classical in
/-- `negAt` preserves the volume . -/
/-
**NumberField.mixedEmbedding.volume_preserving_negAt** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：volume_preserving_negAt [NumberField K] : MeasurePreserving (negAt s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.prod`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {δ : T…
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.volume_preserving_pi`：volume_preserving_pi {α' β' : ι -> T
ype*} [forall i, MeasureSpace (α' i)] [forall i, MeasureSpace (β' i)] [forall i,
 SigmaFinite (volume : M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.Measure.measurePreserving_neg`：∀ {G : Type u_1} [inst : Me
asurableSpace G] [inst_1 : Neg G] [MeasurableNeg G] (μ : MeasureTheory.Measure G
)   [μ.IsNegInvariant], MeasureTh…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.MeasurePreserving.id`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (μ : MeasureTheory.Measure α), MeasureTheory.MeasurePreserving id μ μ

--- 原说明 ---
`negAt` preserves the volume .
-/
theorem volume_preserving_negAt [NumberField K] :
    MeasurePreserving (negAt s) := by
  refine MeasurePreserving.prod (volume_preserving_pi fun w ↦ ?_) (MeasurePreserving.id _)
  by_cases hw : w ∈ s
  · simp_rw [if_pos hw]
    exact Measure.measurePreserving_neg _
  · simp_rw [if_neg hw]
    exact MeasurePreserving.id _

variable (s) in
/-- `negAt` preserves `normAtPlace`. -/
@[simp]
/-
**NumberField.mixedEmbedding.normAtPlace_negAt** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：normAtPlace_negAt (x : mixedSpace K) (w : InfinitePlace K) : normAtPlace w
 (negAt s x) = normAtPlace w x
参数：x : mixedSpace K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_norm_isReal`：negAt_apply_norm_isR
eal (x : mixedSpace K) (w : {w // IsReal w}) : ‖(negAt s x).1 w‖ = ‖x.1 w‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖

--- 原说明 ---
`negAt` preserves `normAtPlace`.
-/
theorem normAtPlace_negAt (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (negAt s x) = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtPlace_apply_of_isReal hw, negAt_apply_norm_isReal]
  · simp_rw [normAtPlace_apply_of_isComplex hw, negAt_apply_isComplex]

/-- `negAt` preserves the `norm`. -/
@[simp]
/-
**NumberField.mixedEmbedding.norm_negAt** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：norm_negAt [NumberField K] (x : mixedSpace K) : mixedEmbedding.norm (negAt
 s x) = mixedEmbedding.norm x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.norm_eq_of_normAtPlace_eq`：norm_eq_of_normAtP
lace_eq {x y : mixedSpace K} (h : forall w, normAtPlace w x = normAtPlace w y) :
 mixedEmbedding.norm x = mixedEmbedding.no…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_negAt`：normAtPlace_negAt (x : mix
edSpace K) (w : InfinitePlace K) : normAtPlace w (negAt s x) = normAtPlace w x

--- 原说明 ---
`negAt` preserves the `norm`.
-/
theorem norm_negAt [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (negAt s x) = mixedEmbedding.norm x :=
  norm_eq_of_normAtPlace_eq (fun w ↦ normAtPlace_negAt _ _ w)

/-- `negAt` is its own inverse. -/
@[simp]
/-
**NumberField.mixedEmbedding.negAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：negAt_symm : (negAt s).symm = negAt s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_mem`：negAt_apply_isRea
l_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w in s) : (negAt s x).1
 w = -x.1 w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearEquiv.neg_apply`：neg_apply [ContinuousNeg M] (x : M) : n
eg R x = -x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_notMem`：negAt_apply_is
Real_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) : (negAt s
 x).1 w = x.1 w
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
`negAt` is its own inverse.
-/
theorem negAt_symm :
    (negAt s).symm = negAt s := by
  ext x w
  · by_cases hw : w ∈ s
    · simp_rw [negAt_apply_isReal_and_mem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_pos hw, symm_neg,
        ContinuousLinearEquiv.neg_apply]
    · simp_rw [negAt_apply_isReal_and_notMem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_neg hw, refl_symm,
        refl_apply]
  · rfl

/-- For `x : mixedSpace K`, the set `signSet x` is the set of real places `w` s.t. `x w ≤ 0`. -/
/-
**NumberField.mixedEmbedding.signSet** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.mixe
dEmbedding`。
形式化陈述：signSet (x : mixedSpace K) : Set {w : InfinitePlace K // IsReal w}
参数：x : mixedSpace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `x : mixedSpace K`, the set `signSet x` is the set of real places `w` s.t. `
x w ≤ 0`.
-/
def signSet (x : mixedSpace K) : Set {w : InfinitePlace K // IsReal w} := {w | x.1 w ≤ 0}

@[simp]
/-
**NumberField.mixedEmbedding.negAt_signSet_apply_isReal** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：negAt_signSet_apply_isReal (x : mixedSpace K) (w : {w // IsReal w}) : (neg
At (signSet x) x).1 w = ‖x.1 w‖
参数：x : mixedSpace K；w : {w // IsReal w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_mem`：negAt_apply_isRea
l_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w in s) : (negAt s x).1
 w = -x.1 w
· 使用定理 `Real.norm_of_nonpos`：norm_of_nonpos (hr : r <= 0) : ‖r‖ = -r
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_notMem`：negAt_apply_is
Real_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) : (negAt s
 x).1 w = x.1 w
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
theorem negAt_signSet_apply_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    (negAt (signSet x) x).1 w = ‖x.1 w‖ := by
  by_cases hw : x.1 w ≤ 0
  · rw [negAt_apply_isReal_and_mem _ hw, Real.norm_of_nonpos hw]
  · rw [negAt_apply_isReal_and_notMem _ hw, Real.norm_of_nonneg (lt_of_not_ge hw).le]

@[simp]
/-
**NumberField.mixedEmbedding.negAt_signSet_apply_isComplex** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding`。
形式化陈述：negAt_signSet_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) 
: (negAt (signSet x) x).2 w = x.2 w
参数：x : mixedSpace K；w : {w // IsComplex w}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem negAt_signSet_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    (negAt (signSet x) x).2 w = x.2 w := rfl

variable (A : Set (mixedSpace K)) {x : mixedSpace K}

variable (s) in
/-- `negAt s A` is also equal to the preimage of `A` by `negAt s`. This fact is used to simplify
some proofs. -/
/-
**NumberField.mixedEmbedding.negAt_preimage** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：negAt_preimage : negAt s ⁻¹' A = negAt s '' A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.image_eq_preimage_symm`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `NumberField.mixedEmbedding.negAt_symm`：negAt_symm : (negAt s).symm = neg
At s

--- 原说明 ---
`negAt s A` is also equal to the preimage of `A` by `negAt s`. This fact is used
 to simplify
some proofs.
-/
theorem negAt_preimage : negAt s ⁻¹' A = negAt s '' A := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm, negAt_symm]

/-- The `plusPart` of a subset `A` of the `mixedSpace` is the set of points in `A` that are
positive at all real places. -/
/-
**NumberField.mixedEmbedding.plusPart** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：plusPart : Set (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `plusPart` of a subset `A` of the `mixedSpace` is the set of points in `A` t
hat are
positive at all real places.
-/
abbrev plusPart : Set (mixedSpace K) := A ∩ {x | ∀ w, 0 < x.1 w}
/-
**NumberField.mixedEmbedding.neg_of_mem_negA_plusPart** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.mixedEmbedding`。
形式化陈述：neg_of_mem_negA_plusPart (hx : x in negAt s '' (plusPart A)) {w : {w // Is
Real w}} (hw : w in s) : x.1 w < 0
参数：hx : x in negAt s '' (plusPart A)；hw : w in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_mem`：negAt_apply_isRea
l_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w in s) : (negAt s x).1
 w = -x.1 w
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem neg_of_mem_negA_plusPart (hx : x ∈ negAt s '' (plusPart A)) {w : {w // IsReal w}}
    (hw : w ∈ s) : x.1 w < 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_mem _ hw, neg_lt_zero]
  exact hy.2 w
/-
**NumberField.mixedEmbedding.pos_of_notMem_negAt_plusPart** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding`。
形式化陈述：pos_of_notMem_negAt_plusPart (hx : x in negAt s '' (plusPart A)) {w : {w /
/ IsReal w}} (hw : w ∉ s) : 0 < x.1 w
参数：hx : x in negAt s '' (plusPart A)；hw : w ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_notMem`：negAt_apply_is
Real_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) : (negAt s
 x).1 w = x.1 w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem pos_of_notMem_negAt_plusPart (hx : x ∈ negAt s '' (plusPart A)) {w : {w // IsReal w}}
    (hw : w ∉ s) : 0 < x.1 w := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_notMem _ hw]
  exact hy.2 w

open scoped Function in -- required for scoped `on` notation
/-- The images of `plusPart` by `negAt` are pairwise disjoint. -/
/-
**NumberField.mixedEmbedding.disjoint_negAt_plusPart** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：disjoint_negAt_plusPart : Pairwise (Disjoint on (fun s => negAt s '' (plus
Part A)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Set.symmDiff_nonempty`：symmDiff_nonempty : (s ∆ t).Nonempty ↔ s != t
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `NumberField.mixedEmbedding.neg_of_mem_negA_plusPart`：neg_of_mem_negA_plu
sPart (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}} (hw : w in s) : 
x.1 w < 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NumberField.mixedEmbedding.pos_of_notMem_negAt_plusPart`：pos_of_notMem_n
egAt_plusPart (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}} (hw : w 
∉ s) : 0 < x.1 w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The images of `plusPart` by `negAt` are pairwise disjoint.
-/
theorem disjoint_negAt_plusPart : Pairwise (Disjoint on (fun s ↦ negAt s '' (plusPart A))) := by
  intro s t hst
  refine Set.disjoint_left.mpr fun _ hx hx' ↦ ?_
  obtain ⟨w, hw | hw⟩ : ∃ w, (w ∈ s ∧ w ∉ t) ∨ (w ∈ t ∧ w ∉ s) := Set.symmDiff_nonempty.mpr hst
  · exact lt_irrefl _ <|
      (neg_of_mem_negA_plusPart A hx hw.1).trans (pos_of_notMem_negAt_plusPart A hx' hw.2)
  · exact lt_irrefl _ <|
      (neg_of_mem_negA_plusPart A hx' hw.1).trans (pos_of_notMem_negAt_plusPart A hx hw.2)

-- We will assume from now that `A` is symmetric at real places
variable (hA : ∀ x, x ∈ A ↔ (fun w ↦ ‖x.1 w‖, x.2) ∈ A)

include hA in
/-
**NumberField.mixedEmbedding.mem_negAt_plusPart_of_mem** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.mixedEmbedding`。
形式化陈述：mem_negAt_plusPart_of_mem (hx₁ : x in A) (hx₂ : forall w, x.1 w != 0) : x 
in negAt s '' (plusPart A) ↔ (forall w, w in s -> x.1 w < 0) ∧ (forall w, w ∉ s 
-> x.1 w > 0)
参数：hx₁ : x in A；hx₂ : forall w, x.1 w != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.neg_of_mem_negA_plusPart`：neg_of_mem_negA_plu
sPart (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}} (hw : w in s) : 
x.1 w < 0
· 使用定理 `NumberField.mixedEmbedding.pos_of_notMem_negAt_plusPart`：pos_of_notMem_n
egAt_plusPart (hx : x in negAt s '' (plusPart A)) {w : {w // IsReal w}} (hw : w 
∉ s) : 0 < x.1 w
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_mem`：negAt_apply_isRea
l_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w in s) : (negAt s x).1
 w = -x.1 w
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_isReal_and_notMem`：negAt_apply_is
Real_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) : (negAt s
 x).1 w = x.1 w
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
-/
theorem mem_negAt_plusPart_of_mem (hx₁ : x ∈ A) (hx₂ : ∀ w, x.1 w ≠ 0) :
    x ∈ negAt s '' (plusPart A) ↔ (∀ w, w ∈ s → x.1 w < 0) ∧ (∀ w, w ∉ s → x.1 w > 0) := by
  refine ⟨fun hx ↦ ⟨fun _ hw ↦ neg_of_mem_negA_plusPart A hx hw,
      fun _ hw ↦ pos_of_notMem_negAt_plusPart A hx hw⟩,
      fun ⟨h₁, h₂⟩ ↦
        ⟨(fun w ↦ ‖x.1 w‖, x.2), ⟨(hA x).mp hx₁, fun w ↦ norm_pos_iff.mpr (hx₂ w)⟩, ?_⟩⟩
  ext w
  · by_cases hw : w ∈ s
    · simp [negAt_apply_isReal_and_mem _ hw, abs_of_neg (h₁ w hw)]
    · simp [negAt_apply_isReal_and_notMem _ hw, abs_of_pos (h₂ w hw)]
  · rfl

include hA in
/-- Assume that `A`  is symmetric at real places then, the union of the images of `plusPart`
by `negAt` and of the set of elements of `A` that are zero at at least one real place
is equal to `A`. -/
/-
**NumberField.mixedEmbedding.iUnion_negAt_plusPart_union** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：iUnion_negAt_plusPart_union : (⋃ s, negAt s '' (plusPart A)) union (A inte
r (⋃ w, {x | x.1 w = 0})) = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.negAt_apply_norm_isReal`：negAt_apply_norm_isR
eal (x : mixedSpace K) (w : {w // IsReal w}) : ‖(negAt s x).1 w‖ = ‖x.1 w‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `exists_or_forall_not`：exists_or_forall_not (P : α -> Prop) : (exists a, 
P a) ∨ forall a, ¬P a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.mixedEmbedding.mem_negAt_plusPart_of_mem`：mem_negAt_plusPart
_of_mem (hx₁ : x in A) (hx₂ : forall w, x.1 w != 0) : x in negAt s '' (plusPart 
A) ↔ (forall w, w in s -> x.1 w < 0) ∧ (fo…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
Assume that `A`  is symmetric at real places then, the union of the images of `p
lusPart`
by `negAt` and of the set of elements of `A` that are zero at at least one real 
place
is equal to `A`.
-/
theorem iUnion_negAt_plusPart_union :
    (⋃ s, negAt s '' (plusPart A)) ∪ (A ∩ (⋃ w, {x | x.1 w = 0})) = A := by
  ext x
  rw [Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iUnion]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro (⟨s, ⟨x, ⟨hx, _⟩, rfl⟩⟩ | h)
    · simp_rw +singlePass [hA, negAt_apply_norm_isReal, negAt_apply_snd]
      rwa [← hA]
    · exact h.left
  · obtain hx | hx := exists_or_forall_not (fun w ↦ x.1 w = 0)
    · exact Or.inr ⟨h, hx⟩
    · refine Or.inl ⟨signSet x,
        (mem_negAt_plusPart_of_mem A hA h hx).mpr ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
      · exact lt_of_le_of_ne hw (hx w)
      · exact lt_of_le_of_ne (lt_of_not_ge hw).le (Ne.symm (hx w))

open MeasureTheory

variable [NumberField K]

include hA in
open scoped Classical in
/-
**NumberField.mixedEmbedding.iUnion_negAt_plusPart_ae** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.mixedEmbedding`。
形式化陈述：iUnion_negAt_plusPart_ae : ⋃ s, negAt s '' (plusPart A) =ᵐ[volume] A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.iUnion_negAt_plusPart_union`：iUnion_negAt_plu
sPart_union : (⋃ s, negAt s '' (plusPart A)) union (A inter (⋃ w, {x | x.1 w = 0
})) = A
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.union_ae_eq_left_of_ae_eq_empty`：union_ae_eq_left_of_ae_eq
_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_iUnion_null_iff`：measure_iUnion_null_iff {ι : Sort
*} [Countable ι] {s : ι -> Set α} : μ (⋃ i, s i) = 0 ↔ forall i, μ (s i) = 0
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.mixedEmbedding.volume_eq_zero`：volume_eq_zero (w : {w // IsR
eal w}) : volume ({x : mixedSpace K | x.1 w = 0}) = 0
-/
theorem iUnion_negAt_plusPart_ae :
    ⋃ s, negAt s '' (plusPart A) =ᵐ[volume] A := by
  nth_rewrite 2 [← iUnion_negAt_plusPart_union A hA]
  refine (MeasureTheory.union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
  exact measure_mono_null Set.inter_subset_right
    (measure_iUnion_null_iff.mpr fun _ ↦ volume_eq_zero _)

variable {A} in
/-
**NumberField.mixedEmbedding.measurableSet_plusPart** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.mixedEmbedding`。
形式化陈述：measurableSet_plusPart (hm : MeasurableSet A) : MeasurableSet (plusPart A)
参数：hm : MeasurableSet A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
theorem measurableSet_plusPart (hm : MeasurableSet A) :
    MeasurableSet (plusPart A) := by
  convert_to MeasurableSet (A ∩ (⋂ w, {x | 0 < x.1 w}))
  · ext; simp
  · refine hm.inter (MeasurableSet.iInter fun _ ↦ ?_)
    exact measurableSet_lt measurable_const (by fun_prop)

variable (s) in
/-
**NumberField.mixedEmbedding.measurableSet_negAt_plusPart** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding`。
形式化陈述：measurableSet_negAt_plusPart (hm : MeasurableSet A) : MeasurableSet (negAt
 s '' (plusPart A))
参数：hm : MeasurableSet A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `NumberField.mixedEmbedding.measurableSet_plusPart`：measurableSet_plusPar
t (hm : MeasurableSet A) : MeasurableSet (plusPart A)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `NumberField.mixedEmbedding.negAt_preimage`：negAt_preimage : negAt s ⁻¹' 
A = negAt s '' A
-/
theorem measurableSet_negAt_plusPart (hm : MeasurableSet A) :
    MeasurableSet (negAt s '' (plusPart A)) :=
  negAt_preimage s _ ▸ (measurableSet_plusPart hm).preimage (negAt s).continuous.measurable

variable {A}

open scoped Classical in
/-- The image of the `plusPart` of `A` by `negAt` have all the same volume as `plusPart A`. -/
/-
**NumberField.mixedEmbedding.volume_negAt_plusPart** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：volume_negAt_plusPart (hm : MeasurableSet A) : volume (negAt s '' (plusPar
t A)) = volume (plusPart A)
参数：hm : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.negAt_symm`：negAt_symm : (negAt s).symm = neg
At s
· 使用定理 `ContinuousLinearEquiv.image_symm_eq_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `NumberField.mixedEmbedding.volume_preserving_negAt`：volume_preserving_ne
gAt [NumberField K] : MeasurePreserving (negAt s)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `NumberField.mixedEmbedding.measurableSet_plusPart`：measurableSet_plusPar
t (hm : MeasurableSet A) : MeasurableSet (plusPart A)

--- 原说明 ---
The image of the `plusPart` of `A` by `negAt` have all the same volume as `plusP
art A`.
-/
theorem volume_negAt_plusPart (hm : MeasurableSet A) :
    volume (negAt s '' (plusPart A)) = volume (plusPart A) := by
  rw [← negAt_symm, ContinuousLinearEquiv.image_symm_eq_preimage,
    volume_preserving_negAt.measure_preimage (measurableSet_plusPart hm).nullMeasurableSet]

include hA in
open scoped Classical in
/-- If a subset `A` of the `mixedSpace` is symmetric at real places, then its volume is
`2^ nrRealPlaces K` times the volume of its `plusPart`. -/
/-
**NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：volume_eq_two_pow_mul_volume_plusPart (hm : MeasurableSet A) : volume A = 
2 ^ nrRealPlaces K * volume (plusPart A)
参数：hm : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `NumberField.mixedEmbedding.iUnion_negAt_plusPart_ae`：iUnion_negAt_plusPa
rt_ae : ⋃ s, negAt s '' (plusPart A) =ᵐ[volume] A
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.mixedEmbedding.disjoint_negAt_plusPart`：disjoint_negAt_plusP
art : Pairwise (Disjoint on (fun s => negAt s '' (plusPart A)))
· 使用定理 `NumberField.mixedEmbedding.measurableSet_negAt_plusPart`：measurableSet_n
egAt_plusPart (hm : MeasurableSet A) : MeasurableSet (negAt s '' (plusPart A))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.volume_negAt_plusPart`：volume_negAt_plusPart 
(hm : MeasurableSet A) : volume (negAt s '' (plusPart A)) = volume (plusPart A)
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Fintype.card_set`：Fintype.card_set [Fintype α] : Fintype.card (Set α) = 
2 ^ Fintype.card α
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a subset `A` of the `mixedSpace` is symmetric at real places, then its volume
 is
`2^ nrRealPlaces K` times the volume of its `plusPart`.
-/
theorem volume_eq_two_pow_mul_volume_plusPart (hm : MeasurableSet A) :
    volume A = 2 ^ nrRealPlaces K * volume (plusPart A) := by
  simp only [← measure_congr (iUnion_negAt_plusPart_ae A hA),
    measure_iUnion (disjoint_negAt_plusPart A) (fun _ ↦ measurableSet_negAt_plusPart _ A hm),
    volume_negAt_plusPart hm, tsum_fintype, sum_const, card_univ, Fintype.card_set, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, nrRealPlaces]

end plusPart

noncomputable section realSpace

open MeasureTheory

/--
The `realSpace` associated to a number field `K` is the real vector space indexed by the
infinite places of `K`.
-/
/-
**NumberField.mixedEmbedding.realSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.
mixedEmbedding`。
形式化陈述：realSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `realSpace` associated to a number field `K` is the real vector space indexe
d by the
infinite places of `K`.
-/
abbrev realSpace := InfinitePlace K → ℝ

variable {K}

set_option backward.isDefEq.respectTransparency.types false in
/-- The set of points in the `realSpace` that are equal to `0` at a fixed place has volume zero. -/
/-
**NumberField.mixedEmbedding.realSpace.volume_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.mixedEmbedding.realSpace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (w : NumberFiel
d.InfinitePlace K),   MeasureTheory.volume {x | x w = 0} = 0
参数：w : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.addHaar_affineSubspace`：addHaar_affineSubspace {E 
: Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelS
pace E] [FiniteDimensional Real E]…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The set of points in the `realSpace` that are equal to `0` at a fixed place has 
volume zero.
-/
theorem realSpace.volume_eq_zero [NumberField K] (w : InfinitePlace K) :
    volume ({x : realSpace K | x w = 0}) = 0 := by
  let A : AffineSubspace ℝ (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w = 0}, by simp_all⟩, rfl⟩ (by simp_all))
  convert! Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 ∈ A)

/--
The continuous linear map from `realSpace K` to `mixedSpace K` which is the identity at real
places and the natural map `ℝ → ℂ` at complex places.
-/
/-
**NumberField.mixedEmbedding.mixedSpaceOfRealSpace** 是 Mathlib 中的一个定义，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：mixedSpaceOfRealSpace : realSpace K ->L[Real] mixedSpace K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous linear map from `realSpace K` to `mixedSpace K` which is the iden
tity at real
places and the natural map `ℝ → ℂ` at complex places.
-/
def mixedSpaceOfRealSpace : realSpace K →L[ℝ] mixedSpace K :=
  .prod (.pi fun w ↦ .proj w.1) (.pi fun w ↦ Complex.ofRealCLM.comp (.proj w.1))
/-
**NumberField.mixedEmbedding.mixedSpaceOfRealSpace_apply** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：mixedSpaceOfRealSpace_apply (x : realSpace K) : mixedSpaceOfRealSpace x = 
⟨fun w => x w.1, fun w => x w.1⟩
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mixedSpaceOfRealSpace_apply (x : realSpace K) :
    mixedSpaceOfRealSpace x = ⟨fun w ↦ x w.1, fun w ↦ x w.1⟩ := rfl

variable (K) in
/-
**NumberField.mixedEmbedding.injective_mixedSpaceOfRealSpace** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：injective_mixedSpaceOfRealSpace : Function.Injective (mixedSpaceOfRealSpac
e : realSpace K -> mixedSpace K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Prod.mk_eq_zero`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst_1
 : Zero N] {x : M} {y : N}, (x, y) = 0 ↔ x = 0 ∧ y = 0
· 使用定理 `NumberField.mixedEmbedding.mixedSpaceOfRealSpace_apply`：mixedSpaceOfReal
Space_apply (x : realSpace K) : mixedSpaceOfRealSpace x = ⟨fun w => x w.1, fun w
 => x w.1⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem injective_mixedSpaceOfRealSpace :
    Function.Injective (mixedSpaceOfRealSpace : realSpace K → mixedSpace K) := by
  refine (injective_iff_map_eq_zero mixedSpaceOfRealSpace).mpr fun _ h ↦ ?_
  rw [mixedSpaceOfRealSpace_apply, Prod.mk_eq_zero, funext_iff, funext_iff] at h
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · exact h.1 ⟨w, hw⟩
  · exact Complex.ofReal_inj.mp <| h.2 ⟨w, hw⟩
/-
**NumberField.mixedEmbedding.normAtPlace_mixedSpaceOfRealSpace** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtPlace_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} 
(hx : 0 <= x w) : normAtPlace w (mixedSpaceOfRealSpace x) = x w
参数：hx : 0 <= x w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
-/
theorem normAtPlace_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 ≤ x w) :
    normAtPlace w (mixedSpaceOfRealSpace x) = x w := by
  simp only [mixedSpaceOfRealSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg hx]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_of_nonneg hx]

open scoped Classical in
/--
The map from the `mixedSpace K` to `realSpace K` that sends the values at complex places
to their norm.
-/
/-
**NumberField.mixedEmbedding.normAtComplexPlaces** 是 Mathlib 中的一个缩写定义，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：normAtComplexPlaces (x : mixedSpace K) : realSpace K
参数：x : mixedSpace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the `mixedSpace K` to `realSpace K` that sends the values at comple
x places
to their norm.
-/
abbrev normAtComplexPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

@[simp]
/-
**NumberField.mixedEmbedding.normAtComplexPlaces_apply_isReal** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtComplexPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) 
: normAtComplexPlaces x w = x.1 w
参数：w : {w // IsReal w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces.eq_1`：∀ {K : Type u_1} [i
nst : Field K] (x : NumberField.mixedEmbedding.mixedSpace K) (w : NumberField.In
finitePlace K),   NumberField.mixedEmbedd…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem normAtComplexPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) :
    normAtComplexPlaces x w = x.1 w := by
  rw [normAtComplexPlaces, dif_pos]

@[simp]
/-
**NumberField.mixedEmbedding.normAtComplexPlaces_apply_isComplex** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtComplexPlaces_apply_isComplex {x : mixedSpace K} (w : {w // IsComple
x w}) : normAtComplexPlaces x w = ‖x.2 w‖
参数：w : {w // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces.eq_1`：∀ {K : Type u_1} [i
nst : Field K] (x : NumberField.mixedEmbedding.mixedSpace K) (w : NumberField.In
finitePlace K),   NumberField.mixedEmbedd…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
-/
theorem normAtComplexPlaces_apply_isComplex {x : mixedSpace K} (w : {w // IsComplex w}) :
    normAtComplexPlaces x w = ‖x.2 w‖ := by
  rw [normAtComplexPlaces, dif_neg (not_isReal_iff_isComplex.mpr w.prop),
    normAtPlace_apply_of_isComplex]
/-
**NumberField.mixedEmbedding.normAtComplexPlaces_mixedSpaceOfRealSpace** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtComplexPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : forall w
, IsComplex w -> 0 <= x w) : normAtComplexPlaces (mixedSpaceOfRealSpace x) = x
参数：hx : forall w, IsComplex w -> 0 <= x w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_apply_isReal`：normAtCompl
exPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) : normAtComplexPl
aces x w = x.1 w
· 使用定理 `NumberField.mixedEmbedding.mixedSpaceOfRealSpace_apply`：mixedSpaceOfReal
Space_apply (x : realSpace K) : mixedSpaceOfRealSpace x = ⟨fun w => x w.1, fun w
 => x w.1⟩
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_apply_isComplex`：normAtCo
mplexPlaces_apply_isComplex {x : mixedSpace K} (w : {w // IsComplex w}) : normAt
ComplexPlaces x w = ‖x.2 w‖
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
-/
theorem normAtComplexPlaces_mixedSpaceOfRealSpace {x : realSpace K}
    (hx : ∀ w, IsComplex w → 0 ≤ x w) :
    normAtComplexPlaces (mixedSpaceOfRealSpace x) = x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · rw [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply,
      Complex.norm_of_nonneg (hx w hw)]

/--
The map from the `mixedSpace K` to `realSpace K` that sends each component to its norm.
-/
/-
**NumberField.mixedEmbedding.normAtAllPlaces** 是 Mathlib 中的一个缩写定义，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：normAtAllPlaces (x : mixedSpace K) : realSpace K
参数：x : mixedSpace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the `mixedSpace K` to `realSpace K` that sends each component to it
s norm.
-/
abbrev normAtAllPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ normAtPlace w x

@[simp]
/-
**NumberField.mixedEmbedding.normAtAllPlaces_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_apply (x : mixedSpace K) (w : InfinitePlace K) : normAtAll
Places x w = normAtPlace w x
参数：x : mixedSpace K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normAtAllPlaces_apply (x : mixedSpace K) (w : InfinitePlace K) :
    normAtAllPlaces x w = normAtPlace w x := rfl

variable (K) in
/-
**NumberField.mixedEmbedding.continuous_normAtAllPlaces** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：continuous_normAtAllPlaces : Continuous (normAtAllPlaces : mixedSpace K ->
 realSpace K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `NumberField.mixedEmbedding.continuous_normAtPlace`：continuous_normAtPlac
e (w : InfinitePlace K) : Continuous (normAtPlace w)
-/
theorem continuous_normAtAllPlaces :
    Continuous (normAtAllPlaces : mixedSpace K → realSpace K) := by fun_prop
/-
**NumberField.mixedEmbedding.normAtAllPlaces_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_nonneg (x : mixedSpace K) (w : InfinitePlace K) : 0 <= nor
mAtAllPlaces x w
参数：x : mixedSpace K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
-/
theorem normAtAllPlaces_nonneg (x : mixedSpace K) (w : InfinitePlace K) :
    0 ≤ normAtAllPlaces x w := normAtPlace_nonneg _ _
/-
**NumberField.mixedEmbedding.normAtAllPlaces_mixedSpaceOfRealSpace** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : forall w, 0 
<= x w) : normAtAllPlaces (mixedSpaceOfRealSpace x) = x
参数：hx : forall w, 0 <= x w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_apply`：normAtAllPlaces_apply 
(x : mixedSpace K) (w : InfinitePlace K) : normAtAllPlaces x w = normAtPlace w x
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_mixedSpaceOfRealSpace`：normAtPlac
e_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w) 
: normAtPlace w (mixedSpaceOfRealSpace x) = x w
-/
theorem normAtAllPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : ∀ w, 0 ≤ x w) :
    normAtAllPlaces (mixedSpaceOfRealSpace x) = x := by
  ext
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (hx _)]
/-
**NumberField.mixedEmbedding.normAtAllPlaces_mixedEmbedding** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_mixedEmbedding (x : K) (w : InfinitePlace K) : normAtAllPl
aces (mixedEmbedding K x) w = w x
参数：x : K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_apply`：normAtAllPlaces_apply 
(x : mixedSpace K) (w : InfinitePlace K) : normAtAllPlaces x w = normAtPlace w x
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
-/
theorem normAtAllPlaces_mixedEmbedding (x : K) (w : InfinitePlace K) :
    normAtAllPlaces (mixedEmbedding K x) w = w x := by
  rw [normAtAllPlaces_apply, normAtPlace_apply]
/-
**NumberField.mixedEmbedding.normAtAllPlaces_normAtAllPlaces** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_normAtAllPlaces (x : mixedSpace K) : normAtAllPlaces (mixe
dSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_mixedSpaceOfRealSpace`：normAt
AllPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : forall w, 0 <= x w) : no
rmAtAllPlaces (mixedSpaceOfRealSpace x) = x
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_nonneg`：normAtAllPlaces_nonne
g (x : mixedSpace K) (w : InfinitePlace K) : 0 <= normAtAllPlaces x w
-/
theorem normAtAllPlaces_normAtAllPlaces (x : mixedSpace K) :
    normAtAllPlaces (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x :=
  normAtAllPlaces_mixedSpaceOfRealSpace fun _ ↦ (normAtAllPlaces_nonneg _ _)
/-
**NumberField.mixedEmbedding.normAtAllPlaces_norm_at_real_places** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_norm_at_real_places (x : mixedSpace K) : normAtAllPlaces (
fun w => ‖x.1 w‖, x.2) = normAtAllPlaces x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
-/
theorem normAtAllPlaces_norm_at_real_places (x : mixedSpace K) :
    normAtAllPlaces (fun w ↦ ‖x.1 w‖, x.2) = normAtAllPlaces x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isReal hw, norm_norm]
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isComplex hw]
/-
**NumberField.mixedEmbedding.normAtComplexPlaces_normAtAllPlaces** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtComplexPlaces_normAtAllPlaces (x : mixedSpace K) : normAtComplexPlac
es (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_mixedSpaceOfRealSpace`：no
rmAtComplexPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : forall w, IsComp
lex w -> 0 <= x w) : normAtComplexPlaces (mixedSpaceOfReal…
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_nonneg`：normAtAllPlaces_nonne
g (x : mixedSpace K) (w : InfinitePlace K) : 0 <= normAtAllPlaces x w
-/
theorem normAtComplexPlaces_normAtAllPlaces (x : mixedSpace K) :
    normAtComplexPlaces (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x :=
  normAtComplexPlaces_mixedSpaceOfRealSpace fun _ _ ↦ (normAtAllPlaces_nonneg _ _)
/-
**NumberField.mixedEmbedding.normAtAllPlaces_eq_of_normAtComplexPlaces_eq** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_eq_of_normAtComplexPlaces_eq {x y : mixedSpace K} (h : nor
mAtComplexPlaces x = normAtComplexPlaces y) : normAtAllPlaces x = normAtAllPlace
s y
参数：h : normAtComplexPlaces x = normAtComplexPlaces y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_apply_isReal`：normAtCompl
exPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) : normAtComplexPl
aces x w = x.1 w
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_apply_isComplex`：normAtCo
mplexPlaces_apply_isComplex {x : mixedSpace K} (w : {w // IsComplex w}) : normAt
ComplexPlaces x w = ‖x.2 w‖
-/
theorem normAtAllPlaces_eq_of_normAtComplexPlaces_eq {x y : mixedSpace K}
    (h : normAtComplexPlaces x = normAtComplexPlaces y) :
    normAtAllPlaces x = normAtAllPlaces y := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isReal hw,
      normAtComplexPlaces_apply_isReal ⟨w, hw⟩] using congr_arg (|·|) (congr_fun h w)
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
      normAtComplexPlaces_apply_isComplex ⟨w, hw⟩] using congr_fun h w
/-
**NumberField.mixedEmbedding.normAtAllPlaces_image_preimage_of_nonneg** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtAllPlaces_image_preimage_of_nonneg {s : Set (realSpace K)} (hs : for
all x in s, forall w, 0 <= x w) : normAtAllPlaces '' normAtAllPlaces ⁻¹' s = s
参数：realSpace K；hs : forall x in s, forall w, 0 <= x w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_apply`：normAtAllPlaces_apply 
(x : mixedSpace K) (w : InfinitePlace K) : normAtAllPlaces x w = normAtPlace w x
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_mixedSpaceOfRealSpace`：normAtPlac
e_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w) 
: normAtPlace w (mixedSpaceOfRealSpace x) = x w
-/
theorem normAtAllPlaces_image_preimage_of_nonneg {s : Set (realSpace K)}
    (hs : ∀ x ∈ s, ∀ w, 0 ≤ x w) :
    normAtAllPlaces '' normAtAllPlaces ⁻¹' s = s := by
  rw [Set.image_preimage_eq_iff]
  rintro x hx
  refine ⟨mixedSpaceOfRealSpace x, funext fun w ↦ ?_⟩
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (hs x hx w)]

end realSpace

end NumberField.mixedEmbedding

