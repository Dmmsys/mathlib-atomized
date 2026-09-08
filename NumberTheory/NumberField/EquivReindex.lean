/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Reindexed basis

This file introduces an equivalence between the set of embeddings of `K` into `ℂ` and the
index set of the chosen basis of the ring of integers of `K`.

## Tags

house, number field, algebraic number
-/

public section

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

/-- An equivalence between the set of embeddings of `K` into `ℂ` and the
  index set of the chosen basis of the ring of integers of `K`. -/
/-
**NumberField.equivReindex** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField`。
形式化陈述：equivReindex : (K ->+* Complex) ≃ ChooseBasisIndex Int (𝓞 K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
An equivalence between the set of embeddings of `K` into `ℂ` and the
  index set of the chosen basis of the ring of integers of `K`.
-/
abbrev equivReindex : (K →+* ℂ) ≃ ChooseBasisIndex ℤ (𝓞 K) :=
  Fintype.equivOfCardEq <| by
    rw [Embeddings.card, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

/-- The basis matrix for the embeddings of `K` into `ℂ`. This matrix is formed by
  taking the lattice basis vectors of `K` and reindexing them according to the
  equivalence `equivReindex`, then transposing the resulting matrix. -/
/-
**NumberField.basisMatrix** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField`。
形式化陈述：basisMatrix : Matrix (K ->+* Complex) (K ->+* Complex) Complex
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
The basis matrix for the embeddings of `K` into `ℂ`. This matrix is formed by
  taking the lattice basis vectors of `K` and reindexing them according to the
  equivalence `equivReindex`, then transposing the resulting matrix.
-/
abbrev basisMatrix : Matrix (K →+* ℂ) (K →+* ℂ) ℂ :=
  (Matrix.of fun i ↦ latticeBasis K (equivReindex K i))
/-
**NumberField.basisMatrix_eq_embeddingsMatrixReindex** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField`。
形式化陈述：basisMatrix_eq_embeddingsMatrixReindex : basisMatrix K = Algebra.embedding
sMatrixReindex Rat Complex (integralBasis K ∘ (equivReindex K)) (RingHom.equivRa
tAlgHom K Complex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NumberField.canonicalEmbedding.latticeBasis_apply`：latticeBasis_apply [N
umberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (canoni
calEmbedding K) (integralBasis K i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.integralBasis_apply`：integralBasis_apply (i : Free.ChooseBas
isIndex Int (𝓞 K)) : integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basi
s K i)
· 使用定理 `RingHom.equivRatAlgHom_apply`：∀ (R : Type u_1) (S : Type u_2) [inst : Ri
ng R] [inst_1 : Ring S] [inst_2 : Algebra ℚ R] [inst_3 : Algebra ℚ S]   (f : R →
+* S), (RingHom.eq…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisMatrix_eq_embeddingsMatrixReindex :
    basisMatrix K = Algebra.embeddingsMatrixReindex ℚ ℂ
      (integralBasis K ∘ (equivReindex K)) (RingHom.equivRatAlgHom K ℂ) := by
  ext; simp [Algebra.embeddingsMatrixReindex]

open ComplexConjugate in
/-
**NumberField.conj_basisMatrix** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：conj_basisMatrix : (basisMatrix K).map conj = (basisMatrix K).reindex (Equ
iv.refl _) (ComplexEmbedding.involutive_conjugate K).toPerm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `NumberField.ComplexEmbedding.involutive_conjugate`：involutive_conjugate 
: Function.Involutive (conjugate : (K ->+* Complex) -> (K ->+* Complex))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NumberField.canonicalEmbedding.latticeBasis_apply`：latticeBasis_apply [N
umberField K] (i : Free.ChooseBasisIndex Int (𝓞 K)) : latticeBasis K i = (canoni
calEmbedding K) (integralBasis K i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.integralBasis_apply`：integralBasis_apply (i : Free.ChooseBas
isIndex Int (𝓞 K)) : integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basi
s K i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conj_basisMatrix :
    (basisMatrix K).map conj = (basisMatrix K).reindex (Equiv.refl _)
      (ComplexEmbedding.involutive_conjugate K).toPerm := by
  ext; simp
/-
**NumberField.det_of_basisMatrix_non_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
`。
形式化陈述：det_of_basisMatrix_non_zero [DecidableEq (K ->+* Complex)] : (basisMatrix 
K).det != 0
参数：K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.basisMatrix_eq_embeddingsMatrixReindex`：basisMatrix_eq_embed
dingsMatrixReindex : basisMatrix K = Algebra.embeddingsMatrixReindex Rat Complex
 (integralBasis K ∘ (equivReindex K)) (R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_ne_zero_iff`：pow_ne_zero_iff (hn : n != 0) : a ^ n != 0 ↔ a != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Algebra.discr_reindex`：discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : di
scr A (b ∘ ⇑f.symm) = discr A b
· 使用定理 `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`：discr_eq_det_embed
dingsMatrixReindex_pow_two [Algebra.IsSeparable K L] (e : ι ≃ (L ->ₐ[K] E)) : al
gebraMap K E (discr K b) = (embeddingsMatr…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Algebra.discr_not_zero_of_basis`：discr_not_zero_of_basis [Algebra.IsSepa
rable K L] (b : Basis ι K L) : discr K b != 0
-/
theorem det_of_basisMatrix_non_zero [DecidableEq (K →+* ℂ)] : (basisMatrix K).det ≠ 0 := by
  rw [basisMatrix_eq_embeddingsMatrixReindex, ← pow_ne_zero_iff two_ne_zero]
  convert!
    (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
      (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
  rw [← Algebra.discr_reindex ℚ (integralBasis K) (equivReindex K).symm]
  exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
    (integralBasis K ∘ (equivReindex K)) (RingHom.equivRatAlgHom K ℂ)).symm
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq (K →+* ℂ)] : Invertible (basisMatrix K) := invertibleOfIsUnitDet _
    (Ne.isUnit (det_of_basisMatrix_non_zero K))

variable {K}
/-
**NumberField.canonicalEmbedding_eq_basisMatrix_mulVec** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField`。
形式化陈述：canonicalEmbedding_eq_basisMatrix_mulVec (α : K) : canonicalEmbedding K α 
= (basisMatrix K).transpose.mulVec (fun i => (((integralBasis K).reindex (equivR
eindex K).symm).repr α i : Complex))
参数：α : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.canonicalEmbedding.integralBasis_repr_apply`：integralBasis_r
epr_apply [NumberField K] (x : K) (i : Free.ChooseBasisIndex Int (𝓞 K)) : (latti
ceBasis K).repr (canonicalEmbedding K x) i = …
· 使用定理 `Fintype.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [i
nst : Fintype ι] [inst_1 : (a : α) → AddCommMonoid (M a)] (a : α)   (g : ι → (a 
: α) → …
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem canonicalEmbedding_eq_basisMatrix_mulVec (α : K) :
    canonicalEmbedding K α = (basisMatrix K).transpose.mulVec
      (fun i ↦ (((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ)) := by
  ext i
  rw [← (latticeBasis K).sum_repr (canonicalEmbedding K α), ← Equiv.sum_comp (equivReindex K)]
  simp only [canonicalEmbedding.integralBasis_repr_apply, mulVec, dotProduct,
    transpose_apply, of_apply, Fintype.sum_apply, mul_comm, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Pi.smul_apply, smul_eq_mul]
/-
**NumberField.inverse_basisMatrix_mulVec_eq_repr** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField`。
形式化陈述：inverse_basisMatrix_mulVec_eq_repr [DecidableEq (K ->+* Complex)] (α : 𝓞 K
) : forall i, ((basisMatrix K).transpose)⁻¹.mulVec (fun j => canonicalEmbedding 
K (algebraMap (𝓞 K) K α) j) i = ((integralBasis K).reindex (equivReindex K).symm
).repr α i
参数：K ->+* Complex；α : 𝓞 K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.inv_mulVec_eq_vec`：inv_mulVec_eq_vec {A : Matrix n n α} [Invertib
le A] {u v : n -> α} (hM : u = A.mulVec v) : A⁻¹.mulVec u = v
· 使用定理 `NumberField.canonicalEmbedding_eq_basisMatrix_mulVec`：canonicalEmbedding
_eq_basisMatrix_mulVec (α : K) : canonicalEmbedding K α = (basisMatrix K).transp
ose.mulVec (fun i => (((integralBasis K).r…
-/
theorem inverse_basisMatrix_mulVec_eq_repr [DecidableEq (K →+* ℂ)] (α : 𝓞 K) :
    ∀ i, ((basisMatrix K).transpose)⁻¹.mulVec (fun j =>
      canonicalEmbedding K (algebraMap (𝓞 K) K α) j) i =
      ((integralBasis K).reindex (equivReindex K).symm).repr α i := fun i => by
  rw [inv_mulVec_eq_vec (canonicalEmbedding_eq_basisMatrix_mulVec ((algebraMap (𝓞 K) K) α))]

end

end NumberField

