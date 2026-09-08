/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Trace.Defs

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose
  `(i, σ)` coefficient is `σ (b i)`.
* `Algebra.embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ`
  given by a bijection `e : κ ≃ (B →ₐ[A] C)`.
* `Module.Basis.traceDual`: The dual basis of a basis under the trace form in a finite separable
  extension.

## Main results

* `trace_eq_sum_embeddings`: the trace of `x : K(x)` is the sum of all embeddings of `x` into an
  algebraically closed field
* `traceForm_nondegenerate`: the trace form over a separable extension is a nondegenerate
  bilinear form
* `Module.Basis.traceDual_powerBasis_eq`: The dual basis of a power basis `{1, x, x²...}` under the
  trace form is `aᵢ / f'(x)`, with `f` being the minpoly of `x` and `f / (X - x) = ∑ aᵢxⁱ`.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/

@[expose] public section

universe u v w z

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {ι κ : Type w}

open Module

open LinearMap (BilinForm)
open LinearMap

open Matrix

open scoped Matrix

/-
**Algebra.traceForm_toMatrix_powerBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.traceForm_toMatrix_powerBasis (h : PowerBasis R S) : (traceForm R 
S).toMatrix h.basis = of fun i j => trace R S (h.gen ^ (i.1 + j.1))
参数：h : PowerBasis R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.traceForm_toMatrix`：traceForm_toMatrix [DecidableEq ι] (b : Basi
s ι R S) (i j) : (traceForm R S).toMatrix b i j = trace R S (b i * b j)
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `PowerBasis.basis_eq_pow`：∀ {R : Type u_7} {S : Type u_8} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] (self : PowerBasis R S)   (i : Fin
 self.dim), s…
-/
theorem Algebra.traceForm_toMatrix_powerBasis (h : PowerBasis R S) :
    (traceForm R S).toMatrix h.basis = of fun i j => trace R S (h.gen ^ (i.1 + j.1)) := by
  ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]

section EqSumRoots

open Algebra Polynomial

variable {F : Type*} [Field F]
variable [Algebra K S] [Algebra K F]

/-- Given `pb : PowerBasis K S`, the trace of `pb.gen` is `-(minpoly K pb.gen).nextCoeff`. -/
/-
**PowerBasis.trace_gen_eq_nextCoeff_minpoly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PowerBasis.trace_gen_eq_nextCoeff_minpoly [Nontrivial S] (pb : PowerBasis 
K S) : Algebra.trace K S pb.gen = -(minpoly K pb.gen).nextCoeff
参数：pb : PowerBasis K S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerBasis.dim_pos`：dim_pos [Nontrivial S] (pb : PowerBasis R S) : 0 < p
b.dim
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.natDegree_minpoly`：natDegree_minpoly [Nontrivial A] (pb : Pow
erBasis A S) : (minpoly A pb.gen).natDegree = pb.dim
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.trace_eq_matrix_trace`：trace_eq_matrix_trace [DecidableEq ι] (b 
: Basis ι R S) (s : S) : trace R S s = Matrix.trace (Algebra.leftMulMatrix b s)
· 使用定理 `Matrix.trace_eq_neg_charpoly_coeff`：trace_eq_neg_charpoly_coeff [Nonempt
y n] (M : Matrix n n R) : trace M = -M.charpoly.coeff (Fintype.card n - 1)
· 使用定理 `charpoly_leftMulMatrix`：charpoly_leftMulMatrix {S : Type*} [Ring S] [Alg
ebra R S] (h : PowerBasis R S) : (leftMulMatrix h.basis h.gen).charpoly = minpol
y R h.gen
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Polynomial.nextCoeff_of_natDegree_pos`：nextCoeff_of_natDegree_pos (hp : 
0 < p.natDegree) : nextCoeff p = p.coeff (p.natDegree - 1)

--- 原说明 ---
Given `pb : PowerBasis K S`, the trace of `pb.gen` is `-(minpoly K pb.gen).nextC
oeff`.
-/
theorem PowerBasis.trace_gen_eq_nextCoeff_minpoly [Nontrivial S] (pb : PowerBasis K S) :
    Algebra.trace K S pb.gen = -(minpoly K pb.gen).nextCoeff := by
  have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by simpa
  have : Nonempty (Fin pb.dim) := ⟨⟨0, d_pos⟩⟩
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_leftMulMatrix, ←
    pb.natDegree_minpoly, Fintype.card_fin, ← nextCoeff_of_natDegree_pos d_pos']

/-- Given `pb : PowerBasis K S`, then the trace of `pb.gen` is
`((minpoly K pb.gen).aroots F).sum`. -/
/-
**PowerBasis.trace_gen_eq_sum_roots** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S) (hf
 : ((minpoly K pb.gen).map (algebraMap K F)).Splits) : algebraMap K F (trace K S
 pb.gen) = ((minpoly K pb.gen).aroots F).sum
参数：pb : PowerBasis K S；hf : ((minpoly K pb.gen).map (algebraMap K F)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.trace_gen_eq_nextCoeff_minpoly`：PowerBasis.trace_gen_eq_nextC
oeff_minpoly [Nontrivial S] (pb : PowerBasis K S) : Algebra.trace K S pb.gen = -
(minpoly K pb.gen).nextCoeff
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.nextCoeff_map_eq`：nextCoeff_map_eq (p : R[X]) (f : R ->+* S) 
: (p.map f).nextCoeff = f p.nextCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic`：∀ {R : Type u_1} 
[inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Mon
ic → f.nextCoeff = -f.roots.sum
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `PowerBasis.isIntegral_gen`：isIntegral_gen (pb : PowerBasis A S) : IsInte
gral A pb.gen
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
Given `pb : PowerBasis K S`, then the trace of `pb.gen` is
`((minpoly K pb.gen).aroots F).sum`.
-/
theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
    (hf : ((minpoly K pb.gen).map (algebraMap K F)).Splits) :
    algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).aroots F).sum := by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly, map_neg,
    ← nextCoeff_map_eq, hf.nextCoeff_eq_neg_sum_roots_of_monic
      ((minpoly.monic (PowerBasis.isIntegral_gen _)).map _),
    neg_neg]

namespace IntermediateField.AdjoinSimple

open IntermediateField

/-
**IntermediateField.AdjoinSimple.trace_gen_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField.AdjoinSimple`。
形式化陈述：trace_gen_eq_zero {x : L} (hx : ¬IsIntegral K x) : Algebra.trace K K⟮x⟯ (A
djoinSimple.gen K x) = 0
参数：hx : ¬IsIntegral K x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_eq_zero_of_not_exists_basis`：trace_eq_zero_of_not_exists_b
asis (h : ¬exists s : Finset S, Nonempty (Basis s R S)) : trace R S = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_iff_finiteDimensional`：fg_iff_finiteDimensional (s : Submod
ule K V) : s.FG ↔ FiniteDimensional K s
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
-/
theorem trace_gen_eq_zero {x : L} (hx : ¬IsIntegral K x) :
    Algebra.trace K K⟮x⟯ (AdjoinSimple.gen K x) = 0 := by
  rw [trace_eq_zero_of_not_exists_basis, LinearMap.zero_apply]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact subset_adjoin K _ (Set.mem_singleton x)
/-
**IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots** 是 Mathlib 中的一个定理，位于命名空
间 `IntermediateField.AdjoinSimple`。
形式化陈述：trace_gen_eq_sum_roots (x : L) (hf : ((minpoly K x).map (algebraMap K F)).
Splits) : algebraMap K F (trace K K⟮x⟯ (AdjoinSimple.gen K x)) = ((minpoly K x).
aroots F).sum
参数：x : L；hf : ((minpoly K x).map (algebraMap K F)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `PowerBasis.trace_gen_eq_sum_roots`：PowerBasis.trace_gen_eq_sum_roots [No
ntrivial S] (pb : PowerBasis K S) (hf : ((minpoly K pb.gen).map (algebraMap K F)
).Splits) : algebraMap …
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aroots.congr_simp`：∀ {T : Type w} [inst : CommRing T] (p p_1 
: Polynomial T),   p = p_1 →     ∀ (S : Type u_1) [inst_1 : CommRing S] [inst_2 
: IsDomain S] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IntermediateField.AdjoinSimple.trace_gen_eq_zero`：trace_gen_eq_zero {x :
 L} (hx : ¬IsIntegral K x) : Algebra.trace K K⟮x⟯ (AdjoinSimple.gen K x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
-/
theorem trace_gen_eq_sum_roots (x : L) (hf : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (trace K K⟮x⟯ (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).sum := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, trace_gen_eq_zero hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx, (adjoin.powerBasis hx).trace_gen_eq_sum_roots] <;>
    rw [adjoin.powerBasis_gen hx, ← minpoly.algebraMap_eq injKxL] <;>
    try simp only [AdjoinSimple.algebraMap_gen _ _]
  exact hf

end IntermediateField.AdjoinSimple

open IntermediateField

variable (K)

/-
**trace_eq_trace_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) : trace K L x = finr
ank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x)
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.trace_trace`：trace_trace [Algebra S T] [IsScalarTower R S T] [Mo
dule.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T)
 : trace …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
· 使用定理 `Algebra.trace_algebraMap`：trace_algebraMap [StrongRankCondition R] [Modu
le.Free R S] (x : R) : trace R S (algebraMap R S x) = finrank R S • x
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x) := by
  rw [← trace_trace (S := K⟮x⟯)]
  conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
  rw [trace_algebraMap, LinearMap.map_smul_of_tower]

variable {K} in
/-- Trace of the generator of a simple adjoin equals negative of the next coefficient of
its minimal polynomial coefficient. -/
/-
**trace_adjoinSimpleGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trace_adjoinSimpleGen {x : L} (hx : IsIntegral K x) : trace K K⟮x⟯ (Adjoin
Simple.gen K x) = -(minpoly K x).nextCoeff
参数：hx : IsIntegral K x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.minpoly_gen`：minpoly_gen (α : E) : minpoly F (AdjoinSi
mple.gen F α) = minpoly F α
· 使用定理 `PowerBasis.trace_gen_eq_nextCoeff_minpoly`：PowerBasis.trace_gen_eq_nextC
oeff_minpoly [Nontrivial S] (pb : PowerBasis K S) : Algebra.trace K S pb.gen = -
(minpoly K pb.gen).nextCoeff
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
Trace of the generator of a simple adjoin equals negative of the next coefficien
t of
its minimal polynomial coefficient.
-/
theorem trace_adjoinSimpleGen {x : L} (hx : IsIntegral K x) :
    trace K K⟮x⟯ (AdjoinSimple.gen K x) = -(minpoly K x).nextCoeff := by
  simpa [minpoly_gen K x] using PowerBasis.trace_gen_eq_nextCoeff_minpoly <| adjoin.powerBasis hx
/-
**trace_eq_finrank_mul_minpoly_nextCoeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trace_eq_finrank_mul_minpoly_nextCoeff [FiniteDimensional K L] (x : L) : t
race K L x = finrank K⟮x⟯ L * -(minpoly K x).nextCoeff
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trace_eq_trace_adjoin`：trace_eq_trace_adjoin [FiniteDimensional K L] (x 
: L) : trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x)
· 使用定理 `trace_adjoinSimpleGen`：trace_adjoinSimpleGen {x : L} (hx : IsIntegral K 
x) : trace K K⟮x⟯ (AdjoinSimple.gen K x) = -(minpoly K x).nextCoeff
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem trace_eq_finrank_mul_minpoly_nextCoeff [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L * -(minpoly K x).nextCoeff := by
  rw [trace_eq_trace_adjoin, trace_adjoinSimpleGen (.of_finite K x), Algebra.smul_def]; rfl

variable {K}
/-
**trace_eq_sum_roots** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trace_eq_sum_roots [FiniteDimensional K L] {x : L} (hF : ((minpoly K x).ma
p (algebraMap K F)).Splits) : algebraMap K F (Algebra.trace K L x) = finrank K⟮x
⟯ L • ((minpoly K x).aroots F).sum
参数：hF : ((minpoly K x).map (algebraMap K F)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trace_eq_trace_adjoin`：trace_eq_trace_adjoin [FiniteDimensional K L] (x 
: L) : trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots`：trace_gen_eq_sum_
roots (x : L) (hf : ((minpoly K x).map (algebraMap K F)).Splits) : algebraMap K 
F (trace K K⟮x⟯ (AdjoinSimple.gen K x)) = (…
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
-/
theorem trace_eq_sum_roots [FiniteDimensional K L] {x : L}
    (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (Algebra.trace K L x) =
      finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum := by
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, map_mul, ← Algebra.smul_def,
    IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF, IsScalarTower.algebraMap_smul]

end EqSumRoots

variable {F : Type*} [Field F]
variable [Algebra R L] [Algebra L F] [Algebra R F] [IsScalarTower R L F]

open Polynomial

attribute [-instance] Field.toEuclideanDomain

/-
**Algebra.isIntegral_trace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isIntegral_trace [FiniteDimensional L F] {x : F} (hx : IsIntegral 
R x) : IsIntegral R (Algebra.trace L F x)
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `trace_eq_sum_roots`：trace_eq_sum_roots [FiniteDimensional K L] {x : L} (
hF : ((minpoly K x).map (algebraMap K F)).Splits) : algebraMap K F (Algebra.trac
e K L x)…
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `IsIntegral.nsmul`：IsIntegral.nsmul {x : B} (h : IsIntegral R x) (n : Nat
) : IsIntegral R (n • x)
· 使用定理 `IsIntegral.multiset_sum`：IsIntegral.multiset_sum {s : Multiset A} (h : f
orall x in s, IsIntegral R x) : IsIntegral R s.sum
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `minpoly.aeval_of_isScalarTower`：aeval_of_isScalarTower (R : Type*) {K T 
U : Type*} [CommRing R] [Field K] [CommRing T] [Algebra R K] [Algebra K T] [Alge
bra R T] [IsScalarTo…
· 使用定理 `Polynomial.mem_roots_map`：mem_roots_map [CommRing k] [IsDomain k] {f : R
 ->+* k} {x : k} (hp : p != 0) : x in (p.map f).roots ↔ p.eval₂ f x = 0
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
-/
theorem Algebra.isIntegral_trace [FiniteDimensional L F] {x : F} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace L F x) := by
  have hx' : IsIntegral L x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap L (AlgebraicClosure F)).injective, trace_eq_sum_roots]
  · refine (IsIntegral.multiset_sum ?_).nsmul _
    intro y hy
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy ⊢
    exact minpoly.aeval_of_isScalarTower R x y hy
  · apply IsAlgClosed.splits
/-
**Algebra.trace_eq_of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.trace_eq_of_algEquiv {A B C : Type*} [CommRing A] [CommRing B] [Co
mmRing C] [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (x) : Algebra.trace A C (e
 x) = Algebra.trace A B x
参数：e : B ≃ₐ[A] C；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.trace_conj'`：trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : tr
ace R N (e.conj f) = trace R M f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Algebra.trace_eq_of_algEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (x) :
    Algebra.trace A C (e x) = Algebra.trace A B x := by
  simp_rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr; ext; simp

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.trace_eq_of_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.trace_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [C
ommRing C] [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp
 e = algebraMap A C) (x) : e (Algebra.trace A C x) = Algebra.trace B C x
参数：e : A ≃+* B；he : (algebraMap B C).comp e = algebraMap A C；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_eq_matrix_trace`：trace_eq_matrix_trace [DecidableEq ι] (b 
: Basis ι R S) (s : S) : trace R S s = Matrix.trace (Algebra.leftMulMatrix b s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `AddMonoidHom.map_trace`：∀ {n : Type u_3} {R : Type u_6} {S : Type u_7} [
inst : Fintype n] [inst_1 : AddCommMonoid R] [inst_2 : AddCommMonoid S]   {F : T
ype u_8} [in…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Module.Basis.mapCoeffs_repr`：∀ {ι : Type u_10} {R : Type u_11} {M : Type
 u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mapCoeffs`：coe_mapCoeffs : (b.mapCoeffs f h : ι -> M) =
 b
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Module.compHom.toLinearEquiv_symm_apply`：∀ {R : Type u_9} {S : Type u_10
} [inst : Semiring R] [inst_1 : Semiring S] (g : R ≃+* S) (a : S),   (Module.com
pHom.toLinearEquiv g).symm a …
（共 35 条，此处仅展示前 30 条）
-/
lemma Algebra.trace_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C) (x) :
    e (Algebra.trace A C x) = Algebra.trace B C x := by
  classical
  by_cases h : ∃ s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.trace_eq_matrix_trace b,
      Algebra.trace_eq_matrix_trace (b.mapCoeffs e.symm (by simp [Algebra.smul_def, ← he]))]
    rw [AddMonoidHom.map_trace]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [trace_eq_zero_of_not_exists_basis _ h, trace_eq_zero_of_not_exists_basis,
    LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩
/-
**Algebra.trace_eq_of_equiv_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.trace_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommR
ing B₁] [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+*
 A₂) (e₂ : B₁ ≃+* B₂) (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑
e₂ (algebraMap A₁ B₁)) (x) : Algebra.trace A₁ B₁ x = e₁.symm (Algebra.trace A₂ B
₂ (e₂ x))
参数：e₁ : A₁ ≃+* A₂；e₂ : B₁ ≃+* B₂；he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = Ring
Hom.comp ↑e₂ (algebraMap A₁ B₁)；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.trace_eq_of_ringEquiv`：Algebra.trace_eq_of_ringEquiv {A B C : Ty
pe*} [CommRing A] [CommRing B] [CommRing C] [Algebra A C] [Algebra B C] (e : A ≃
+* B) (he : (algebr…
· 使用引理 `Algebra.trace_eq_of_algEquiv`：Algebra.trace_eq_of_algEquiv {A B C : Type
*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (e : B ≃ₐ[
A] C) (x) : Algebr…
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
lemma Algebra.trace_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.trace A₁ B₁ x = e₁.symm (Algebra.trace A₂ B₂ (e₂ x)) := by
  let := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
  rw [← Algebra.trace_eq_of_ringEquiv e₁ he, ← Algebra.trace_eq_of_algEquiv e',
    RingEquiv.symm_apply_apply]
  rfl

section EqSumEmbeddings

variable [Algebra K F] [IsScalarTower K L F]

open Algebra IntermediateField

variable (F) (E : Type*) [Field E] [Algebra K E]

/-
**trace_eq_sum_embeddings_gen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trace_eq_sum_embeddings_gen (pb : PowerBasis K L) (hE : ((minpoly K pb.gen
).map (algebraMap K E)).Splits) (hfx : IsSeparable K pb.gen) : algebraMap K E (A
lgebra.trace K L pb.gen) = (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum f
un σ => σ pb.gen
参数：pb : PowerBasis K L；hE : ((minpoly K pb.gen).map (algebraMap K E)).Splits；hfx
 : IsSeparable K pb.gen。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.trace_gen_eq_sum_roots`：PowerBasis.trace_gen_eq_sum_roots [No
ntrivial S] (pb : PowerBasis K S) (hf : ((minpoly K pb.gen).map (algebraMap K F)
).Splits) : algebraMap …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `PowerBasis.liftEquiv'_apply_coe`：∀ {S : Type u_2} [inst : Ring S] {A : T
ype u_4} {B : Type u_5} [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 : 
Algebra A B] [inst_4 …
· 使用定理 `id_def`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Finset.sum_mem_multiset`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddComm
Monoid M] [inst_1 : DecidableEq ι] (m : Multiset ι)   (f : { x // x ∈ m } → M) (
g : ι → M), (…
· 使用定理 `Finset.sum_eq_multiset_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddC
ommMonoid M] (s : Finset ι) (f : ι → M),   ∑ x ∈ s, f x = (Multiset.map f s.val)
.sum
· 使用定理 `Multiset.toFinset_val`：toFinset_val (s : Multiset α) : s.toFinset.1 = s.
dedup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Polynomial.separable_map`：separable_map {S} [CommRing S] [Nontrivial S] 
(f : F ->+* S) {p : F[X]} : (p.map f).Separable ↔ p.Separable
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
-/
theorem trace_eq_sum_embeddings_gen (pb : PowerBasis K L)
    (hE : ((minpoly K pb.gen).map (algebraMap K E)).Splits) (hfx : IsSeparable K pb.gen) :
    algebraMap K E (Algebra.trace K L pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ => σ pb.gen := by
  let := Classical.decEq E
  let : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [pb.trace_gen_eq_sum_roots hE, Fintype.sum_equiv pb.liftEquiv', Finset.sum_mem_multiset,
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr _,
    Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
  swap
  · intro x; rfl
  · intro σ
    rw [PowerBasis.liftEquiv'_apply_coe, id_def]

variable [IsAlgClosed E]
/-
**sum_embeddings_eq_finrank_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [Algebra.IsSeparable
 K F] (pb : PowerBasis K L) : ∑ σ : F ->ₐ[K] E, σ (algebraMap L F pb.gen) = finr
ank L F • (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ : L ->ₐ[K] E
 => σ pb.gen
参数：pb : PowerBasis K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.right`：∀ (F : Type u) (K : Type v) (A : Type w) [inst 
: Semiring F] [inst_1 : Semiring K] [inst_2 : _root_.Module F K]   [inst_3 : Add
CommMonoid A]…
· 使用定理 `Algebra.isSeparable_tower_top_of_isSeparable`：Algebra.isSeparable_tower_
top_of_isSeparable [Algebra.IsSeparable F E] : Algebra.IsSeparable L E
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sigma_univ`：∀ {ι : Type u_1} {κ : ι → Type u_3} [inst : (i :
 ι) → Fintype (κ i)] [inst_1 : Fintype ι],   (Finset.univ.sigma fun x => Finset.
univ) = Fins…
· 使用定理 `Finset.sum_sigma`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid 
β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : Sigma σ
 → β),…
· 使用定理 `Finset.sum_nsmul`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid 
M] (s : Finset ι) (n : ℕ) (f : ι → M),   ∑ x ∈ s, n • f x = n • ∑ x ∈ s, f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.card`：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra 
F K] : Fintype.card (E ->ₐ[F] K) = finrank F E
-/
theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (pb : PowerBasis K L) :
    ∑ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      finrank L F •
        (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ : L →ₐ[K] E => σ pb.gen := by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen,
    ← Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_nsmul]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    let : Algebra L E := σ.toRingHom.toAlgebra
    simp_rw [Finset.sum_const, Finset.card_univ, ← AlgHom.card L F E]
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.domRestrict, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
/-
**trace_eq_sum_embeddings** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trace_eq_sum_embeddings [FiniteDimensional K L] [Algebra.IsSeparable K L] 
{x : L} : algebraMap K E (Algebra.trace K L x) = ∑ σ : L ->ₐ[K] E, σ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trace_eq_trace_adjoin`：trace_eq_trace_adjoin [FiniteDimensional K L] (x 
: L) : trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `trace_eq_sum_embeddings_gen`：trace_eq_sum_embeddings_gen (pb : PowerBasi
s K L) (hE : ((minpoly K pb.gen).map (algebraMap K E)).Splits) (hfx : IsSeparabl
e K pb.gen) : alg…
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `sum_embeddings_eq_finrank_mul`：sum_embeddings_eq_finrank_mul [FiniteDime
nsional K F] [Algebra.IsSeparable K F] (pb : PowerBasis K L) : ∑ σ : F ->ₐ[K] E,
 σ (algebraMap L F …
-/
theorem trace_eq_sum_embeddings [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L} :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x := by
  have hx := Algebra.IsSeparable.isIntegral K x
  let pb := adjoin.powerBasis hx
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, map_mul, ← adjoin.powerBasis_gen hx,
    trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits _), ← Algebra.smul_def,
    algebraMap_smul]
  · exact (sum_embeddings_eq_finrank_mul L E pb).symm
  · have := Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact Algebra.IsSeparable.isSeparable K _
/-
**trace_eq_sum_automorphisms** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] 
: algebraMap K L (Algebra.trace K L x) = ∑ σ : Gal(L/K), σ x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `trace_eq_sum_embeddings`：trace_eq_sum_embeddings [FiniteDimensional K L]
 [Algebra.IsSeparable K L] {x : L} : algebraMap K E (Algebra.trace K L x) = ∑ σ 
: L ->ₐ[K] E,…
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
-/
theorem trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : Gal(L/K), σ x := by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L) (x := x)]
    simp only [algebraMap_eq_smul_one, smul_one_smul]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, algebraMap_self, RingHom.id_apply]

end EqSumEmbeddings

section NotIsSeparable

/-
**Algebra.trace_eq_zero_of_not_isSeparable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.trace_eq_zero_of_not_isSeparable (H : ¬ Algebra.IsSeparable K L) :
 trace K L = 0
参数：H : ¬ Algebra.IsSeparable K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `expChar_ne_zero`：expChar_ne_zero (p : Nat) [hR : ExpChar R p] : p != 0
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.algebraMap_apply`：∀ {K : Type u_1} {L : Type u_2} [ins
t : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K 
L)   (x : ↥S), (algebraM…
· 使用定理 `Algebra.trace_trace`：trace_trace [Algebra S T] [IsScalarTower R S T] [Mo
dule.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T)
 : trace …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.trace_algebraMap`：trace_algebraMap [StrongRankCondition R] [Modu
le.Free R S] (x : R) : trace R S (algebraMap R S x) = finrank R S • x
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `IsPurelyInseparable.finrank_eq_pow`：IsPurelyInseparable.finrank_eq_pow (
q : Nat) [ExpChar F q] [IsPurelyInseparable F E] [FiniteDimensional F E] : exist
s n, finrank F E = q ^ n
· 使用定理 `separableClosure.eq_top_iff`：separableClosure.eq_top_iff : separableClos
ure F E = ⊤ ↔ Algebra.IsSeparable F E
· 使用引理 `IntermediateField.finrank_eq_one_iff_eq_top`：finrank_eq_one_iff_eq_top {
K : IntermediateField F E} : Module.finrank K E = 1 ↔ K = ⊤
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 69 条，此处仅展示前 30 条）
-/
lemma Algebra.trace_eq_zero_of_not_isSeparable (H : ¬ Algebra.IsSeparable K L) :
    trace K L = 0 := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := expChar_ne_zero K p
  ext x
  by_cases h₀ : FiniteDimensional K L; swap
  · rw [trace_eq_zero_of_not_exists_basis]
    rintro ⟨s, ⟨b⟩⟩
    exact h₀ (Module.Finite.of_basis b)
  by_cases hx : IsSeparable K x
  · lift x to separableClosure K L using hx
    rw [← IntermediateField.algebraMap_apply, ← trace_trace (S := separableClosure K L),
      trace_algebraMap]
    obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure K L) L p
    cases n with
    | zero =>
      rw [pow_zero, IntermediateField.finrank_eq_one_iff_eq_top, separableClosure.eq_top_iff] at hn
      cases H hn
    | succ n =>
      cases hp with
      | zero =>
        rw [one_pow, IntermediateField.finrank_eq_one_iff_eq_top, separableClosure.eq_top_iff] at hn
        cases H hn
      | prime hprime =>
        rw [hn, pow_succ', mul_smul, LinearMap.map_smul_of_tower, nsmul_eq_mul,
          CharP.cast_eq_zero, zero_mul, LinearMap.zero_apply]
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff]
    obtain ⟨g, hg₁, m, hg₂⟩ :=
      (minpoly.irreducible (IsIntegral.isIntegral (R := K) x)).hasSeparableContraction p
    cases m with
    | zero =>
      obtain rfl : g = minpoly K x := by simpa using hg₂
      cases hx hg₁
    | succ n =>
      rw [nextCoeff, if_neg, ← hg₂, coeff_expand (by positivity),
        if_neg, neg_zero, mul_zero, LinearMap.zero_apply]
      · rw [natDegree_expand]
        intro h
        have := Nat.dvd_sub (dvd_mul_left (p ^ (n + 1)) g.natDegree) h
        rw [tsub_tsub_cancel_of_le, Nat.dvd_one] at this
        · obtain rfl : g = minpoly K x := by simpa [this] using hg₂
          cases hx hg₁
        · rw [Nat.one_le_iff_ne_zero]
          have : g.natDegree ≠ 0 := fun e ↦ by
            have := congr(natDegree $hg₂)
            rw [natDegree_expand, e, zero_mul] at this
            exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne this
          positivity
      · exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne'

end NotIsSeparable

section DetNeZero

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z)
variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

open Finset

/-- Given an `A`-algebra `B` and `b`, a `κ`-indexed family of elements of `B`, we define
`traceMatrix A b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
/-
**Algebra.traceMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：traceMatrix (b : κ -> B) : Matrix κ κ A
参数：b : κ -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `A`-algebra `B` and `b`, a `κ`-indexed family of elements of `B`, we de
fine
`traceMatrix A b` as the matrix whose `(i j)`-th element is the trace of `b i * 
b j`.
-/
noncomputable def traceMatrix (b : κ → B) : Matrix κ κ A :=
  of fun i j => traceForm A B (b i) (b j)

-- TODO: set as an equation lemma for `traceMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Algebra.traceMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceMatrix_apply (b : κ -> B) (i j) : traceMatrix A b i j = traceForm A B
 (b i) (b j)
参数：b : κ -> B；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem traceMatrix_apply (b : κ → B) (i j) : traceMatrix A b i j = traceForm A B (b i) (b j) :=
  rfl
/-
**Algebra.traceMatrix_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceMatrix_reindex {κ' : Type*} (b : Basis κ A B) (f : κ ≃ κ') : traceMat
rix A (b.reindex f) = reindex f f (traceMatrix A b)
参数：b : Basis κ A B；f : κ ≃ κ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem traceMatrix_reindex {κ' : Type*} (b : Basis κ A B) (f : κ ≃ κ') :
    traceMatrix A (b.reindex f) = reindex f f (traceMatrix A b) := by ext (x y); simp

variable {A}
/-
**Algebra.traceMatrix_of_matrix_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceMatrix_of_matrix_vecMul [Fintype κ] (b : κ -> B) (P : Matrix κ κ A) :
 traceMatrix A (b ᵥ* P.map (algebraMap A B)) = Pᵀ * traceMatrix A b * P
参数：b : κ -> B；P : Matrix κ κ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.traceMatrix_apply`：traceMatrix_apply (b : κ -> B) (i j) : traceM
atrix A b i j = traceForm A B (b i) (b j)
· 使用定理 `Matrix.vecMul.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst :
 NonUnitalNonAssocSemiring α] [inst_1 : Fintype m] (v : m → α)   (M : Matrix m n
 α) (x :…
· 使用定理 `dotProduct.eq_1`：∀ {m : Type u_2} {α : Type v} [inst : Fintype m] [inst_
1 : Mul α] [inst_2 : AddCommMonoid α] (v w : m → α),   v ⬝ᵥ w = ∑ i, v i * w i
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `LinearMap.BilinForm.sum_left`：sum_left {α} (t : Finset α) (g : α -> M) (
w : M) : B (∑ i in t, g i) w = ∑ i in t, B (g i) w
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
· 使用定理 `LinearMap.BilinForm.sum_right`：sum_right {α} (t : Finset α) (w : M) (g :
 α -> M) : B w (∑ i in t, g i) = ∑ i in t, B w (g i)
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Matrix.map_apply`：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j :
 n} : M.map f i j = f (M i j)
· 使用定理 `Algebra.traceForm_apply`：traceForm_apply (x y : S) : traceForm R S x y =
 trace R S (x * y)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 45 条，此处仅展示前 30 条）
-/
theorem traceMatrix_of_matrix_vecMul [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A (b ᵥ* P.map (algebraMap A B)) = Pᵀ * traceMatrix A b * P := by
  ext (α β)
  rw [traceMatrix_apply, vecMul, dotProduct, vecMul, dotProduct, Matrix.mul_apply,
    BilinForm.sum_left,
    Fintype.sum_congr _ _ fun i : κ =>
      BilinForm.sum_right _ _ (b i * P.map (algebraMap A B) i α) fun y : κ =>
        b y * P.map (algebraMap A B) y β,
    sum_comm]
  congr; ext x
  rw [Matrix.mul_apply, sum_mul]
  congr; ext y
  rw [map_apply, traceForm_apply, mul_comm (b y), ← smul_def]
  simp only [smul_eq_mul, RingHom.id_apply, map_apply, transpose_apply, map_smulₛₗ,
    Algebra.smul_mul_assoc]
  rw [mul_comm (b x), ← smul_def]
  ring_nf
  rw [mul_assoc]
  simp [mul_comm]
/-
**Algebra.traceMatrix_of_matrix_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceMatrix_of_matrix_mulVec [Fintype κ] (b : κ -> B) (P : Matrix κ κ A) :
 traceMatrix A (P.map (algebraMap A B) *ᵥ b) = P * traceMatrix A b * Pᵀ
参数：b : κ -> B；P : Matrix κ κ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transposeAddEquiv_apply`：∀ (m : Type u_2) (n : Type u_3) (α : Typ
e u_11) [inst : Add α] (M : Matrix m n α),   (Matrix.transposeAddEquiv m n α) M 
= M.transpose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `Algebra.traceMatrix_of_matrix_vecMul`：traceMatrix_of_matrix_vecMul [Fint
ype κ] (b : κ -> B) (P : Matrix κ κ A) : traceMatrix A (b ᵥ* P.map (algebraMap A
 B)) = Pᵀ * traceMatrix A …
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
-/
theorem traceMatrix_of_matrix_mulVec [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A (P.map (algebraMap A B) *ᵥ b) = P * traceMatrix A b * Pᵀ := by
  refine AddEquiv.injective (transposeAddEquiv κ κ A) ?_
  rw [transposeAddEquiv_apply, transposeAddEquiv_apply, ← vecMul_transpose, ← transpose_map,
    traceMatrix_of_matrix_vecMul, transpose_transpose]
/-
**Algebra.traceMatrix_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceMatrix_of_basis [Fintype κ] [DecidableEq κ] (b : Basis κ A B) : trace
Matrix A b = (traceForm A B).toMatrix b
参数：b : Basis κ A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.traceMatrix_apply`：traceMatrix_apply (b : κ -> B) (i j) : traceM
atrix A b i j = traceForm A B (b i) (b j)
· 使用定理 `Algebra.traceForm_apply`：traceForm_apply (x y : S) : traceForm R S x y =
 trace R S (x * y)
· 使用定理 `Algebra.traceForm_toMatrix`：traceForm_toMatrix [DecidableEq ι] (b : Basi
s ι R S) (i j) : (traceForm R S).toMatrix b i j = trace R S (b i * b j)
-/
theorem traceMatrix_of_basis [Fintype κ] [DecidableEq κ] (b : Basis κ A B) :
    traceMatrix A b = (traceForm A B).toMatrix b := by
  ext (i j)
  rw [traceMatrix_apply, traceForm_apply, traceForm_toMatrix]
/-
**Algebra.traceMatrix_of_basis_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceMatrix_of_basis_mulVec [Fintype ι] (b : Basis ι A B) (z : B) : traceM
atrix A b *ᵥ b.equivFun z = fun i => trace A B (z * b i)
参数：b : Basis ι A B；z : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.replicateCol_apply`：replicateCol_apply {ι : Type*} (w : m -> α) (
i) (j : ι) : replicateCol ι w i j = w i
· 使用定理 `Matrix.replicateCol_mulVec`：replicateCol_mulVec [Fintype n] [NonUnitalNo
nAssocSemiring α] (M : Matrix m n α) (v : n -> α) : replicateCol ι (M *ᵥ v) = M 
* replicateCol ι…
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Algebra.traceMatrix.eq_1`：∀ {κ : Type w} (A : Type u) {B : Type v} [inst
 : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] (b : κ → B),   Algeb
ra.traceMatrix…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Module.Basis.sum_equivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6
} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : Finty…
-/
theorem traceMatrix_of_basis_mulVec [Fintype ι] (b : Basis ι A B) (z : B) :
    traceMatrix A b *ᵥ b.equivFun z = fun i => trace A B (z * b i) := by
  ext i
  rw [← replicateCol_apply (ι := Fin 1) (traceMatrix A b *ᵥ b.equivFun z) i 0, replicateCol_mulVec,
    Matrix.mul_apply, traceMatrix]
  simp only [replicateCol_apply, traceForm_apply]
  conv_lhs =>
    congr
    rfl
    ext
    rw [mul_comm _ (b.equivFun z _), ← smul_eq_mul, of_apply, ← map_smul]
  rw [← _root_.map_sum]
  congr
  conv_lhs =>
    congr
    rfl
    ext
    rw [← mul_smul_comm]
  rw [← Finset.mul_sum, mul_comm z]
  congr
  rw [b.sum_equivFun]

variable (A)

/-- `embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose `(i, σ)` coefficient is
  `σ (b i)`. It is mostly useful for fields when `Fintype.card κ = finrank A B` and `C` is
  algebraically closed. -/
/-
**Algebra.embeddingsMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：embeddingsMatrix (b : κ -> B) : Matrix κ (B ->ₐ[A] C) C
参数：b : κ -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose `(i, σ)` c
oefficient is
  `σ (b i)`. It is mostly useful for fields when `Fintype.card κ = finrank A B` 
and `C` is
  algebraically closed.
-/
def embeddingsMatrix (b : κ → B) : Matrix κ (B →ₐ[A] C) C :=
  of fun i (σ : B →ₐ[A] C) => σ (b i)

-- TODO: set as an equation lemma for `embeddingsMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Algebra.embeddingsMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：embeddingsMatrix_apply (b : κ -> B) (i) (σ : B ->ₐ[A] C) : embeddingsMatri
x A C b i σ = σ (b i)
参数：b : κ -> B；i；σ : B ->ₐ[A] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embeddingsMatrix_apply (b : κ → B) (i) (σ : B →ₐ[A] C) :
    embeddingsMatrix A C b i σ = σ (b i) :=
  rfl

/-- `embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)` coefficient
  is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ` given by a
  bijection `e : κ ≃ (B →ₐ[A] C)`. It is mostly useful for fields and `C` is algebraically closed.
  In this case, in presence of `h : Fintype.card κ = finrank A B`, one can take
  `e := equivOfCardEq ((AlgHom.card A B C).trans h.symm)`. -/
/-
**Algebra.embeddingsMatrixReindex** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：embeddingsMatrixReindex (b : κ -> B) (e : κ ≃ (B ->ₐ[A] C))
参数：b : κ -> B；e : κ ≃ (B ->ₐ[A] C)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)` co
efficient
  is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ
` given by a
  bijection `e : κ ≃ (B →ₐ[A] C)`. It is mostly useful for fields and `C` is alg
ebraically closed.
  In this case, in presence of `h : Fintype.card κ = finrank A B`, one can take
  `e := equivOfCardEq ((AlgHom.card A B C).trans h.symm)`.
-/
def embeddingsMatrixReindex (b : κ → B) (e : κ ≃ (B →ₐ[A] C)) :=
  reindex (Equiv.refl κ) e.symm (embeddingsMatrix A C b)

variable {A}
/-
**Algebra.embeddingsMatrixReindex_eq_vandermonde** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra`。
形式化陈述：embeddingsMatrixReindex_eq_vandermonde (pb : PowerBasis A B) (e : Fin pb.d
im ≃ (B ->ₐ[A] C)) : embeddingsMatrixReindex A C pb.basis e = (vandermonde fun i
 => e i pb.gen)ᵀ
参数：pb : PowerBasis A B；e : Fin pb.dim ≃ (B ->ₐ[A] C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem embeddingsMatrixReindex_eq_vandermonde (pb : PowerBasis A B)
    (e : Fin pb.dim ≃ (B →ₐ[A] C)) :
    embeddingsMatrixReindex A C pb.basis e = (vandermonde fun i => e i pb.gen)ᵀ := by
  ext i j
  simp [embeddingsMatrixReindex, embeddingsMatrix]

section Field

variable (K) (E : Type z) [Field E]
variable [Algebra K E]
variable [Module.Finite K L] [Algebra.IsSeparable K L] [IsAlgClosed E]
variable (b : κ → L) (pb : PowerBasis K L)

/-
**Algebra.traceMatrix_eq_embeddingsMatrix_mul_trans** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra`。
形式化陈述：traceMatrix_eq_embeddingsMatrix_mul_trans : (traceMatrix K b).map (algebra
Map K E) = embeddingsMatrix K E b * (embeddingsMatrix K E b)ᵀ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trace_eq_sum_embeddings`：trace_eq_sum_embeddings [FiniteDimensional K L]
 [Algebra.IsSeparable K L] {x : L} : algebraMap K E (Algebra.trace K L x) = ∑ σ 
: L ->ₐ[K] E,…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem traceMatrix_eq_embeddingsMatrix_mul_trans : (traceMatrix K b).map (algebraMap K E) =
    embeddingsMatrix K E b * (embeddingsMatrix K E b)ᵀ := by
  ext (i j); simp [trace_eq_sum_embeddings, embeddingsMatrix, Matrix.mul_apply]
/-
**Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans** 是 Mathlib 中的一个定理，位于
命名空间 `Algebra`。
形式化陈述：traceMatrix_eq_embeddingsMatrixReindex_mul_trans [Fintype κ] (e : κ ≃ (L -
>ₐ[K] E)) : (traceMatrix K b).map (algebraMap K E) = embeddingsMatrixReindex K E
 b e * (embeddingsMatrixReindex K E b e)ᵀ
参数：e : κ ≃ (L ->ₐ[K] E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.traceMatrix_eq_embeddingsMatrix_mul_trans`：traceMatrix_eq_embedd
ingsMatrix_mul_trans : (traceMatrix K b).map (algebraMap K E) = embeddingsMatrix
 K E b * (embeddingsMatrix K E b)ᵀ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Algebra.embeddingsMatrixReindex.eq_1`：∀ {κ : Type w} (A : Type u) {B : T
ype v} (C : Type z) [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra 
A B]   [inst_3 : CommRing …
· 使用定理 `Matrix.reindex_apply`：reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matri
x m n α) : reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.submatrix_mul_transpose_submatrix`：submatrix_mul_transpose_submat
rix [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α] (e : m ≃ n) (M : Matrix m 
n α) : M.submatrix id e * Mᵀ.s…
· 使用定理 `Equiv.coe_refl`：∀ {α : Sort u}, ⇑(Equiv.refl α) = id
· 使用定理 `Equiv.refl_symm`：∀ {α : Sort u}, (Equiv.refl α).symm = Equiv.refl α
-/
theorem traceMatrix_eq_embeddingsMatrixReindex_mul_trans [Fintype κ] (e : κ ≃ (L →ₐ[K] E)) :
    (traceMatrix K b).map (algebraMap K E) =
      embeddingsMatrixReindex K E b e * (embeddingsMatrixReindex K E b e)ᵀ := by
  rw [traceMatrix_eq_embeddingsMatrix_mul_trans, embeddingsMatrixReindex, reindex_apply,
    transpose_submatrix, ← submatrix_mul_transpose_submatrix, ← Equiv.coe_refl, Equiv.refl_symm]

end Field

end Algebra

open Algebra

variable (pb : PowerBasis K L)

/-
**det_traceMatrix_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：det_traceMatrix_ne_zero' [Algebra.IsSeparable K L] : det (traceMatrix K pb
.basis) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerBasis.finite`：finite (pb : PowerBasis R S) : Module.Finite R S
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.card`：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra 
F K] : Fintype.card (E ->ₐ[F] K) = finrank F E
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans`：traceMatrix_eq
_embeddingsMatrixReindex_mul_trans [Fintype κ] (e : κ ≃ (L ->ₐ[K] E)) : (traceMa
trix K b).map (algebraMap K E) = embeddingsMat…
· 使用定理 `Algebra.embeddingsMatrixReindex_eq_vandermonde`：embeddingsMatrixReindex_
eq_vandermonde (pb : PowerBasis A B) (e : Fin pb.dim ≃ (B ->ₐ[A] C)) : embedding
sMatrixReindex A C pb.basis e = (van…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_self_eq_zero`：mul_self_eq_zero : a * a = 0 ↔ a = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_vandermonde`：det_vandermonde (v : Fin n -> R) : det (vandermo
nde v) = ∏ i : Fin n, ∏ j in Ioi i, (v j - v i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.mem_Ioi`：mem_Ioi : x in Ioi a ↔ a < x
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `PowerBasis.algHom_ext`：algHom_ext {S' : Type*} [Semiring S'] [Algebra R 
S'] (pb : PowerBasis R S) ⦃f g : S ->ₐ[R] S'⦄ (h : f pb.gen = g pb.gen) : f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem det_traceMatrix_ne_zero' [Algebra.IsSeparable K L] : det (traceMatrix K pb.basis) ≠ 0 := by
  suffices algebraMap K (AlgebraicClosure L) (det (traceMatrix K pb.basis)) ≠ 0 by
    refine mt (fun ht => ?_) this
    rw [ht, map_zero]
  have : FiniteDimensional K L := pb.finite
  let e : Fin pb.dim ≃ (L →ₐ[K] AlgebraicClosure L) := (Fintype.equivFinOfCardEq ?_).symm
  · rw [RingHom.map_det, RingHom.mapMatrix_apply,
      traceMatrix_eq_embeddingsMatrixReindex_mul_trans K _ _ e,
      embeddingsMatrixReindex_eq_vandermonde, det_mul, det_transpose]
    refine mt mul_self_eq_zero.mp ?_
    simp only [det_vandermonde, Finset.prod_eq_zero_iff, not_exists, sub_eq_zero]
    rintro i ⟨_, j, hij, h⟩
    exact (Finset.mem_Ioi.mp hij).ne' (e.injective <| pb.algHom_ext h)
  · rw [AlgHom.card, pb.finrank]
/-
**det_traceForm_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：det_traceForm_ne_zero [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι
] (b : Basis ι K L) : det ((traceForm K L).toMatrix b) != 0
参数：b : Basis ι K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.toMatrix_mul_basis_toMatrix`：LinearMap.BilinForm.toM
atrix_mul_basis_toMatrix (c : Basis o R₁ M₁) (B : BilinForm R₁ M₁) : (b.toMatrix
 c)ᵀ * BilinForm.toMatrix b B * b.toM…
· 使用定理 `Matrix.det_comm'`：det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix 
n m A} {N : Matrix m n A} {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M
 = 1) …
· 使用定理 `Module.Basis.toMatrix_mul_toMatrix_flip`：toMatrix_mul_toMatrix_flip [Dec
idableEq ι] [Fintype ι'] : b.toMatrix b' * b'.toMatrix b = 1
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `Algebra.traceMatrix_of_basis`：traceMatrix_of_basis [Fintype κ] [Decidabl
eEq κ] (b : Basis κ A B) : traceMatrix A b = (traceForm A B).toMatrix b
（共 31 条，此处仅展示前 30 条）
-/
theorem det_traceForm_ne_zero [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) :
    det ((traceForm K L).toMatrix b) ≠ 0 := by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix pb.basis b, ←
    det_comm' (pb.basis.toMatrix_mul_toMatrix_flip b) _, ← Matrix.mul_assoc, det_mul]
  swap; · apply Basis.toMatrix_mul_toMatrix_flip
  refine
    mul_ne_zero
      (IsUnit.of_mul_eq_one ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det ?_).ne_zero ?_
  · calc
      (pb.basis.toMatrix b * (pb.basis.toMatrix b)ᵀ).det *
            ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det =
          (pb.basis.toMatrix b * (b.toMatrix pb.basis * pb.basis.toMatrix b)ᵀ *
              b.toMatrix pb.basis).det := by
        simp only [← det_mul, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = 1 := by
        simp only [Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one, Matrix.mul_one,
          Matrix.det_one]
  simpa only [traceMatrix_of_basis] using det_traceMatrix_ne_zero' pb

variable (K L)

/-- Let $L/K$ be a finite extension of fields. If $L/K$ is separable,
then `traceForm` is nondegenerate. -/
@[stacks 0BIL "(1) => (3)"]
/-
**traceForm_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：traceForm_nondegenerate [FiniteDimensional K L] [Algebra.IsSeparable K L] 
: (traceForm K L).Nondegenerate
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.nondegenerate_of_det_ne_zero`：nondegenerate_of_det_n
e_zero (b : Basis ι A M₂) (h : (BilinForm.toMatrix b B₃).det != 0) : B₃.Nondegen
erate
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `det_traceForm_ne_zero`：det_traceForm_ne_zero [Algebra.IsSeparable K L] [
Fintype ι] [DecidableEq ι] (b : Basis ι K L) : det ((traceForm K L).toMatrix b) 
!= 0

--- 原说明 ---
Let $L/K$ be a finite extension of fields. If $L/K$ is separable,
then `traceForm` is nondegenerate.
-/
theorem traceForm_nondegenerate [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (traceForm K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _
    (det_traceForm_ne_zero (Module.finBasis K L))

@[stacks 0BIL]
/-
**traceForm_nondegenerate_tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：traceForm_nondegenerate_tfae [FiniteDimensional K L] : [Algebra.IsSeparabl
e K L, Algebra.trace K L != 0, (traceForm K L).Nondegenerate].TFAE
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `LinearMap.BilinForm.Nondegenerate.ne_zero`：∀ {R : Type u_1} {M : Type u_
2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R 
M]   [Nontrivial M] {B : Linear…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用引理 `Algebra.trace_eq_zero_of_not_isSeparable`：Algebra.trace_eq_zero_of_not_i
sSeparable (H : ¬ Algebra.IsSeparable K L) : trace K L = 0
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
theorem traceForm_nondegenerate_tfae [FiniteDimensional K L] :
    [Algebra.IsSeparable K L, Algebra.trace K L ≠ 0, (traceForm K L).Nondegenerate].TFAE := by
  tfae_have 1 → 3 := fun _ ↦ traceForm_nondegenerate K L
  tfae_have 3 → 2 := fun H₁ H₂ ↦ H₁.ne_zero (by ext; simp [H₂])
  tfae_have 2 → 1 := not_imp_comm.mp Algebra.trace_eq_zero_of_not_isSeparable
  tfae_finish
/-
**Algebra.trace_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.trace_ne_zero [FiniteDimensional K L] [Algebra.IsSeparable K L] : 
Algebra.trace K L != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `traceForm_nondegenerate_tfae`：traceForm_nondegenerate_tfae [FiniteDimens
ional K L] : [Algebra.IsSeparable K L, Algebra.trace K L != 0, (traceForm K L).N
ondegenerate].TFAE
-/
theorem Algebra.trace_ne_zero [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.trace K L ≠ 0 :=
  ((traceForm_nondegenerate_tfae K L).out 0 1).mp ‹_›
/-
**Algebra.trace_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.trace_surjective [FiniteDimensional K L] [Algebra.IsSeparable K L]
 : Function.Surjective (Algebra.trace K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `LinearMap.range_eq_bot`：range_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊥ 
↔ f = 0
· 使用定理 `Algebra.trace_ne_zero`：Algebra.trace_ne_zero [FiniteDimensional K L] [Al
gebra.IsSeparable K L] : Algebra.trace K L != 0
-/
theorem Algebra.trace_surjective [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Function.Surjective (Algebra.trace K L) := by
  rw [← LinearMap.range_eq_top]
  apply (IsSimpleOrder.eq_bot_or_eq_top (α := Ideal K) _).resolve_left
  rw [LinearMap.range_eq_bot]
  exact Algebra.trace_ne_zero K L

end DetNeZero

section isNilpotent

namespace Algebra

/-- The trace of a nilpotent element is nilpotent. -/
/-
**Algebra.isNilpotent_trace_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isNilpotent_trace_of_isNilpotent {R S : Type*} [CommRing R] [CommRing S] [
Algebra R S] {x : S} (hx : IsNilpotent x) : IsNilpotent (trace R S x)
参数：hx : IsNilpotent x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.isNilpotent_trace_of_isNilpotent`：isNilpotent_trace_of_isNilpo
tent {f : M ->ₗ[R] M} (hf : IsNilpotent f) : IsNilpotent (trace R M f)
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …

--- 原说明 ---
The trace of a nilpotent element is nilpotent.
-/
lemma isNilpotent_trace_of_isNilpotent {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (trace R S x) :=
  LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))

end Algebra

end isNilpotent

section Basis

open Algebra

variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Finite ι] [DecidableEq ι]
  (b : Basis ι K L)

/--
The dual basis of a basis under the trace form in a finite separable extension.
-/
/-
**Module.Basis.traceDual** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual : Basis ι K L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate

--- 原说明 ---
The dual basis of a basis under the trace form in a finite separable extension.
-/
noncomputable def Module.Basis.traceDual :
    Basis ι K L :=
  (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
/-
**Module.Basis.traceDual_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_def : b.traceDual = (traceForm K L).dualBasis (trac
eForm_nondegenerate K L) b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Module.Basis.traceDual_def :
    b.traceDual = (traceForm K L).dualBasis (traceForm_nondegenerate K L) b := rfl

@[simp]
/-
**Module.Basis.traceDual_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_repr_apply (x : L) (i : ι) : (b.traceDual).repr x i
 = (traceForm K L x) (b i)
参数：x : L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.dualBasis_repr_apply`：dualBasis_repr_apply (hB : B.N
ondegenerate) (b : Basis ι K V) (x i) : (B.dualBasis hB b).repr x i = B x (b i)
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
-/
theorem Module.Basis.traceDual_repr_apply (x : L) (i : ι) :
    (b.traceDual).repr x i = (traceForm K L x) (b i) :=
  (traceForm K L).dualBasis_repr_apply _ b _ i

@[simp]
/-
**Module.Basis.trace_traceDual_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.trace_traceDual_mul (i j : ι) : trace K L ((b.traceDual i) * 
(b j)) = if j = i then 1 else 0
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.apply_dualBasis_left`：apply_dualBasis_left (hB : B.N
ondegenerate) (b : Basis ι K V) (i j) : B (B.dualBasis hB b i) (b j) = if j = i 
then 1 else 0
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
-/
theorem Module.Basis.trace_traceDual_mul (i j : ι) :
    trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (traceForm K L).apply_dualBasis_left _ _ i j

@[simp]
/-
**Module.Basis.trace_mul_traceDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.trace_mul_traceDual (i j : ι) : trace K L ((b i) * (b.traceDu
al j)) = if i = j then 1 else 0
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.apply_dualBasis_right`：apply_dualBasis_right (hB : B
.Nondegenerate) (sym : B.IsSymm) (b : Basis ι K V) (i j) : B (b i) (B.dualBasis 
hB b j) = if i = j then 1 else …
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `Algebra.traceForm_isSymm`：traceForm_isSymm : (traceForm R S).IsSymm
-/
theorem Module.Basis.trace_mul_traceDual (i j : ι) :
    trace K L ((b i) * (b.traceDual j)) = if i = j then 1 else 0 :=
  (traceForm K L).apply_dualBasis_right _ (traceForm_isSymm K) _ i j

@[simp]
/-
**Module.Basis.traceDual_traceDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_traceDual : b.traceDual.traceDual = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.dualBasis_dualBasis`：dualBasis_dualBasis (hB : B.Non
degenerate) (hB' : B.IsSymm) (b : Basis ι K V) : B.dualBasis hB (B.dualBasis hB 
b) = b
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `Algebra.traceForm_isSymm`：traceForm_isSymm : (traceForm R S).IsSymm
-/
theorem Module.Basis.traceDual_traceDual :
    b.traceDual.traceDual = b :=
  (traceForm K L).dualBasis_dualBasis _ (traceForm_isSymm K) _

variable (K L)
/-
**Module.Basis.traceDual_involutive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_involutive : Function.Involutive (Basis.traceDual :
 Basis ι K L -> Basis ι K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.dualBasis_involutive`：dualBasis_involutive (hB : B.N
ondegenerate) (hB' : B.IsSymm) : Function.Involutive (B.dualBasis hB : Basis ι K
 V -> Basis ι K V)
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `Algebra.traceForm_isSymm`：traceForm_isSymm : (traceForm R S).IsSymm
-/
theorem Module.Basis.traceDual_involutive :
    Function.Involutive (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceForm K L).dualBasis_involutive _ (traceForm_isSymm K)
/-
**Module.Basis.traceDual_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_injective : Function.Injective (Basis.traceDual : B
asis ι K L -> Basis ι K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.dualBasis_injective`：dualBasis_injective (hB : B.Non
degenerate) (hB' : B.IsSymm) : Function.Injective (B.dualBasis hB : Basis ι K V 
-> Basis ι K V)
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `Algebra.traceForm_isSymm`：traceForm_isSymm : (traceForm R S).IsSymm
-/
theorem Module.Basis.traceDual_injective :
    Function.Injective (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceForm K L).dualBasis_injective _ (traceForm_isSymm K)

variable {K L b}

@[simp]
/-
**Module.Basis.traceDual_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_inj {b' : Basis ι K L} : b.traceDual = b'.traceDual
 ↔ b = b'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Module.Basis.traceDual_injective`：Module.Basis.traceDual_injective : Fun
ction.Injective (Basis.traceDual : Basis ι K L -> Basis ι K L)
-/
theorem Module.Basis.traceDual_inj {b' : Basis ι K L} :
    b.traceDual = b'.traceDual ↔ b = b' :=
  (traceDual_injective K L).eq_iff

/--
A family of vectors `v` is the dual for the trace of the basis `b` if and only if
`∀ i j, Tr(v i * b j) = δ_ij`.
-/
@[simp]
/-
**Module.Basis.traceDual_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_eq_iff {v : ι -> L} : b.traceDual = v ↔ forall i j,
 traceForm K L (v i) (b j) = if j = i then 1 else 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.dualBasis_eq_iff`：dualBasis_eq_iff (hB : B.Nondegene
rate) (b : Basis ι K V) (v : ι -> V) : B.dualBasis hB b = v ↔ forall i j, B (v i
) (b j) = if j = i then 1 …
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate

--- 原说明 ---
A family of vectors `v` is the dual for the trace of the basis `b` if and only i
f
`∀ i j, Tr(v i * b j) = δ_ij`.
-/
theorem Module.Basis.traceDual_eq_iff {v : ι → L} :
    b.traceDual = v ↔ ∀ i j, traceForm K L (v i) (b j) = if j = i then 1 else 0 :=
  (traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

/--
The dual basis of a powerbasis `{1, x, x²...}` under the trace form is `aᵢ / f'(x)`,
with `f` being the minimal polynomial of `x` and `f / (X - x) = ∑ aᵢxⁱ`.
-/
/-
**Module.Basis.traceDual_powerBasis_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Basis.traceDual_powerBasis_eq (pb : PowerBasis K L) (i) : pb.basis.
traceDual i = (minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative <| minpol
y K pb.gen)
参数：pb : PowerBasis K L；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Module.Basis.traceDual_eq_iff`：Module.Basis.traceDual_eq_iff {v : ι -> L
} : b.traceDual = v ↔ forall i j, traceForm K L (v i) (b j) = if j = i then 1 el
se 0
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `sum_smul_minpolyDiv_eq_X_pow`：sum_smul_minpolyDiv_eq_X_pow (E) [Field E]
 [Algebra K E] [IsAlgClosed E] [FiniteDimensional K L] [Algebra.IsSeparable K L]
 {x : L} (hxL : K[…
· 使用定理 `PowerBasis.adjoin_gen_eq_top`：adjoin_gen_eq_top (B : PowerBasis R S) : a
djoin R ({B.gen} : Set S) = ⊤
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `MonoidWithZeroHom.map_ite_one_zero`：map_ite_one_zero {F : Type*} [FunLik
e F α β] [MonoidWithZeroHomClass F α β] (f : F) (p : Prop) [Decidable p] : f (it
e p 1 0) = ite p 1 0
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_smul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p 
: Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (r : R),   Polynomial.map f 
(r • p) =…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The dual basis of a powerbasis `{1, x, x²...}` under the trace form is `aᵢ / f'(
x)`,
with `f` being the minimal polynomial of `x` and `f / (X - x) = ∑ aᵢxⁱ`.
-/
lemma Module.Basis.traceDual_powerBasis_eq (pb : PowerBasis K L) (i) :
    pb.basis.traceDual i =
      (minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative <| minpoly K pb.gen) := by
  revert i
  rw [← funext_iff, Basis.traceDual_eq_iff]
  intro i j
  apply (algebraMap K (AlgebraicClosure K)).injective
  have := congr_arg (coeff · i) (sum_smul_minpolyDiv_eq_X_pow (AlgebraicClosure K)
    pb.adjoin_gen_eq_top (r := j) (pb.finrank.symm ▸ j.prop))
  simp only [Polynomial.map_smul, map_div₀, map_pow, RingHom.coe_coe, finsetSum_coeff, coeff_smul,
    coeff_map, smul_eq_mul, coeff_X_pow, ← Fin.ext_iff, @eq_comm _ i] at this
  rw [PowerBasis.coe_basis]
  simp only [traceForm_apply, MonoidWithZeroHom.map_ite_one_zero]
  rw [← this, trace_eq_sum_embeddings (E := AlgebraicClosure K)]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [map_mul, map_div₀, map_pow]
  ring

end Basis

