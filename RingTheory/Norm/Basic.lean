/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `Algebra.trace`, which is defined similarly as the trace of
`Algebra.leftMulMatrix`.

## References

* https://en.wikipedia.org/wiki/Field_norm

-/

public section


universe u v w

variable {R S T : Type*} [CommRing R] [Ring S]
variable [Algebra R S]
variable {K L F : Type*} [Field K] [Field L] [Field F]
variable [Algebra K L] [Algebra K F]
variable {ι : Type w}

open Module

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

section EqProdRoots

/-- Given `pb : PowerBasis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
/-
**Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.PowerBasis`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : Ring S] [ins
t_2 : Algebra R S] (pb : PowerBasis R S),   (Algebra.norm R) pb.gen = (-1) ^ pb.
dim * (minpoly R pb.gen).coeff 0
参数：pb : PowerBasis R S；Algebra.norm R；-1；minpoly R pb.gen。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
· 使用定理 `Matrix.det_eq_sign_charpoly_coeff`：det_eq_sign_charpoly_coeff (M : Matri
x n n R) : M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0
· 使用定理 `charpoly_leftMulMatrix`：charpoly_leftMulMatrix {S : Type*} [Ring S] [Alg
ebra R S] (h : PowerBasis R S) : (leftMulMatrix h.basis h.gen).charpoly = minpol
y R h.gen
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n

--- 原说明 ---
Given `pb : PowerBasis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`.
-/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb : PowerBasis R S) :
    norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_leftMulMatrix,
    Fintype.card_fin]

/-- Given `pb : PowerBasis R S`, then the norm of `pb.gen` is
`((minpoly R pb.gen).aroots F).prod`. -/
/-
**Algebra.PowerBasis.norm_gen_eq_prod_roots** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.P
owerBasis`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : Ring S] [ins
t_2 : Algebra R S] {F : Type u_6}   [inst_3 : Field F] [inst_4 : Algebra R F] (p
b : PowerBasis R S),   (Polynomial.map (algebraMap R F) (minpoly R pb.gen)).Spli
ts →     (algebraMap R F) ((Algebra.norm R) pb.gen) = ((minpoly R pb.gen).aroots
 F).prod
参数：pb : PowerBasis R S；Polynomial.map (algebraMap R F) (minpoly R pb.gen)；algebr
aMap R F；(Algebra.norm R) pb.gen；(minpoly R pb.gen).aroots F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `PowerBasis.isIntegral_gen`：isIntegral_gen (pb : PowerBasis A S) : IsInte
gral A pb.gen
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`：∀ {R : Type u_1} {S :
 Type u_2} [inst : CommRing R] [inst_1 : Ring S] [inst_2 : Algebra R S] (pb : Po
werBasis R S),   (Algebra.norm R) pb.ge…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.natDegree_minpoly`：natDegree_minpoly [Nontrivial A] (pb : Pow
erBasis A S) : (minpoly A pb.gen).natDegree = pb.dim
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic`：∀ {R : Type u_1} [i
nst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic
 → f.coeff 0 = (-1) ^ f.natDegree * f.roo…
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Given `pb : PowerBasis R S`, then the norm of `pb.gen` is
`((minpoly R pb.gen).aroots F).prod`.
-/
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra R F] (pb : PowerBasis R S)
    (hf : ((minpoly R pb.gen).map (algebraMap R F)).Splits) :
    algebraMap R F (norm R pb.gen) = ((minpoly R pb.gen).aroots F).prod := by
  have := Module.nontrivial R F
  have := minpoly.monic pb.isIntegral_gen
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly, ← pb.natDegree_minpoly, map_mul,
    ← coeff_map,
    hf.coeff_zero_eq_prod_roots_of_monic (this.map _),
    this.natDegree_map, map_pow, ← mul_assoc, ← mul_pow]
  simp only [map_neg, map_one, neg_mul, neg_neg, one_pow, one_mul]

end EqProdRoots

section EqZeroIff

variable [Finite ι]

@[simp]
/-
**Algebra.norm_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_zero [Nontrivial S] [Module.Free R S] [Module.Finite R S] : norm R (0
 : S) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.coe_lmul_eq_mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   ⇑(Algebra.lmul R A) = ⇑
(LinearMap.mu…
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
· 使用定理 `LinearMap.det_zero'`：det_zero' {ι : Type*} [Finite ι] [Nonempty ι] (b : 
Basis ι A M) : LinearMap.det (0 : M ->ₗ[A] M) = 0
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
-/
theorem norm_zero [Nontrivial S] [Module.Free R S] [Module.Finite R S] : norm R (0 : S) = 0 := by
  nontriviality
  rw [norm_apply, coe_lmul_eq_mul, map_zero, LinearMap.det_zero' (Module.Free.chooseBasis R S)]

@[simp]
/-
**Algebra.norm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finit
e R S] {x : S} : norm R x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.exists_mulVec_eq_zero_iff`：exists_mulVec_eq_zero_iff [DecidableEq
 n] : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Algebra.leftMulMatrix_mulVec_repr`：leftMulMatrix_mulVec_repr (x y : S) :
 leftMulMatrix b x *ᵥ b.repr y = b.repr (x * y)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.equivFun_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Algebra.norm_zero`：norm_zero [Nontrivial S] [Module.Free R S] [Module.Fi
nite R S] : norm R (0 : S) = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem norm_eq_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x = 0 ↔ x = 0 := by
  constructor
  swap
  · rintro rfl; exact norm_zero
  · let b := Module.Free.chooseBasis R S
    let decEq := Classical.decEq (Module.Free.ChooseBasisIndex R S)
    rw [norm_eq_matrix_det b, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equivFun.apply_symm_apply v, b.equivFun_symm_apply, b.equivFun_apply,
      leftMulMatrix_mulVec_repr] at hv
    refine (mul_eq_zero.mp (b.ext_elem fun i => ?_)).resolve_right (show ∑ i, v i • b i ≠ 0 from ?_)
    · simpa only [map_zero, Pi.zero_apply] using! congr_fun hv i
    · contrapose v_ne with sum_eq
      apply b.equivFun.symm.injective
      rw [b.equivFun_symm_apply, sum_eq, map_zero]
/-
**Algebra.norm_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_ne_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finit
e R S] {x : S} : norm R x != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Algebra.norm_eq_zero_iff`：norm_eq_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x = 0 ↔ x = 0
-/
theorem norm_ne_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x ≠ 0 ↔ x ≠ 0 := not_iff_not.mpr norm_eq_zero_iff

/-- This is `Algebra.norm_eq_zero_iff` composed with `Algebra.norm_apply`. -/
@[simp]
/-
**Algebra.norm_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_zero_iff' [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Fini
te R S] {x : S} : LinearMap.det (LinearMap.mul R S x) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.norm_eq_zero_iff`：norm_eq_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x = 0 ↔ x = 0

--- 原说明 ---
This is `Algebra.norm_eq_zero_iff` composed with `Algebra.norm_apply`.
-/
theorem norm_eq_zero_iff' [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    LinearMap.det (LinearMap.mul R S x) = 0 ↔ x = 0 := norm_eq_zero_iff
/-
**Algebra.norm_eq_zero_iff_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x :
 S} : Algebra.norm R x = 0 ↔ x = 0
参数：b : Basis ι R S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Algebra.norm_eq_zero_iff`：norm_eq_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x = 0 ↔ x = 0
-/
theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x = 0 ↔ x = 0 := by
  have : Module.Free R S := Module.Free.of_basis b
  have : Module.Finite R S := Module.Finite.of_basis b
  exact norm_eq_zero_iff
/-
**Algebra.norm_ne_zero_iff_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x :
 S} : Algebra.norm R x != 0 ↔ x != 0
参数：b : Basis ι R S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Algebra.norm_eq_zero_iff_of_basis`：norm_eq_zero_iff_of_basis [IsDomain R
] [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x = 0 ↔ x = 0
-/
theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr (norm_eq_zero_iff_of_basis b)

end EqZeroIff

section DivisionRing

variable {L : Type*} [DivisionRing L] [Algebra K L] [Module.Finite K L]

/-
**Algebra.norm_inv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_inv (x : L) : Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Algebra.norm_zero`：norm_zero [Nontrivial S] [Module.Free R S] [Module.Fi
nite R S] : norm R (0 : S) = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.norm_ne_zero_iff`：norm_ne_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x != 0 ↔ x != 0
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem norm_inv (x : L) : Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  exact mul_left_injective₀ (norm_ne_zero_iff.mpr hx) (by simp [hx, ← map_mul])
/-
**Algebra.norm_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_zpow (x : L) (n : Int) : Algebra.norm K (x ^ n) = Algebra.norm K x ^ 
n
参数：x : L；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow'`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : DivInvMonoid G]   [inst_2 : DivInvMonoid H] [MonoidHomClass …
· 使用定理 `Algebra.norm_inv`：norm_inv (x : L) : Algebra.norm K x⁻¹ = (Algebra.norm 
K x)⁻¹
-/
theorem norm_zpow (x : L) (n : ℤ) : Algebra.norm K (x ^ n) = Algebra.norm K x ^ n :=
  map_zpow' _ norm_inv _ _

end DivisionRing

open IntermediateField

section IntermediateField

/-
**Algebra._root_.IntermediateField.AdjoinSimple.norm_gen_eq_one** 是 Mathlib 中的一个
定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_one {x : L} (hx : ¬IsIntegral K x) :
    norm K (AdjoinSimple.gen K x) = 1 := by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)
/-
**Algebra._root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots** 是 Mathl
ib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots (x : L)
    (hf : ((minpoly K x).map (algebraMap K F)).Splits) :
    (algebraMap K F) (norm K (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).prod := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, IntermediateField.AdjoinSimple.norm_gen_eq_one hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx, PowerBasis.norm_gen_eq_prod_roots] <;>
    rw [adjoin.powerBasis_gen hx, ← minpoly.algebraMap_eq injKxL] <;>
    simp only [AdjoinSimple.algebraMap_gen _ _, hf]

end IntermediateField

section EqProdEmbeddings

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable (F) (E : Type*) [Field E] [Algebra K E]

/-
**Algebra.norm_eq_prod_embeddings_gen** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_prod_embeddings_gen [Algebra R F] (pb : PowerBasis R S) (hE : ((mi
npoly R pb.gen).map (algebraMap R F)).Splits) (hfx : IsSeparable R pb.gen) : alg
ebraMap R F (norm R pb.gen) = (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).pr
od fun σ => σ pb.gen
参数：pb : PowerBasis R S；hE : ((minpoly R pb.gen).map (algebraMap R F)).Splits；hfx
 : IsSeparable R pb.gen。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.PowerBasis.norm_gen_eq_prod_roots`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : Ring S] [inst_2 : Algebra R S] {F : Type u_6}  
 [inst_3 : Field F] [inst_4 : A…
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerBasis.liftEquiv'_apply_coe`：∀ {S : Type u_2} [inst : Ring S] {A : T
ype u_4} {B : Type u_5} [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 : 
Algebra A B] [inst_4 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_mem_multiset`：prod_mem_multiset [DecidableEq ι] (m : Multise
t ι) (f : { x // x in m } -> M) (g : ι -> M) (hfg : forall x, f x = g x) : ∏ x :
 { x // x in m…
· 使用定理 `Finset.prod_eq_multiset_prod`：prod_eq_multiset_prod [CommMonoid M] (s : 
Finset ι) (f : ι -> M) : ∏ x in s, f x = (s.1.map f).prod
· 使用定理 `Multiset.toFinset_val`：toFinset_val (s : Multiset α) : s.toFinset.1 = s.
dedup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
-/
theorem norm_eq_prod_embeddings_gen [Algebra R F] (pb : PowerBasis R S)
    (hE : ((minpoly R pb.gen).map (algebraMap R F)).Splits) (hfx : IsSeparable R pb.gen) :
    algebraMap R F (norm R pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod fun σ => σ pb.gen := by
  let := Classical.decEq F
  rw [PowerBasis.norm_gen_eq_prod_roots pb hE]
  rw [@Fintype.prod_equiv (S →ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'
    (fun σ => σ pb.gen) (fun x => x) ?_]
  · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr, Multiset.map_id]
    · exact nodup_roots (.map hfx)
    · intro x; rfl
  · intro σ; simp only [PowerBasis.liftEquiv'_apply_coe]
/-
**Algebra.prod_embeddings_eq_finrank_pow** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgC
losed E] [Algebra.IsSeparable K F] [FiniteDimensional K F] (pb : PowerBasis K L)
 : ∏ σ : F ->ₐ[K] E, σ (algebraMap L F pb.gen) = ((@Finset.univ _ (PowerBasis.Al
gHom.fintype pb)).prod fun σ : L ->ₐ[K] E => σ pb.gen) ^ finrank L F
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
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sigma_univ`：∀ {ι : Type u_1} {κ : ι → Type u_3} [inst : (i :
 ι) → Fintype (κ i)] [inst_1 : Fintype ι],   (Finset.univ.sigma fun x => Finset.
univ) = Fins…
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `AlgHom.card`：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra 
F K] : Fintype.card (E ->ₐ[F] K) = finrank F E
-/
theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E]
    [Algebra.IsSeparable K F] [FiniteDimensional K F] (pb : PowerBasis K L) :
    ∏ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      ((@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod
        fun σ : L →ₐ[K] E => σ pb.gen) ^ finrank L F := by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen,
    ← Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
  · refine Finset.prod_congr rfl fun σ _ => ?_
    let : Algebra L E := σ.toRingHom.toAlgebra
    simp_rw [Finset.prod_const]
    congr
    exact AlgHom.card L F E
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.domRestrict, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
/-
**Algebra.norm_eq_of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_of_algEquiv [Ring T] [Algebra R T] (e : S ≃ₐ[R] T) (x) : Algebra.n
orm R (e x) = Algebra.norm R x
参数：e : S ≃ₐ[R] T；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_conj`：det_conj {N : Type*} [AddCommGroup N] [Module A N] (
f : M ->ₗ[A] M) (e : M ≃ₗ[A] N) : LinearMap.det ((e : M ->ₗ[A] N) ∘ₗ f ∘ₗ (e.sym
m : N ->…
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
lemma norm_eq_of_algEquiv [Ring T] [Algebra R T] (e : S ≃ₐ[R] T) (x) :
    Algebra.norm R (e x) = Algebra.norm R x := by
  simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ e.toLinearEquiv]; congr; ext; simp

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.norm_eq_of_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [Ring C] [A
lgebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraM
ap A C) (x : C) : e (Algebra.norm A x) = Algebra.norm B x
参数：e : A ≃+* B；he : (algebraMap B C).comp e = algebraMap A C；x : C。
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
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
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
· 使用定理 `RingEquiv.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fin
type n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] 
(f : R …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingEquiv.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_
12} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] 
[inst_3 : NonAs…
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
（共 38 条，此处仅展示前 30 条）
-/
lemma norm_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [Ring C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C)
    (x : C) :
    e (Algebra.norm A x) = Algebra.norm B x := by
  classical
  by_cases h : ∃ s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.norm_eq_matrix_det b,
      Algebra.norm_eq_matrix_det (b.mapCoeffs e.symm (by simp [Algebra.smul_def, ← he])),
      e.map_det]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [norm_eq_one_of_not_exists_basis _ h, norm_eq_one_of_not_exists_basis, map_one]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩
/-
**Algebra.norm_eq_of_equiv_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [Ring B₁] [Comm
Ring A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+*
 B₂) (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁
 B₁)) (x) : Algebra.norm A₁ x = e₁.symm (Algebra.norm A₂ (e₂ x))
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
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.norm_eq_of_ringEquiv`：norm_eq_of_ringEquiv {A B C : Type*} [Comm
Ring A] [CommRing B] [Ring C] [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (a
lgebraMap B C).com…
· 使用引理 `Algebra.norm_eq_of_algEquiv`：norm_eq_of_algEquiv [Ring T] [Algebra R T] 
(e : S ≃ₐ[R] T) (x) : Algebra.norm R (e x) = Algebra.norm R x
-/
lemma norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [Ring B₁]
    [CommRing A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.norm A₁ x = e₁.symm (Algebra.norm A₂ (e₂ x)) := by
  let := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra' ?_
  · let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
    rw [← Algebra.norm_eq_of_ringEquiv e₁ he, ← Algebra.norm_eq_of_algEquiv e']
    simp [e']
  intro c x
  apply e₂.symm.injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_mul,
    RingEquiv.symm_apply_apply, commutes]

end EqProdEmbeddings

end Algebra

