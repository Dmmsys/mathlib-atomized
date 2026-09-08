/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Wedderburn–Artin Theorem over an algebraically closed field
-/

public section

variable (F R : Type*) [Field F] [IsAlgClosed F] [Ring R] [Algebra F R]

/-- The **Wedderburn–Artin Theorem** over algebraically closed fields: a finite-dimensional
simple algebra over an algebraically closed field is isomorphic to a matrix algebra over the field.
-/
/-
**IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed [IsSimpleRing R] [Finit
eDimensional F R] : exists (n : Nat) (_ : NeZero n), Nonempty (R ≃ₐ[F] Matrix (F
in n) (Fin n) F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.of_finite`：IsArtinianRing.of_finite (R S) [Ring R] [Ring 
S] [Module R S] [IsScalarTower R S S] [IsArtinianRing R] [Module.Finite R S] : I
sArtinianRing …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`：exists_algEquiv
_matrix_divisionRing_finite [Module.Finite R₀ R] : exists (n : Nat) (_ : NeZero 
n) (D : Type u) (_ : DivisionRing D) (_ : Alg…
· 使用定理 `IsAlgClosed.algebraMap_bijective_of_isIntegral`：algebraMap_bijective_of_
isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K] [hk : IsAlgClosed k] [A
lgebra k K] [Algebra.IsIntegral k K]…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
The **Wedderburn–Artin Theorem** over algebraically closed fields: a finite-dime
nsional
simple algebra over an algebraically closed field is isomorphic to a matrix alge
bra over the field.
-/
theorem IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    [IsSimpleRing R] [FiniteDimensional F R] :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (R ≃ₐ[F] Matrix (Fin n) (Fin n) F) :=
  have := IsArtinianRing.of_finite F R
  have ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := exists_algEquiv_matrix_divisionRing_finite F R
  ⟨n, hn, ⟨e.trans <| .mapMatrix <| .symm <| .ofBijective (Algebra.ofId F D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

/-- The **Wedderburn–Artin Theorem** over algebraically closed fields: a finite-dimensional
semisimple algebra over an algebraically closed field is isomorphic to a product of matrix algebras
over the field. -/
/-
**IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed [IsSemisimpleRin
g R] [FiniteDimensional F R] : exists (n : Nat) (d : Fin n -> Nat), (forall i, N
eZero (d i)) ∧ Nonempty (R ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`：exists_a
lgEquiv_pi_matrix_divisionRing_finite [Module.Finite R₀ R] : exists (n : Nat) (D
 : Fin n -> Type u) (d : Fin n -> Nat) (_ : forall i…
· 使用定理 `IsAlgClosed.algebraMap_bijective_of_isIntegral`：algebraMap_bijective_of_
isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K] [hk : IsAlgClosed k] [A
lgebra k K] [Algebra.IsIntegral k K]…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
The **Wedderburn–Artin Theorem** over algebraically closed fields: a finite-dime
nsional
semisimple algebra over an algebraically closed field is isomorphic to a product
 of matrix algebras
over the field.
-/
theorem IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    [IsSemisimpleRing R] [FiniteDimensional F R] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F) :=
  have ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing_finite F R
  ⟨n, d, hd, ⟨e.trans <| .piCongrRight fun i ↦ .mapMatrix <| .symm <| .ofBijective
    (Algebra.ofId F (D i)) IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩
