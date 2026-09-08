/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Wedderburn–Artin Theorem

## Main results

* `IsSimpleRing.tfae`: a simple ring is semisimple iff it is Artinian,
  iff it has a minimal left ideal.

* `isSimpleRing_isArtinianRing_iff`: a ring is simple Artinian iff it is semisimple, isotypic,
  and nontrivial.

* `IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite`: a simple Artinian algebra is
  isomorphic to a (finite-dimensional) matrix algebra over a division algebra. The division
  algebra is the opposite of the endomorphism algebra of a simple (i.e., minimal) left ideal.

* `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`: a semisimple algebra is
  isomorphic to a finite direct product of matrix algebras over division algebras. The division
  algebras are the opposites of the endomorphism algebras of the simple (i.e., minimal)
  left ideals.

* `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`:
  if the simple Artinian / semisimple algebra is finite as a module over a base ring, then the
  division algebra(s) are also finite over the same ring.
  If the base ring is an algebraically closed field, the only finite-dimensional division algebra
  over it is itself, and we obtain `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` and
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` (in a later file).

-/

public section

universe u
variable (R₀ : Type*) {R : Type u} [CommSemiring R₀] [Ring R] [Algebra R₀ R]

/-- A simple ring is semisimple iff it is Artinian, iff it has a minimal left ideal. -/
/-
**IsSimpleRing.tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimpleRing.tfae [IsSimpleRing R] : List.TFAE [IsSemisimpleRing R, IsArti
nianRing R, exists I : Ideal R, IsAtom I]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用引理 `IsAtomic.exists_atom`：IsAtomic.exists_atom [OrderBot α] [Nontrivial α] [
IsAtomic α] : exists a : α, IsAtom a
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsSimpleRing.instNontrivial`：∀ {R : Type u_1} [inst : NonUnitalNonAssocR
ing R] [IsSimpleRing R], Nontrivial R
· 使用定理 `instIsStronglyAtomicOfWellFoundedLT`：∀ {α : Type u_2} [inst : PartialOrd
er α] [WellFoundedLT α], IsStronglyAtomic α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleRing_iff_isTwoSided_imp`：isSimpleRing_iff_isTwoSided_imp {R : Ty
pe*} [Ring R] : IsSimpleRing R ↔ Nontrivial R ∧ forall I : Ideal R, I.IsTwoSided
 -> I = ⊥ ∨ I = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isSimpleModule_iff_isAtom`：isSimpleModule_iff_isAtom : IsSimpleModule R 
m ↔ IsAtom m
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.IsFullyInvariant.isotypicComponent`：∀ (R : Type u_2) (M : Type
 u) (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGr
oup S]   [inst_3 : _root_.Module R…
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `IsAtom.bot_lt`：IsAtom.bot_lt (h : IsAtom a) : ⊥ < a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `IsSemisimpleModule.congr`：congr (e : N ≃ₗ[R] M) : IsSemisimpleModule R N
 where __
· 使用定理 `instIsSemisimpleModuleSubtypeMemSubmoduleIsotypicComponent`：∀ {R : Type 
u_2} {M : Type u} (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst
_2 : AddCommGroup S]   [inst_3 : _root_.Module R…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
A simple ring is semisimple iff it is Artinian, iff it has a minimal left ideal.
-/
theorem IsSimpleRing.tfae [IsSimpleRing R] : List.TFAE
    [IsSemisimpleRing R, IsArtinianRing R, ∃ I : Ideal R, IsAtom I] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ IsAtomic.exists_atom _
  tfae_have 3 → 1 := fun ⟨I, hI⟩ ↦ by
    have ⟨_, h⟩ := isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing R›
    simp_rw [← isFullyInvariant_iff_isTwoSided] at h
    have := isSimpleModule_iff_isAtom.mpr hI
    obtain eq | eq := h _ (.isotypicComponent R R I)
    · exact (hI.bot_lt.not_ge <| (le_sSup <| by exact ⟨.refl ..⟩).trans_eq eq).elim
    exact .congr (.symm <| .trans (.ofEq _ _ eq) Submodule.topEquiv)
  tfae_finish
/-
**IsSimpleRing.isSemisimpleRing_iff_isArtinianRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimpleRing.isSemisimpleRing_iff_isArtinianRing [IsSimpleRing R] : IsSemi
simpleRing R ↔ IsArtinianRing R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsSimpleRing.tfae`：IsSimpleRing.tfae [IsSimpleRing R] : List.TFAE [IsSem
isimpleRing R, IsArtinianRing R, exists I : Ideal R, IsAtom I]
-/
theorem IsSimpleRing.isSemisimpleRing_iff_isArtinianRing [IsSimpleRing R] :
    IsSemisimpleRing R ↔ IsArtinianRing R := tfae.out 0 1
/-
**isSimpleRing_isArtinianRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimpleRing_isArtinianRing_iff : IsSimpleRing R ∧ IsArtinianRing R ↔ IsSe
misimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSimpleRing.isSemisimpleRing_iff_isArtinianRing`：IsSimpleRing.isSemisim
pleRing_iff_isArtinianRing [IsSimpleRing R] : IsSemisimpleRing R ↔ IsArtinianRin
g R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
-/
theorem isSimpleRing_isArtinianRing_iff :
    IsSimpleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨_, _, _⟩ ↦ ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top,
      isFullyInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rwa [and_comm]⟩
  · exact ⟨⟨‹_›, ‹_›⟩, inferInstance⟩

namespace IsSimpleRing

variable (R) [IsSimpleRing R] [IsArtinianRing R]

/-
**IsSimpleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : IsSemisimpleRing R :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).1
/-
**IsSimpleRing.isIsotypic** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleRing`。
形式化陈述：isIsotypic (M) [AddCommGroup M] [Module R M] : IsIsotypic R M
参数：M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypic.of_self`：IsIsotypic.of_self [IsSemisimpleRing R] (h : IsIsoty
pic R R) : IsIsotypic R M
· 使用定理 `IsSimpleRing.instIsSemisimpleRing`：∀ (R : Type u) [inst : Ring R] [IsSim
pleRing R] [IsArtinianRing R], IsSemisimpleRing R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleRing_isArtinianRing_iff`：isSimpleRing_isArtinianRing_iff : IsSim
pleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial 
R
-/
theorem isIsotypic (M) [AddCommGroup M] [Module R M] : IsIsotypic R M :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).2.1.of_self M

/-- The **Wedderburn–Artin Theorem**: an Artinian simple ring is isomorphic to a matrix
ring over the opposite of the endomorphism ring of its simple module. -/
/-
**IsSimpleRing.exists_ringEquiv_matrix_end_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间
 `IsSimpleRing`。
形式化陈述：exists_ringEquiv_matrix_end_mulOpposite : exists (n : Nat) (_ : NeZero n) 
(I : Ideal R) (_ : IsSimpleModule R I), Nonempty (R ≃+* Matrix (Fin n) (Fin n) (
Module.End R I)ᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypic.linearEquiv_fun`：IsIsotypic.linearEquiv_fun [Module.Finite R 
M] [Nontrivial M] (h : IsIsotypic R M) : exists (n : Nat) (_ : NeZero n) (S : Su
bmodule R M), Is…
· 使用定理 `IsSimpleRing.instIsSemisimpleRing`：∀ (R : Type u) [inst : Ring R] [IsSim
pleRing R] [IsArtinianRing R], IsSemisimpleRing R
· 使用定理 `IsSimpleRing.instNontrivial`：∀ {R : Type u_1} [inst : NonUnitalNonAssocR
ing R] [IsSimpleRing R], Nontrivial R
· 使用定理 `IsSimpleRing.isIsotypic`：isIsotypic (M) [AddCommGroup M] [Module R M] : 
IsIsotypic R M

--- 原说明 ---
The **Wedderburn–Artin Theorem**: an Artinian simple ring is isomorphic to a mat
rix
ring over the opposite of the endomorphism ring of its simple module.
-/
theorem exists_ringEquiv_matrix_end_mulOpposite :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
  refine ⟨n, hn, S, hS, ⟨.trans (.opOp R) <| .trans (.op ?_) (.symm .mopMatrix)⟩⟩
  exact .trans (.moduleEndSelf R) <| .trans e.conjRingEquiv (endVecRingEquivMatrixEnd ..)

/-- The **Wedderburn–Artin Theorem**: an Artinian simple ring is isomorphic to a matrix
ring over a division ring. -/
/-
**IsSimpleRing.exists_ringEquiv_matrix_divisionRing** 是 Mathlib 中的一个定理，位于命名空间 `I
sSimpleRing`。
形式化陈述：exists_ringEquiv_matrix_divisionRing : exists (n : Nat) (_ : NeZero n) (D 
: Type u) (_ : DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleRing.exists_ringEquiv_matrix_end_mulOpposite`：exists_ringEquiv_m
atrix_end_mulOpposite : exists (n : Nat) (_ : NeZero n) (I : Ideal R) (_ : IsSim
pleModule R I), Nonempty (R ≃+* Matrix (Fi…

--- 原说明 ---
The **Wedderburn–Artin Theorem**: an Artinian simple ring is isomorphic to a mat
rix
ring over a division ring.
-/
theorem exists_ringEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_ringEquiv_matrix_end_mulOpposite R
  classical exact ⟨n, hn, _, _, ⟨e⟩⟩

/-- The **Wedderburn–Artin Theorem**, algebra form: an Artinian simple algebra is isomorphic
to a matrix algebra over the opposite of the endomorphism algebra of its simple module. -/
/-
**IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 
`IsSimpleRing`。
形式化陈述：exists_algEquiv_matrix_end_mulOpposite : exists (n : Nat) (_ : NeZero n) (
I : Ideal R) (_ : IsSimpleModule R I), Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n)
 (Module.End R I)ᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsIsotypic.linearEquiv_fun`：IsIsotypic.linearEquiv_fun [Module.Finite R 
M] [Nontrivial M] (h : IsIsotypic R M) : exists (n : Nat) (_ : NeZero n) (S : Su
bmodule R M), Is…
· 使用定理 `IsSimpleRing.instIsSemisimpleRing`：∀ (R : Type u) [inst : Ring R] [IsSim
pleRing R] [IsArtinianRing R], IsSemisimpleRing R
· 使用定理 `IsSimpleRing.instNontrivial`：∀ {R : Type u_1} [inst : NonUnitalNonAssocR
ing R] [IsSimpleRing R], Nontrivial R
· 使用定理 `IsSimpleRing.isIsotypic`：isIsotypic (M) [AddCommGroup M] [Module R M] : 
IsIsotypic R M

--- 原说明 ---
The **Wedderburn–Artin Theorem**, algebra form: an Artinian simple algebra is is
omorphic
to a matrix algebra over the opposite of the endomorphism algebra of its simple 
module.
-/
theorem exists_algEquiv_matrix_end_mulOpposite :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
  refine ⟨n, hn, S, hS, ⟨.trans (.opOp R₀ R) <| .trans (.op ?_) (.symm .mopMatrix)⟩⟩
  exact .trans (.moduleEndSelf R₀) <| .trans (e.conjAlgEquiv R₀) (endVecAlgEquivMatrixEnd ..)

/-- The **Wedderburn–Artin Theorem**, algebra form: an Artinian simple algebra is isomorphic
to a matrix algebra over a division algebra. -/
/-
**IsSimpleRing.exists_algEquiv_matrix_divisionRing** 是 Mathlib 中的一个定理，位于命名空间 `Is
SimpleRing`。
形式化陈述：exists_algEquiv_matrix_divisionRing : exists (n : Nat) (_ : NeZero n) (D :
 Type u) (_ : DivisionRing D) (_ : Algebra R₀ D), Nonempty (R ≃ₐ[R₀] Matrix (Fin
 n) (Fin n) D)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite`：exists_algEquiv_mat
rix_end_mulOpposite : exists (n : Nat) (_ : NeZero n) (I : Ideal R) (_ : IsSimpl
eModule R I), Nonempty (R ≃ₐ[R₀] Matrix (…

--- 原说明 ---
The **Wedderburn–Artin Theorem**, algebra form: an Artinian simple algebra is is
omorphic
to a matrix algebra over a division algebra.
-/
theorem exists_algEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, hn, _, _, _, ⟨e⟩⟩

/-- The **Wedderburn–Artin Theorem**, algebra form, finite case: a finite Artinian simple algebra is
isomorphic to a matrix algebra over a finite division algebra. -/
/-
**IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite** 是 Mathlib 中的一个定理，位于命
名空间 `IsSimpleRing`。
形式化陈述：exists_algEquiv_matrix_divisionRing_finite [Module.Finite R₀ R] : exists (
n : Nat) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D) (_ 
: Module.Finite R₀ D), Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite`：exists_algEquiv_mat
rix_end_mulOpposite : exists (n : Nat) (_ : NeZero n) (I : Ideal R) (_ : IsSimpl
eModule R I), Nonempty (R ≃ₐ[R₀] Matrix (…
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P

--- 原说明 ---
The **Wedderburn–Artin Theorem**, algebra form, finite case: a finite Artinian s
imple algebra is
isomorphic to a matrix algebra over a finite division algebra.
-/
theorem exists_algEquiv_matrix_divisionRing_finite [Module.Finite R₀ R] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D)
      (_ : Module.Finite R₀ D), Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  classical exact ⟨n, hn, _, _, _, .of_surjective
    (Matrix.entryLinearMap R₀ _ (0 : Fin n) (0 : Fin n)) fun f ↦ ⟨fun _ _ ↦ f, rfl⟩, ⟨e⟩⟩

end IsSimpleRing

namespace IsSemisimpleModule

open Module (End)

universe v
variable (R) (M : Type v) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
  [IsSemisimpleModule R M] [Module.Finite R M]

/-
**IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end** 是 Mathlib 中的一个定理，位于命名空间
 `IsSemisimpleModule`。
形式化陈述：exists_end_algEquiv_pi_matrix_end : exists (n : Nat) (S : Fin n -> Submodu
le R M) (d : Fin n -> Nat), (forall i, IsSimpleModule R (S i)) ∧ (forall i, NeZe
ro (d i)) ∧ Nonempty (End R M ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (End R 
(S i)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instFiniteElemSubmoduleIsotypicComponentsOfIsNoetherian`：∀ (R : Type u_2
) (M : Type u) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M] [IsNoetherian R M],   Finite ↑(isotypic…
· 使用定理 `IsSemisimpleModule.instIsNoetherianOfFinite`：∀ {R : Type u_2} [inst : Ri
ng R] {M : Type u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [I
sSemisimpleModule R M] [Module.Fi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `IsIsotypic.submodule_linearEquiv_fun`：IsIsotypic.submodule_linearEquiv_f
un {m : Submodule R M} [Module.Finite R m] [Nontrivial m] (h : IsIsotypic R m) :
 exists (n : Nat) (_ : NeZ…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `instNontrivialSubtypeMemSubmoduleValSetIsotypicComponents`：∀ {R : Type u
_2} {M : Type u} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Modu
le R M]   (c : ↑(isotypicComponents R M)), Nont…
· 使用定理 `IsIsotypic.isotypicComponents`：∀ {R : Type u_2} {M : Type u} [inst : Rin
g R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {m : Submodule R M
}, m ∈ isotypicComp…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem exists_end_algEquiv_pi_matrix_end :
    ∃ (n : ℕ) (S : Fin n → Submodule R M) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (End R M ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (End R (S i))) := by
  choose d pos S _ simple e using fun c : isotypicComponents R M ↦
    (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun
  exact ⟨_, _, _, fun _ ↦ simple _, fun _ ↦ pos _, ⟨.trans (endAlgEquiv R₀ R M) <| .trans
    (.piCongrRight fun c ↦ ((e c).some.conjAlgEquiv R₀).trans (endVecAlgEquivMatrixEnd ..)) <|
    (.piCongrLeft' R₀ _ (Finite.equivFin _))⟩⟩
/-
**IsSemisimpleModule.exists_end_ringEquiv_pi_matrix_end** 是 Mathlib 中的一个定理，位于命名空
间 `IsSemisimpleModule`。
形式化陈述：exists_end_ringEquiv_pi_matrix_end : exists (n : Nat) (S : Fin n -> Submod
ule R M) (d : Fin n -> Nat), (forall i, IsSimpleModule R (S i)) ∧ (forall i, NeZ
ero (d i)) ∧ Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (End R (S
 i)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end`：exists_end_algEqui
v_pi_matrix_end : exists (n : Nat) (S : Fin n -> Submodule R M) (d : Fin n -> Na
t), (forall i, IsSimpleModule R (S i)) ∧ (…
-/
theorem exists_end_ringEquiv_pi_matrix_end :
    ∃ (n : ℕ) (S : Fin n → Submodule R M) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (End R (S i))) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end ℕ R M; ⟨n, S, d, hS, hd, ⟨e⟩⟩

-- TODO: can also require D be in `Type u`, since every simple module is the quotient by an ideal.
/-
**IsSemisimpleModule.exists_end_algEquiv_pi_matrix_divisionRing** 是 Mathlib 中的一个
定理，位于命名空间 `IsSemisimpleModule`。
形式化陈述：exists_end_algEquiv_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n -
> Type v) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i)) (_ : forall i, A
lgebra R₀ (D i)), (forall i, NeZero (d i)) ∧ Nonempty (End R M ≃ₐ[R₀] Π i, Matri
x (Fin (d i)) (Fin (d i)) (D i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end`：exists_end_algEqui
v_pi_matrix_end : exists (n : Nat) (S : Fin n -> Submodule R M) (d : Fin n -> Na
t), (forall i, IsSimpleModule R (S i)) ∧ (…
-/
theorem exists_end_algEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type v) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra R₀ (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (End R M ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end R₀ R M
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩
/-
**IsSemisimpleModule.exists_end_ringEquiv_pi_matrix_divisionRing** 是 Mathlib 中的一
个定理，位于命名空间 `IsSemisimpleModule`。
形式化陈述：exists_end_ringEquiv_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n 
-> Type v) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i)), (forall i, NeZ
ero (d i)) ∧ Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsSemisimpleModule.exists_end_algEquiv_pi_matrix_divisionRing`：exists_en
d_algEquiv_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n -> Type v) (d : 
Fin n -> Nat) (_ : forall i, DivisionRing (D i)) (_…
-/
theorem exists_end_ringEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type v) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i)),
      (∀ i, NeZero (d i)) ∧ Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_divisionRing ℕ R M
  ⟨n, D, d, _, hd, ⟨e⟩⟩
/-
**IsSemisimpleModule._root_.IsSemisimpleRing.moduleEnd** 是 Mathlib 中的一个定理，位于命名空间
 `IsSemisimpleModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSemisimpleRing.moduleEnd : IsSemisimpleRing (Module.End R M) :=
  have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_end_ringEquiv_pi_matrix_divisionRing R M
  e.symm.isSemisimpleRing

end IsSemisimpleModule

namespace IsSemisimpleRing

variable (R) [IsSemisimpleRing R]

/-- The **Wedderburn–Artin Theorem**, algebra form: a semisimple algebra is isomorphic to a
product of matrix algebras over the opposite of the endomorphism algebras of its simple modules. -/
/-
**IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite** 是 Mathlib 中的一个定理，
位于命名空间 `IsSemisimpleRing`。
形式化陈述：exists_algEquiv_pi_matrix_end_mulOpposite : exists (n : Nat) (S : Fin n ->
 Ideal R) (d : Fin n -> Nat), (forall i, IsSimpleModule R (S i)) ∧ (forall i, Ne
Zero (d i)) ∧ Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End
 R (S i))ᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end`：exists_end_algEqui
v_pi_matrix_end : exists (n : Nat) (S : Fin n -> Submodule R M) (d : Fin n -> Na
t), (forall i, IsSimpleModule R (S i)) ∧ (…

--- 原说明 ---
The **Wedderburn–Artin Theorem**, algebra form: a semisimple algebra is isomorph
ic to a
product of matrix algebras over the opposite of the endomorphism algebras of its
 simple modules.
-/
theorem exists_algEquiv_pi_matrix_end_mulOpposite :
    ∃ (n : ℕ) (S : Fin n → Ideal R) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R (S i))ᵐᵒᵖ) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end R₀ R R
  ⟨n, S, d, hS, hd, ⟨.trans (.opOp R₀ R) <| .trans (.op <| .trans (.moduleEndSelf R₀) e) <|
    .trans (.piMulOpposite _ _) (.piCongrRight fun _ ↦ .symm .mopMatrix)⟩⟩

/-- The **Wedderburn–Artin Theorem**, algebra form: a semisimple algebra is isomorphic to a
product of matrix algebras over division algebras. -/
/-
**IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing** 是 Mathlib 中的一个定理，位于命
名空间 `IsSemisimpleRing`。
形式化陈述：exists_algEquiv_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n -> Ty
pe u) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i)) (_ : forall i, Algeb
ra R₀ (D i)), (forall i, NeZero (d i)) ∧ Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d 
i)) (Fin (d i)) (D i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`：exists_algEq
uiv_pi_matrix_end_mulOpposite : exists (n : Nat) (S : Fin n -> Ideal R) (d : Fin
 n -> Nat), (forall i, IsSimpleModule R (S i)) ∧…

--- 原说明 ---
The **Wedderburn–Artin Theorem**, algebra form: a semisimple algebra is isomorph
ic to a
product of matrix algebras over division algebras.
-/
theorem exists_algEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra R₀ (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The **Wedderburn–Artin Theorem**, algebra form, finite case: a finite semisimple algebra is
isomorphic to a product of matrix algebras over finite division algebras. -/
/-
**IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite** 是 Mathlib 中的一
个定理，位于命名空间 `IsSemisimpleRing`。
形式化陈述：exists_algEquiv_pi_matrix_divisionRing_finite [Module.Finite R₀ R] : exist
s (n : Nat) (D : Fin n -> Type u) (d : Fin n -> Nat) (_ : forall i, DivisionRing
 (D i)) (_ : forall i, Algebra R₀ (D i)) (_ : forall i, Module.Finite R₀ (D i)),
 (forall i, NeZero (d i)) ∧ Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i
)) (D i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing`：exists_algEquiv
_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n -> Type u) (d : Fin n -> N
at) (_ : forall i, DivisionRing (D i)) (_ : f…
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Matrix.entryLinearMap_apply`：∀ {m : Type u_2} {n : Type u_3} (R : Type u
_7) (α : Type u_11) [inst : Semiring R] [inst_1 : AddCommMonoid α]   [inst_2 : _
root_.Module R α]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The **Wedderburn–Artin Theorem**, algebra form, finite case: a finite semisimple
 algebra is
isomorphic to a product of matrix algebras over finite division algebras.
-/
theorem exists_algEquiv_pi_matrix_divisionRing_finite [Module.Finite R₀ R] :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra R₀ (D i)) (_ : ∀ i, Module.Finite R₀ (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  refine ⟨n, D, d, _, _, fun i ↦ ?_, hd, ⟨e⟩⟩
  let l := Matrix.entryLinearMap R₀ (D i) 0 0 ∘ₗ
    .proj (φ := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) _) i
  exact .of_surjective l fun x ↦ ⟨fun j _ _ ↦ Function.update (fun _ ↦ 0) i x j, by simp [l]⟩

/-- The **Wedderburn–Artin Theorem**: a semisimple ring is isomorphic to a
product of matrix rings over the opposite of the endomorphism rings of its simple modules. -/
/-
**IsSemisimpleRing.exists_ringEquiv_pi_matrix_end_mulOpposite** 是 Mathlib 中的一个定理
，位于命名空间 `IsSemisimpleRing`。
形式化陈述：exists_ringEquiv_pi_matrix_end_mulOpposite : exists (n : Nat) (D : Fin n -
> Ideal R) (d : Fin n -> Nat), (forall i, IsSimpleModule R (D i)) ∧ (forall i, N
eZero (d i)) ∧ Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R
 (D i))ᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`：exists_algEq
uiv_pi_matrix_end_mulOpposite : exists (n : Nat) (S : Fin n -> Ideal R) (d : Fin
 n -> Nat), (forall i, IsSimpleModule R (S i)) ∧…

--- 原说明 ---
The **Wedderburn–Artin Theorem**: a semisimple ring is isomorphic to a
product of matrix rings over the opposite of the endomorphism rings of its simpl
e modules.
-/
theorem exists_ringEquiv_pi_matrix_end_mulOpposite :
    ∃ (n : ℕ) (D : Fin n → Ideal R) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (D i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R (D i))ᵐᵒᵖ) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite ℕ R
  ⟨n, S, d, hS, hd, ⟨e⟩⟩

/-- The **Wedderburn–Artin Theorem**: a semisimple ring is isomorphic to a
product of matrix rings over division rings. -/
/-
**IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing** 是 Mathlib 中的一个定理，位于
命名空间 `IsSemisimpleRing`。
形式化陈述：exists_ringEquiv_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n -> T
ype u) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i)), (forall i, NeZero 
(d i)) ∧ Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing`：exists_algEquiv
_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n -> Type u) (d : Fin n -> N
at) (_ : forall i, DivisionRing (D i)) (_ : f…

--- 原说明 ---
The **Wedderburn–Artin Theorem**: a semisimple ring is isomorphic to a
product of matrix rings over division rings.
-/
theorem exists_ringEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i)),
      (∀ i, NeZero (d i)) ∧ Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing ℕ R
  ⟨n, D, d, _, hd, ⟨e⟩⟩
/-
**IsSemisimpleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsSemisimpleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n) [Fintype n] [DecidableEq n] : IsSemisimpleRing (Matrix n n R) :=
  (isEmpty_or_nonempty n).elim (fun _ ↦ inferInstance) fun _ ↦
    have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
    (e.mapMatrix (m := n).trans Matrix.piRingEquiv).symm.isSemisimpleRing
/-
**IsSemisimpleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsSemisimpleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSemisimpleRing Rᵐᵒᵖ :=
  have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
  ((e.op.trans (.piMulOpposite _)).trans (.piCongrRight fun _ ↦ .symm .mopMatrix)).symm
    |>.isSemisimpleRing

end IsSemisimpleRing

/-
**isSemisimpleRing_mulOpposite_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSemisimpleRing_mulOpposite_iff : IsSemisimpleRing Rᵐᵒᵖ ↔ IsSemisimpleRin
g R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.isSemisimpleRing`：RingEquiv.isSemisimpleRing (e : R ≃+* S) [Is
SemisimpleRing R] : IsSemisimpleRing S where __
· 使用定理 `IsSemisimpleRing.instMulOpposite`：∀ (R : Type u) [inst : Ring R] [IsSemi
simpleRing R], IsSemisimpleRing Rᵐᵒᵖ
-/
theorem isSemisimpleRing_mulOpposite_iff : IsSemisimpleRing Rᵐᵒᵖ ↔ IsSemisimpleRing R :=
  ⟨fun _ ↦ (RingEquiv.opOp R).symm.isSemisimpleRing, fun _ ↦ inferInstance⟩

/-- The existence part of the Artin–Wedderburn theorem. -/
/-
**isSemisimpleRing_iff_pi_matrix_divisionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSemisimpleRing_iff_pi_matrix_divisionRing : IsSemisimpleRing R ↔ exists 
(n : Nat) (D : Fin n -> Type u) (d : Fin n -> Nat) (_ : Π i, DivisionRing (D i))
, Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`：exists_ringEqu
iv_pi_matrix_divisionRing : exists (n : Nat) (D : Fin n -> Type u) (d : Fin n ->
 Nat) (_ : forall i, DivisionRing (D i)), (for…
· 使用定理 `RingEquiv.isSemisimpleRing`：RingEquiv.isSemisimpleRing (e : R ≃+* S) [Is
SemisimpleRing R] : IsSemisimpleRing S where __
· 使用定理 `instIsSemisimpleRingForallOfFinite`：∀ {ι : Type u_7} [Finite ι] (R : ι →
 Type u_6) [inst : (i : ι) → Ring (R i)] [∀ (i : ι), IsSemisimpleRing (R i)],   
IsSemisimpleRing ((i : ι…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsSemisimpleRing.instMatrix`：∀ (R : Type u) [inst : Ring R] [IsSemisimpl
eRing R] (n : Type u_2) [inst_2 : Fintype n] [inst_3 : DecidableEq n],   IsSemis
impleRing (Matrix…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R

--- 原说明 ---
The existence part of the Artin–Wedderburn theorem.
-/
theorem isSemisimpleRing_iff_pi_matrix_divisionRing : IsSemisimpleRing R ↔
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : Π i, DivisionRing (D i)),
      Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) where
  mp _ := have ⟨n, D, d, _, _, e⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
    ⟨n, D, d, _, e⟩
  mpr := fun ⟨_, _, _, _, ⟨e⟩⟩ ↦ e.symm.isSemisimpleRing

-- Need left-right symmetry of Jacobson radical
proof_wanted IsSemiprimaryRing.mulOpposite [IsSemiprimaryRing R] : IsSemiprimaryRing Rᵐᵒᵖ

proof_wanted isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R

-- A left Artinian ring is right Noetherian iff it is right Artinian. To be left as an `example`.
proof_wanted IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ
