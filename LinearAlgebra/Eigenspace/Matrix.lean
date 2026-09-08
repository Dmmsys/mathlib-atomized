/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!

# Eigenvalues, Eigenvectors and Spectrum for Matrices

This file collects results about eigenvectors, eigenvalues and spectrum specific to matrices
over a nontrivial commutative ring, nontrivial commutative ring without zero divisors, or field.

## Tags
eigenspace, eigenvector, eigenvalue, spectrum, matrix

-/

public section

open Matrix Module End

variable {R n M : Type*} [DecidableEq n] [Fintype n]

section SpectrumDiagonal

section NontrivialCommRing

variable [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]

/-- Basis vectors are eigenvectors of associated diagonal linear operator. -/
/-
**hasEigenvector_toLin_diagonal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasEigenvector_toLin_diagonal (d : n -> R) (i : n) (b : Basis n R M) : Has
Eigenvector (toLin b b (diagonal d)) (d i) (b i)
参数：d : n -> R；i : n；b : Basis n R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.ne_zero`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…

--- 原说明 ---
Basis vectors are eigenvectors of associated diagonal linear operator.
-/
lemma hasEigenvector_toLin_diagonal (d : n → R) (i : n) (b : Basis n R M) :
    HasEigenvector (toLin b b (diagonal d)) (d i) (b i) :=
  ⟨mem_eigenspace_iff.mpr <| by simp [diagonal], Basis.ne_zero b i⟩

/-- Standard basis vectors are eigenvectors of any associated diagonal linear operator. -/
/-
**hasEigenvector_toLin'_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype n
] [inst_2 : CommRing R] [Nontrivial R]   (d : n → R) (i : n), Module.End.HasEige
nvector (Matrix.toLin' (Matrix.diagonal d)) (d i) ((Pi.basisFun R n) i)
参数：d : n → R；i : n；Matrix.toLin' (Matrix.diagonal d)；d i；(Pi.basisFun R n) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasEigenvector_toLin_diagonal`：hasEigenvector_toLin_diagonal (d : n -> R
) (i : n) (b : Basis n R M) : HasEigenvector (toLin b b (diagonal d)) (d i) (b i
)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Standard basis vectors are eigenvectors of any associated diagonal linear operat
or.
-/
lemma hasEigenvector_toLin'_diagonal (d : n → R) (i : n) :
    HasEigenvector (toLin' (diagonal d)) (d i) (Pi.basisFun R n i) :=
  hasEigenvector_toLin_diagonal _ _ (Pi.basisFun R n)

set_option linter.overlappingInstances false

/-- Eigenvalues of a diagonal linear operator are the diagonal entries. -/
/-
**hasEigenvalue_toLin_diagonal_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasEigenvalue_toLin_diagonal_iff (d : n -> R) {μ : R} [IsDomain R] [IsTors
ionFree R M] (b : Basis n R M) : HasEigenvalue (toLin b b (diagonal d)) μ ↔ exis
ts i, d i = μ
参数：d : n -> R；b : Basis n R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.End.hasEigenvalue_of_hasEigenvector`：hasEigenvalue_of_hasEigenvec
tor {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) : HasEigenvalue f μ
· 使用引理 `hasEigenvector_toLin_diagonal`：hasEigenvector_toLin_diagonal (d : n -> R
) (i : n) (b : Basis n R M) : HasEigenvector (toLin b b (diagonal d)) (d i) (b i
)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `Module.End.HasEigenvector.apply_eq_smul`：∀ {R : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : M
odule.End R M} {μ : R} {x : M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSupIndep.disjoint_biSup`：iSupIndep.disjoint_biSup {ι : Type*} {α : Type
*} [CompleteLattice α] {t : ι -> α} (ht : iSupIndep t) {x : ι} {y : Set ι} (hx :
 x ∉ y) : Disj…
· 使用定理 `Module.End.eigenspaces_iSupIndep`：eigenspaces_iSupIndep [IsDomain R] [Is
TorsionFree R M] (f : End R M) : iSupIndep f.eigenspace
· 使用定理 `disjoint_top`：disjoint_top : Disjoint a ⊤ ↔ a = ⊥

--- 原说明 ---
Eigenvalues of a diagonal linear operator are the diagonal entries.
-/
lemma hasEigenvalue_toLin_diagonal_iff (d : n → R) {μ : R} [IsDomain R] [IsTorsionFree R M]
    (b : Basis n R M) : HasEigenvalue (toLin b b (diagonal d)) μ ↔ ∃ i, d i = μ := by
  have (i : n) : HasEigenvalue (toLin b b (diagonal d)) (d i) :=
    hasEigenvalue_of_hasEigenvector <| hasEigenvector_toLin_diagonal d i b
  constructor
  · contrapose!
    intro hμ h_eig
    have h_iSup : ⨆ μ ∈ Set.range d, eigenspace (toLin b b (diagonal d)) μ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro - ⟨i, rfl⟩
      simp only [SetLike.mem_coe]
      apply Submodule.mem_iSup_of_mem (d i)
      apply Submodule.mem_iSup_of_mem ⟨i, rfl⟩
      rw [mem_eigenspace_iff]
      exact (hasEigenvector_toLin_diagonal d i b).apply_eq_smul
    have hμ_notMem : μ ∉ Set.range d := by simpa using fun i ↦ (hμ i)
    have := eigenspaces_iSupIndep (toLin b b (diagonal d)) |>.disjoint_biSup hμ_notMem
    rw [h_iSup, disjoint_top] at this
    exact h_eig this
  · rintro ⟨i, rfl⟩
    exact this i

/-- Eigenvalues of a diagonal linear operator with respect to standard basis
are the diagonal entries. -/
/-
**hasEigenvalue_toLin'_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype n
] [inst_2 : CommRing R] [Nontrivial R]   [IsDomain R] (d : n → R) {μ : R}, Modul
e.End.HasEigenvalue (Matrix.toLin' (Matrix.diagonal d)) μ ↔ ∃ i, d i = μ
参数：d : n → R；Matrix.toLin' (Matrix.diagonal d)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasEigenvalue_toLin_diagonal_iff`：hasEigenvalue_toLin_diagonal_iff (d : 
n -> R) {μ : R} [IsDomain R] [IsTorsionFree R M] (b : Basis n R M) : HasEigenval
ue (toLin b b (diagona…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Eigenvalues of a diagonal linear operator with respect to standard basis
are the diagonal entries.
-/
lemma hasEigenvalue_toLin'_diagonal_iff [IsDomain R] (d : n → R) {μ : R} :
    HasEigenvalue (toLin' (diagonal d)) μ ↔ (∃ i, d i = μ) :=
  hasEigenvalue_toLin_diagonal_iff _ <| Pi.basisFun R n

end NontrivialCommRing

namespace Matrix

variable [CommRing R] [AddCommGroup M] [Module R M] (d : n → R) {μ : R} (b : Basis n R M)

/-
**Matrix._root_.Module.End.HasEigenvalue.nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Mat
rix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.End.HasEigenvalue.nonempty
    {A : Matrix n n R} {μ : R} (hμ : HasEigenvalue A.toLin' μ) :
    Nonempty n := by
  rw [hasEigenvalue_iff] at hμ
  contrapose! hμ
  exact Submodule.eq_bot_of_subsingleton

@[simp]
/-
**Matrix.iSup_eigenspace_toLin_diagonal_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
`。
形式化陈述：iSup_eigenspace_toLin_diagonal_eq_top : ⨆ μ, eigenspace ((diagonal d).toLi
n b b) μ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.eq_top_iff_forall_basis_mem`：∀ {ι : Type u_1} {R : Type u_3} {
M : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] (b : Module.Bas…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_eigenspace_toLin_diagonal_eq_top :
    ⨆ μ, eigenspace ((diagonal d).toLin b b) μ = ⊤ := by
  refine (Submodule.eq_top_iff_forall_basis_mem b).mpr fun j ↦ ?_
  exact Submodule.mem_iSup_of_mem (d j) <| by simp [diagonal_apply]

@[simp]
/-
**Matrix.iSup_eigenspace_toLin'_diagonal_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype n
] [inst_2 : CommRing R] (d : n → R),   ⨆ μ, Module.End.eigenspace (Matrix.toLin'
 (Matrix.diagonal d)) μ = ⊤
参数：d : n → R；Matrix.toLin' (Matrix.diagonal d)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.iSup_eigenspace_toLin_diagonal_eq_top`：iSup_eigenspace_toLin_diag
onal_eq_top : ⨆ μ, eigenspace ((diagonal d).toLin b b) μ = ⊤
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma iSup_eigenspace_toLin'_diagonal_eq_top :
    ⨆ μ, eigenspace (diagonal d).toLin' μ = ⊤ :=
  iSup_eigenspace_toLin_diagonal_eq_top d <| Pi.basisFun R n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace** 是 Mathlib 中的一个引理，位于命名空间
 `Matrix`。
形式化陈述：maxGenEigenspace_toLin_diagonal_eq_eigenspace [IsDomain R] : maxGenEigensp
ace ((diagonal d).toLin b b) μ = eigenspace ((diagonal d).toLin b b) μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.mem_maxGenEigenspace`：mem_maxGenEigenspace (f : End R M) (μ :
 R) (m : M) : m in f.maxGenEigenspace μ ↔ exists k : Nat, ((f - μ • (1 : End R M
)) ^ k) m = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.sub_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub (G
 i)] (f g : (i : ι) → G i), f - g = fun i => f i - g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_sub`：diagonal_sub [SubNegZeroMonoid α] (d₁ d₂ : n -> α) 
: diagonal d₁ - diagonal d₂ = diagonal fun i => d₁ i - d₂ i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagonal_smul`：diagonal_smul [Zero α] [SMulZeroClass R α] (r : R)
 (d : n -> α) : diagonal (r • d) = r • diagonal d
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
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
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Matrix.toLin_one`：Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
（共 49 条，此处仅展示前 30 条）
-/
lemma maxGenEigenspace_toLin_diagonal_eq_eigenspace [IsDomain R] :
    maxGenEigenspace ((diagonal d).toLin b b) μ = eigenspace ((diagonal d).toLin b b) μ := by
  refine le_antisymm (fun x hx ↦ ?_) eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace _ _ _).mp hx
  replace hk (j : n) : b.repr x j = 0 ∨ d j = μ ∧ k ≠ 0 := by
    have aux : (diagonal d).toLin b b - μ • 1 = (diagonal (d - μ • 1)).toLin b b := by
      rw [Pi.sub_def, ← diagonal_sub]; simp [one_eq_id]
    rw [aux, ← toLin_pow, diagonal_pow, toLin_apply_eq_zero_iff] at hk
    simpa [mulVec_eq_sum, diagonal_apply, sub_eq_zero] using hk j
  have aux (j : n) : (b.repr x j * d j) • b j = μ • (b.repr x j • b j) := by
    rcases hk j with hj | hj
    · simp [hj]
    · rw [← hj.1, mul_comm, mul_smul]
  simp [toLin_apply, mulVec_eq_sum, diagonal_apply, aux, ← Finset.smul_sum]

@[simp]
/-
**Matrix.maxGenEigenspace_toLin'_diagonal_eq_eigenspace** 是 Mathlib 中的一个定理，位于命名空
间 `Matrix`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype n
] [inst_2 : CommRing R] (d : n → R) {μ : R}   [IsDomain R],   Module.End.maxGenE
igenspace (Matrix.toLin' (Matrix.diagonal d)) μ =     Module.End.eigenspace (Mat
rix.toLin' (Matrix.diagonal d)) μ
参数：d : n → R；Matrix.toLin' (Matrix.diagonal d)；Matrix.toLin' (Matrix.diagonal d)
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace`：maxGenEigenspace_t
oLin_diagonal_eq_eigenspace [IsDomain R] : maxGenEigenspace ((diagonal d).toLin 
b b) μ = eigenspace ((diagonal d).toLin b …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma maxGenEigenspace_toLin'_diagonal_eq_eigenspace [IsDomain R] :
    maxGenEigenspace (diagonal d).toLin' μ = eigenspace (diagonal d).toLin' μ :=
  maxGenEigenspace_toLin_diagonal_eq_eigenspace d <| Pi.basisFun R n

@[simp]
/-
**Matrix._root_.LinearMap.spectrum_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.spectrum_toMatrix (f : M →ₗ[R] M) (b : Basis n R M) :
    spectrum R (f.toMatrix b b) = spectrum R f :=
  AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv b) f

@[simp]
/-
**Matrix._root_.LinearMap.spectrum_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.spectrum_toMatrix' (f : (n → R) →ₗ[R] (n → R)) :
    spectrum R f.toMatrix' = spectrum R f :=
  AlgEquiv.spectrum_eq LinearMap.toMatrixAlgEquiv' f

@[simp]
/-
**Matrix.spectrum_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：spectrum_toLin (A : Matrix n n R) (b : Basis n R M) : spectrum R (A.toLin 
b b) = spectrum R A
参数：A : Matrix n n R；b : Basis n R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.spectrum_eq`：AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiri
ng R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivC
lass F R A…
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem spectrum_toLin (A : Matrix n n R) (b : Basis n R M) :
    spectrum R (A.toLin b b) = spectrum R A :=
  AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv b) A

@[simp]
/-
**Matrix.spectrum_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：spectrum_toLin' (A : Matrix n n R) : spectrum R A.toLin' = spectrum R A
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.spectrum_eq`：AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiri
ng R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivC
lass F R A…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem spectrum_toLin' (A : Matrix n n R) : spectrum R A.toLin' = spectrum R A :=
  AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' A

end Matrix

/-- The spectrum of the diagonal operator is the range of the diagonal viewed as a function. -/
/-
**spectrum_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype n
] [inst_2 : Field R] (d : n → R),   spectrum R (Matrix.diagonal d) = Set.range d
参数：d : n → R；Matrix.diagonal d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.spectrum_eq`：AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiri
ng R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivC
lass F R A…
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Module.End.hasEigenvalue_iff_mem_spectrum`：hasEigenvalue_iff_mem_spectru
m [FiniteDimensional K V] {f : End K V} {μ : K} : f.HasEigenvalue μ ↔ μ in spect
rum K f
· 使用定理 `hasEigenvalue_toLin'_diagonal_iff`：∀ {R : Type u_1} {n : Type u_2} [inst
 : DecidableEq n] [inst_1 : Fintype n] [inst_2 : CommRing R] [Nontrivial R]   [I
sDomain R] (d : n → R) …
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
The spectrum of the diagonal operator is the range of the diagonal viewed as a f
unction.
-/
@[simp] lemma spectrum_diagonal [Field R] (d : n → R) :
    spectrum R (diagonal d) = Set.range d := by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n), ← hasEigenvalue_iff_mem_spectrum]
  exact hasEigenvalue_toLin'_diagonal_iff d

end SpectrumDiagonal

