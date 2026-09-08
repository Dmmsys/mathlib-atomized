/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.SpanRank

/-!

# Cayley-Hamilton theorem for f.g. modules.

Given a fixed finite spanning set `b : ι → M` of an `R`-module `M`, we say that a matrix `M`
represents an endomorphism `f : M →ₗ[R] M` if the matrix as an endomorphism of `ι → R` commutes
with `f` via the projection `(ι → R) →ₗ[R] M` given by `b`.

We show that every endomorphism has a matrix representation, and if `f.range ≤ I • ⊤` for some
ideal `I`, we may furthermore obtain a matrix representation whose entries fall in `I`.

This is used to conclude the Cayley-Hamilton theorem for f.g. modules over arbitrary rings.
-/

@[expose] public section


variable {ι : Type*} [Fintype ι]
variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)
variable (b : ι → M)

open Polynomial Matrix

/-- The composition of a matrix (as an endomorphism of `ι → R`) with the projection
`(ι → R) →ₗ[R] M`. -/
/-
**PiToModule.fromMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PiToModule.fromMatrix [DecidableEq ι] : Matrix ι ι R ->ₗ[R] (ι -> R) ->ₗ[R
] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of a matrix (as an endomorphism of `ι → R`) with the projection
`(ι → R) →ₗ[R] M`.
-/
def PiToModule.fromMatrix [DecidableEq ι] : Matrix ι ι R →ₗ[R] (ι → R) →ₗ[R] M :=
  (LinearMap.llcomp R _ _ _ (Fintype.linearCombination R b)).comp algEquivMatrix'.symm.toLinearMap
/-
**PiToModule.fromMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiToModule.fromMatrix_apply [DecidableEq ι] (A : Matrix ι ι R) (w : ι -> R
) : PiToModule.fromMatrix R b A w = Fintype.linearCombination R b (A *ᵥ w)
参数：A : Matrix ι ι R；w : ι -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PiToModule.fromMatrix_apply [DecidableEq ι] (A : Matrix ι ι R) (w : ι → R) :
    PiToModule.fromMatrix R b A w = Fintype.linearCombination R b (A *ᵥ w) :=
  rfl
/-
**PiToModule.fromMatrix_apply_single_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiToModule.fromMatrix_apply_single_one [DecidableEq ι] (A : Matrix ι ι R) 
(j : ι) : PiToModule.fromMatrix R b A (Pi.single j 1) = ∑ i : ι, A i j • b i
参数：A : Matrix ι ι R；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiToModule.fromMatrix_apply`：PiToModule.fromMatrix_apply [DecidableEq ι]
 (A : Matrix ι ι R) (w : ι -> R) : PiToModule.fromMatrix R b A w = Fintype.linea
rCombination R b …
· 使用定理 `Fintype.linearCombination_apply`：Fintype.linearCombination_apply (f) : F
intype.linearCombination R v f = ∑ i, f i • v i
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PiToModule.fromMatrix_apply_single_one [DecidableEq ι] (A : Matrix ι ι R) (j : ι) :
    PiToModule.fromMatrix R b A (Pi.single j 1) = ∑ i : ι, A i j • b i := by
  rw [PiToModule.fromMatrix_apply, Fintype.linearCombination_apply, Matrix.mulVec_single]
  simp_rw [MulOpposite.op_one, one_smul, col_apply]

/-- The endomorphisms of `M` acts on `(ι → R) →ₗ[R] M`, and takes the projection
to a `(ι → R) →ₗ[R] M`. -/
/-
**PiToModule.fromEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PiToModule.fromEnd : Module.End R M ->ₗ[R] (ι -> R) ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endomorphisms of `M` acts on `(ι → R) →ₗ[R] M`, and takes the projection
to a `(ι → R) →ₗ[R] M`.
-/
def PiToModule.fromEnd : Module.End R M →ₗ[R] (ι → R) →ₗ[R] M :=
  LinearMap.lcomp _ _ (Fintype.linearCombination R b)
/-
**PiToModule.fromEnd_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiToModule.fromEnd_apply (f : Module.End R M) (w : ι -> R) : PiToModule.fr
omEnd R b f w = f (Fintype.linearCombination R b w)
参数：f : Module.End R M；w : ι -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PiToModule.fromEnd_apply (f : Module.End R M) (w : ι → R) :
    PiToModule.fromEnd R b f w = f (Fintype.linearCombination R b w) :=
  rfl
/-
**PiToModule.fromEnd_apply_single_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiToModule.fromEnd_apply_single_one [DecidableEq ι] (f : Module.End R M) (
i : ι) : PiToModule.fromEnd R b f (Pi.single i 1) = f (b i)
参数：f : Module.End R M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiToModule.fromEnd_apply`：PiToModule.fromEnd_apply (f : Module.End R M) 
(w : ι -> R) : PiToModule.fromEnd R b f w = f (Fintype.linearCombination R b w)
· 使用定理 `Fintype.linearCombination_apply_single`：Fintype.linearCombination_apply_
single [DecidableEq α] (i : α) (r : R) : Fintype.linearCombination R v (Pi.singl
e i r) = r • v i
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem PiToModule.fromEnd_apply_single_one [DecidableEq ι] (f : Module.End R M) (i : ι) :
    PiToModule.fromEnd R b f (Pi.single i 1) = f (b i) := by
  rw [PiToModule.fromEnd_apply, Fintype.linearCombination_apply_single, one_smul]
/-
**PiToModule.fromEnd_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiToModule.fromEnd_injective (hb : Submodule.span R (Set.range b) = ⊤) : F
unction.Injective (PiToModule.fromEnd R b)
参数：hb : Submodule.span R (Set.range b) = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.range_linearCombination`：Fintype.range_linearCombination : Linea
rMap.range (Fintype.linearCombination R v) = Submodule.span R (Set.range v)
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem PiToModule.fromEnd_injective (hb : Submodule.span R (Set.range b) = ⊤) :
    Function.Injective (PiToModule.fromEnd R b) := by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m ∈ LinearMap.range (Fintype.linearCombination R b) := by
    rw [(Fintype.range_linearCombination R b).trans hb]
    exact Submodule.mem_top
  exact (LinearMap.congr_fun e m :)

section

variable {R} [DecidableEq ι]

/-- We say that a matrix represents an endomorphism of `M` if the matrix acting on `ι → R` is
equal to `f` via the projection `(ι → R) →ₗ[R] M` given by a fixed (spanning) set. -/
/-
**Matrix.Represents** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.Represents (A : Matrix ι ι R) (f : Module.End R M) : Prop
参数：A : Matrix ι ι R；f : Module.End R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a matrix represents an endomorphism of `M` if the matrix acting on `
ι → R` is
equal to `f` via the projection `(ι → R) →ₗ[R] M` given by a fixed (spanning) se
t.
-/
def Matrix.Represents (A : Matrix ι ι R) (f : Module.End R M) : Prop :=
  PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f

variable {b}
/-
**Matrix.Represents.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.congr_fun {A : Matrix ι ι R} {f : Module.End R M} (h : A
.Represents b f) (x) : Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linea
rCombination R b x)
参数：h : A.Represents b f；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem Matrix.Represents.congr_fun {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (x) : Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCombination R b x) :=
  LinearMap.congr_fun h x
/-
**Matrix.represents_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.represents_iff {A : Matrix ι ι R} {f : Module.End R M} : A.Represen
ts b f ↔ forall x, Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCom
bination R b x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Represents.congr_fun`：Matrix.Represents.congr_fun {A : Matrix ι ι
 R} {f : Module.End R M} (h : A.Represents b f) (x) : Fintype.linearCombination 
R b (A *ᵥ x) = f …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem Matrix.represents_iff {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔
      ∀ x, Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCombination R b x) :=
  ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩
/-
**Matrix.represents_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.represents_iff' {A : Matrix ι ι R} {f : Module.End R M} : A.Represe
nts b f ↔ forall j, ∑ i : ι, A i j • b i = f (b j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiToModule.fromMatrix_apply_single_one`：PiToModule.fromMatrix_apply_sing
le_one [DecidableEq ι] (A : Matrix ι ι R) (j : ι) : PiToModule.fromMatrix R b A 
(Pi.single j 1) = ∑ i : ι, A…
· 使用定理 `PiToModule.fromEnd_apply_single_one`：PiToModule.fromEnd_apply_single_one
 [DecidableEq ι] (f : Module.End R M) (i : ι) : PiToModule.fromEnd R b f (Pi.sin
gle i 1) = f (b i)
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem Matrix.represents_iff' {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔ ∀ j, ∑ i : ι, A i j • b i = f (b j) := by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.fromEnd_apply_single_one,
      PiToModule.fromMatrix_apply_single_one]
    apply h
/-
**Matrix.Represents.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.mul {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A
.Represents b f) (h' : Matrix.Represents b A' f') : (A * A').Represents b (f * f
')
参数：h : A.Represents b f；h' : Matrix.Represents b A' f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `AlgEquiv.toLinearMap_apply`：toLinearMap_apply (x : A₁) : e.toLinearMap x
 = e x
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
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.Represents.congr_fun`：Matrix.Represents.congr_fun {A : Matrix ι ι
 R} {f : Module.End R M} (h : A.Represents b f) (x) : Fintype.linearCombination 
R b (A *ᵥ x) = f …
-/
theorem Matrix.Represents.mul {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A * A').Represents b (f * f') := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
  ext
  dsimp [PiToModule.fromEnd]
  rw [← h'.congr_fun, ← h.congr_fun]
  rfl
/-
**Matrix.Represents.one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.one : (1 : Matrix ι ι R).Represents b 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `AlgEquiv.toLinearMap_apply`：toLinearMap_apply (x : A₁) : e.toLinearMap x
 = e x
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
theorem Matrix.Represents.one : (1 : Matrix ι ι R).Represents b 1 := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one]
  ext
  rfl
/-
**Matrix.Represents.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A
.Represents b f) (h' : Matrix.Represents b A' f') : (A + A').Represents b (f + f
')
参数：h : A.Represents b f；h' : Matrix.Represents b A' f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A + A').Represents b (f + f') := by
  delta Matrix.Represents at h h' ⊢; rw [map_add, map_add, h, h']
/-
**Matrix.Represents.zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.zero : (0 : Matrix ι ι R).Represents b 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
-/
theorem Matrix.Represents.zero : (0 : Matrix ι ι R).Represents b 0 := by
  delta Matrix.Represents
  rw [map_zero, map_zero]
/-
**Matrix.Represents.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.End R M} (h : A.Repr
esents b f) (r : R) : (r • A).Represents b (r • f)
参数：h : A.Represents b f；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (r : R) : (r • A).Represents b (r • f) := by
  delta Matrix.Represents at h ⊢
  rw [map_smul, map_smul, h]
/-
**Matrix.Represents.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.algebraMap (r : R) : (algebraMap _ (Matrix ι ι R) r).Rep
resents b (algebraMap _ (Module.End R M) r)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Represents.congr_simp`：∀ {ι : Type u_1} [inst : Fintype ι] {M : T
ype u_2} [inst_1 : AddCommGroup M] {R : Type u_3} [inst_2 : CommRing R]   [inst_
3 : _root_.Module …
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Matrix.Represents.smul`：Matrix.Represents.smul {A : Matrix ι ι R} {f : M
odule.End R M} (h : A.Represents b f) (r : R) : (r • A).Represents b (r • f)
· 使用定理 `Matrix.Represents.one`：Matrix.Represents.one : (1 : Matrix ι ι R).Repres
ents b 1
-/
theorem Matrix.Represents.algebraMap (r : R) :
    (algebraMap _ (Matrix ι ι R) r).Represents b (algebraMap _ (Module.End R M) r) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.Represents.one.smul r
/-
**Matrix.Represents.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.Represents.eq (hb : Submodule.span R (Set.range b) = ⊤) {A : Matrix
 ι ι R} {f f' : Module.End R M} (h : A.Represents b f) (h' : A.Represents b f') 
: f = f'
参数：hb : Submodule.span R (Set.range b) = ⊤；h : A.Represents b f；h' : A.Represent
s b f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiToModule.fromEnd_injective`：PiToModule.fromEnd_injective (hb : Submodu
le.span R (Set.range b) = ⊤) : Function.Injective (PiToModule.fromEnd R b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Matrix.Represents.eq (hb : Submodule.span R (Set.range b) = ⊤)
    {A : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : A.Represents b f') : f = f' :=
  PiToModule.fromEnd_injective R b hb (h.symm.trans h')

variable (b R)

/-- The subalgebra of `Matrix ι ι R` that consists of matrices that actually represent
endomorphisms on `M`. -/
/-
**Matrix.isRepresentation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.isRepresentation : Subalgebra R (Matrix ι ι R) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subalgebra of `Matrix ι ι R` that consists of matrices that actually represe
nt
endomorphisms on `M`.
-/
def Matrix.isRepresentation : Subalgebra R (Matrix ι ι R) where
  carrier := { A | ∃ f : Module.End R M, A.Represents b f }
  mul_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ * f₂, e₁.mul e₂⟩
  one_mem' := ⟨1, Matrix.Represents.one⟩
  add_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ + f₂, e₁.add e₂⟩
  zero_mem' := ⟨0, Matrix.Represents.zero⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, .algebraMap _⟩

variable (hb : Submodule.span R (Set.range b) = ⊤)
include hb

/-- The map sending a matrix to the endomorphism it represents. This is an `R`-algebra morphism. -/
/-
**Matrix.isRepresentation.toEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.isRepresentation.toEnd : Matrix.isRepresentation R b ->ₐ[R] Module.
End R M where toFun A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map sending a matrix to the endomorphism it represents. This is an `R`-algeb
ra morphism.
-/
noncomputable def Matrix.isRepresentation.toEnd :
    Matrix.isRepresentation R b →ₐ[R] Module.End R M where
  toFun A := A.2.choose
  map_one' := (1 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.one
  map_mul' A₁ A₂ := (A₁ * A₂).2.choose_spec.eq hb (A₁.2.choose_spec.mul A₂.2.choose_spec)
  map_zero' := (0 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.zero
  map_add' A₁ A₂ := (A₁ + A₂).2.choose_spec.eq hb (A₁.2.choose_spec.add A₂.2.choose_spec)
  commutes' r :=
    (algebraMap _ (Matrix.isRepresentation R b) r).2.choose_spec.eq hb (.algebraMap r)
/-
**Matrix.isRepresentation.toEnd_represents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isRepresentation.toEnd_represents (A : Matrix.isRepresentation R b)
 : (A : Matrix ι ι R).Represents b (Matrix.isRepresentation.toEnd R b hb A)
参数：A : Matrix.isRepresentation R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Matrix.isRepresentation.toEnd_represents (A : Matrix.isRepresentation R b) :
    (A : Matrix ι ι R).Represents b (Matrix.isRepresentation.toEnd R b hb A) :=
  A.2.choose_spec
/-
**Matrix.isRepresentation.eq_toEnd_of_represents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isRepresentation.eq_toEnd_of_represents (A : Matrix.isRepresentatio
n R b) {f : Module.End R M} (h : (A : Matrix ι ι R).Represents b f) : Matrix.isR
epresentation.toEnd R b hb A = f
参数：A : Matrix.isRepresentation R b；h : (A : Matrix ι ι R).Represents b f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Represents.eq`：Matrix.Represents.eq (hb : Submodule.span R (Set.r
ange b) = ⊤) {A : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f) (
h' : A.Rep…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Matrix.isRepresentation.eq_toEnd_of_represents (A : Matrix.isRepresentation R b)
    {f : Module.End R M} (h : (A : Matrix ι ι R).Represents b f) :
    Matrix.isRepresentation.toEnd R b hb A = f :=
  A.2.choose_spec.eq hb h
/-
**Matrix.isRepresentation.toEnd_exists_mem_ideal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isRepresentation.toEnd_exists_mem_ideal (f : Module.End R M) (I : I
deal R) (hI : LinearMap.range f <= I • ⊤) : exists M, Matrix.isRepresentation.to
End R b hb M = f ∧ forall i j, M.1 i j in I
参数：f : Module.End R M；I : Ideal R；hI : LinearMap.range f <= I • ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.range_finsuppTotal`：range_finsuppTotal : LinearMap.range (finsuppT
otal ι M I v) = I • Submodule.span R (Set.range v)
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `Matrix.represents_iff'`：Matrix.represents_iff' {A : Matrix ι ι R} {f : M
odule.End R M} : A.Represents b f ↔ forall j, ∑ i : ι, A i j • b i = f (b j)
· 使用定理 `Ideal.finsuppTotal_apply_eq_of_fintype`：finsuppTotal_apply_eq_of_fintype
 [Fintype ι] (f : ι ->₀ I) : finsuppTotal ι M I v f = ∑ i, (f i : R) • v i
· 使用定理 `Matrix.isRepresentation.eq_toEnd_of_represents`：Matrix.isRepresentation.
eq_toEnd_of_represents (A : Matrix.isRepresentation R b) {f : Module.End R M} (h
 : (A : Matrix ι ι R).Represents b f…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Matrix.isRepresentation.toEnd_exists_mem_ideal (f : Module.End R M) (I : Ideal R)
    (hI : LinearMap.range f ≤ I • ⊤) :
    ∃ M, Matrix.isRepresentation.toEnd R b hb M = f ∧ ∀ i j, M.1 i j ∈ I := by
  have : ∀ x, f x ∈ LinearMap.range (Ideal.finsuppTotal ι M I b) := by
    rw [Ideal.range_finsuppTotal, hb]
    exact fun x => hI (LinearMap.mem_range_self f x)
  choose bM' hbM' using this
  let A : Matrix ι ι R := fun i j => bM' (b j) i
  have : A.Represents b f := by
    rw [Matrix.represents_iff']
    dsimp [A]
    intro j
    specialize hbM' (b j)
    rwa [Ideal.finsuppTotal_apply_eq_of_fintype] at hbM'
  exact
    ⟨⟨A, f, this⟩, Matrix.isRepresentation.eq_toEnd_of_represents R b hb ⟨A, f, this⟩ this,
      fun i j => (bM' (b j) i).prop⟩
/-
**Matrix.isRepresentation.toEnd_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isRepresentation.toEnd_surjective : Function.Surjective (Matrix.isR
epresentation.toEnd R b hb)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isRepresentation.toEnd_exists_mem_ideal`：Matrix.isRepresentation.
toEnd_exists_mem_ideal (f : Module.End R M) (I : Ideal R) (hI : LinearMap.range 
f <= I • ⊤) : exists M, Matrix.isRep…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
-/
theorem Matrix.isRepresentation.toEnd_surjective :
    Function.Surjective (Matrix.isRepresentation.toEnd R b hb) := by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R b hb f ⊤ (by simp)
  exact ⟨M, e⟩

end

/-- The **Cayley-Hamilton Theorem** for f.g. modules over arbitrary rings states that for each
`R`-endomorphism `φ` of an `R`-module `M` generated by `n` elements such that `φ(M) ≤ I • M`
for some ideal `I`, there exist some `aᵢ ∈ Iⁱ` such that `φⁿ + a₁ φⁿ⁻¹ + ⋯ + aₙ = 0`.

This is the version in [Matsumura 2.1][matsumura1987], which is stronger than those in
[Eisenbud 4.3][Eisenbud1995] and [Atiyah-Macdonald 2.4][atiyah-macdonald].
-/
/-
**LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zer
o [Module.Finite R M] (f : Module.End R M) (I : Ideal R) (hI : LinearMap.range f
 <= I • ⊤) : exists p : R[X], p.Monic ∧ p.natDegree = (⊤ : Submodule R M).spanFi
nrank ∧ (forall k, p.coeff k in I ^ (p.natDegree - k)) ∧ Polynomial.aeval f p = 
0
参数：f : Module.End R M；I : Ideal R；hI : LinearMap.range f <= I • ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.spanFinrank_subsingleton`：spanFinrank_subsingleton [Subsinglet
on R] (p : Submodule R M) : p.spanFinrank = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Submodule.FG.exists_span_finset_card_eq_spanFinrank`：∀ {R : Type u_1} {M
 : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modul
e R M]   {p : Submodule R M}, p.FG → ∃ s,…
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Matrix.isRepresentation.toEnd_exists_mem_ideal`：Matrix.isRepresentation.
toEnd_exists_mem_ideal (f : Module.End R M) (I : Ideal R) (hI : LinearMap.range 
f <= I • ⊤) : exists M, Matrix.isRep…
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Matrix.coeff_charpoly_mem_ideal_pow`：coeff_charpoly_mem_ideal_pow {I : I
deal R} (h : forall i j, M i j in I) (k : Nat) : M.charpoly.coeff k in I ^ (Fint
ype.card n - k)
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The **Cayley-Hamilton Theorem** for f.g. modules over arbitrary rings states tha
t for each
`R`-endomorphism `φ` of an `R`-module `M` generated by `n` elements such that `φ
(M) ≤ I • M`
for some ideal `I`, there exist some `aᵢ ∈ Iⁱ` such that `φⁿ + a₁ φⁿ⁻¹ + ⋯ + aₙ 
= 0`.

This is the version in [Matsumura 2.1][matsumura1987], which is stronger than th
ose in
[Eisenbud 4.3][Eisenbud1995] and [Atiyah-Macdonald 2.4][atiyah-macdonald].
-/
theorem LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
    [Module.Finite R M] (f : Module.End R M) (I : Ideal R) (hI : LinearMap.range f ≤ I • ⊤) :
    ∃ p : R[X], p.Monic ∧ p.natDegree = (⊤ : Submodule R M).spanFinrank ∧
                (∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) ∧ Polynomial.aeval f p = 0 := by
  classical
    cases subsingleton_or_nontrivial R
    · exact ⟨0, by simp [nontriviality]⟩
    obtain ⟨s, hs_card, hs_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank (R := R) (M := M) Module.Finite.fg_top
    have : Submodule.span R (Set.range ((↑) : s → M)) = ⊤ := by simp [hs_span]
    obtain ⟨A, rfl, h⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R ((↑) : s → M) this f I hI
    refine ⟨A.1.charpoly, A.1.charpoly_monic, by simp [hs_card],
            by simpa using coeff_charpoly_mem_ideal_pow h, ?_⟩
    rw [Polynomial.aeval_algHom_apply,
      ← map_zero (Matrix.isRepresentation.toEnd R ((↑) : s → M) this)]
    congr 1
    ext1
    rw [Polynomial.aeval_subalgebra_coe, Matrix.aeval_self_charpoly, Subalgebra.coe_zero]

@[deprecated
"strengthened conclusion to
`LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero`"
(since := "2026-04-10")] alias
LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul :=
  LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
/-
**LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero [Module.Finite R
 M] (f : Module.End R M) : exists p : R[X], p.Monic ∧ p.natDegree = (⊤ : Submodu
le R M).spanFinrank ∧ Polynomial.aeval f p = 0
参数：f : Module.End R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_z
ero`：LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
 [Module.Finite R M] (f : Module.End R M) (I : Ideal R) (hI : Lin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
-/
theorem LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero
    [Module.Finite R M] (f : Module.End R M) :
    ∃ p : R[X], p.Monic ∧ p.natDegree = (⊤ : Submodule R M).spanFinrank ∧
                Polynomial.aeval f p = 0 :=
  (LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R f ⊤ (by simp)).imp
    fun _ h ↦ h.imp_right (And.imp_right And.right)
/-
**LinearMap.exists_monic_and_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_monic_and_aeval_eq_zero [Module.Finite R M] (f : Module.E
nd R M) : exists p : R[X], p.Monic ∧ Polynomial.aeval f p = 0
参数：f : Module.End R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero`：LinearMap.exi
sts_monic_and_natDegree_eq_and_aeval_eq_zero [Module.Finite R M] (f : Module.End
 R M) : exists p : R[X], p.Monic ∧ p.natDegree …
-/
theorem LinearMap.exists_monic_and_aeval_eq_zero [Module.Finite R M] (f : Module.End R M) :
    ∃ p : R[X], p.Monic ∧ Polynomial.aeval f p = 0 :=
  (LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero R f).imp
    fun _ h => h.imp_right And.right
