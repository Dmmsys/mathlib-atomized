/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `WStarAlgebra M` is a C⋆ algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `VonNeumannAlgebra H` (where `H` is a Hilbert space)
is a \*-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a \*-closed subalgebra which is weakly closed.
-/

@[expose] public section


universe u v

/-- Sakai's definition of a von Neumann algebra as a C⋆ algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed \*-subalgebras of B(H)),
we name this definition `WStarAlgebra`.

Note that for now we only assert the mere existence of predual, rather than picking one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instances.
One the other hand, not picking one means that the weak-\* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
/-
**WStarAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u) → [CStarAlgebra M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sakai's definition of a von Neumann algebra as a C⋆ algebra with a Banach space 
predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed \*-subalgebras of B(H)),
we name this definition `WStarAlgebra`.

Note that for now we only assert the mere existence of predual, rather than pick
ing one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instan
ces.
One the other hand, not picking one means that the weak-\* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
class WStarAlgebra (M : Type u) [CStarAlgebra M] : Prop where
  /-- There is a Banach space `X` whose dual is isometrically (conjugate-linearly) isomorphic
  to the `WStarAlgebra`. -/
  exists_predual :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X) (_ : CompleteSpace X),
      Nonempty (StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

-- TODO: Without this, `VonNeumannAlgebra` times out. Why?
/-- The double commutant definition of a von Neumann algebra,
as a \*-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `WStarAlgebra` for the abstract notion (a C⋆-algebra with Banach space predual).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `VonNeumannAlgebra`
(although we will later construct the instance `WStarAlgebra (H →L[ℂ] H)`),
and instead will use `⊤ : VonNeumannAlgebra H`.
-/
/-
**VonNeumannAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(H : Type u) → [inst : NormedAddCommGroup H] → [InnerProductSpace ℂ H] → [
CompleteSpace H] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The double commutant definition of a von Neumann algebra,
as a \*-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `WStarAlgebra` for the abstract notion (a C⋆-algebra with Banach space predu
al).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `VonNeumannAlgeb
ra`
(although we will later construct the instance `WStarAlgebra (H →L[ℂ] H)`),
and instead will use `⊤ : VonNeumannAlgebra H`.
-/
structure VonNeumannAlgebra (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] extends StarSubalgebra ℂ (H →L[ℂ] H) where
  /-- The double commutant (a.k.a. centralizer) of a `VonNeumannAlgebra` is itself. -/
  centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier

/-- Consider a von Neumann algebra acting on a Hilbert space `H` as a \*-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc VonNeumannAlgebra.toStarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-
**VonNeumannAlgebra.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `VonNeumannAlgebra`。
形式化陈述：instSetLike : SetLike (VonNeumannAlgebra H) (H ->L[Complex] H) where coe S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.instStarModuleId`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
-/
instance instSetLike : SetLike (VonNeumannAlgebra H) (H →L[ℂ] H) where
  coe S := S.carrier
  coe_injective S T h := by obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := S; cases T; congr
/-
**VonNeumannAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `VonNeumannAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (VonNeumannAlgebra H) := .ofSetLike (VonNeumannAlgebra H) (H →L[ℂ] H)
/-
**VonNeumannAlgebra.instStarMemClass** 是 Mathlib 中的一个实例，位于命名空间 `VonNeumannAlgebr
a`。
形式化陈述：instStarMemClass : StarMemClass (VonNeumannAlgebra H) (H ->L[Complex] H) w
here star_mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.star_mem'`：∀ {R : Type u} {A : Type v} [inst : CommSemiri
ng R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarRing A]   [inst_
4 : Algebra R …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.instStarModuleId`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
-/
noncomputable instance instStarMemClass : StarMemClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  star_mem {s} := s.star_mem'
/-
**VonNeumannAlgebra.instSubringClass** 是 Mathlib 中的一个实例，位于命名空间 `VonNeumannAlgebr
a`。
形式化陈述：instSubringClass : SubringClass (VonNeumannAlgebra H) (H ->L[Complex] H) w
here add_mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subsemigroup.mul_mem'`：∀ {M : Type u_3} [inst : Mul M] (self : Subsemigr
oup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.instStarModuleId`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
· 使用定理 `Subsemiring.add_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self :
 Subsemiring R) {a b : R},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.
carrier
· 使用定理 `Subsemiring.zero_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self 
: Subsemiring R), 0 ∈ self.carrier
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
-/
instance instSubringClass : SubringClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} a ha := show -a ∈ s.toStarSubalgebra from neg_mem ha

@[simp]
/-
**VonNeumannAlgebra.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `VonNeumannAlgebra`。
形式化陈述：mem_carrier {S : VonNeumannAlgebra H} {x : H ->L[Complex] H} : x in S.toSt
arSubalgebra ↔ x in (S : Set (H ->L[Complex] H))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.instStarModuleId`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
-/
theorem mem_carrier {S : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ S.toStarSubalgebra ↔ x ∈ (S : Set (H →L[ℂ] H)) :=
  Iff.rfl

@[simp]
/-
**VonNeumannAlgebra.coe_toStarSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `VonNeumannAl
gebra`。
形式化陈述：coe_toStarSubalgebra (S : VonNeumannAlgebra H) : (S.toStarSubalgebra : Set
 (H ->L[Complex] H)) = S
参数：S : VonNeumannAlgebra H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.instStarModuleId`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
-/
theorem coe_toStarSubalgebra (S : VonNeumannAlgebra H) :
    (S.toStarSubalgebra : Set (H →L[ℂ] H)) = S :=
  rfl

@[simp]
/-
**VonNeumannAlgebra.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `VonNeumannAlgebra`。
形式化陈述：coe_mk (S : StarSubalgebra Complex (H ->L[Complex] H)) (h) : ((⟨S, h⟩ : Vo
nNeumannAlgebra H) : Set (H ->L[Complex] H)) = S
参数：S : StarSubalgebra Complex (H ->L[Complex] H)；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.instStarModuleId`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
-/
theorem coe_mk (S : StarSubalgebra ℂ (H →L[ℂ] H)) (h) :
    ((⟨S, h⟩ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = S :=
  rfl

@[ext]
/-
**VonNeumannAlgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `VonNeumannAlgebra`。
形式化陈述：ext {S T : VonNeumannAlgebra H} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {S T : VonNeumannAlgebra H} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
/-
**VonNeumannAlgebra.centralizer_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `VonNeuman
nAlgebra`。
形式化陈述：centralizer_centralizer (S : VonNeumannAlgebra H) : Set.centralizer (Set.c
entralizer (S : Set (H ->L[Complex] H))) = S
参数：S : VonNeumannAlgebra H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VonNeumannAlgebra.centralizer_centralizer'`：∀ {H : Type u} [inst : Norme
dAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H]   (
self : VonNeumannAlgebra H), sel…
-/
theorem centralizer_centralizer (S : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S :=
  S.centralizer_centralizer'

/-- The centralizer of a `VonNeumannAlgebra`, as a `VonNeumannAlgebra`. -/
/-
**VonNeumannAlgebra.commutant** 是 Mathlib 中的一个定义，位于命名空间 `VonNeumannAlgebra`。
形式化陈述：commutant (S : VonNeumannAlgebra H) : VonNeumannAlgebra H where toStarSuba
lgebra
参数：S : VonNeumannAlgebra H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.instStarModuleId`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…

--- 原说明 ---
The centralizer of a `VonNeumannAlgebra`, as a `VonNeumannAlgebra`.
-/
noncomputable def commutant (S : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by simp

@[simp]
/-
**VonNeumannAlgebra.coe_commutant** 是 Mathlib 中的一个定理，位于命名空间 `VonNeumannAlgebra`。
形式化陈述：coe_commutant (S : VonNeumannAlgebra H) : ↑S.commutant = Set.centralizer (
S : Set (H ->L[Complex] H))
参数：S : VonNeumannAlgebra H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `StarMemClass.star_coe_eq`：StarMemClass.star_coe_eq {S α : Type*} [Involu
tiveStar α] [SetLike S α] [StarMemClass S α] (s : S) : star (s : Set α) = s
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_commutant (S : VonNeumannAlgebra H) :
    ↑S.commutant = Set.centralizer (S : Set (H →L[ℂ] H)) := by
  simp [commutant]

@[simp]
/-
**VonNeumannAlgebra.mem_commutant_iff** 是 Mathlib 中的一个定理，位于命名空间 `VonNeumannAlgeb
ra`。
形式化陈述：mem_commutant_iff {S : VonNeumannAlgebra H} {z : H ->L[Complex] H} : z in 
S.commutant ↔ forall g in S, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `VonNeumannAlgebra.coe_commutant`：coe_commutant (S : VonNeumannAlgebra H)
 : ↑S.commutant = Set.centralizer (S : Set (H ->L[Complex] H))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_commutant_iff {S : VonNeumannAlgebra H} {z : H →L[ℂ] H} :
    z ∈ S.commutant ↔ ∀ g ∈ S, g * z = z * g := by
  rw [← SetLike.mem_coe, coe_commutant]
  rfl

@[simp]
/-
**VonNeumannAlgebra.commutant_commutant** 是 Mathlib 中的一个定理，位于命名空间 `VonNeumannAlg
ebra`。
形式化陈述：commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S
参数：S : VonNeumannAlgebra H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VonNeumannAlgebra.coe_commutant`：coe_commutant (S : VonNeumannAlgebra H)
 : ↑S.commutant = Set.centralizer (S : Set (H ->L[Complex] H))
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `VonNeumannAlgebra.centralizer_centralizer`：centralizer_centralizer (S : 
VonNeumannAlgebra H) : Set.centralizer (Set.centralizer (S : Set (H ->L[Complex]
 H))) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S :=
  SetLike.coe_injective <| by simp

open ContinuousLinearMap in
/-- An idempotent is an element in a von Neumann algebra if and only if
its range and kernel are invariant under the commutant. -/
/-
**VonNeumannAlgebra.IsIdempotentElem.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `VonNeuma
nnAlgebra.IsIdempotentElem`。
形式化陈述：∀ {H : Type u} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ
 H] [inst_2 : CompleteSpace H]   {e : H →L[ℂ] H},   IsIdempotentElem e →     ∀ (
S : VonNeumannAlgebra H),       e ∈ S ↔ ∀ y ∈ S.commutant, (↑e).range ∈ Module.E
nd.invtSubmodule ↑y ∧ (↑e).ker ∈ Module.End.invtSubmodule ↑y
参数：S : VonNeumannAlgebra H；↑e；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.IsIdempotentElem.commute_iff`：commute_iff {f T : M -
>L[R] M} (hf : IsIdempotentElem f) : Commute f T ↔ (f.range in Module.End.invtSu
bmodule T ∧ f.ker in Module.End.invtSu…
· 使用定理 `Commute.symm_iff`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b
 ↔ Commute b a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VonNeumannAlgebra.commutant_commutant`：commutant_commutant (S : VonNeuma
nnAlgebra H) : S.commutant.commutant = S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An idempotent is an element in a von Neumann algebra if and only if
its range and kernel are invariant under the commutant.
-/
theorem IsIdempotentElem.mem_iff {e : H →L[ℂ] H} (h : IsIdempotentElem e)
    (S : VonNeumannAlgebra H) :
    e ∈ S ↔ ∀ y ∈ S.commutant,
      e.range ∈ Module.End.invtSubmodule y ∧ e.ker ∈ Module.End.invtSubmodule y := by
  conv_rhs => simp [← h.commute_iff, Commute.symm_iff (a := e), commute_iff_eq, ← mem_commutant_iff]

open VonNeumannAlgebra ContinuousLinearMap in
/-- A star projection is an element in a von Neumann algebra if and only if
its range is invariant under the commutant. -/
/-
**VonNeumannAlgebra.IsStarProjection.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `VonNeuma
nnAlgebra.IsStarProjection`。
形式化陈述：∀ {H : Type u} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ
 H] [inst_2 : CompleteSpace H]   {e : H →L[ℂ] H},   IsStarProjection e → ∀ (S : 
VonNeumannAlgebra H), e ∈ S ↔ ∀ y ∈ S.commutant, (↑e).range ∈ Module.End.invtSub
module ↑y
参数：S : VonNeumannAlgebra H；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VonNeumannAlgebra.IsIdempotentElem.mem_iff`：∀ {H : Type u} [inst : Norme
dAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H]   {
e : H →L[ℂ] H},   IsIdempotentEl…
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff`：range_
mem_invtSubmodule_iff {f T : M ->L[R] M} (hf : IsIdempotentElem f) : f.range in 
Module.End.invtSubmodule T ↔ f ∘L T ∘L f = T ∘L f
· 使用引理 `ContinuousLinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff`：ker_mem_
invtSubmodule_iff {f T : M ->L[R] M} (hf : IsIdempotentElem f) : f.ker in Module
.End.invtSubmodule T ↔ f ∘L T ∘L f = f ∘L T
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s

--- 原说明 ---
A star projection is an element in a von Neumann algebra if and only if
its range is invariant under the commutant.
-/
theorem IsStarProjection.mem_iff {e : H →L[ℂ] H} (he : IsStarProjection e)
    (S : VonNeumannAlgebra H) :
    e ∈ S ↔ ∀ y ∈ S.commutant, e.range ∈ Module.End.invtSubmodule y := by
  simp_rw [he.isIdempotentElem.mem_iff, he.isIdempotentElem.range_mem_invtSubmodule_iff,
    he.isIdempotentElem.ker_mem_invtSubmodule_iff, forall_and, and_iff_left_iff_imp, ← mul_def]
  intro h x hx
  simpa [he.isSelfAdjoint.star_eq] using! congr(star $(h _ (star_mem hx)))

end VonNeumannAlgebra

