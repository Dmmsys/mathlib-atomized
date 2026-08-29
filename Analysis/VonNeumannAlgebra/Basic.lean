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

/--
Definition of `WStarAlgebra` / `WStarAlgebra` 的定义

English:
class WStarAlgebra
  parameters: (M : Type u) [CStarAlgebra M]
  axioms and operations (1):
    - exists_predual : exists (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace Complex X) (_ : CompleteSpace X), Nonempty (StrongDual Complex X ≃ₗᵢ⋆[Complex] M)

中文:
类 WStarAlgebra
  参数: (M : 类型u) [CStarAlgebra M]
  公理与运算 (1 个):
    - exists_predual : 存在 (X : 类型u) (_ : NormedAddCommGroup X) (_ : NormedSpace Complex X) (_ : CompleteSpace X), Nonempty (StrongDual Complex X ≃ₗᵢ⋆[Complex] M)
-/
class WStarAlgebra (M : Type u) [CStarAlgebra M] : Prop where
  /-- There is a Banach space `X` whose dual is isometrically (conjugate-linearly) isomorphic
  to the `WStarAlgebra`. -/
  exists_predual :
    exists (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace Complex X) (_ : CompleteSpace X),
      Nonempty (StrongDual Complex X ≃ₗᵢ⋆[Complex] M)

-- TODO: Without this, `VonNeumannAlgebra` times out. Why?
/--
Definition of `VonNeumannAlgebra` / `VonNeumannAlgebra` 的定义

English:
structure VonNeumannAlgebra
  parameters: (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
  extends: StarSubalgebra Complex (H ->L[Complex] H)
  axioms and operations (1):
    - centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier

中文:
结构 VonNeumannAlgebra
  参数: (H : 类型u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
  继承: StarSubalgebra Complex (H ->L[Complex] H)
  公理与运算 (1 个):
    - centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier
-/
structure VonNeumannAlgebra (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [CompleteSpace H] extends StarSubalgebra Complex (H ->L[Complex] H) where
  /-- The double commutant (a.k.a. centralizer) of a `VonNeumannAlgebra` is itself. -/
  centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier

/-- Consider a von Neumann algebra acting on a Hilbert space `H` as a \*-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc VonNeumannAlgebra.toStarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [CompleteSpace H]

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (VonNeumannAlgebra H) (H ->L[Complex] H) where
  body: S.carrier
  coe_injective S T h := by obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := S; cases T; congr

中文:
实例 instSetLike
  签名: : SetLike (VonNeumannAlgebra H) (H ->L[Complex] H) where
  定义体: S.carrier
  coe_injective S T h := by obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := S; cases T; congr

Depends on / 依赖: S.carrier, carrier
-/
instance instSetLike : SetLike (VonNeumannAlgebra H) (H ->L[Complex] H) where
  coe S := S.carrier
  coe_injective S T h := by obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := S; cases T; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (VonNeumannAlgebra H)
  body: .ofSetLike (VonNeumannAlgebra H) (H ->L[Complex] H)

中文:
实例 :
  签名: PartialOrder (VonNeumannAlgebra H)
  定义体: .ofSetLike (VonNeumannAlgebra H) (H ->L[Complex] H)

Depends on / 依赖: VonNeumannAlgebra, ofSetLike
-/
instance : PartialOrder (VonNeumannAlgebra H) := .ofSetLike (VonNeumannAlgebra H) (H ->L[Complex] H)

/--
Instance `instStarMemClass` / 实例 `instStarMemClass`

English:
instance instStarMemClass
  signature: : StarMemClass (VonNeumannAlgebra H) (H ->L[Complex] H) where
  body: s.star_mem'

中文:
实例 instStarMemClass
  签名: : StarMemClass (VonNeumannAlgebra H) (H ->L[Complex] H) where
  定义体: s.star_mem'

Depends on / 依赖: s.star_mem, star_mem
-/
noncomputable instance instStarMemClass : StarMemClass (VonNeumannAlgebra H) (H ->L[Complex] H) where
  star_mem {s} := s.star_mem'

/--
Instance `instSubringClass` / 实例 `instSubringClass`

English:
instance instSubringClass
  signature: : SubringClass (VonNeumannAlgebra H) (H ->L[Complex] H) where
  body: s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} a ha := show -a in s.toStarSubalgebra from neg_mem ha

@[simp]

中文:
实例 instSubringClass
  签名: : SubringClass (VonNeumannAlgebra H) (H ->L[Complex] H) where
  定义体: s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} a ha := show -a in s.toStarSubalgebra from neg_mem ha

@[simp]

Depends on / 依赖: add_mem, s.add_mem
-/
instance instSubringClass : SubringClass (VonNeumannAlgebra H) (H ->L[Complex] H) where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} a ha := show -a in s.toStarSubalgebra from neg_mem ha

@[simp]
/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {S : VonNeumannAlgebra H} {x : H ->L[Complex] H}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_carrier
  条件: {S : VonNeumannAlgebra H} {x : H ->L[Complex] H}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {S : VonNeumannAlgebra H} {x : H ->L[Complex] H} :
    x in S.toStarSubalgebra ↔ x in (S : Set (H ->L[Complex] H)) :=
  Iff.rfl

@[simp]
/--
theorem `coe_toStarSubalgebra` / 定理 `coe_toStarSubalgebra`

English:
theorem coe_toStarSubalgebra
  given: (S : VonNeumannAlgebra H)
  proof: rfl

@[simp]

中文:
定理 coe_toStarSubalgebra
  条件: (S : VonNeumannAlgebra H)
  证明: rfl

@[simp]
-/
theorem coe_toStarSubalgebra (S : VonNeumannAlgebra H) :
    (S.toStarSubalgebra : Set (H ->L[Complex] H)) = S :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (S : StarSubalgebra Complex (H ->L[Complex] H)) (h)
  proof: rfl

@[ext]

中文:
定理 coe_mk
  条件: (S : StarSubalgebra Complex (H ->L[Complex] H)) (h)
  证明: rfl

@[ext]
-/
theorem coe_mk (S : StarSubalgebra Complex (H ->L[Complex] H)) (h) :
    ((⟨S, h⟩ : VonNeumannAlgebra H) : Set (H ->L[Complex] H)) = S :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : VonNeumannAlgebra H} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: {S T : VonNeumannAlgebra H} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : VonNeumannAlgebra H} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

@[simp]
/--
theorem `centralizer_centralizer` / 定理 `centralizer_centralizer`

English:
theorem centralizer_centralizer
  given: (S : VonNeumannAlgebra H)
  proof: S.centralizer_centralizer'

中文:
定理 centralizer_centralizer
  条件: (S : VonNeumannAlgebra H)
  证明: S.centralizer_centralizer'

Depends on / 依赖: S.centralizer_centralizer, centralizer_centralizer
-/
theorem centralizer_centralizer (S : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (S : Set (H ->L[Complex] H))) = S :=
  S.centralizer_centralizer'

/--
Definition of `commutant` / `commutant` 的定义

English:
definition commutant
  signature: (S : VonNeumannAlgebra H)
  body: StarSubalgebra.centralizer Complex (S : Set (H ->L[Complex] H))
  centralizer_centralizer' := by simp

@[simp]

中文:
定义 commutant
  签名: (S : VonNeumannAlgebra H)
  定义体: StarSubalgebra.centralizer Complex (S : Set (H ->L[Complex] H))
  centralizer_centralizer' := by simp

@[simp]

Depends on / 依赖: StarSubalgebra, StarSubalgebra.centralizer, centralizer
-/
noncomputable def commutant (S : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer Complex (S : Set (H ->L[Complex] H))
  centralizer_centralizer' := by simp

@[simp]
/--
theorem `coe_commutant` / 定理 `coe_commutant`

English:
theorem coe_commutant
  given: (S : VonNeumannAlgebra H)
  proof: by
  simp [commutant]

@[simp]

中文:
定理 coe_commutant
  条件: (S : VonNeumannAlgebra H)
  证明: by
  simp [commutant]

@[simp]

Depends on / 依赖: commutant
-/
theorem coe_commutant (S : VonNeumannAlgebra H) :
    ↑S.commutant = Set.centralizer (S : Set (H ->L[Complex] H)) := by
  simp [commutant]

@[simp]
/--
theorem `mem_commutant_iff` / 定理 `mem_commutant_iff`

English:
theorem mem_commutant_iff
  given: {S : VonNeumannAlgebra H} {z : H ->L[Complex] H}
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_commutant]
  rfl

@[simp]

中文:
定理 mem_commutant_iff
  条件: {S : VonNeumannAlgebra H} {z : H ->L[Complex] H}
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_commutant]
  rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_commutant, mem_coe
-/
theorem mem_commutant_iff {S : VonNeumannAlgebra H} {z : H ->L[Complex] H} :
    z in S.commutant ↔ forall g in S, g * z = z * g := by
  rw [← SetLike.mem_coe]; rw [coe_commutant]
  rfl

@[simp]
/--
theorem `commutant_commutant` / 定理 `commutant_commutant`

English:
theorem commutant_commutant
  given: (S : VonNeumannAlgebra H)
  statement: S.commutant.commutant = S
  proof: SetLike.coe_injective by simp

中文:
定理 commutant_commutant
  条件: (S : VonNeumannAlgebra H)
  结论: S.commutant.commutant = S
  证明: SetLike.coe_injective by simp

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S :=
SetLike.coe_injective by simp

open ContinuousLinearMap in
/--
theorem `IsIdempotentElem.mem_iff` / 定理 `IsIdempotentElem.mem_iff`

English:
theorem IsIdempotentElem.mem_iff
  statement: {e : H ->L[Complex] H} (h : IsIdempotentElem e)
  proof: by
  conv_rhs => simp [← h.commute_iff, Commute.symm_iff (a := e), commute_iff_eq, ← mem_commutant_iff]

中文:
定理 IsIdempotentElem.mem_iff
  结论: {e : H ->L[Complex] H} (h : IsIdempotentElem e)
  证明: by
  conv_rhs => simp [← h.commute_iff, Commute.symm_iff (a := e), commute_iff_eq, ← mem_commutant_iff]

Depends on / 依赖: Commute, Commute.symm_iff, commute_iff, commute_iff_eq, conv_rhs, h.commute_iff, mem_commutant_iff, symm_iff
-/
theorem IsIdempotentElem.mem_iff {e : H ->L[Complex] H} (h : IsIdempotentElem e)
    (S : VonNeumannAlgebra H) :
    e in S ↔ forall y in S.commutant,
      e.range in Module.End.invtSubmodule y ∧ e.ker in Module.End.invtSubmodule y := by
  conv_rhs => simp [← h.commute_iff, Commute.symm_iff (a := e), commute_iff_eq, ← mem_commutant_iff]

open VonNeumannAlgebra ContinuousLinearMap in
/--
theorem `IsStarProjection.mem_iff` / 定理 `IsStarProjection.mem_iff`

English:
theorem IsStarProjection.mem_iff
  statement: {e : H ->L[Complex] H} (he : IsStarProjection e)
  proof: by
  simp_rw [he.isIdempotentElem.mem_iff, he.isIdempotentElem.range_mem_invtSubmodule_iff,
    he.isIdempotentElem.ker_mem_invtSubmodule_iff, forall_and, and_iff_left_iff_imp, ← mul_def]
  intro h x hx
  simpa [he.isSelfAdjoint.star_eq] using! congr(star $(h _ (star_mem hx)))

中文:
定理 IsStarProjection.mem_iff
  结论: {e : H ->L[Complex] H} (he : IsStarProjection e)
  证明: by
  simp_rw [he.isIdempotentElem.mem_iff, he.isIdempotentElem.range_mem_invtSubmodule_iff,
    he.isIdempotentElem.ker_mem_invtSubmodule_iff, forall_and, and_iff_left_iff_imp, ← mul_def]
  intro h x hx
  simpa [he.isSelfAdjoint.star_eq] using! congr(star $(h _ (star_mem hx)))

Depends on / 依赖: and_iff_left_iff_imp, forall_and, he.isIdempotentElem.ker_mem_invtSubmodule_iff, he.isIdempotentElem.mem_iff, he.isIdempotentElem.range_mem_invtSubmodule_iff, he.isSelfAdjoint.star_eq, isIdempotentElem, isSelfAdjoint, ker_mem_invtSubmodule_iff, mem_iff, mul_def, range_mem_invtSubmodule_iff, simp_rw, star_eq, star_mem
-/
theorem IsStarProjection.mem_iff {e : H ->L[Complex] H} (he : IsStarProjection e)
    (S : VonNeumannAlgebra H) :
    e in S ↔ forall y in S.commutant, e.range in Module.End.invtSubmodule y := by
  simp_rw [he.isIdempotentElem.mem_iff, he.isIdempotentElem.range_mem_invtSubmodule_iff,
    he.isIdempotentElem.ker_mem_invtSubmodule_iff, forall_and, and_iff_left_iff_imp, ← mul_def]
  intro h x hx
  simpa [he.isSelfAdjoint.star_eq] using! congr(star $(h _ (star_mem hx)))

end VonNeumannAlgebra
