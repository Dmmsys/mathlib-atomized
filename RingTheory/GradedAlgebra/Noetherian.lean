/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The properties of a graded Noetherian ring.

This file proves that the 0-th grade of a Noetherian ring is
also a Noetherian ring.
-/

public section

variable {ι A σ : Type*}
variable [Ring A] [IsNoetherianRing A]
variable [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

namespace GradedRing

/-- If the internally graded ring `A` is Noetherian, then `𝒜 0` is a Noetherian ring. -/
/-
**GradedRing.GradeZero.isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 `GradedRing.Gr
adeZero`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : Ring A] [IsNoetheri
anRing A] [inst_2 : DecidableEq ι]   [inst_3 : AddCommMonoid ι] [inst_4 : Partia
lOrder ι] [CanonicallyOrderedAdd ι] [inst_6 : SetLike σ A]   [inst_7 : AddSubgro
upClass σ A] (𝒜 : ι → σ) [inst_8 : GradedRing 𝒜], IsNoetherianRing ↥(𝒜 0)
参数：𝒜 : ι → σ；𝒜 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `isNoetherianRing_of_surjective`：isNoetherianRing_of_surjective (R) [Semi
ring R] (S) [Semiring S] (f : R ->+* S) (hf : Function.Surjective f) [H : IsNoet
herianRing R] : IsNo…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `GradedRing.projZeroRingHom'_surjective`：∀ {ι : Type u_1} {A : Type u_3} 
{σ : Type u_4} [inst : Semiring A] [inst_1 : DecidableEq ι] [inst_2 : AddCommMon
oid ι]   [inst_3 : PartialOr…

--- 原说明 ---
If the internally graded ring `A` is Noetherian, then `𝒜 0` is a Noetherian ring
.
-/
instance GradeZero.isNoetherianRing : IsNoetherianRing (𝒜 0) :=
  isNoetherianRing_of_surjective
    A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜) (GradedRing.projZeroRingHom'_surjective 𝒜)

end GradedRing

