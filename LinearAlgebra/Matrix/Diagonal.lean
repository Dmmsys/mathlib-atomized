/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear map
-/

public section


noncomputable section

open LinearMap Matrix Set Submodule Matrix

universe u v w

namespace Matrix

section CommSemiring

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type v} [CommSemiring R]

/-
**Matrix.proj_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：proj_diagonal (i : n) (w : n -> R) : (proj i).comp (toLin' (diagonal w)) =
 w i • proj i
参数：i : n；w : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
-/
theorem proj_diagonal (i : n) (w : n → R) : (proj i).comp (toLin' (diagonal w)) = w i • proj i :=
  LinearMap.ext fun _ => mulVec_diagonal _ _ _
/-
**Matrix.diagonal_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_comp_single (w : n -> R) (i : n) : (diagonal w).toLin'.comp (Line
arMap.single R (fun _ : n => R) i) = w i • LinearMap.single R (fun _ : n => R) i
参数：w : n -> R；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagonal_mulVec_single`：diagonal_mulVec_single [Fintype n] [Decid
ableEq n] [NonUnitalNonAssocSemiring R] (v : n -> R) (j : n) (x : R) : diagonal 
v *ᵥ Pi.single j x …
· 使用定理 `Pi.single_smul'`：single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMul
Action α β] [DecidableEq I] (i : I) (r : α) (x : β) : single (M
-/
theorem diagonal_comp_single (w : n → R) (i : n) :
    (diagonal w).toLin'.comp (LinearMap.single R (fun _ : n => R) i) =
      w i • LinearMap.single R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)
/-
**Matrix.diagonal_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_toLin' (w : n -> R) : toLin' (diagonal w) = LinearMap.pi fun i =>
 w i • LinearMap.proj i
参数：w : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
-/
theorem diagonal_toLin' (w : n → R) :
    toLin' (diagonal w) = LinearMap.pi fun i => w i • LinearMap.proj i :=
  LinearMap.ext fun _ => funext fun _ => mulVec_diagonal _ _ _

end CommSemiring

section Semifield

variable {m : Type*} [Fintype m] {K : Type u} [Semifield K]

-- maybe try to relax the universe constraint
/-
**Matrix.ker_diagonal_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ker_diagonal_toLin' [DecidableEq m] (w : m -> K) : ker (toLin' (diagonal w
)) = ⨆ i in { i | w i = 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i)
参数：w : m -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.comap_iInf`：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι
 -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.proj_diagonal`：proj_diagonal (i : n) (w : n -> R) : (proj i).comp
 (toLin' (diagonal w)) = w i • proj i
· 使用定理 `LinearMap.ker_smul'`：ker_smul' (f : V ->ₗ[K] V₂) (a : K) : ker (a • f) =
 ⨅ _ : a != 0, ker f
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearMap.iSup_range_single_eq_iInf_ker_proj`：iSup_range_single_eq_iInf_
ker_proj {I J : Set ι} (hIJ : IsCompl I J) (hI : I.Finite) : ⨆ i in I, range (si
ngle R φ i) = ⨅ i in J, ker (proj …
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem ker_diagonal_toLin' [DecidableEq m] (w : m → K) :
    ker (toLin' (diagonal w)) =
      ⨆ i ∈ { i | w i = 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) := by
  rw [← comap_bot]
  simpa [← ker_comp, proj_diagonal, ker_smul', ← iInf_ker_proj] using
    (iSup_range_single_eq_iInf_ker_proj K _ isCompl_compl {i | w i = 0}.toFinite).symm
/-
**Matrix.range_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：range_diagonal [DecidableEq m] (w : m -> K) : LinearMap.range (toLin' (dia
gonal w)) = ⨆ i in { i | w i != 0 }, LinearMap.range (LinearMap.single K (fun _ 
=> K) i)
参数：w : m -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.iSup_range_single`：iSup_range_single [Finite ι] : ⨆ i, range (
single R φ i) = ⊤
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Matrix.diagonal_comp_single`：diagonal_comp_single (w : n -> R) (i : n) :
 (diagonal w).toLin'.comp (LinearMap.single R (fun _ : n => R) i) = w i • Linear
Map.single R (fun…
· 使用定理 `LinearMap.range_smul'`：range_smul' (f : V ->ₗ[K] V₂) (a : K) : range (a 
• f) = ⨆ _ : a != 0, range f
-/
theorem range_diagonal [DecidableEq m] (w : m → K) :
    LinearMap.range (toLin' (diagonal w)) =
      ⨆ i ∈ { i | w i ≠ 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) := by
  dsimp only [mem_ofPred_eq]
  rw [← Submodule.map_top, ← iSup_range_single, Submodule.map_iSup]
  congr; funext i
  rw [← LinearMap.range_comp, diagonal_comp_single, ← range_smul']

end Semifield

end Matrix

namespace LinearMap

section Field

variable {m : Type*} [Fintype m] {K : Type u} [Field K]

/-
**LinearMap.rank_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_diagonal [DecidableEq m] [DecidableEq K] (w : m -> K) : LinearMap.ran
k (toLin' (diagonal w)) = Fintype.card { i // w i != 0 }
参数：w : m -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
· 使用定理 `LinearMap.iSup_range_single_eq_iInf_ker_proj`：iSup_range_single_eq_iInf_
ker_proj {I J : Set ι} (hIJ : IsCompl I J) (hI : I.Finite) : ⨆ i in I, range (si
ngle R φ i) = ⨅ i in J, ker (proj …
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rank.eq_1`：∀ {K : Type u} {V : Type v} {V' : Type v'} [inst : 
Semiring K] [inst_1 : AddCommMonoid V] [inst_2 : _root_.Module K V]   [inst_3 : 
AddCommMo…
· 使用定理 `Matrix.range_diagonal`：range_diagonal [DecidableEq m] (w : m -> K) : Lin
earMap.range (toLin' (diagonal w)) = ⨆ i in { i | w i != 0 }, LinearMap.range (L
inearMap.si…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_fun'`：rank_fun' : Module.rank R (η -> R) = Fintype.card η
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Codisjoint.top_le`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → ⊤ ≤ a ⊔ b
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem rank_diagonal [DecidableEq m] [DecidableEq K] (w : m → K) :
    LinearMap.rank (toLin' (diagonal w)) = Fintype.card { i // w i ≠ 0 } := by
  have hIJ : IsCompl { i : m | w i ≠ 0 } { i : m | w i = 0 } := isCompl_compl.symm
  have B₁ := iSup_range_single_eq_iInf_ker_proj K (fun _ : m => K) hIJ (Set.toFinite _)
  rw [LinearMap.rank, range_diagonal, B₁, ← @rank_fun' K]
  exact iInfKerProjEquiv K (fun _ ↦ K) hIJ.disjoint hIJ.codisjoint.top_le |>.rank_eq

end Field

end LinearMap

