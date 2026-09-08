/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Xavier Roblot
-/
module

public import Mathlib.Data.Int.Associated
public import Mathlib.Data.Int.NatAbs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # Cardinal of quotient of free finite `ℤ`-modules by submodules of full rank

## Main results

* `Submodule.natAbs_det_basis_change`: let `b` be a `ℤ`-basis for a module `M` over `ℤ` and
  let `bN` be a basis for a submodule `N` of the same dimension. Then the cardinal of `M ⧸ N`
  is given by taking the determinant of `bN` over `b`.

-/

public section

open Module Submodule

section Submodule

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- Let `e : M ≃ N` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the cardinality of the quotient `M ⧸ N` is given by taking
the determinant of `e`.
See `natAbs_det_basis_change` for a more familiar formulation of this result. -/
/-
**Submodule.natAbs_det_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.natAbs_det_equiv (N : Submodule Int M) {E : Type*} [EquivLike E 
M N] [AddEquivClass E M N] (e : E) : Int.natAbs (LinearMap.det (N.subtype ∘ₗ Add
MonoidHom.toIntLinearMap (e : M ->+ N))) = Nat.card (M ⧸ N)
参数：N : Submodule Int M；e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.smithNormalFormBotBasis_def`：Submodule.smithNormalFormBotBasis
_def (b : Basis ι R M) (h : Module.finrank R N = Module.finrank R M) : forall i,
 (smithNormalFormBotBasis b…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `Equiv.refl_apply`：∀ {α : Sort u} (x : α), (Equiv.refl α) x = x
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Let `e : M ≃ N` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the cardinality of the quotient `M ⧸ N` is gi
ven by taking
the determinant of `e`.
See `natAbs_det_basis_change` for a more familiar formulation of this result.
-/
theorem Submodule.natAbs_det_equiv (N : Submodule ℤ M) {E : Type*} [EquivLike E M N]
    [AddEquivClass E M N] (e : E) :
    Int.natAbs
      (LinearMap.det
        (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M →+ N))) =
      Nat.card (M ⧸ N) := by
  let b := Module.Free.chooseBasis ℤ M
  -- Since `e : M ≃ₗ[ℤ] N`, the submodule `N` has full rank.
  have h : Module.finrank ℤ N = Module.finrank ℤ M :=
    (AddEquiv.toIntLinearEquiv e : M ≃ₗ[ℤ] N).symm.finrank_eq
  -- Use the Smith normal form to choose a nice basis for `N`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[ℤ] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[ℤ] M := N.subtype.comp (e' : M →ₗ[ℤ] N)
  let f_apply : ∀ x, f x = b'.equiv ab (Equiv.refl _) x := fun x ↦ rfl
  suffices (LinearMap.det f).natAbs = Nat.card (M ⧸ N) by
    calc
      _ = (LinearMap.det (N.subtype ∘ₗ
            (AddEquiv.toIntLinearEquiv e : M ≃ₗ[ℤ] N))).natAbs := rfl
      _ = (LinearMap.det (N.subtype ∘ₗ _)).natAbs :=
            Int.natAbs_eq_iff_associated.mpr (LinearMap.associated_det_comp_equiv _ _ _)
      _ = Nat.card (M ⧸ N) := this
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    rw [f_apply, b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  calc
    Int.natAbs (LinearMap.det f) = Int.natAbs (LinearMap.toMatrix b' b' f).det := by
      rw [LinearMap.det_toMatrix]
    _ = Int.natAbs (Matrix.diagonal a).det := ?_
    _ = Int.natAbs (∏ i, a i) := by rw [Matrix.det_diagonal]
    _ = ∏ i, Int.natAbs (a i) := map_prod Int.natAbsHom a Finset.univ
    _ = Nat.card (M ⧸ N) := ?_
  -- since `LinearMap.toMatrix b' b' f` is the diagonal matrix with `a` along the diagonal.
  · congr 2; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  -- Now we map everything through the linear equiv `M ≃ₗ (ι → ℤ)`,
  -- which maps `(M ⧸ N)` to `Π i, ZMod (a i).nat_abs`.
  simp_rw [Nat.card_congr (quotientEquivPiZMod N b h).toEquiv, Nat.card_pi, Nat.card_zmod, a]

/-- Let `b` be a basis for `M` over `ℤ` and `bN` a basis for `N` over `ℤ` of the same dimension.
Then an alternative way to compute the cardinality of `M ⧸ N` is given by taking the determinant
of `bN` over `b`. -/
/-
**Submodule.natAbs_det_basis_change** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] 
(b : Basis ι Int M) (N : Submodule Int M) (bN : Basis ι Int N) : (b.det ((↑) ∘ b
N)).natAbs = Nat.card (M ⧸ N)
参数：b : Basis ι Int M；N : Submodule Int M；bN : Basis ι Int N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_comp_basis`：det_comp_basis [Module A M'] (b : Basis ι A
 M) (b' : Basis ι A M') (f : M ->ₗ[A] M') : b'.det (f ∘ b) = LinearMap.det (f ∘ₗ
 (b'.equiv b (Equ…
· 使用定理 `Submodule.natAbs_det_equiv`：Submodule.natAbs_det_equiv (N : Submodule In
t M) {E : Type*} [EquivLike E M N] [AddEquivClass E M N] (e : E) : Int.natAbs (L
inearMap.det (N.…
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…

--- 原说明 ---
Let `b` be a basis for `M` over `ℤ` and `bN` a basis for `N` over `ℤ` of the sam
e dimension.
Then an alternative way to compute the cardinality of `M ⧸ N` is given by taking
 the determinant
of `bN` over `b`.
-/
theorem Submodule.natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (b.det ((↑) ∘ bN)).natAbs = Nat.card (M ⧸ N) := by
  let e := b.equiv bN (Equiv.refl _)
  calc
    (b.det (N.subtype ∘ bN)).natAbs = (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[ℤ] N))).natAbs := by
      rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv N e

end Submodule

section AddSubgroup

/-
**AddSubgroup.index_eq_natAbs_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.index_eq_natAbs_det {E : Type*} [AddCommGroup E] {ι : Type*} [
DecidableEq ι] [Fintype ι] (bE : Basis ι Int E) (N : AddSubgroup E) (bN : Basis 
ι Int N) : N.index = (bE.det (bN ·)).natAbs
参数：bE : Basis ι Int E；N : AddSubgroup E；bN : Basis ι Int N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.natAbs_det_basis_change`：Submodule.natAbs_det_basis_change {ι 
: Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int M) (N : Submodule Int M) (
bN : Basis ι Int N) : (…
-/
theorem AddSubgroup.index_eq_natAbs_det {E : Type*} [AddCommGroup E] {ι : Type*}
    [DecidableEq ι] [Fintype ι] (bE : Basis ι ℤ E) (N : AddSubgroup E) (bN : Basis ι ℤ N) :
    N.index = (bE.det (bN ·)).natAbs :=
  have : Module.Free ℤ E := Module.Free.of_basis bE
  have : Module.Finite ℤ E := Module.Finite.of_basis bE
  (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AddSubgroup.relIndex_eq_natAbs_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.relIndex_eq_natAbs_det {E : Type*} [AddCommGroup E] (L₁ L₂ : A
ddSubgroup E) (H : L₁ <= L₂) {ι : Type*} [DecidableEq ι] [Fintype ι] (b₁ : Basis
 ι Int L₁.toIntSubmodule) (b₂ : Basis ι Int L₂.toIntSubmodule) : L₁.relIndex L₂ 
= (b₂.det (fun i => ⟨b₁ i, (H (SetLike.coe_mem _))⟩)).natAbs
参数：L₁ L₂ : AddSubgroup E；H : L₁ <= L₂；b₁ : Basis ι Int L₁.toIntSubmodule；b₂ : Ba
sis ι Int L₂.toIntSubmodule。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : AddGroup G] (H K : A
ddSubgroup G), H.relIndex K = (H.addSubgroupOf K).index
· 使用定理 `AddSubgroup.index_eq_natAbs_det`：AddSubgroup.index_eq_natAbs_det {E : Ty
pe*} [AddCommGroup E] {ι : Type*} [DecidableEq ι] [Fintype ι] (bE : Basis ι Int 
E) (N : AddSubgroup E…
-/
theorem AddSubgroup.relIndex_eq_natAbs_det {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Basis ι ℤ L₁.toIntSubmodule) (b₂ : Basis ι ℤ L₂.toIntSubmodule) :
    L₁.relIndex L₂ = (b₂.det (fun i ↦ ⟨b₁ i, (H (SetLike.coe_mem _))⟩)).natAbs := by
  rw [relIndex, index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AddSubgroup.relIndex_eq_abs_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.relIndex_eq_abs_det {E : Type*} [AddCommGroup E] [Module Rat E
] (L₁ L₂ : AddSubgroup E) (H : L₁ <= L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
 (b₁ b₂ : Basis ι Rat E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure
 (Set.range b₂)) : L₁.relIndex L₂ = |b₂.det b₁|
参数：L₁ L₂ : AddSubgroup E；H : L₁ <= L₂；b₁ b₂ : Basis ι Rat E；h₁ : L₁ = .closure (
Set.range b₁)；h₂ : L₂ = .closure (Set.range b₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.relIndex_eq_natAbs_det`：AddSubgroup.relIndex_eq_natAbs_det {
E : Type*} [AddCommGroup E] (L₁ L₂ : AddSubgroup E) (H : L₁ <= L₂) {ι : Type*} [
DecidableEq ι] [Fintype …
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.addSubgroupOfClosure_apply`：∀ {M : Type u_7} {R : Type u_8}
 [inst : Ring R] [inst_1 : Nontrivial R] [inst_2 : IsAddTorsionFree R]   [inst_3
 : AddCommGroup M] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Module.Basis.addSubgroupOfClosure_repr_apply`：∀ {M : Type u_7} {R : Type
 u_8} [inst : Ring R] [inst_1 : Nontrivial R] [inst_2 : IsAddTorsionFree R]   [i
nst_3 : AddCommGroup M] [inst_4 : …
（共 31 条，此处仅展示前 30 条）
-/
theorem AddSubgroup.relIndex_eq_abs_det {E : Type*} [AddCommGroup E] [Module ℚ E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    L₁.relIndex L₂ = |b₂.det b₁| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
    (b₂.addSubgroupOfClosure L₂ h₂), Nat.cast_natAbs, Int.cast_abs]
  change |algebraMap ℤ ℚ _| = _
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr; ext
  simp [Basis.toMatrix_apply]

end AddSubgroup

