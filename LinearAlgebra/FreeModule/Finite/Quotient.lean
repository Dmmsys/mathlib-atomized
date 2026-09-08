/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Quotient.Pi

/-! # Quotient of submodules of full rank in free finite modules over PIDs

## Main results

* `Submodule.quotientEquivPiSpan`: `M ⧸ N`, if `M` is free finite module over a PID `R` and `N`
  is a submodule of full rank, can be written as a product of quotients of `R` by principal ideals.

-/

@[expose] public section

open Module
open scoped DirectSum

namespace Submodule

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsDomain R] [IsPrincipalIdealRing R] [Finite ι]

/--
We can write the quotient by a submodule of full rank over a PID as a product of quotients
by principal ideals.
-/
/-
**Submodule.quotientEquivPiSpan** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientEquivPiSpan (N : Submodule R M) (b : Basis ι R M) (h : Module.finr
ank R N = Module.finrank R M) : (M ⧸ N) ≃ₗ[R] Π i, R ⧸ Ideal.span ({smithNormalF
ormCoeffs b h i} : Set R)
参数：N : Submodule R M；b : Basis ι R M；h : Module.finrank R N = Module.finrank R M
。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smithNormalFormBotBasis_def`：Submodule.smithNormalFormBotBasis
_def (b : Basis ι R M) (h : Module.finrank R N = Module.finrank R M) : forall i,
 (smithNormalFormBotBasis b…

--- 原说明 ---
We can write the quotient by a submodule of full rank over a PID as a product of
 quotients
by principal ideals.
-/
noncomputable def quotientEquivPiSpan (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    (M ⧸ N) ≃ₗ[R] Π i, R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R) := by
  haveI := Fintype.ofFinite ι
  -- Choose `e : M ≃ₗ N` and a basis `b'` for `M` that turns the map
  -- `f := ((Submodule.subtype N).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  have mem_I_iff : ∀ x, x ∈ N ↔ ∀ i, a i ∣ b'.repr x i := by
    intro x
    simp_rw [ab.mem_submodule_iff', ab, ab_eq]
    have : ∀ (c : ι → R) (i), b'.repr (∑ j : ι, c j • a j • b' j) i = a i * c i := by
      intro c i
      simp only [← mul_smul, b'.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, this c i⟩
    · rintro ha
      choose c hc using ha
      exact ⟨c, b'.ext_elem fun i => Eq.trans (hc i) (this c i).symm⟩
  -- Now we map everything through the linear equiv `M ≃ₗ (ι → R)`,
  -- which maps `N` to `N' := Π i, a i ℤ`.
  let N' : Submodule R (ι → R) := Submodule.pi Set.univ fun i => span R ({a i} : Set R)
  have : Submodule.map (b'.equivFun : M →ₗ[R] ι → R) N = N' := by
    ext x
    simp only [N', Submodule.mem_map, Submodule.mem_pi, mem_span_singleton, Set.mem_univ,
      mem_I_iff, smul_eq_mul, forall_true_left, LinearEquiv.coe_coe,
      Basis.equivFun_apply, mul_comm _ (a _), eq_comm (b := (x _))]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact hy i
    · rintro hdvd
      refine ⟨∑ i, x i • b' i, fun i => ?_, ?_⟩ <;> rw [b'.repr_sum_self]
      · exact hdvd i
  refine (Submodule.Quotient.equiv N N' b'.equivFun this).trans (re₂₃ := inferInstance)
    (re₃₂ := inferInstance) ?_
  classical
  exact Submodule.quotientPi (show _ → Submodule R R from fun i => span R ({a i} : Set R))

/--
Quotients by submodules of full rank of free finite `ℤ`-modules are isomorphic
to a direct product of `ZMod`.
-/
/-
**Submodule.quotientEquivPiZMod** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientEquivPiZMod (N : Submodule Int M) (b : Basis ι Int M) (h : Module.
finrank Int N = Module.finrank Int M) : M ⧸ N ≃+ Π i, ZMod (smithNormalFormCoeff
s b h i).natAbs
参数：N : Submodule Int M；b : Basis ι Int M；h : Module.finrank Int N = Module.finra
nk Int M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R

--- 原说明 ---
Quotients by submodules of full rank of free finite `ℤ`-modules are isomorphic
to a direct product of `ZMod`.
-/
noncomputable def quotientEquivPiZMod (N : Submodule ℤ M) (b : Basis ι ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) :
    M ⧸ N ≃+ Π i, ZMod (smithNormalFormCoeffs b h i).natAbs :=
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiSpan b h
  let e' : (∀ i : ι, ℤ ⧸ Ideal.span ({a i} : Set ℤ)) ≃+ ∀ i : ι, ZMod (a i).natAbs :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
  (↑(e : (M ⧸ N) ≃ₗ[ℤ] _) : M ⧸ N ≃+ _).trans e'

/--
A submodule of full rank of a free finite `ℤ`-module has a finite quotient.
It can't be an instance because of the side condition `Module.finrank ℤ N = Module.finrank ℤ M`.
-/
/-
**Submodule.finiteQuotientOfFreeOfRankEq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finiteQuotientOfFreeOfRankEq [Module.Free Int M] [Module.Finite Int M] (N 
: Submodule Int M) (h : Module.finrank Int N = Module.finrank Int M) : Finite (M
 ⧸ N)
参数：N : Submodule Int M；h : Module.finrank Int N = Module.finrank Int M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用定理 `Submodule.smithNormalFormCoeffs_ne_zero`：Submodule.smithNormalFormCoeffs
_ne_zero (b : Basis ι R M) (h : Module.finrank R N = Module.finrank R M) (i : ι)
 : smithNormalFormCoeffs b h …
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β

--- 原说明 ---
A submodule of full rank of a free finite `ℤ`-module has a finite quotient.
It can't be an instance because of the side condition `Module.finrank ℤ N = Modu
le.finrank ℤ M`.
-/
theorem finiteQuotientOfFreeOfRankEq [Module.Free ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) (h : Module.finrank ℤ N = Module.finrank ℤ M) : Finite (M ⧸ N) := by
  let b := Module.Free.chooseBasis ℤ M
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiZMod b h
  have : ∀ i, NeZero (a i).natAbs := fun i ↦
    ⟨Int.natAbs_ne_zero.mpr (smithNormalFormCoeffs_ne_zero b h i)⟩
  exact Finite.of_equiv (Π i, ZMod (a i).natAbs) e.symm
/-
**Submodule.finiteQuotient_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finiteQuotient_iff [Module.Free Int M] [Module.Finite Int M] (N : Submodul
e Int M) : Finite (M ⧸ N) ↔ Module.finrank Int N = Module.finrank Int M
参数：N : Submodule Int M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `LinearMap.finrank_le_finrank_of_injective`：LinearMap.finrank_le_finrank_
of_injective [Module.Finite R M'] {f : M ->ₗ[R] M'} (hf : Function.Injective f) 
: finrank R M <= finrank R M'
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `AddSubgroup.nsmul_index_mem`：∀ {G : Type u_6} [inst : AddGroup G] (H : A
ddSubgroup G) [H.Normal] (g : G), H.index • g ∈ H
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Function.Injective.codRestrict`：∀ {α : Type u_1} {ι : Sort u_5} {f : ι →
 α} {s : Set α} (h : ∀ (x : ι), f x ∈ s),   Function.Injective f → Function.Inje
ctive (Set.codRestri…
· 使用定理 `LinearMap.lsmul_injective`：lsmul_injective [IsTorsionFree R M] {x : R} (
hx : x != 0) : Function.Injective (lsmul R M x)
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Module.Free.instIsTorsionFree`：∀ (R : Type u) (M : Type v) [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Free R 
M], Module.IsTorsio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用引理 `Nat.card_ne_zero`：card_ne_zero : Nat.card α != 0 ↔ Nonempty α ∧ Finite α
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Submodule.finiteQuotientOfFreeOfRankEq`：finiteQuotientOfFreeOfRankEq [Mo
dule.Free Int M] [Module.Finite Int M] (N : Submodule Int M) (h : Module.finrank
 Int N = Module.finrank Int …
-/
theorem finiteQuotient_iff [Module.Free ℤ M] [Module.Finite ℤ M] (N : Submodule ℤ M) :
    Finite (M ⧸ N) ↔ Module.finrank ℤ N = Module.finrank ℤ M := by
  refine ⟨fun h ↦ le_antisymm (finrank_le N) <|
    ((LinearMap.lsmul ℤ M (Nat.card (M ⧸ N))).codRestrict N
      fun x ↦ ?_).finrank_le_finrank_of_injective ?_, fun h ↦ finiteQuotientOfFreeOfRankEq N h⟩
  · simpa using! AddSubgroup.nsmul_index_mem N.toAddSubgroup x
  · refine (LinearMap.lsmul_injective ?_).codRestrict _
    exact Int.ofNat_ne_zero.mpr <| Nat.card_ne_zero.mpr
      ⟨Set.nonempty_iff_univ_nonempty.mpr Set.univ_nonempty, h⟩

variable (F : Type*) [CommRing F] [Algebra F R] [Module F M] [IsScalarTower F R M]
  (b : Basis ι R M) {N : Submodule R M}

/-- Decompose `M⧸N` as a direct sum of cyclic `R`-modules
  (quotients by the ideals generated by Smith coefficients of `N`). -/
/-
**Submodule.quotientEquivDirectSum** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientEquivDirectSum (h : Module.finrank R N = Module.finrank R M) : (M 
⧸ N) ≃ₗ[F] ⨁ i, R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R)
参数：h : Module.finrank R N = Module.finrank R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decompose `M⧸N` as a direct sum of cyclic `R`-modules
  (quotients by the ideals generated by Smith coefficients of `N`).
-/
noncomputable def quotientEquivDirectSum (h : Module.finrank R N = Module.finrank R M) :
    (M ⧸ N) ≃ₗ[F] ⨁ i, R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R) := by
  haveI := Fintype.ofFinite ι
  exact ((N.quotientEquivPiSpan b _).restrictScalars F).trans
    (DirectSum.linearEquivFunOnFintype _ _ _).symm
/-
**Submodule.finrank_quotient_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R M) [Nontrivial F] (
h : Module.finrank R N = Module.finrank R M) [forall i, Module.Free F (R ⧸ Ideal
.span ({smithNormalFormCoeffs b h i} : Set R))] [forall i, Module.Finite F (R ⧸ 
Ideal.span ({smithNormalFormCoeffs b h i} : Set R))] : Module.finrank F (M ⧸ N) 
= ∑ i, Module.finrank F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R))
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M；R ⧸ Ideal.span ({
smithNormalFormCoeffs b h i} : Set R)；R ⧸ Ideal.span ({smithNormalFormCoeffs b h
 i} : Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_directSum`：finrank_directSum {ι : Type v} [Fintype ι] (M 
: ι -> Type w) [forall i : ι, AddCommMonoid (M i)] [forall i : ι, Module R (M i)
] [forall i : …
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R M) [Nontrivial F]
    (h : Module.finrank R N = Module.finrank R M)
    [∀ i, Module.Free F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R))]
    [∀ i, Module.Finite F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R))] :
    Module.finrank F (M ⧸ N) =
      ∑ i, Module.finrank F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R)) := by
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b h, Module.finrank_directSum]

end Submodule

