/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!

# Base change for linear independence

This file is a place to collect base change results for linear independence.

-/

public section

open Function Set TensorProduct

variable {ι ι' : Type*} [Finite ι']

/-- This is an auxiliary lemma dominated by `linearIndependent_algebraMap_comp_iff`. -/
/-
**LinearIndependent.linearIndependent_algebraMap_comp_aux** 是 Mathlib 中的一个引理，位于命
名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an auxiliary lemma dominated by `linearIndependent_algebraMap_comp_iff`.
-/
private lemma LinearIndependent.linearIndependent_algebraMap_comp_aux {K : Type*} (L : Type*)
    [Field K] [Field L] [Algebra K L]
    {v : ι → ι' → K} (hv : LinearIndependent K v) :
    LinearIndependent L (fun i ↦ algebraMap K L ∘ v i) := by
  classical
  let : Fintype ι' := .ofFinite ι'
  let I : Set (ι' → K) := hv.linearIndepOn_id.extend (subset_univ _)
  let b : Module.Basis I K (ι' → K) := .extend hv.linearIndepOn_id
  let b' : Module.Basis I L (ι' → L) := (b.baseChange L).map (TensorProduct.piScalarRight K L L ι')
  let v' (i : ι) : I := ⟨v i, hv.linearIndepOn_id.subset_extend _ <| mem_range_self i⟩
  have hv' : b' ∘ v' = fun i ↦ algebraMap K L ∘ v i := by
    ext; simp [b', b, v', Module.Basis.extend, Algebra.algebraMap_eq_smul_one]
  have h_inj : Injective v' := fun i j hij ↦ by have : Injective v := hv.injective; aesop
  rw [← hv']
  exact b'.linearIndependent.comp _ h_inj
/-
**linearIndependent_algebraMap_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} [Finite ι'] {R : Type u_3} {S : Type u_4}
 [inst : CommRing R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [FaithfulSMu
l R S] [IsDomain S] {v : ι → ι' → R},   (LinearIndependent S fun i => ⇑(algebraM
ap R S) ∘ v i) ↔ LinearIndependent R v
参数：LinearIndependent S fun i => ⇑(algebraMap R S) ∘ v i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIndependent.iff_fractionRing`：LinearIndependent.iff_fractionRing {
ι : Type*} {b : ι -> V} : LinearIndependent R b ↔ LinearIndependent K b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.LinearAlgebra.LinearIndependent.BaseChange.0.LinearInde
pendent.linearIndependent_algebraMap_comp_aux`：∀ {ι : Type u_1} {ι' : Type u_2} 
[Finite ι'] {K : Type u_3} (L : Type u_4) [inst : Field K] [inst_1 : Field L]   
[inst_2 : Algebra K L] {v :…
-/
@[simp] lemma linearIndependent_algebraMap_comp_iff {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S] [IsDomain S]
    {v : ι → ι' → R} :
    LinearIndependent S (fun i ↦ algebraMap R S ∘ v i) ↔ LinearIndependent R v := by
  change LinearIndependent S (Pi.algebraMap ι' R S ∘ v) ↔ LinearIndependent R v
  refine ⟨fun h ↦ (h.restrict_scalars' R).of_comp, fun h ↦ ?_⟩
  have : IsDomain R := .of_faithfulSMul R S
  set K := FractionRing R
  set L := FractionRing S
  replace h : LinearIndependent K (Pi.algebraMap ι' R K ∘ v) := by
    rw [← LinearIndependent.iff_fractionRing (R := R)]
    have : Function.Injective (Pi.algebraMap ι' R K) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv; ext i; simpa [Pi.algebraMap] using congr($hv i)
    rwa [LinearMap.linearIndependent_iff_of_injOn _ this.injOn]
  let : Algebra K L := FractionRing.liftAlgebra R L
  suffices LinearIndependent L (Pi.algebraMap ι' R L ∘ v) by
    rw [← LinearIndependent.iff_fractionRing (R := S)] at this
    have aux : Pi.algebraMap ι' R L ∘ v = Pi.algebraMap ι' S L ∘ Pi.algebraMap ι' R S ∘ v := by
      ext; simp [Pi.algebraMap, ← IsScalarTower.algebraMap_apply]
    rw [aux] at this
    exact this.of_comp
  have aux : Pi.algebraMap ι' R L ∘ v = Pi.algebraMap ι' K L ∘ Pi.algebraMap ι' R K ∘ v := by
    ext; simp [Pi.algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [aux]
  replace h := h.linearIndependent_algebraMap_comp_aux L
  exact h
