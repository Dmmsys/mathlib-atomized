/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten, Junyan Xu
-/
module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Order.Ring.Finset
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!

# Separably generated extensions

We aim to formalize the following result:

Let `K/k` be a finitely generated field extension with characteristic `p > 0`, then TFAE
1. `K/k` is separably generated
2. If `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
  `{ sᵢᵖ } ⊆ K` is also `k`-linearly independent
3. `K ⊗ₖ k^{1/p}` is reduced
4. `K` is geometrically reduced over `k`.
5. `k` and `Kᵖ` are linearly disjoint over `kᵖ` in `K`.

## Main result
- `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`: (2) ⇒ (1)

-/

@[expose] public noncomputable section

section

attribute [local instance 2000] Polynomial.isScalarTower Algebra.toSMul IsScalarTower.right

open MvPolynomial
open scoped IntermediateField

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) (hp : p.Prime)
variable (H : ∀ s : Finset K,
  LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K))
variable {a : ι → K} (n : ι)

namespace MvPolynomial

/-- View a multivariate polynomial `F(x₁,...,xₙ)` as a polynomial in `xᵢ` with coefficients
in `F(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ)`. -/
/-
**MvPolynomial.toPolynomialAdjoinImageCompl** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynom
ial`。
形式化陈述：toPolynomialAdjoinImageCompl (F : MvPolynomial ι k) (a : ι -> K) (i : ι) :
 Polynomial (Algebra.adjoin k (a '' {i}ᶜ))
参数：F : MvPolynomial ι k；a : ι -> K；i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
View a multivariate polynomial `F(x₁,...,xₙ)` as a polynomial in `xᵢ` with coeff
icients
in `F(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ)`.
-/
def toPolynomialAdjoinImageCompl (F : MvPolynomial ι k) (a : ι → K) (i : ι) :
    Polynomial (Algebra.adjoin k (a '' {i}ᶜ)) :=
  letI := Classical.typeDecidableEq ι
  (optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)).mapAlgHom
    (aeval fun j : {j // j ≠ i} ↦
      (⟨a j, Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩ : Algebra.adjoin k (a '' {i}ᶜ)))
/-
**MvPolynomial.aeval_toPolynomialAdjoinImageCompl_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `MvPolynomial`。
形式化陈述：aeval_toPolynomialAdjoinImageCompl_eq_zero {a : ι -> K} {F : MvPolynomial 
ι k} (hFa : F.aeval a = 0) (i : ι) : (toPolynomialAdjoinImageCompl F a i).aeval 
(a i) = 0
参数：hFa : F.aeval a = 0；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.restrictScalars_apply`：restrictScalars_apply (f : A ->ₐ[S] B) (x 
: A) : f.restrictScalars R x = f x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `Equiv.optionSubtypeNe_symm_apply`：∀ {α : Type u_1} [inst : DecidableEq α
] (a b : α),   (Equiv.optionSubtypeNe a).symm b = if h : b = a then none else so
me ⟨b, h⟩
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `MvPolynomial.optionEquivLeft_X_some`：optionEquivLeft_X_some (x : S₁) : o
ptionEquivLeft R S₁ (X (some x)) = Polynomial.C (X x)
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `MvPolynomial.optionEquivLeft_X_none`：optionEquivLeft_X_none : optionEqui
vLeft R S₁ (X none) = Polynomial.X
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem aeval_toPolynomialAdjoinImageCompl_eq_zero
    {a : ι → K} {F : MvPolynomial ι k} (hFa : F.aeval a = 0) (i : ι) :
    (toPolynomialAdjoinImageCompl F a i).aeval (a i) = 0 := by
  rw [← hFa, ← AlgHom.restrictScalars_apply k]
  simp_rw [toPolynomialAdjoinImageCompl, ← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr; ext; aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)
/-
**MvPolynomial.irreducible_toPolynomialAdjoinImageCompl** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
形式化陈述：irreducible_toPolynomialAdjoinImageCompl {F : MvPolynomial ι k} (hF : Irre
ducible F) (i : ι) (H : AlgebraicIndependent k fun x : {j | j != i} => a x) : Ir
reducible (toPolynomialAdjoinImageCompl F a i)
参数：hF : Irreducible F；i : ι；H : AlgebraicIndependent k fun x : {j | j != i} => a
 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Polynomial.coe_mapAlgEquiv`：coe_mapAlgEquiv (f : A ≃ₐ[R] B) : ⇑(mapAlgEq
uiv f) = map f
· 使用定理 `Polynomial.coe_mapAlgHom`：coe_mapAlgHom (f : A ->ₐ[R] B) : ⇑(mapAlgHom f
) = map f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AlgebraicIndependent.aevalEquiv_apply_coe`：∀ {ι : Type u_1} {R : Type u_
3} {A : Type u_5} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A]   [inst_
2 : Algebra R A] (hx : Algebrai…
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `Subalgebra.equivOfEq_apply`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S T : Subalgebra R A)   (h
 : S = T) (x : ↥…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
（共 35 条，此处仅展示前 30 条）
-/
theorem irreducible_toPolynomialAdjoinImageCompl {F : MvPolynomial ι k} (hF : Irreducible F) (i : ι)
    (H : AlgebraicIndependent k fun x : {j | j ≠ i} ↦ a x) :
    Irreducible (toPolynomialAdjoinImageCompl F a i) := by
  classical
  unfold toPolynomialAdjoinImageCompl
  have hc : a '' {i}ᶜ = Set.range (fun x : {j | j ≠ i} ↦ a x) := by ext; simp
  let d : {j // j ≠ i} ≃ {j | j ≠ i} := .subtypeEquivRight (by simp)
  refine (congrArg Irreducible ?_).mp <|
    hF.map (renameEquiv k ((Equiv.optionSubtypeNe i).symm)) |>.map
      (optionEquivLeft k _) |>.map (Polynomial.mapAlgEquiv <|
        (renameEquiv k d).trans <| H.aevalEquiv.trans
        (Subalgebra.equivOfEq _ _ congr(Algebra.adjoin k $hc.symm)))
  rw [Polynomial.coe_mapAlgEquiv, Polynomial.coe_mapAlgHom]
  refine congrFun (congrArg Polynomial.map ?_) _
  ext <;> simp [d]

-- Suppose `F` has minimal total degree among the relations of `a`.
variable {F : MvPolynomial ι k}
variable (HF : ∀ F' : MvPolynomial ι k, F' ≠ 0 → F'.aeval a = 0 → F.totalDegree ≤ F'.totalDegree)

include HF

/-- If `F` has minimal total degree among the relations of `a`, then `F` is irreducible. -/
/-
**MvPolynomial.irreducible_of_forall_totalDegree_le** 是 Mathlib 中的一个引理，位于命名空间 `M
vPolynomial`。
形式化陈述：irreducible_of_forall_totalDegree_le (hF0 : F != 0) (hFa : F.aeval a = 0) 
: Irreducible F
参数：hF0 : F != 0；hFa : F.aeval a = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.isUnit_iff_totalDegree_of_isReduced`：isUnit_iff_totalDegree
_of_isReduced [IsReduced R] : IsUnit P ↔ IsUnit (P.coeff 0) ∧ P.totalDegree = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `add_le_iff_nonpos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_
1 : LE α] [AddLeftMono α] [AddLeftReflectLE α] (a : α) {b : α},   a + b ≤ a ↔ b 
≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `MvPolynomial.totalDegree_mul_of_isDomain`：totalDegree_mul_of_isDomain {f
 g : MvPolynomial σ R} (hf : f != 0) (hg : g != 0) : totalDegree (f * g) = total
Degree f + totalDegree g
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `F` has minimal total degree among the relations of `a`, then `F` is irreduci
ble.
-/
lemma irreducible_of_forall_totalDegree_le (hF0 : F ≠ 0) (hFa : F.aeval a = 0) : Irreducible F := by
  refine ⟨fun h' ↦ (h'.map (aeval a)).ne_zero hFa, fun q₁ q₂ e ↦ ?_⟩
  wlog h₁ : aeval a q₁ = 0 generalizing q₁ q₂
  · exact .symm (this q₂ q₁ (e.trans (mul_comm ..)) <| by
      simpa [h₁, hFa] using Eq.symm <| congr(aeval a $e))
  have ne := mul_ne_zero_iff.mp (e ▸ hF0)
  have := HF q₁ ne.1 h₁
  rw [e, totalDegree_mul_of_isDomain ne.1 ne.2, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
  refine .inr (isUnit_iff_totalDegree_of_isReduced.mpr ⟨?_, this⟩)
  rw [totalDegree_eq_zero_iff_eq_C.mp this] at ne
  simpa using ne.2
/-
**MvPolynomial.coeff_toPolynomialAdjoinImageCompl_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `MvPolynomial`。
形式化陈述：coeff_toPolynomialAdjoinImageCompl_ne_zero (σ : ι ->₀ Nat) (hσ : σ in F.su
pport) (i : ι) (hσi : σ i != 0) : (toPolynomialAdjoinImageCompl F a i).coeff (σ 
i) != 0
参数：σ : ι ->₀ Nat；hσ : σ in F.support；i : ι；hσi : σ i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `MvPolynomial.optionEquivLeft_coeff_some_coeff_none`：optionEquivLeft_coef
f_some_coeff_none (n : Option S₁ ->₀ Nat) (f : MvPolynomial (Option S₁) R) : coe
ff n.some (Polynomial.coeff (optionEquiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MvPolynomial.coeff_zero`：coeff_zero (m : σ ->₀ Nat) : coeff m (0 : MvPol
ynomial σ R) = 0
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `Equiv.optionSubtypeNe_none`：∀ {α : Type u_1} [inst : DecidableEq α] (a :
 α), (Equiv.optionSubtypeNe a) none = a
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `MvPolynomial.coeff_rename_mapDomain`：coeff_rename_mapDomain (f : σ -> τ)
 (hf : Injective f) (φ : MvPolynomial σ R) (d : σ ->₀ Nat) : (rename f φ).coeff 
(d.mapDomain f) = φ.coeff…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Finsupp.equivMapDomain_eq_mapDomain`：equivMapDomain_eq_mapDomain {M} [Ad
dCommMonoid M] (f : α ≃ β) (l : α ->₀ M) : equivMapDomain f l = mapDomain f l
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
（共 48 条，此处仅展示前 30 条）
-/
theorem coeff_toPolynomialAdjoinImageCompl_ne_zero
    (σ : ι →₀ ℕ) (hσ : σ ∈ F.support) (i : ι) (hσi : σ i ≠ 0) :
    (toPolynomialAdjoinImageCompl F a i).coeff (σ i) ≠ 0 := by
  classical
  intro H
  let F₀ := optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
  have H := HF (rename (↑) (F₀.coeff (σ i))) ?_ ?_
  · have : (F₀.coeff (σ i)).totalDegree + σ i ≤ _ :=
      totalDegree_coeff_optionEquivLeft_add_le _ _ _ (σ i) <| by
        rw [totalDegree_renameEquiv]
        exact (Finsupp.le_degree ..).trans (le_totalDegree hσ)
    rw [totalDegree_renameEquiv] at this
    simpa [hσi] using (this.trans H).trans (totalDegree_rename_le _ _)
  · refine (map_eq_zero_iff _ (rename_injective _ Subtype.val_injective)).not.mpr fun H ↦ ?_
    let e := (Equiv.optionSubtypeNe i).symm
    have : coeff _ (F₀.coeff _) = _ :=
      optionEquivLeft_coeff_some_coeff_none _ _ (σ.equivMapDomain e) (renameEquiv k e F)
    dsimp only [F₀] at this
    rw [renameEquiv_apply, Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _
      e.injective, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_none,
      ← renameEquiv_apply, H, coeff_zero, eq_comm, ← notMem_support_iff] at this
    exact this hσ
  · apply_fun Subalgebra.val _ at H
    simp_rw [toPolynomialAdjoinImageCompl, Polynomial.coe_mapAlgHom, Polynomial.coeff_map,
      AlgHom.coe_toRingHom, map_zero] at H
    simp_rw [← H, ← AlgHom.comp_apply]
    congr; ext; simp
/-
**MvPolynomial.isAlgebraic_of_mem_vars_of_forall_totalDegree_le** 是 Mathlib 中的一个
定理，位于命名空间 `MvPolynomial`。
形式化陈述：isAlgebraic_of_mem_vars_of_forall_totalDegree_le (hFa : F.aeval a = 0) (i 
: ι) (hi : i in F.vars) : IsAlgebraic (Algebra.adjoin k (a '' {i}ᶜ)) (a i)
参数：hFa : F.aeval a = 0；i : ι；hi : i in F.vars。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_vars_iff_mem_support`：mem_vars_iff_mem_support (i : σ) 
: i in p.vars ↔ exists d in p.support, i in d.support
· 使用定理 `MvPolynomial.coeff_toPolynomialAdjoinImageCompl_ne_zero`：coeff_toPolynom
ialAdjoinImageCompl_ne_zero (σ : ι ->₀ Nat) (hσ : σ in F.support) (i : ι) (hσi :
 σ i != 0) : (toPolynomialAdjoinImageCompl F …
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
· 使用定理 `MvPolynomial.aeval_toPolynomialAdjoinImageCompl_eq_zero`：aeval_toPolynom
ialAdjoinImageCompl_eq_zero {a : ι -> K} {F : MvPolynomial ι k} (hFa : F.aeval a
 = 0) (i : ι) : (toPolynomialAdjoinImageCompl…
-/
theorem isAlgebraic_of_mem_vars_of_forall_totalDegree_le (hFa : F.aeval a = 0) (i : ι)
    (hi : i ∈ F.vars) : IsAlgebraic (Algebra.adjoin k (a '' {i}ᶜ)) (a i) := by
  have ⟨σ, hσ, hσi⟩ := (mem_vars_iff_mem_support i).mp hi
  refine ⟨toPolynomialAdjoinImageCompl F a i,
    fun h ↦ coeff_toPolynomialAdjoinImageCompl_ne_zero HF σ hσ i
      (Finsupp.mem_support_iff.mp hσi) ?_, aeval_toPolynomialAdjoinImageCompl_eq_zero hFa ..⟩
  rw [h, Polynomial.coeff_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hp H in
/-
**MvPolynomial.exists_mem_support_not_dvd_of_forall_totalDegree_le** 是 Mathlib 中
的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：exists_mem_support_not_dvd_of_forall_totalDegree_le (hF0 : F != 0) (hFa : 
F.aeval a = 0) : exists i, exists σ in F.support, ¬ p ∣ σ i
参数：hF0 : F != 0；hFa : F.aeval a = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `linearIndepOn_range_iff`：linearIndepOn_range_iff {ι} {f : ι -> ι'} (hf :
 Injective f) (g : ι' -> M) : LinearIndepOn R g (range f) ↔ LinearIndependent R 
(g ∘ f)
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 91 条，此处仅展示前 30 条）
-/
theorem exists_mem_support_not_dvd_of_forall_totalDegree_le (hF0 : F ≠ 0) (hFa : F.aeval a = 0) :
    ∃ i, ∃ σ ∈ F.support, ¬ p ∣ σ i := by
  by_contra!
  have (σ) (hσ : σ ∈ F.support) : ∃ σ', σ = p • σ' := by
    choose σ' hσ' using (this · σ hσ)
    exact ⟨⟨σ.support, σ', by simp [hσ', hp.ne_zero]⟩, Finsupp.ext hσ'⟩
  choose! σ' hσ' using this
  have hσ'' (σ : F.support) : σ.1 = p • σ' σ := hσ' σ.1 σ.2
  classical
  replace H (ι : Type u_3) (_ : Fintype ι) (v : ι → K) (hv : LinearIndependent k v) :
      LinearIndependent k (v · ^ p) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, linearIndepOn_range_iff
      hv.injective] using! H (Finset.univ.image v) (by simpa using! hv.linearIndepOn_id)
  have := mt (H F.support inferInstance (fun s ↦ aeval a (monomial (σ' s) (1 : k)))) (by
    simp_rw [← map_pow, monomial_pow, ← hσ'', one_pow, not_linearIndependent_iff]
    refine ⟨.univ, (F.coeff ·), ?_, by simpa [MvPolynomial.eq_zero_iff] using! hF0⟩
    simp only [← map_smul, ← map_sum, Finset.univ_eq_attach, smul_eq_mul, mul_one]
    rw [F.support.sum_attach (fun i ↦ monomial i (F.coeff i)), support_sum_monomial_coeff, hFa])
  simp only [LinearIndependent, injective_iff_map_eq_zero, not_forall] at this
  obtain ⟨F', hF', hF'0⟩ := this
  let F'' : MvPolynomial ι k := .ofCoeff <| F'.mapDomain fun s ↦ σ' s.1
  have hF''0 : F'' ≠ 0 := ne_of_ne_of_eq (AddMonoidAlgebra.ofCoeff_eq_zero.ne.2 <|
    (Finsupp.mapDomain_injective fun s t h ↦ Subtype.ext
    (Finsupp.ext fun i ↦ by rw [hσ' _ s.2, hσ' _ t.2, h])).ne hF'0) (by simp)
  have hF'' : aeval a F'' = 0 := by
    have : (aeval a).toLinearMap ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap ∘ₗ
      Finsupp.lmapDomain k k (fun s : F.support ↦ σ' s) =
        (Finsupp.linearCombination k fun s : F.support ↦ aeval a (monomial (σ' s) (1 : k))) := by
      ext v; simp [monomial]
    simp only [← hF', F'', ← this]; rfl
  suffices hpm : p * F''.totalDegree ≤ F.totalDegree by
    have hF''0' : F''.totalDegree ≠ 0 := by
      contrapose hF''0
      rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, aeval_C, map_eq_zero] at hF''
      rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, hF'', map_zero]
    replace this := hpm.trans ((HF F'' hF''0 hF'').trans_eq (one_mul _).symm)
    exact hp.one_lt.not_ge ((mul_le_mul_iff_of_pos_right hF''0'.bot_lt).mp this)
  rw [totalDegree, Finset.mul_sup₀, Finset.sup_le_iff]
  intro σ hσ
  obtain ⟨σ, hσ₂, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
  refine le_trans ?_ (Finset.le_sup σ.2)
  conv_rhs => rw [hσ' _ σ.2, Finsupp.sum_smul_index (fun _ ↦ rfl), ← Finsupp.mul_sum]

end MvPolynomial

open IntermediateField

section

variable [ExpChar k p]

include hp H

/--
Suppose `k` has characteristic `p` and `a₁,...,aₙ` is a transcendence basis of `K/k`.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a transcendence basis over which `a₁,...,aₙ₊₁` are
separable.
-/
/-
**exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow** 是 Mathlib 中
的一个引理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow (ha' : Is
TranscendenceBasis k fun i : {i // i != n} => a i) : exists i : ι, IsTranscenden
ceBasis k (fun j : {j // j != i} => a j) ∧ IsSeparable (adjoin k (a '' {i}ᶜ)) (a
 i)
参数：ha' : IsTranscendenceBasis k fun i : {i // i != n} => a i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.transcendental_adjoin`：transcendental_adjoin {s : S
et ι} {i : ι} (hi : i ∉ s) : Transcendental (adjoin R (x '' s)) (x i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Function.argminOn_mem`：argminOn_mem (s : Set α) (hs : s.Nonempty) : argm
inOn f s hs in s
· 使用定理 `Function.argminOn_le`：argminOn_le (s : Set α) {a : α} (ha : a in s) : f 
(argminOn f s ⟨a, ha⟩) <= f a
· 使用引理 `MvPolynomial.irreducible_of_forall_totalDegree_le`：irreducible_of_forall
_totalDegree_le (hF0 : F != 0) (hFa : F.aeval a = 0) : Irreducible F
· 使用定理 `MvPolynomial.exists_mem_support_not_dvd_of_forall_totalDegree_le`：exists
_mem_support_not_dvd_of_forall_totalDegree_le (hF0 : F != 0) (hFa : F.aeval a = 
0) : exists i, exists σ in F.support, ¬ p ∣ σ i
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `MvPolynomial.isAlgebraic_of_mem_vars_of_forall_totalDegree_le`：isAlgebra
ic_of_mem_vars_of_forall_totalDegree_le (hFa : F.aeval a = 0) (i : ι) (hi : i in
 F.vars) : IsAlgebraic (Algebra.adjoin k (a '' {i}ᶜ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_vars_iff_mem_support`：mem_vars_iff_mem_support (i : σ) 
: i in p.vars ↔ exists d in p.support, i in d.support
· 使用引理 `IsTranscendenceBasis.of_isAlgebraic_adjoin_image_compl`：of_isAlgebraic_a
djoin_image_compl (H₁ : IsTranscendenceBasis R fun x : {x // x != i} => v x) (H₂
 : IsAlgebraic (Algebra.adjoin R (v '' {j}ᶜ)…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose `k` has characteristic `p` and `a₁,...,aₙ` is a transcendence basis of `
K/k`.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independen
t set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}
` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a transcendence basis over which `a₁,...
,aₙ₊₁` are
separable.
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    (ha' : IsTranscendenceBasis k fun i : {i // i ≠ n} ↦ a i) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : {j // j ≠ i} ↦ a j) ∧
      IsSeparable (adjoin k (a '' {i}ᶜ)) (a i) := by
  set S := {F : MvPolynomial ι k | F ≠ 0 ∧ F.aeval a = 0}
  obtain ⟨F, ⟨hF₀, hFa⟩, hFmin⟩ :
      ∃ F ∈ S, ∀ G : MvPolynomial ι k, G ≠ 0 → G.aeval a = 0 → totalDegree F ≤ totalDegree G := by
    suffices S.Nonempty from
      ⟨totalDegree.argminOn S this, totalDegree.argminOn_mem ..,
        fun _ h₁ h₂ ↦ totalDegree.argminOn_le S ⟨h₁, h₂⟩⟩
    suffices ¬ AlgebraicIndependent k a by simpa [S, algebraicIndependent_iff, and_comm] using! this
    intro h
    refine h.transcendental_adjoin (i := n) (s := {n}ᶜ) (by simp) ?_
    have : a '' {n}ᶜ = Set.range (ι := {i // i ≠ n}) (a ·) := by aesop
    convert! ha'.isAlgebraic.isAlgebraic _
  have hFirr : Irreducible F := irreducible_of_forall_totalDegree_le hFmin hF₀ hFa
  obtain ⟨i, σ, hσ, hi⟩ := exists_mem_support_not_dvd_of_forall_totalDegree_le p hp H hFmin hF₀ hFa
  have hσi : σ i ≠ 0 := by aesop
  have alg := isAlgebraic_of_mem_vars_of_forall_totalDegree_le hFmin hFa i <|
    (mem_vars_iff_mem_support i).mpr ⟨σ, hσ, by simpa⟩
  have Hi := ha'.of_isAlgebraic_adjoin_image_compl _ i _ alg
  refine ⟨i, Hi, ?_⟩
  let k' := adjoin k (a '' {i}ᶜ)
  have hF₁irr := irreducible_toPolynomialAdjoinImageCompl hFirr i Hi.1
  have := (AlgebraicIndepOn.aevalEquiv (s := {i}ᶜ) Hi.1).uniqueFactorizationMonoid inferInstance
  have coeff_ne := coeff_toPolynomialAdjoinImageCompl_ne_zero hFmin σ hσ i hσi
  open scoped algebraAdjoinAdjoin in
  have hF₂irr := (hF₁irr.isPrimitive fun h ↦ coeff_ne <| Polynomial.coeff_eq_zero_of_natDegree_lt <|
    h.trans_lt <| Nat.pos_iff_ne_zero.2 hσi).irreducible_iff_irreducible_map_fraction_map
    (K := k').1 hF₁irr
  contrapose coeff_ne with Hsep
  have : CharP k' p := (expChar_of_injective_algebraMap (algebraMap k k').injective p).casesOn
    (fun e ↦ (e rfl).elim) (fun _ _ _ ↦ ‹_›) hp.ne_one
  obtain ⟨g, hg, eq⟩ := (((minpoly k' (a i)).separable_or p (minpoly.irreducible
    (isAlgebraic_iff_isIntegral.mp <| isAlgebraic_adjoin_iff.mpr alg))).resolve_left Hsep).2
  replace eq := congr(Polynomial.coeff $eq (σ i))
  rwa [← minpoly.eq_of_irreducible hF₂irr ((Polynomial.aeval_map_algebraMap ..).trans
    (aeval_toPolynomialAdjoinImageCompl_eq_zero hFa i)), Polynomial.coeff_mul_C,
    Polynomial.coeff_expand hp.pos, if_neg hi, eq_mul_inv_iff_mul_eq₀
    (by simpa using hF₂irr.ne_zero), zero_mul, eq_comm,
    Polynomial.coeff_map, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ..)] at eq
/-
**exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'** 是 Mathlib 
中的一个引理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow' (s : Set
 ι) (n : ι) (ha : IsTranscendenceBasis k fun i : s => a i) (hn : n ∉ s) : exists
 i : ι, IsTranscendenceBasis k (fun j : ↥(insert n s \ {i}) => a j) ∧ IsSeparabl
e (adjoin k (a '' (insert n s \ {i}))) (a i)
参数：s : Set ι；n : ι；ha : IsTranscendenceBasis k fun i : s => a i；hn : n ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用引理 `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`：exists
_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow (ha' : IsTranscendenc
eBasis k fun i : {i // i != n} => a i) : exists i : ι,…
· 使用定理 `IsTranscendenceBasis.comp_equiv`：∀ {ι : Type u_1} {ι' : Type u_2} {R : T
ype u_3} {A : Type u_5} [inst : CommRing R] [inst_1 : CommRing A]   [inst_2 : Al
gebra R A] (e : ι ≃ ι…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
    (s : Set ι) (n : ι) (ha : IsTranscendenceBasis k fun i : s ↦ a i) (hn : n ∉ s) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : ↥(insert n s \ {i}) ↦ a j) ∧
      IsSeparable (adjoin k (a '' (insert n s \ {i}))) (a i) := by
  let e₁ : {j : ↥(insert n s) // j ≠ ⟨n, by simp⟩} ≃ ↑s :=
    ⟨fun x ↦ ⟨x, by aesop⟩, fun x ↦ ⟨⟨x, by aesop⟩, by aesop⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨i, hi, hi'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H
    (a := fun i : ↥(insert n s) ↦ a i) ⟨n, by simp⟩ (ha.comp_equiv e₁)
  let e₂ : {j // j ≠ i} ≃ ↥(insert n s \ {i.1}) := ⟨fun x ↦ ⟨x, x.1.2, fun h ↦ x.2 (Subtype.ext h)⟩,
    fun x ↦ ⟨⟨x, x.2.1⟩, fun h ↦ x.2.2 congr($h.1)⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have : a '' (insert n s \ {i.1}) = (a ·.1) '' {i}ᶜ := by ext; aesop
  refine ⟨i, hi.comp_equiv e₂.symm, by convert! hi'⟩

/--
Suppose `k` has characteristic `p` and `K/k` is generated by `a₁,...,aₙ₊₁`,
where `a₁,...aₙ` form a transcendence basis.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a separating transcendence basis.
-/
@[stacks 0H71]
/-
**exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_
top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin
_eq_top (ha : IntermediateField.adjoin k (Set.range a) = ⊤) (ha' : IsTranscenden
ceBasis k fun i : {i // i != n} => a i) : exists i : ι, IsTranscendenceBasis k (
fun j : {j // j != i} => a j) ∧ Algebra.IsSeparable (adjoin k (a '' {i}ᶜ)) K
参数：ha : IntermediateField.adjoin k (Set.range a) = ⊤；ha' : IsTranscendenceBasis 
k fun i : {i // i != n} => a i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`：exists
_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow (ha' : IsTranscendenc
eBasis k fun i : {i // i != n} => a i) : exists i : ι,…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `separableClosure.eq_top_iff`：separableClosure.eq_top_iff : separableClos
ure F E = ⊤ ↔ Algebra.IsSeparable F E
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.restrictScalars_injective`：restrictScalars_injective :
 Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateF
ield K L)
· 使用定理 `IntermediateField.restrictScalars_top`：restrictScalars_top : (⊤ : Interm
ediateField F E).restrictScalars K = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isSeparable_algebraMap`：isSeparable_algebraMap (x : F) : IsSeparable F (
algebraMap F K x)
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S

--- 原说明 ---
Suppose `k` has characteristic `p` and `K/k` is generated by `a₁,...,aₙ₊₁`,
where `a₁,...aₙ` form a transcendence basis.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independen
t set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}
` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a separating transcendence basis.
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
    (ha : IntermediateField.adjoin k (Set.range a) = ⊤)
    (ha' : IsTranscendenceBasis k fun i : {i // i ≠ n} ↦ a i) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : {j // j ≠ i} ↦ a j) ∧
      Algebra.IsSeparable (adjoin k (a '' {i}ᶜ)) K := by
  have ⟨i, hi⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H n ha'
  refine ⟨i, hi.1, ?_⟩
  rw [← separableClosure.eq_top_iff, ← (restrictScalars_injective k).eq_iff,
    restrictScalars_top, eq_top_iff, ← ha, adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  obtain rfl | ne := eq_or_ne x i
  · exact hi.2
  · exact isSeparable_algebraMap (F := adjoin k (a '' {i}ᶜ)) ⟨_, subset_adjoin _ _ ⟨x, ne, rfl⟩⟩

/--
Suppose `k` has characteristic `p` and `K/k` is finitely generated.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then `K/k` is finite separably generated.

TODO: show that this is an if and only if.
-/
@[stacks 030W "(2) ⇒ (1) finitely generated case"]
/-
**exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteT
ype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFin
iteType [Algebra.EssFiniteType k K] : exists s : Finset K, IsTranscendenceBasis 
k ((↑) : s -> K) ∧ Algebra.IsSeparable (adjoin k (s : Set K)) K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.exists_finset_maximalFor_isTranscendenceBasis_separabl
eClosure`：exists_finset_maximalFor_isTranscendenceBasis_separableClosure [Algebr
a.EssFiniteType F E] : exists s : Finset E, MaximalFor (fun t : Set E …
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `le_restrictScalars_separableClosure`：le_restrictScalars_separableClosure
 (L : IntermediateField F E) : L <= (separableClosure L E).restrictScalars F
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用引理 `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'`：exist
s_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow' (s : Set ι) (n : ι)
 (ha : IsTranscendenceBasis k fun i : s => a i) (hn : n…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `not_lt_iff_le_imp_ge`：not_lt_iff_le_imp_ge : ¬ a < b ↔ (a <= b -> b <= a
)
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `separableClosure_le_separableClosure_iff`：separableClosure_le_separableC
losure_iff [Algebra K E] [IsScalarTower F K E] {L : IntermediateField F E} : (se
parableClosure L E).restrictSc…
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s

--- 原说明 ---
Suppose `k` has characteristic `p` and `K/k` is finitely generated.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independen
t set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}
` is reduced).

Then `K/k` is finite separably generated.

TODO: show that this is an if and only if.
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
    [Algebra.EssFiniteType k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (adjoin k (s : Set K)) K := by
  have ⟨s, hs, Hs⟩ := exists_finset_maximalFor_isTranscendenceBasis_separableClosure k K
  refine ⟨s, hs, ⟨fun n ↦ of_not_not fun hn ↦ ?_⟩⟩
  have hns : n ∉ s := fun h ↦ hn (le_restrictScalars_separableClosure _ (subset_adjoin _ _ h))
  have ⟨i, hi₁, hi₂⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
    p hp (a := id) H s n hs hns
  rw [Set.image_id] at hi₂
  refine not_lt_iff_le_imp_ge.mpr (Hs hi₁) (SetLike.lt_iff_le_and_exists.mpr ⟨?_, n, ?_, hn⟩)
  · rw [separableClosure_le_separableClosure_iff, adjoin_le_iff]
    intro x hx
    obtain rfl | ne := eq_or_ne x i
    exacts [hi₂, le_restrictScalars_separableClosure _ (subset_adjoin _ _ ⟨.inr hx, ne⟩)]
  · obtain rfl | ne := eq_or_ne n i
    exacts [hi₂, le_restrictScalars_separableClosure _ (subset_adjoin _ _ ⟨.inl rfl, ne⟩)]

end

set_option backward.isDefEq.respectTransparency.types false in
variable (k K) in
/-- Any finitely generated extension over perfect fields are separably generated. -/
/-
**exists_isTranscendenceBasis_and_isSeparable_of_perfectField** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_and_isSeparable_of_perfectField [PerfectField 
k] [Algebra.EssFiniteType k K] : exists s : Finset K, IsTranscendenceBasis k ((↑
) : s -> K) ∧ Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.exists'`：exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [
Nontrivial R] : CharZero R ∨ exists p : Nat, Fact p.Prime ∧ CharP R p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用引理 `IntermediateField.fg_top`：fg_top [Algebra.EssFiniteType F E] : (⊤ : Inte
rmediateField F E).FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.isAlgebraic_adjoin_iff_top`：isAlgebraic_adjoin_iff_top
 : Algebra.IsAlgebraic (adjoin F s) S ↔ Algebra.IsAlgebraic (Algebra.adjoin F s)
 S
· 使用定理 `Algebra.isAlgebraic_iff_isIntegral`：∀ {K : Type u} {A : Type v} [inst : 
Field K] [inst_1 : Ring A] [inst_2 : Algebra K A],   Algebra.IsAlgebraic K A ↔ A
lgebra.IsIntegral K A
· 使用引理 `Algebra.isIntegral_of_surjective`：Algebra.isIntegral_of_surjective (H : 
Function.Surjective (algebraMap R B)) : Algebra.IsIntegral R B
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `exists_isTranscendenceBasis_subset`：exists_isTranscendenceBasis_subset [
NoZeroDivisors A] [FaithfulSMul R A] (s : Set A) [Algebra.IsAlgebraic (adjoin R 
s) A] : exists t, t subs…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsTranscendenceBasis.isAlgebraic_field`：IsTranscendenceBasis.isAlgebraic
_field {F E : Type*} {x : ι -> E} [Field F] [Field E] [Algebra F E] (hx : IsTran
scendenceBasis F x) : Algebr…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `CharP.of_ringHom_of_ne_zero`：CharP.of_ringHom_of_ne_zero [NonAssocSemiri
ng R] [NoZeroDivisors R] [NonAssocSemiring A] [Nontrivial A] (f : R ->+* A) (p :
 Nat) (hp : p != …
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Any finitely generated extension over perfect fields are separably generated.
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_perfectField
    [PerfectField k] [Algebra.EssFiniteType k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · obtain ⟨s, hs⟩ := IntermediateField.fg_top k K
    have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set K)) K := by
      rw [← isAlgebraic_adjoin_iff_top, hs, Algebra.isAlgebraic_iff_isIntegral]
      exact Algebra.isIntegral_of_surjective topEquiv.surjective
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (s : Set K)
    lift t to Finset K using s.finite_toSet.subset hts
    have : Algebra.IsAlgebraic (IntermediateField.adjoin k (t : Set K)) K := by
      convert! ht.isAlgebraic_field <;> simp
    exact ⟨t, ht, inferInstance⟩
  have : ExpChar k p := .prime hp.out
  have : CharP K p := .of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
  refine exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
    p hp.out fun s hs ↦ ?_
  apply hs.map_of_injective_injective (frobeniusEquiv k p).symm (frobenius K p).toAddMonoidHom <;>
    simp [frobenius, Algebra.smul_def, mul_pow, ← map_pow, frobeniusEquiv_symm_pow]

end

