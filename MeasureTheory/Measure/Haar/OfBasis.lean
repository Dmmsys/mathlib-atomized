/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Additive Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelepiped spanned by the basis.

## Main definitions

* `parallelepiped v` is the parallelepiped spanned by a finite family of vectors.
* `Basis.parallelepiped` is the parallelepiped associated to a basis, seen as a compact set with
  nonempty interior.
* `Basis.addHaar` is the Lebesgue measure associated to a basis, giving measure `1` to the
  corresponding parallelepiped.

In particular, we declare a `MeasureSpace` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/

@[expose] public section


open Set TopologicalSpace MeasureTheory MeasureTheory.Measure Module

open scoped Pointwise

noncomputable section

variable {ι ι' E F : Type*}

section Fintype

variable [Fintype ι] [Fintype ι']

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The closed parallelepiped spanned by a finite family of vectors. -/
/-
**parallelepiped** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：parallelepiped (v : ι -> E) : Set E
参数：v : ι -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed parallelepiped spanned by a finite family of vectors.
-/
def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Icc 0 1
/-
**mem_parallelepiped_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_parallelepiped_iff (v : ι -> E) (x : E) : x in parallelepiped v ↔ exis
ts t in Icc (0 : ι -> Real) 1, x = ∑ i, t i • v i
参数：v : ι -> E；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_parallelepiped_iff (v : ι → E) (x : E) :
    x ∈ parallelepiped v ↔ ∃ t ∈ Icc (0 : ι → ℝ) 1, x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]

set_option backward.isDefEq.respectTransparency false in
/-
**parallelepiped_basis_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelepiped_basis_eq (b : Basis ι Real E) : parallelepiped b = {x | for
all i, b.repr x i in Set.Icc 0 1}
参数：b : Basis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finset.sum_apply'`：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k
 i
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem parallelepiped_basis_eq (b : Basis ι ℝ E) :
    parallelepiped b = {x | ∀ i, b.repr x i ∈ Set.Icc 0 1} := by
  classical
  ext x
  simp_rw [mem_parallelepiped_iff, mem_ofPred_eq, b.ext_elem_iff, _root_.map_sum,
    map_smul, Finset.sum_apply', Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mem_Icc,
    Pi.le_def, Pi.zero_apply, Pi.one_apply, ← forall_and]
  aesop
/-
**image_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_parallelepiped (f : E ->ₗ[Real] F) (v : ι -> E) : f '' parallelepipe
d v = parallelepiped (f ∘ v)
参数：f : E ->ₗ[Real] F；v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_parallelepiped (f : E →ₗ[ℝ] F) (v : ι → E) :
    f '' parallelepiped v = parallelepiped (f ∘ v) := by
  simp only [parallelepiped, ← image_comp]
  congr 1 with t
  simp only [Function.comp_apply, _root_.map_sum, map_smulₛₗ, RingHom.id_apply]

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp]
/-
**parallelepiped_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelepiped_comp_equiv (v : ι -> E) (e : ι' ≃ ι) : parallelepiped (v ∘ 
e) = parallelepiped v
参数：v : ι -> E；e : ι' ≃ ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {α β} (e : α ≃ 
β) (s t) : e ⁻¹' s = t ↔ s = e '' t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.piCongrLeft'_apply`：∀ {α : Sort u_1} {β : Sort u_4} (P : α → Sort 
u_9) (e : α ≃ β) (f : (a : α) → P a) (x : β),   (Equiv.piCongrLeft' P e) f x = f
 (e.symm x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Reindexing a family of vectors does not change their parallelepiped.
-/
theorem parallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    parallelepiped (v ∘ e) = parallelepiped v := by
  simp only [parallelepiped]
  let K : (ι' → ℝ) ≃ (ι → ℝ) := Equiv.piCongrLeft' (fun _a : ι' => ℝ) e
  have : Icc (0 : ι → ℝ) 1 = K '' Icc (0 : ι' → ℝ) 1 := by
    rw [← Equiv.preimage_eq_iff_eq_image]
    ext x
    simp only [K, mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply, Equiv.piCongrLeft'_apply,
      Pi.one_apply]
    refine
      ⟨fun h => ⟨fun i => ?_, fun i => ?_⟩, fun h =>
        ⟨fun i => h.1 (e.symm i), fun i => h.2 (e.symm i)⟩⟩
    · simpa only [Equiv.symm_apply_apply] using h.1 (e i)
    · simpa only [Equiv.symm_apply_apply] using h.2 (e i)
  rw [this, ← image_comp]
  ext x
  have := fun z : ι' → ℝ => e.symm.sum_comp fun i => z i • v (e i)
  simp_rw [Equiv.apply_symm_apply] at this
  simp_rw [Function.comp_apply, mem_image, mem_Icc, K, Equiv.piCongrLeft'_apply, this]

-- The parallelepiped associated to an orthonormal basis of `ℝ` is either `[0, 1]` or `[-1, 0]`.
/-
**parallelepiped_orthonormalBasis_one_dim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelepiped_orthonormalBasis_one_dim (b : OrthonormalBasis ι Real Real)
 : parallelepiped b = Icc 0 1 ∨ parallelepiped b = Icc (-1) 0
参数：b : OrthonormalBasis ι Real Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrthonormalBasis.coe_reindex`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type
 u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpa…
· 使用定理 `parallelepiped_comp_equiv`：parallelepiped_comp_equiv (v : ι -> E) (e : ι
' ≃ ι) : parallelepiped (v ∘ e) = parallelepiped v
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `orthonormalBasis_one_dim`：orthonormalBasis_one_dim (b : OrthonormalBasis
 ι Real Real) : (⇑b = fun _ => (1 : Real)) ∨ ⇑b = fun _ => (-1 : Real)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
（共 34 条，此处仅展示前 30 条）
-/
theorem parallelepiped_orthonormalBasis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    parallelepiped b = Icc 0 1 ∨ parallelepiped b = Icc (-1) 0 := by
  have e : ι ≃ Fin 1 := by
    apply Fintype.equivFinOfCardEq
    simp only [← finrank_eq_card_basis b.toBasis, finrank_self]
  have B : parallelepiped (b.reindex e) = parallelepiped b := by
    convert! parallelepiped_comp_equiv b e.symm
    ext i
    simp only [OrthonormalBasis.coe_reindex]
  rw [← B]
  let F : ℝ → Fin 1 → ℝ := fun t => fun _i => t
  have A : Icc (0 : Fin 1 → ℝ) 1 = F '' Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨x 0, ⟨hx.1 0, hx.2 0⟩, ?_⟩
      ext j
      simp only [F, Subsingleton.elim j 0]
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨fun _j => hy.1, fun _j => hy.2⟩
  rcases orthonormalBasis_one_dim (b.reindex e) with (H | H)
  · left
    simp_rw [parallelepiped, H, A, smul_eq_mul, mul_one]
    simp only [F, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      ← image_comp, Function.comp_apply, image_id']
  · right
    simp_rw [H, parallelepiped, smul_eq_mul, A]
    simp only [F, Finset.univ_unique, Fin.default_eq_zero, mul_neg, mul_one, Finset.sum_neg_distrib,
      Finset.sum_singleton, ← image_comp, Function.comp, image_neg_eq_neg, neg_Icc, neg_zero]
/-
**parallelepiped_eq_sum_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelepiped_eq_sum_segment (v : ι -> E) : parallelepiped v = ∑ i, segme
nt Real 0 (v i)
参数：v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `segment_eq_image`：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 =
> (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem parallelepiped_eq_sum_segment (v : ι → E) : parallelepiped v = ∑ i, segment ℝ 0 (v i) := by
  ext
  simp only [mem_parallelepiped_iff, Set.mem_finsetSum, Finset.mem_univ, forall_true_left,
    segment_eq_image, smul_zero, zero_add, ← Set.pi_univ_Icc, Set.mem_univ_pi]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t • v, fun {i} => ⟨t i, ht _, by simp⟩, rfl⟩
  rintro ⟨g, hg, rfl⟩
  choose t ht hg using @hg
  refine ⟨@t, @ht, ?_⟩
  simp_rw [hg]
/-
**convex_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_parallelepiped (v : ι -> E) : Convex Real (parallelepiped v)
参数：v : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `parallelepiped_eq_sum_segment`：parallelepiped_eq_sum_segment (v : ι -> E
) : parallelepiped v = ∑ i, segment Real 0 (v i)
· 使用定理 `convex_sum`：convex_sum {ι} {s : Finset ι} (t : ι -> Set E) (h : forall i
 in s, Convex 𝕜 (t i)) : Convex 𝕜 (∑ i in s, t i)
· 使用定理 `convex_segment`：convex_segment [IsOrderedRing 𝕜] (x y : E) : Convex 𝕜 [x
 -[𝕜] y]
-/
theorem convex_parallelepiped (v : ι → E) : Convex ℝ (parallelepiped v) := by
  rw [parallelepiped_eq_sum_segment]
  exact convex_sum _ fun _i _hi => convex_segment _ _

/-- A `parallelepiped` is the convex hull of its vertices -/
/-
**parallelepiped_eq_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelepiped_eq_convexHull (v : ι -> E) : parallelepiped v = convexHull 
Real (∑ i, {(0 : E), v i})
参数：v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_sum`：convexHull_sum {ι} (s : Finset ι) (t : ι -> Set E) : con
vexHull R (∑ i in s, t i) = ∑ i in s, convexHull R (t i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `convexHull_pair`：convexHull_pair [IsOrderedRing 𝕜] (x y : E) : convexHul
l 𝕜 {x, y} = segment 𝕜 x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `parallelepiped_eq_sum_segment`：parallelepiped_eq_sum_segment (v : ι -> E
) : parallelepiped v = ∑ i, segment Real 0 (v i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A `parallelepiped` is the convex hull of its vertices
-/
theorem parallelepiped_eq_convexHull (v : ι → E) :
    parallelepiped v = convexHull ℝ (∑ i, {(0 : E), v i}) := by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]

/-- The axis aligned parallelepiped over `ι → ℝ` is a cuboid. -/
/-
**parallelepiped_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelepiped_single [DecidableEq ι] (a : ι -> Real) : (parallelepiped fu
n i => Pi.single i (a i)) = Set.uIcc 0 a
参数：a : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `le_mul_of_le_one_left`：le_mul_of_le_one_left [ExistsAddOfLE R] [MulPosMo
no R] [AddRightMono R] [AddRightReflectLE R] (hb : b <= 0) (h : a <= 1) : b <= a
 * b
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The axis aligned parallelepiped over `ι → ℝ` is a cuboid.
-/
theorem parallelepiped_single [DecidableEq ι] (a : ι → ℝ) :
    (parallelepiped fun i => Pi.single i (a i)) = Set.uIcc 0 a := by
  ext x
  simp_rw [Set.uIcc, mem_parallelepiped_iff, Set.mem_Icc, Pi.le_def, ← forall_and, Pi.inf_apply,
    Pi.sup_apply, ← Pi.single_smul', Pi.one_apply, Pi.zero_apply, ← Pi.smul_apply',
    Finset.univ_sum_single (_ : ι → ℝ)]
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    specialize ht i
    simp_rw [smul_eq_mul, Pi.mul_apply]
    rcases le_total (a i) 0 with hai | hai
    · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai]
      exact ⟨le_mul_of_le_one_left hai ht.2, mul_nonpos_of_nonneg_of_nonpos ht.1 hai⟩
    · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai]
      exact ⟨mul_nonneg ht.1 hai, mul_le_of_le_one_left hai ht.2⟩
  · intro h
    refine ⟨fun i => x i / a i, fun i => ?_, funext fun i => ?_⟩
    · specialize h i
      rcases le_total (a i) 0 with hai | hai
      · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai] at h
        exact ⟨div_nonneg_of_nonpos h.2 hai, div_le_one_of_ge h.1 hai⟩
      · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai] at h
        exact ⟨div_nonneg h.1 hai, div_le_one_of_le₀ h.2 hai⟩
    · specialize h i
      simp only [smul_eq_mul, Pi.mul_apply]
      rcases eq_or_ne (a i) 0 with hai | hai
      · rw [hai, inf_idem, sup_idem, ← le_antisymm_iff] at h
        rw [hai, ← h, zero_div, zero_mul]
      · rw [div_mul_cancel₀ _ hai]

end AddCommGroup

section NormedSpace

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Module.Basis

/-- The parallelepiped spanned by a basis, as a compact set with nonempty interior. -/
/-
**Module.Basis.parallelepiped** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：parallelepiped (b : Basis ι Real E) : PositiveCompacts E where carrier
参数：b : Basis ι Real E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The parallelepiped spanned by a basis, as a compact set with nonempty interior.
-/
def parallelepiped (b : Basis ι ℝ E) : PositiveCompacts E where
  carrier := _root_.parallelepiped b
  isCompact' := IsCompact.image isCompact_Icc
      (continuous_finsetSum Finset.univ
        fun (i : ι) (_H : i ∈ Finset.univ) ↦ by fun_prop)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equivFunL.symm.toHomeomorph '' Icc 0 1)) by
      dsimp only [_root_.parallelepiped]
      convert! H
      exact (b.equivFun_symm_apply _).symm
    have A : Set.Nonempty (interior (Icc (0 : ι → ℝ) 1)) := by
      rw [← pi_univ_Icc, interior_pi_set (@finite_univ ι _)]
      simp only [univ_pi_nonempty_iff, Pi.zero_apply, Pi.one_apply, interior_Icc, nonempty_Ioo,
        zero_lt_one, imp_true_iff]
    rwa [← Homeomorph.image_interior, image_nonempty]

@[simp]
/-
**Module.Basis.coe_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_parallelepiped (b : Basis ι Real E) : (b.parallelepiped : Set E) = _ro
ot_.parallelepiped b
参数：b : Basis ι Real E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_parallelepiped (b : Basis ι ℝ E) :
    (b.parallelepiped : Set E) = _root_.parallelepiped b := rfl

@[simp]
/-
**Module.Basis.parallelepiped_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：parallelepiped_reindex (b : Basis ι Real E) (e : ι ≃ ι') : (b.reindex e).p
arallelepiped = b.parallelepiped
参数：b : Basis ι Real E；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.PositiveCompacts α}, ↑s = ↑t → s = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `parallelepiped_comp_equiv`：parallelepiped_comp_equiv (v : ι -> E) (e : ι
' ≃ ι) : parallelepiped (v ∘ e) = parallelepiped v
-/
theorem parallelepiped_reindex (b : Basis ι ℝ E) (e : ι ≃ ι') :
    (b.reindex e).parallelepiped = b.parallelepiped :=
  PositiveCompacts.ext <|
    (congr_arg _root_.parallelepiped (b.coe_reindex e)).trans (parallelepiped_comp_equiv b e.symm)
/-
**Module.Basis.parallelepiped_map** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：parallelepiped_map (b : Basis ι Real E) (e : E ≃ₗ[Real] F) : (b.map e).par
allelepiped = b.parallelepiped.map e (haveI
参数：b : Basis ι Real E；e : E ≃ₗ[Real] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.PositiveCompacts α}, ↑s = ↑t → s = t
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.isOpenMap_of_finiteDimensional`：isOpenMap_of_finiteDimensional
 (f : F ->ₗ[𝕜] E) (hf : Function.Surjective f) : IsOpenMap f
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `image_parallelepiped`：image_parallelepiped (f : E ->ₗ[Real] F) (v : ι ->
 E) : f '' parallelepiped v = parallelepiped (f ∘ v)
-/
theorem parallelepiped_map (b : Basis ι ℝ E) (e : E ≃ₗ[ℝ] F) :
    (b.map e).parallelepiped = b.parallelepiped.map e
    (haveI := b.finiteDimensional_of_finite
    LinearMap.continuous_of_finiteDimensional e.toLinearMap)
    (haveI := (b.map e).finiteDimensional_of_finite
    LinearMap.isOpenMap_of_finiteDimensional _ e.surjective) :=
  PositiveCompacts.ext (image_parallelepiped e.toLinearMap _).symm
/-
**Module.Basis.prod_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_parallelepiped (v : Basis ι Real E) (w : Basis ι' Real F) : (v.prod w
).parallelepiped = v.parallelepiped ×ˢ w.parallelepiped
参数：v : Basis ι Real E；w : Basis ι' Real F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.PositiveCompacts α}, ↑s = ↑t → s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.fst_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Prod.snd_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem prod_parallelepiped (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
    (v.prod w).parallelepiped = v.parallelepiped ×ˢ w.parallelepiped := by
  ext x
  simp only [Basis.coe_parallelepiped, TopologicalSpace.PositiveCompacts.coe_prod, Set.mem_prod,
    mem_parallelepiped_iff]
  constructor
  · intro h
    rcases h with ⟨t, ht1, ht2⟩
    constructor
    · use t ∘ Sum.inl
      constructor
      · exact ⟨(ht1.1 <| Sum.inl ·), (ht1.2 <| Sum.inl ·)⟩
      simp [ht2, Prod.fst_sum]
    · use t ∘ Sum.inr
      constructor
      · exact ⟨(ht1.1 <| Sum.inr ·), (ht1.2 <| Sum.inr ·)⟩
      simp [ht2, Prod.snd_sum]
  intro h
  rcases h with ⟨⟨t, ht1, ht2⟩, ⟨s, hs1, hs2⟩⟩
  use Sum.elim t s
  constructor
  · constructor
    · change ∀ x : ι ⊕ ι', 0 ≤ Sum.elim t s x
      aesop
    · change ∀ x : ι ⊕ ι', Sum.elim t s x ≤ 1
      aesop
  ext
  · simp [ht2, Prod.fst_sum]
  · simp [hs2, Prod.snd_sum]

variable [MeasurableSpace E] [BorelSpace E]

/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
irreducible_def addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped

/-
**Module.Basis._root_.isAddHaarMeasure_basis_addHaar** 是 Mathlib 中的一个实例，位于命名空间 `
Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.isAddHaarMeasure_basis_addHaar (b : Basis ι ℝ E) : IsAddHaarMeasure b.addHaar := by
  rw [Basis.addHaar]; exact Measure.isAddHaarMeasure_addHaarMeasure _
/-
**Module.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (b : Basis ι ℝ E) : SigmaFinite b.addHaar := by
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  rw [Basis.addHaar_def]; exact sigmaFinite_addHaarMeasure

/-- Let `μ` be a σ-finite left invariant measure on `E`. Then `μ` is equal to the Haar measure
defined by `b` iff the parallelepiped defined by `b` has measure `1` for `μ`. -/
/-
**Module.Basis.addHaar_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：addHaar_eq_iff [SecondCountableTopology E] (b : Basis ι Real E) (μ : Measu
re E) [SigmaFinite μ] [IsAddLeftInvariant μ] : b.addHaar = μ ↔ μ b.parallelepipe
d = 1
参数：b : Basis ι Real E；μ : Measure E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.addHaar_def`：∀ {ι : Type u_5} {E : Type u_6} [inst : Fintyp
e ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : Meas
urableSpace E]…
· 使用定理 `MeasureTheory.Measure.addHaarMeasure_eq_iff`：∀ {G : Type u_1} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G]   [in
st_3 : MeasurableSpace G] [inst_4…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Let `μ` be a σ-finite left invariant measure on `E`. Then `μ` is equal to the Ha
ar measure
defined by `b` iff the parallelepiped defined by `b` has measure `1` for `μ`.
-/
theorem addHaar_eq_iff [SecondCountableTopology E] (b : Basis ι ℝ E) (μ : Measure E)
    [SigmaFinite μ] [IsAddLeftInvariant μ] :
    b.addHaar = μ ↔ μ b.parallelepiped = 1 := by
  rw [Basis.addHaar_def]
  exact addHaarMeasure_eq_iff b.parallelepiped μ

@[simp]
/-
**Module.Basis.addHaar_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：addHaar_reindex (b : Basis ι Real E) (e : ι ≃ ι') : (b.reindex e).addHaar 
= b.addHaar
参数：b : Basis ι Real E；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.addHaar_def`：∀ {ι : Type u_5} {E : Type u_6} [inst : Fintyp
e ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : Meas
urableSpace E]…
· 使用定理 `Module.Basis.parallelepiped_reindex`：parallelepiped_reindex (b : Basis ι
 Real E) (e : ι ≃ ι') : (b.reindex e).parallelepiped = b.parallelepiped
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem addHaar_reindex (b : Basis ι ℝ E) (e : ι ≃ ι') :
    (b.reindex e).addHaar = b.addHaar := by
  rw [Basis.addHaar, b.parallelepiped_reindex e, ← Basis.addHaar]
/-
**Module.Basis.addHaar_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：addHaar_self (b : Basis ι Real E) : b.addHaar (_root_.parallelepiped b) = 
1
参数：b : Basis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.addHaar_def`：∀ {ι : Type u_5} {E : Type u_6} [inst : Fintyp
e ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : Meas
urableSpace E]…
· 使用定理 `MeasureTheory.Measure.addHaarMeasure_self`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G]   [inst
_3 : MeasurableSpace G] [inst_4…
-/
theorem addHaar_self (b : Basis ι ℝ E) : b.addHaar (_root_.parallelepiped b) = 1 := by
  rw [Basis.addHaar]; exact addHaarMeasure_self

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopologyEither E F]
/-
**Module.Basis.prod_addHaar** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_addHaar (v : Basis ι Real E) (w : Basis ι' Real F) : (v.prod w).addHa
ar = v.addHaar.prod w.addHaar
参数：v : Basis ι Real E；w : Basis ι' Real F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.addHaar_eq_iff`：addHaar_eq_iff [SecondCountableTopology E] 
(b : Basis ι Real E) (μ : Measure E) [SigmaFinite μ] [IsAddLeftInvariant μ] : b.
addHaar = μ ↔ μ b…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.prod.instSigmaFinite`：∀ {α : Type u_4} {β : Type u
_5} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFi
nite μ]   {x_1 : MeasurableSpace…
· 使用定理 `Module.Basis.instSigmaFiniteAddHaar`：∀ {ι : Type u_1} {E : Type u_3} [in
st : Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [in
st_3 : MeasurableSpace E]…
· 使用定理 `MeasureTheory.Measure.prod.instIsAddLeftInvariant`：∀ {G : Type u_1} [ins
t : MeasurableSpace G] [inst_1 : Add G] {μ : MeasureTheory.Measure G} [Measurabl
eAdd G]   [μ.IsAddLeftInvariant] [Measu…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `isAddHaarMeasure_basis_addHaar`：∀ {ι : Type u_1} {E : Type u_3} [inst : 
Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 
: MeasurableSpace E]…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.prod_parallelepiped`：prod_parallelepiped (v : Basis ι Real 
E) (w : Basis ι' Real F) : (v.prod w).parallelepiped = v.parallelepiped ×ˢ w.par
allelepiped
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.addHaar_self`：addHaar_self (b : Basis ι Real E) : b.addHaar
 (_root_.parallelepiped b) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_addHaar (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
    (v.prod w).addHaar = v.addHaar.prod w.addHaar := by
  have : FiniteDimensional ℝ E := v.finiteDimensional_of_finite
  have : FiniteDimensional ℝ F := w.finiteDimensional_of_finite
  simp [(v.prod w).addHaar_eq_iff, Basis.prod_parallelepiped, Basis.addHaar_self]

end Module.Basis

end NormedSpace

end Fintype

/-- A finite-dimensional inner product space has a canonical measure, the Lebesgue measure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orthonormal basis
is proved in `orthonormalBasis.volume_parallelepiped`.

This instance creates:

- a potential non-defeq diamond with the natural instance for `MeasureSpace (ULift E)`,
  which does not exist in Mathlib at the moment;

- a diamond with the existing instance `MeasureTheory.Measure.instMeasureSpacePUnit`.

However, we've decided not to refactor until one of these diamonds starts creating issues, see
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Hausdorff.20measure.20normalisation
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-dimensional inner product space has a canonical measure, the Lebesgue m
easure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the
 measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orth
onormal basis
is proved in `orthonormalBasis.volume_parallelepiped`.

This instance creates:

- a potential non-defeq diamond with the natural instance for `MeasureSpace (ULi
ft E)`,
  which does not exist in Mathlib at the moment;

- a diamond with the existing instance `MeasureTheory.Measure.instMeasureSpacePU
nit`.

However, we've decided not to refactor until one of these diamonds starts creati
ng issues, see
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Hausdorff.
20measure.20normalisation
-/
instance (priority := 100) measureSpaceOfInnerProductSpace [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    MeasureSpace E where volume := (stdOrthonormalBasis ℝ E).toBasis.addHaar
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : IsAddHaarMeasure (volume : Measure E) :=
  isAddHaarMeasure_basis_addHaar _

/- This instance should not be necessary, but Lean has difficulties to find it in product
situations if we do not declare it explicitly. -/
/-
**Real.measureSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.measureSpace : MeasureSpace Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance should not be necessary, but Lean has difficulties to find it in p
roduct
situations if we do not declare it explicitly.
-/
instance Real.measureSpace : MeasureSpace ℝ := by infer_instance
