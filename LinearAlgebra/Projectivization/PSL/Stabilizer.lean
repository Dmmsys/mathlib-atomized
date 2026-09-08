/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/

module

public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Stabilizer of a line in PSL(n, F)
This file contains key constructions to prove that `PSL(n, F)` is simple via
showing it has an Iwasawa structure.

## Main definitions

* `Matrix.SpecialLinearGroup.lineStab` : the unipotent radical attached to a subspace `L ⊆ ι → F`
  defined as the subgroup of `SL ι F` consisting of matrices `A` such that `A - 1`
  sends every vector into `L`.

* `PSL.iwasawaT` : the candidate family of subgroups for the Iwasawa structure on
  `PSL ι F` acting on the projective space `ℙ F (ι → F)` from `Matrix.SpecialLinearGroup.lineStab`.

-/

@[expose] public section

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The "unipotent radical" attached to a subspace `L ⊆ ι → F`: the subgroup of
`SL ι F` consisting of matrices `A` such that `A - 1` sends every vector into `L`.
When `L` is one-dimensional this is an abelian subgroup of the stabilizer of `L` in `SL`. -/
/-
**Matrix.SpecialLinearGroup.lineStab** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.SpecialLinearGroup.lineStab (L : Submodule F (ι -> F)) : Subgroup (
SpecialLinearGroup ι F) where carrier
参数：L : Submodule F (ι -> F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "unipotent radical" attached to a subspace `L ⊆ ι → F`: the subgroup of
`SL ι F` consisting of matrices `A` such that `A - 1` sends every vector into `L
`.
When `L` is one-dimensional this is an abelian subgroup of the stabilizer of `L`
 in `SL`.
-/
def Matrix.SpecialLinearGroup.lineStab (L : Submodule F (ι → F)) :
    Subgroup (SpecialLinearGroup ι F) where
  carrier := {A | ∀ w : ι → F, A • w - w ∈ L}
  one_mem' := by simp
  mul_mem' {A B} hA hB := fun w ↦ by
    simp only [Set.mem_ofPred_eq, mul_smul] at hA hB ⊢
    rw [show A • B • w - w = ((A • (B • w) - A • w) - (B • w - w)) +
      (B • w - w) + (A • w - w) by abel, ← smul_sub]
    exact add_mem (add_mem (hA _) (hB w)) (hA w)
  inv_mem' {A} hA := fun w ↦ by
    convert neg_mem (hA (A⁻¹ • w)) using 1
    rw [← mul_smul, mul_inv_cancel, one_smul, neg_sub]

@[simp]
/-
**Matrix.SpecialLinearGroup.mem_lineStab_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.SpecialLinearGroup.mem_lineStab_iff (A : SpecialLinearGroup ι F) (L
 : Submodule F (ι -> F)) : A in lineStab L ↔ forall w : ι -> F, A • w - w in L
参数：A : SpecialLinearGroup ι F；L : Submodule F (ι -> F)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Matrix.SpecialLinearGroup.mem_lineStab_iff (A : SpecialLinearGroup ι F)
    (L : Submodule F (ι → F)) : A ∈ lineStab L ↔ ∀ w : ι → F, A • w - w ∈ L :=
  Iff.rfl

open scoped LinearAlgebra.Projectivization

/-- The candidate family of subgroups for the Iwasawa structure on
`PSL ι F` acting on the projective space `ℙ F (ι → F)`: the unipotent radical
attached to the line through `p`. -/
/-
**PSL.iwasawaT** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PSL.iwasawaT (p : ℙ F (ι -> F)) : Subgroup (Matrix.ProjectiveSpecialLinear
Group ι F)
参数：p : ℙ F (ι -> F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The candidate family of subgroups for the Iwasawa structure on
`PSL ι F` acting on the projective space `ℙ F (ι → F)`: the unipotent radical
attached to the line through `p`.
-/
noncomputable abbrev PSL.iwasawaT (p : ℙ F (ι → F)) :
    Subgroup (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  Subgroup.map (QuotientGroup.mk' _)
    (Matrix.SpecialLinearGroup.lineStab p.submodule)

open scoped Pointwise
/-
**PSL.smul_submodule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PSL.smul_submodule (g : Matrix.SpecialLinearGroup ι F) (p : ℙ F (ι -> F)) 
: (g • p).submodule = g • p.submodule
参数：g : Matrix.SpecialLinearGroup ι F；p : ℙ F (ι -> F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `Matrix.instSMulCommClassSpecialLinearGroupForall`：∀ {F : Type u_1} [inst
 : CommRing F] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι],   S
MulCommClass (Matrix.SpecialLinearGrou…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma PSL.smul_submodule (g : Matrix.SpecialLinearGroup ι F) (p : ℙ F (ι → F)) :
    (g • p).submodule = g • p.submodule:= by
  induction p using Projectivization.ind with | _ v hv => ?_
  simp [Submodule.ext_iff, Submodule.pointwise_smul_def, Submodule.mem_span_singleton, smul_comm]

/-- Equivariance of `lineStab` under conjugation by elements of `SL`. -/
/-
**Matrix.SpecialLinearGroup.lineStab_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.SpecialLinearGroup.lineStab_smul (g : Matrix.SpecialLinearGroup ι F
) (L : Submodule F (ι -> F)) : Matrix.SpecialLinearGroup.lineStab (g • L) = MulA
ut.conj g • Matrix.SpecialLinearGroup.lineStab L
参数：g : Matrix.SpecialLinearGroup ι F；L : Submodule F (ι -> F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Matrix.instSMulCommClassSpecialLinearGroupForall`：∀ {F : Type u_1} [inst
 : CommRing F] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι],   S
MulCommClass (Matrix.SpecialLinearGrou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_pointwise_smul_iff_inv_smul_mem`：mem_pointwise_smul_iff_inv
_smul_mem {a : α} {S : Subgroup G} {x : G} : x in a • S ↔ a⁻¹ • x in S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulAut.inv_apply`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M)
, e⁻¹ m = (MulEquiv.symm e) m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Equivariance of `lineStab` under conjugation by elements of `SL`.
-/
lemma Matrix.SpecialLinearGroup.lineStab_smul
    (g : Matrix.SpecialLinearGroup ι F) (L : Submodule F (ι → F)) :
    Matrix.SpecialLinearGroup.lineStab (g • L) =
      MulAut.conj g • Matrix.SpecialLinearGroup.lineStab L := by
  ext A
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_lineStab_iff, Submodule.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.inv_apply, MulAut.conj_symm_apply]
  refine ⟨fun hA w ↦ ?_, fun hA w ↦ ⟨g⁻¹ • (A • w - w), ?_, by simp⟩⟩
  · obtain ⟨v, hv, hvw⟩ := hA (g • w)
    simp_all [eq_comm (a := g • v), sub_eq_iff_eq_add, mul_smul]
  · simpa [mul_smul, smul_sub] using hA (g⁻¹ • w)

/-- The SL-level equivariance pushed through the quotient: the image in `PSL` of
the conjugate `MulAut.conj g_SL • H` equals `MulAut.conj (mk g_SL) • (image of H)`. -/
/-
**PSL.iwasawaT_map_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PSL.iwasawaT_map_conj (g : Matrix.SpecialLinearGroup ι F) (H : Subgroup (M
atrix.SpecialLinearGroup ι F)) : Subgroup.map (QuotientGroup.mk' (Subgroup.cente
r (Matrix.SpecialLinearGroup ι F))) (MulAut.conj g • H) = MulAut.conj (QuotientG
roup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F) • Subgroup.map (QuotientGro
up.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F))) H
参数：g : Matrix.SpecialLinearGroup ι F；H : Subgroup (Matrix.SpecialLinearGroup ι F
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulAut.inv_apply`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M)
, e⁻¹ m = (MulEquiv.symm e) m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b

--- 原说明 ---
The SL-level equivariance pushed through the quotient: the image in `PSL` of
the conjugate `MulAut.conj g_SL • H` equals `MulAut.conj (mk g_SL) • (image of H
)`.
-/
lemma PSL.iwasawaT_map_conj (g : Matrix.SpecialLinearGroup ι F)
    (H : Subgroup (Matrix.SpecialLinearGroup ι F)) :
    Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F)))
        (MulAut.conj g • H) =
      MulAut.conj (QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F) •
        Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F))) H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, QuotientGroup.mk'_apply]
  exact ⟨fun ⟨a, ha, ha'⟩ ↦ ⟨g⁻¹ * a * g, ha, by simp [ha']⟩,
    fun ⟨a, ha, hx⟩ ↦ ⟨g * a * g⁻¹, by simp [mul_assoc, ha], by simp [hx, mul_assoc]⟩⟩
/-
**LinearMap.exists_restrict_span_singleton_eq_smul_id** 是 Mathlib 中的一个引理，位于命名空间 
``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma LinearMap.exists_restrict_span_singleton_eq_smul_id
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    {v : V} {A : V →ₗ[R] V} (hAv : A v ∈ Submodule.span R {v}) :
    ∃ c : R, A v = c • v ∧ ∃ hcomap : Submodule.span R {v} ≤ (Submodule.span R {v}).comap A,
      A.restrict hcomap = (c • LinearMap.id : Submodule.span R {v} →ₗ[R] _) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hAv
  refine ⟨c, hc.symm, fun w hw ↦ ?_, LinearMap.ext fun ⟨w, hw⟩ ↦ ?_⟩
  <;> obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  · simpa [Submodule.mem_comap, map_smul] using Submodule.smul_mem _ _ hAv
  · simp [Subtype.ext_iff, ← hc, smul_comm a c v]
/-
**Matrix.SpecialLinearGroup.lineStab_fix_of_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.SpecialLinearGroup.lineStab_fix_of_span (v : ι -> F) (hv : v != 0) 
(A : Matrix.SpecialLinearGroup ι F) (hA : A in lineStab (Submodule.span F {v})) 
: A • v = v
参数：v : ι -> F；hv : v != 0；A : Matrix.SpecialLinearGroup ι F；hA : A in lineStab (
Submodule.span F {v})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer.0.LinearM
ap.exists_restrict_span_singleton_eq_smul_id`：∀ {R : Type u_3} {V : Type u_4} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid V] [inst_2 : _root_.Module R V] {v
 : V}   {A : V →ₗ[R] V},  …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.Quotient.induction_on`：induction_on {C : M ⧸ p -> Prop} (x : M
 ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) : C x
· 使用定理 `LinearMap.det_eq_det_mul_det`：LinearMap.det_eq_det_mul_det (e : V ->ₗ[R]
 V) (he : W <= W.comap e) : e.det = (e.restrict he).det * (W.mapQ W e he).det
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.det_id`：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `LinearMap.det_smul`：det_smul [Module.Free A M] (c : A) (f : M ->ₗ[A] M) 
: LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.det_toLin'`：det_toLin' (f : Matrix ι ι R) : LinearMap.det (Mat
rix.toLin' f) = Matrix.det f
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Matrix.SpecialLinearGroup.lineStab_fix_of_span
    (v : ι → F) (hv : v ≠ 0)
    (A : Matrix.SpecialLinearGroup ι F)
    (hA : A ∈ lineStab (Submodule.span F {v})) :
    A • v = v := by
  set L : Submodule F (ι → F) := Submodule.span F {v}
  obtain ⟨c, hcv, hcomap, hres⟩ :=
    LinearMap.exists_restrict_span_singleton_eq_smul_id (A := A.toLin'.toLinearMap)
      (by simpa using! add_mem (hA v) (Submodule.mem_span_singleton_self v))
  have hQ : L.mapQ L A.toLin'.toLinearMap hcomap = LinearMap.id := LinearMap.ext fun x ↦ by
    induction x using Submodule.Quotient.induction_on with
    | _ w => simpa [Submodule.Quotient.eq] using! hA w
  have hdet := A.toLin'.toLinearMap.det_eq_det_mul_det L hcomap
  rw [show LinearMap.det A.toLin'.toLinearMap = 1 by simp [toLin'_to_linearMap],
      hres, hQ, LinearMap.det_smul, finrank_span_singleton hv, pow_one,
      LinearMap.det_id, LinearMap.det_id, mul_one, mul_one] at hdet
  exact hcv.trans (hdet ▸ one_smul F v)

/-- The subgroup `lineStab (span F {v})` is commutative when `v ≠ 0`. -/
/-
**Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span' (v : ι -> F) 
(hv : v != 0) (A B : SpecialLinearGroup ι F) (hA : A in SpecialLinearGroup.lineS
tab (Submodule.span F {v})) (hB : B in SpecialLinearGroup.lineStab (Submodule.sp
an F {v})) : A * B = B * A
参数：v : ι -> F；hv : v != 0；A B : SpecialLinearGroup ι F；hA : A in SpecialLinearGr
oup.lineStab (Submodule.span F {v})；hB : B in SpecialLinearGroup.lineStab (Submo
dule.span F {v})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matrix.ext_iff_smul`：ext_iff_smul {A B : Matrix n n R} : A = B ↔ forall 
v : n -> R, A • v = B • v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `sub_left_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, b - a = 
c - a ↔ b = c
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Matrix.instSMulCommClassSpecialLinearGroupForall`：∀ {F : Type u_1} [inst
 : CommRing F] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι],   S
MulCommClass (Matrix.SpecialLinearGrou…
· 使用引理 `Matrix.SpecialLinearGroup.lineStab_fix_of_span`：Matrix.SpecialLinearGrou
p.lineStab_fix_of_span (v : ι -> F) (hv : v != 0) (A : Matrix.SpecialLinearGroup
 ι F) (hA : A in lineStab (Submodule…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
The subgroup `lineStab (span F {v})` is commutative when `v ≠ 0`.
-/
lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'
    (v : ι → F) (hv : v ≠ 0) (A B : SpecialLinearGroup ι F)
    (hA : A ∈ SpecialLinearGroup.lineStab (Submodule.span F {v}))
    (hB : B ∈ SpecialLinearGroup.lineStab (Submodule.span F {v})) :
    A * B = B * A := by
  refine Subtype.ext <| ext_iff_smul.2 fun w ↦ ?_
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp (hA w)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp (hB w)
  simp only [coe_mul, mul_smul, ← Matrix.SpecialLinearGroup.smul_def]
  rw [← sub_add_cancel (A • w) w, ← hα, ← sub_add_cancel (B • w) w,
    ← hβ, smul_add, smul_add, ← sub_left_inj (a := w), ← add_sub, ← hα, ← add_sub, ← hβ,
    smul_comm, lineStab_fix_of_span v hv A hA, smul_comm, lineStab_fix_of_span v hv B hB, add_comm]
/-
**Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span (v : ι -> F) (
hv : v != 0) : IsMulCommutative (lineStab (Submodule.span F {v}))
参数：v : ι -> F；hv : v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用引理 `Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'`：Matrix.Spe
cialLinearGroup.lineStab_isMulCommutative_of_span' (v : ι -> F) (hv : v != 0) (A
 B : SpecialLinearGroup ι F) (hA : A in SpecialLin…
-/
lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span
    (v : ι → F) (hv : v ≠ 0) : IsMulCommutative (lineStab (Submodule.span F {v})) :=
  ⟨⟨fun ⟨A, hA⟩ ⟨B, hB⟩ ↦ by simpa using lineStab_isMulCommutative_of_span' v hv A B hA hB⟩⟩
