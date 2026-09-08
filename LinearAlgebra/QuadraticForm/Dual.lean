/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Quadratic form structures related to `Module.Dual`

## Main definitions

* `LinearMap.dualProd R M`, the bilinear form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.dualProd R M`, the quadratic form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.toDualProd : (Q.prod <| -Q) →qᵢ QuadraticForm.dualProd R M` a form-preserving map
  from `(Q.prod <| -Q)` to `QuadraticForm.dualProd R M`.

-/

@[expose] public section

variable (R M N : Type*)

namespace LinearMap

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The symmetric bilinear form on `Module.Dual R M × M` defined as
`B (f, x) (g, y) = f y + g x`. -/
@[simps!]
/-
**LinearMap.dualProd** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：dualProd : LinearMap.BilinForm R (Module.Dual R M × M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetric bilinear form on `Module.Dual R M × M` defined as
`B (f, x) (g, y) = f y + g x`.
-/
def dualProd : LinearMap.BilinForm R (Module.Dual R M × M) :=
    (applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M) +
      ((applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M)).flip
/-
**LinearMap.isSymm_dualProd** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymm_dualProd : (dualProd R M).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem isSymm_dualProd : (dualProd R M).IsSymm := ⟨fun _x _y => add_comm _ _⟩

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.separatingLeft_dualProd** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：separatingLeft_dualProd : (dualProd R M).SeparatingLeft ↔ Function.Injecti
ve (Module.Dual.eval R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.dualProdDualEquivDual_symm_apply`：∀ (R : Type u_1) (M : Type u_3)
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   (M' : Type u_4) [inst_3 : …
· 使用定理 `LinearMap.dualProd_apply_apply`：∀ (R : Type u_1) (M : Type u_2) [inst : 
CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (a a_1
 : Module.Dual R M ×…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearMap.coe_prodMap`：coe_prodMap (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) 
: ⇑(f.prodMap g) = Prod.map f g
· 使用定理 `Prod.map_injective`：map_injective [Nonempty α] [Nonempty β] {f : α -> γ}
 {g : β -> δ} : Injective (map f g) ↔ Injective f ∧ Injective g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
（共 32 条，此处仅展示前 30 条）
-/
theorem separatingLeft_dualProd :
    (dualProd R M).SeparatingLeft ↔ Function.Injective (Module.Dual.eval R M) := by
  rw [separatingLeft_iff_ker_eq_bot, ker_eq_bot]
  let e := LinearEquiv.prodComm R _ _ ≪≫ₗ Module.dualProdDualEquivDual R (Module.Dual R M) M
  let h_d := e.symm.toLinearMap.comp (dualProd R M)
  refine (Function.Injective.of_comp_iff e.symm.injective
    (dualProd R M)).symm.trans ?_
  rw [← LinearEquiv.coe_toLinearMap, ← coe_comp]
  change Function.Injective h_d ↔ _
  have : h_d = prodMap id (Module.Dual.eval R M) := by
    refine ext fun x => Prod.ext ?_ ?_
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
  rw [this, coe_prodMap]
  refine Prod.map_injective.trans ?_
  exact and_iff_right Function.injective_id

end Ring

end LinearMap

open QuadraticMap

namespace QuadraticForm
section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The quadratic form on `Module.Dual R M × M` defined as `Q (f, x) = f x`. -/
@[simps]
/-
**QuadraticForm.dualProd** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：dualProd : QuadraticForm R (Module.Dual R M × M) where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quadratic form on `Module.Dual R M × M` defined as `Q (f, x) = f x`.
-/
def dualProd : QuadraticForm R (Module.Dual R M × M) where
  toFun p := p.1 p.2
  toFun_smul a p := by
    rw [Prod.smul_fst, Prod.smul_snd, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_assoc]
  exists_companion' :=
    ⟨LinearMap.dualProd R M, fun p q => by
      rw [LinearMap.dualProd_apply_apply, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add,
        map_add, add_right_comm _ (q.1 q.2), add_comm (q.1 p.2) (p.1 q.2), ← add_assoc, ←
        add_assoc]⟩

@[simp]
/-
**QuadraticForm._root_.LinearMap.dualProd.toQuadraticForm** 是 Mathlib 中的一个定理，位于命
名空间 `QuadraticForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.dualProd.toQuadraticForm :
    (LinearMap.dualProd R M).toQuadraticMap = 2 • dualProd R M :=
  ext fun _a => (two_nsmul _).symm

variable {R M N}

/-- Any module isomorphism induces a quadratic isomorphism between the corresponding `dual_prod.` -/
@[simps!]
/-
**QuadraticForm.dualProdIsometry** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：dualProdIsometry (f : M ≃ₗ[R] N) : (dualProd R M).IsometryEquiv (dualProd 
R N) where toLinearEquiv
参数：f : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any module isomorphism induces a quadratic isomorphism between the corresponding
 `dual_prod.`
-/
def dualProdIsometry (f : M ≃ₗ[R] N) : (dualProd R M).IsometryEquiv (dualProd R N) where
  toLinearEquiv := f.dualMap.symm.prodCongr f
  map_app' x := DFunLike.congr_arg x.fst <| f.symm_apply_apply _

/-- `QuadraticForm.dualProd` commutes (isometrically) with `QuadraticForm.prod`. -/
@[simps!]
/-
**QuadraticForm.dualProdProdIsometry** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：dualProdProdIsometry : (dualProd R (M × N)).IsometryEquiv ((dualProd R M).
prod (dualProd R N)) where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuadraticForm.dualProd` commutes (isometrically) with `QuadraticForm.prod`.
-/
def dualProdProdIsometry :
    (dualProd R (M × N)).IsometryEquiv ((dualProd R M).prod (dualProd R N)) where
  toLinearEquiv :=
    (Module.dualProdDualEquivDual R M N).symm.prodCongr (LinearEquiv.refl R (M × N)) ≪≫ₗ
      LinearEquiv.prodProdProdComm R _ _ M N
  map_app' m :=
    (m.fst.map_add _ _).symm.trans <| DFunLike.congr_arg m.fst <| Prod.ext (add_zero _) (zero_add _)

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]
variable {R M}

set_option backward.defeqAttrib.useBackward true in
/-- The isometry sending `(Q.prod <| -Q)` to `(QuadraticForm.dualProd R M)`.

This is `σ` from Proposition 4.8, page 84 of
[*Hermitian K-Theory and Geometric Applications*][hyman1973]; though we swap the order of the pairs.
-/
@[simps!]
/-
**QuadraticForm.toDualProd** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：toDualProd (Q : QuadraticForm R M) [Invertible (2 : R)] : (Q.prod <| -Q) -
>qᵢ QuadraticForm.dualProd R M where toLinearMap
参数：Q : QuadraticForm R M；2 : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isometry sending `(Q.prod <| -Q)` to `(QuadraticForm.dualProd R M)`.

This is `σ` from Proposition 4.8, page 84 of
[*Hermitian K-Theory and Geometric Applications*][hyman1973]; though we swap the
 order of the pairs.
-/
def toDualProd (Q : QuadraticForm R M) [Invertible (2 : R)] :
    (Q.prod <| -Q) →qᵢ QuadraticForm.dualProd R M where
  toLinearMap := LinearMap.prod
    (Q.associated.comp (LinearMap.fst _ _ _) + Q.associated.comp (LinearMap.snd _ _ _))
    (LinearMap.fst _ _ _ - LinearMap.snd _ _ _)
  map_app' x := by
    dsimp only [QuadraticMap.associated, QuadraticMap.associatedHom]
    dsimp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearMap.prod_apply, Function.prod_apply, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.sub_apply, dualProd_apply, polarBilin_apply_apply, QuadraticMap.prod_apply]
    simp only [neg_apply, polar_sub_right, polar_self, nsmul_eq_mul, Nat.cast_ofNat,
      polar_comm _ x.1 x.2, smul_sub, Module.End.smul_def, sub_add_sub_cancel,
      ← sub_eq_add_neg (Q x.1) (Q x.2)]
    rw [← map_sub (⅟2 : Module.End R R), ← mul_sub, ← Module.End.smul_def]
    simp only [Module.End.smul_def, half_moduleEnd_apply_eq_half_smul, smul_eq_mul,
      invOf_mul_cancel_left']

/-!
TODO: show that `QuadraticForm.toDualProd` is an `QuadraticForm.IsometryEquiv`
-/

end Ring

end QuadraticForm

/-- Vectors which subtend obtuse angles with each other and all lie in the same half-space are
linearly independent.

This is [serre1965](Ch. V, §9, Lemma 4). -/
/-
**LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero {ι R M : Type*} 
[CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R 
M] (B : LinearMap.BilinForm R M) (hB : B.toQuadraticMap.PosDef) (f : Module.Dual
 R M) (v : ι -> M) (hp : forall i, 0 < f (v i)) (hn : Pairwise fun i j => B (v i
) (v j) <= 0) : LinearIndependent R v
参数：B : LinearMap.BilinForm R M；hB : B.toQuadraticMap.PosDef；f : Module.Dual R M；
v : ι -> M；hp : forall i, 0 < f (v i)；hn : Pairwise fun i j => B (v i) (v j) <= 
0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Vectors which subtend obtuse angles with each other and all lie in the same half
-space are
linearly independent.

This is [serre1965](Ch. V, §9, Lemma 4).
-/
lemma LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero {ι R M : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (hB : B.toQuadraticMap.PosDef)
    (f : Module.Dual R M) (v : ι → M)
    (hp : ∀ i, 0 < f (v i))
    (hn : Pairwise fun i j ↦ B (v i) (v j) ≤ 0) :
    LinearIndependent R v := by
  refine linearIndependent_iff'.mpr fun s c hc ↦ ?_
  set x := ∑ i ∈ s with 0 < c i, c i • v i with hx
  set y := ∑ i ∈ s with 0 < -c i, (-c i) • v i with hy
  replace hc : x = y := by
    classical
    simp_rw [hx, hy, neg_smul, Finset.sum_neg_distrib, ← add_eq_zero_iff_eq_neg]
    rw [← hc, ← Finset.sum_union, Finset.sum_subset]
    · grind only [= Finset.subset_iff, = Finset.mem_union, = Finset.mem_filter]
    · simp +contextual [eq_comm (a := (0 : R))]
    · grind only [Finset.disjoint_filter]
  have hx₀ : x = 0 := by
    suffices B x y ≤ 0 by simpa [hc, ← hB.le_zero_iff, B.toQuadraticMap_apply]
    suffices 0 ≤ ∑ x ∈ s with c x < 0, ∑ i ∈ s with 0 < c i, c x * (c i * (B (v i)) (v x)) by
      simpa [hx, hy, map_neg, Finset.mul_sum]
    refine Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦ ?_
    grind [Pairwise, mul_nonneg_iff, mul_nonpos_iff]
  have H (c : ι → R) (h : ∑ i ∈ s with 0 < c i, c i • v i = 0) (i : ι) (hi : i ∈ s) : c i ≤ 0 := by
    have : ∑ i ∈ s with 0 < c i, c i * f (v i) = 0 := by simpa using (congr(f $h))
    rw [Finset.sum_eq_zero_iff_of_nonneg (by grind [mul_nonneg])] at this
    by_contra! hi'
    have : 0 < c i * f (v i) := mul_pos hi' (hp i)
    grind
  replace hx (i : ι) (hi : i ∈ s) : c i ≤ 0 := H _ (by grind) i hi
  replace hy (i : ι) (hi : i ∈ s) : -c i ≤ 0 := H (-c ·) (by grind) i hi
  grind
