/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Reducing a module modulo an element of the ring

Given a commutative ring `R` and an element `r : R`, the association
`M ↦ M ⧸ rM` extends to a functor on the category of `R`-modules. This functor
is isomorphic to the functor of tensoring by `R ⧸ (r)` on either side, but can
be more convenient to work with since we can work with quotient types instead
of fiddling with simple tensors.

## Tags

module, commutative algebra
-/

@[expose] public section

open scoped Pointwise

variable {R} [CommRing R] (r : R) (M : Type*) {M' M''}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']

/-- An abbreviation for `M⧸rM` that keeps us from having to write
`(⊤ : Submodule R M)` over and over to satisfy the typechecker. -/
/-
**QuotSMulTop** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：QuotSMulTop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `M⧸rM` that keeps us from having to write
`(⊤ : Submodule R M)` over and over to satisfy the typechecker.
-/
abbrev QuotSMulTop := M ⧸ r • (⊤ : Submodule R M)

namespace QuotSMulTop

open Submodule Function TensorProduct

/-- If `M'` is isomorphic to `M''` as `R`-modules, then `M'⧸rM'` is isomorphic to `M''⧸rM''`. -/
/-
**QuotSMulTop.congr** 是 Mathlib 中的一个定义，位于命名空间 `QuotSMulTop`。
形式化陈述：{R : Type u_2} →   [inst : CommRing R] →     (r : R) →       {M' : Type u_
3} →         {M'' : Type u_4} →           [inst_1 : AddCommGroup M'] →          
   [inst_2 : _root_.Module R M'] →               [inst_3 : AddCommGroup M''] →  
               [inst_4 : _root_.Module R M''] → (M' ≃ₗ[R] M'') → QuotSMulTop r M
' ≃ₗ[R] QuotSMulTop r M''
参数：r : R；M' ≃ₗ[R] M''。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M'` is isomorphic to `M''` as `R`-modules, then `M'⧸rM'` is isomorphic to `M
''⧸rM''`.
-/
protected def congr (e : M' ≃ₗ[R] M'') : QuotSMulTop r M' ≃ₗ[R] QuotSMulTop r M'' :=
  Submodule.Quotient.equiv (r • ⊤) (r • ⊤) e <|
    (Submodule.map_pointwise_smul r _ e.toLinearMap).trans (by simp)

/-- Reducing a module modulo `r` is the same as left tensoring with `R/(r)`. -/
/-
**QuotSMulTop.equivQuotTensor** 是 Mathlib 中的一个定义，位于命名空间 `QuotSMulTop`。
形式化陈述：equivQuotTensor : QuotSMulTop r M ≃ₗ[R] (R ⧸ Ideal.span {r}) otimes[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reducing a module modulo `r` is the same as left tensoring with `R/(r)`.
-/
noncomputable def equivQuotTensor :
    QuotSMulTop r M ≃ₗ[R] (R ⧸ Ideal.span {r}) ⊗[R] M :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (quotTensorEquivQuotSMul M _).symm

/-- Reducing a module modulo `r` is the same as right tensoring with `R/(r)`. -/
/-
**QuotSMulTop.equivTensorQuot** 是 Mathlib 中的一个定义，位于命名空间 `QuotSMulTop`。
形式化陈述：equivTensorQuot : QuotSMulTop r M ≃ₗ[R] M otimes[R] (R ⧸ Ideal.span {r})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reducing a module modulo `r` is the same as right tensoring with `R/(r)`.
-/
noncomputable def equivTensorQuot :
    QuotSMulTop r M ≃ₗ[R] M ⊗[R] (R ⧸ Ideal.span {r}) :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (tensorQuotEquivQuotSMul M _).symm

variable {M}

/-- The action of the functor `QuotSMulTop r` on morphisms. -/
/-
**QuotSMulTop.map** 是 Mathlib 中的一个定义，位于命名空间 `QuotSMulTop`。
形式化陈述：map : (M ->ₗ[R] M') ->ₗ[R] QuotSMulTop r M ->ₗ[R] QuotSMulTop r M'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the functor `QuotSMulTop r` on morphisms.
-/
def map : (M →ₗ[R] M') →ₗ[R] QuotSMulTop r M →ₗ[R] QuotSMulTop r M' :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
    map_le_iff_le_comap.mp <| le_of_eq_of_le (map_pointwise_smul _ _ _) <|
      smul_mono_right r le_top

@[simp]
/-
**QuotSMulTop.map_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`。
形式化陈述：map_apply_mk (f : M ->ₗ[R] M') (x : M) : map r f (Submodule.Quotient.mk x)
 = (Submodule.Quotient.mk (f x) : QuotSMulTop r M')
参数：f : M ->ₗ[R] M'；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply_mk (f : M →ₗ[R] M') (x : M) :
    map r f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : QuotSMulTop r M') := rfl

-- weirdly expensive to typecheck the type here?
/-
**QuotSMulTop.map_comp_mkQ** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`。
形式化陈述：map_comp_mkQ (f : M ->ₗ[R] M') : map r f ∘ₗ mkQ (r • ⊤) = mkQ (r • ⊤) ∘ₗ f
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma map_comp_mkQ (f : M →ₗ[R] M') :
    map r f ∘ₗ mkQ (r • ⊤) = mkQ (r • ⊤) ∘ₗ f := by
  ext; rfl

variable (M)

@[simp]
/-
**QuotSMulTop.map_id** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`。
形式化陈述：map_id : map r (LinearMap.id : M ->ₗ[R] M) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
lemma map_id : map r (LinearMap.id : M →ₗ[R] M) = .id :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

variable {M}

@[simp]
/-
**QuotSMulTop.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`。
形式化陈述：map_comp (g : M' ->ₗ[R] M'') (f : M ->ₗ[R] M') : map r (g ∘ₗ f) = map r g 
∘ₗ map r f
参数：g : M' ->ₗ[R] M''；f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
lemma map_comp (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map r (g ∘ₗ f) = map r g ∘ₗ map r f :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl
/-
**QuotSMulTop.equivQuotTensor_naturality_mk** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulT
op`。
形式化陈述：equivQuotTensor_naturality_mk (f : M ->ₗ[R] M') (x : M) : equivQuotTensor 
r M' (map r f (Submodule.Quotient.mk x)) = f.lTensor (R ⧸ Ideal.span {r}) (equiv
QuotTensor r M (Submodule.Quotient.mk x))
参数：f : M ->ₗ[R] M'；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_tmul`：lTensor_tmul (m : M) (n : N) : f.lTensor M (m ot
imesₜ n) = m otimesₜ f n
-/
lemma equivQuotTensor_naturality_mk (f : M →ₗ[R] M') (x : M) :
    equivQuotTensor r M' (map r f (Submodule.Quotient.mk x)) =
      f.lTensor (R ⧸ Ideal.span {r})
        (equivQuotTensor r M (Submodule.Quotient.mk x)) :=
  (LinearMap.lTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm
/-
**QuotSMulTop.equivQuotTensor_naturality** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`
。
形式化陈述：equivQuotTensor_naturality (f : M ->ₗ[R] M') : equivQuotTensor r M' ∘ₗ map
 r f = f.lTensor (R ⧸ Ideal.span {r}) ∘ₗ equivQuotTensor r M
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.quot_hom_ext`：quot_hom_ext (f g : (M ⧸ p) ->ₗ[R] M₂) (h : fora
ll x : M, f (Quotient.mk x) = g (Quotient.mk x)) : f = g
· 使用引理 `QuotSMulTop.equivQuotTensor_naturality_mk`：equivQuotTensor_naturality_mk
 (f : M ->ₗ[R] M') (x : M) : equivQuotTensor r M' (map r f (Submodule.Quotient.m
k x)) = f.lTensor (R ⧸ Ideal.sp…
-/
lemma equivQuotTensor_naturality (f : M →ₗ[R] M') :
    equivQuotTensor r M' ∘ₗ map r f =
      f.lTensor (R ⧸ Ideal.span {r}) ∘ₗ equivQuotTensor r M :=
  quot_hom_ext _ _ _ (equivQuotTensor_naturality_mk r f)
/-
**QuotSMulTop.equivTensorQuot_naturality_mk** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulT
op`。
形式化陈述：equivTensorQuot_naturality_mk (f : M ->ₗ[R] M') (x : M) : equivTensorQuot 
r M' (map r f (Submodule.Quotient.mk x)) = f.rTensor (R ⧸ Ideal.span {r}) (equiv
TensorQuot r M (Submodule.Quotient.mk x))
参数：f : M ->ₗ[R] M'；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_tmul`：rTensor_tmul (m : M) (n : N) : f.rTensor M (n ot
imesₜ m) = f n otimesₜ m
-/
lemma equivTensorQuot_naturality_mk (f : M →ₗ[R] M') (x : M) :
    equivTensorQuot r M' (map r f (Submodule.Quotient.mk x)) =
      f.rTensor (R ⧸ Ideal.span {r})
        (equivTensorQuot r M (Submodule.Quotient.mk x)) :=
  (LinearMap.rTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm
/-
**QuotSMulTop.equivTensorQuot_naturality** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`
。
形式化陈述：equivTensorQuot_naturality (f : M ->ₗ[R] M') : equivTensorQuot r M' ∘ₗ map
 r f = f.rTensor (R ⧸ Ideal.span {r}) ∘ₗ equivTensorQuot r M
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.quot_hom_ext`：quot_hom_ext (f g : (M ⧸ p) ->ₗ[R] M₂) (h : fora
ll x : M, f (Quotient.mk x) = g (Quotient.mk x)) : f = g
· 使用引理 `QuotSMulTop.equivTensorQuot_naturality_mk`：equivTensorQuot_naturality_mk
 (f : M ->ₗ[R] M') (x : M) : equivTensorQuot r M' (map r f (Submodule.Quotient.m
k x)) = f.rTensor (R ⧸ Ideal.sp…
-/
lemma equivTensorQuot_naturality (f : M →ₗ[R] M') :
    equivTensorQuot r M' ∘ₗ map r f =
      f.rTensor (R ⧸ Ideal.span {r}) ∘ₗ equivTensorQuot r M :=
  quot_hom_ext _ _ _ (equivTensorQuot_naturality_mk r f)
/-
**QuotSMulTop.map_surjective** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`。
形式化陈述：map_surjective {f : M ->ₗ[R] M'} (hf : Surjective f) : Surjective (map r f
)
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用引理 `QuotSMulTop.map_comp_mkQ`：map_comp_mkQ (f : M ->ₗ[R] M') : map r f ∘ₗ mk
Q (r • ⊤) = mkQ (r • ⊤) ∘ₗ f
-/
lemma map_surjective {f : M →ₗ[R] M'} (hf : Surjective f) : Surjective (map r f) :=
  have H₁ := (mkQ_surjective (r • ⊤ : Submodule R M')).comp hf
  @Surjective.of_comp _ _ _ _ (mkQ (r • ⊤ : Submodule R M)) <| by
    rwa [← LinearMap.coe_comp, map_comp_mkQ, LinearMap.coe_comp]
/-
**QuotSMulTop.map_exact** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`。
形式化陈述：map_exact {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''} (hfg : Exact f g) (hg : Su
rjective g) : Exact (map r f) (map r g)
参数：hfg : Exact f g；hg : Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.Exact.iff_of_ladder_linearEquiv`：iff_of_ladder_linearEquiv (h₁₂
 : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) : Exact g₁₂ g₂₃ ↔ Exact 
f₁₂ f₂₃
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `QuotSMulTop.equivQuotTensor_naturality`：equivQuotTensor_naturality (f : 
M ->ₗ[R] M') : equivQuotTensor r M' ∘ₗ map r f = f.lTensor (R ⧸ Ideal.span {r}) 
∘ₗ equivQuotTensor r M
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
-/
lemma map_exact {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Exact f g) (hg : Surjective g) : Exact (map r f) (map r g) :=
  (Exact.iff_of_ladder_linearEquiv (equivQuotTensor_naturality r f).symm
                             (equivQuotTensor_naturality r g).symm).mp
    (lTensor_exact (R ⧸ Ideal.span {r}) hfg hg)

variable (M M')

/-- Tensoring on the left and applying `QuotSMulTop · r` commute. -/
/-
**QuotSMulTop.tensorQuotSMulTopEquivQuotSMulTop** 是 Mathlib 中的一个定义，位于命名空间 `QuotS
MulTop`。
形式化陈述：tensorQuotSMulTopEquivQuotSMulTop : M otimes[R] QuotSMulTop r M' ≃ₗ[R] Quo
tSMulTop r (M otimes[R] M')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the left and applying `QuotSMulTop · r` commute.
-/
noncomputable def tensorQuotSMulTopEquivQuotSMulTop :
    M ⊗[R] QuotSMulTop r M' ≃ₗ[R] QuotSMulTop r (M ⊗[R] M') :=
  (equivTensorQuot r M').lTensor M ≪≫ₗ
    (TensorProduct.assoc R M M' (R ⧸ Ideal.span {r})).symm ≪≫ₗ
      (equivTensorQuot r (M ⊗[R] M')).symm

/-- Tensoring on the right and applying `QuotSMulTop · r` commute. -/
/-
**QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop** 是 Mathlib 中的一个定义，位于命名空间 `QuotS
MulTop`。
形式化陈述：quotSMulTopTensorEquivQuotSMulTop : QuotSMulTop r M' otimes[R] M ≃ₗ[R] Quo
tSMulTop r (M' otimes[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the right and applying `QuotSMulTop · r` commute.
-/
noncomputable def quotSMulTopTensorEquivQuotSMulTop :
    QuotSMulTop r M' ⊗[R] M ≃ₗ[R] QuotSMulTop r (M' ⊗[R] M) :=
  (equivQuotTensor r M').rTensor M ≪≫ₗ
    TensorProduct.assoc R (R ⧸ Ideal.span {r}) M' M ≪≫ₗ
      (equivQuotTensor r (M' ⊗[R] M)).symm

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be an `R`-algebra, then
  `S ⊗[R] (M/rM)` is isomorphic to `(S ⊗[R] M)⧸r(S ⊗[R] M)` as `S`-modules. -/
/-
**QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop** 是 Mathlib 中的一个定义，位于命名空间 `
QuotSMulTop`。
形式化陈述：algebraMapTensorEquivTensorQuotSMulTop (S : Type*) [CommRing S] [Algebra R
 S] : QuotSMulTop ((algebraMap R S) r) (S otimes[R] M) ≃ₗ[S] S otimes[R] QuotSMu
lTop r M
参数：S : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a commutative ring, `M` be an `R`-module, `S` be an `R`-algebra, then
  `S ⊗[R] (M/rM)` is isomorphic to `(S ⊗[R] M)⧸r(S ⊗[R] M)` as `S`-modules.
-/
noncomputable def algebraMapTensorEquivTensorQuotSMulTop (S : Type*) [CommRing S] [Algebra R S] :
    QuotSMulTop ((algebraMap R S) r) (S ⊗[R] M) ≃ₗ[S] S ⊗[R] QuotSMulTop r M :=
  Submodule.quotEquivOfEq _ _ (by simp [Ideal.map_span, ideal_span_singleton_smul]) ≪≫ₗ
    tensorQuotMapSMulEquivTensorQuot M S (Ideal.span {r}) ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ (ideal_span_singleton_smul r _)).baseChange R S _ _
/-
**QuotSMulTop.mem_annihilator** 是 Mathlib 中的一个引理，位于命名空间 `QuotSMulTop`。
形式化陈述：mem_annihilator (x : R) : x in Module.annihilator R (QuotSMulTop x M)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : M) (a : 
α) (S : Submodule R M) : m in S -> a • m in a • S
· 使用定理 `trivial`：True
-/
lemma mem_annihilator (x : R) : x ∈ Module.annihilator R (QuotSMulTop x M) := by
  refine Module.mem_annihilator.mpr (fun m ↦ ?_)
  rcases Submodule.Quotient.mk_surjective _ m with ⟨m', hm'⟩
  simpa [← hm', ← Submodule.Quotient.mk_smul] using Submodule.smul_mem_pointwise_smul m' x ⊤ trivial

end QuotSMulTop

