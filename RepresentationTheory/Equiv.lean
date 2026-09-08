/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Intertwining

/-!
## Main purpose

This file is a preliminary file for the `Iso`s in `Rep`, we build all the isomorphisms from
representation level to avoid abusing defeq.

TODO (Edison) : refactor `Rep` into a two-field structure (bundled `Representation`) and rebuild
all the `Iso`s in `Rep` using the equivs in this file.

-/

@[expose] public section

open scoped MonoidAlgebra

universe u u' v v' w w'

variable {k : Type u} [Semiring k] {G : Type v} [Monoid G] {V : Type v'} [AddCommMonoid V]
  [Module k V] {W : Type w'} [AddCommMonoid W] [Module k W] (H : Type w) [Subsingleton H]
  [MulOneClass H] [MulAction G H]

namespace Representation

noncomputable section

variable (k G) in
/-- If there exists `G`-action on a trivial monoid `H` then the induced representation
  on `k[H]` is equivalent to the trivial representation. -/
/-
**Representation.ofMulActionSubsingletonEquivTrivial** 是 Mathlib 中的一个定义，位于命名空间 `
Representation`。
形式化陈述：ofMulActionSubsingletonEquivTrivial : (ofMulAction k G H).Equiv (trivial k
 G k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there exists `G`-action on a trivial monoid `H` then the induced representati
on
  on `k[H]` is equivalent to the trivial representation.
-/
def ofMulActionSubsingletonEquivTrivial : (ofMulAction k G H).Equiv (trivial k G k) :=
  .mk (MonoidAlgebra.uniqueLinearEquiv k H) fun g ↦ by ext a; simp [Subsingleton.elim (g • a) a]

@[simp]
/-
**Representation.ofMulActionSubsingletonEquivTrivial_apply** 是 Mathlib 中的一个引理，位于
命名空间 `Representation`。
形式化陈述：ofMulActionSubsingletonEquivTrivial_apply (f : k[H]) : (ofMulActionSubsing
letonEquivTrivial k G H).toIntertwiningMap.toLinearMap f = f.coeff 1
参数：f : k[H]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofMulActionSubsingletonEquivTrivial_apply (f : k[H]) :
    (ofMulActionSubsingletonEquivTrivial k G H).toIntertwiningMap.toLinearMap f = f.coeff 1 := rfl

@[simp]
/-
**Representation.ofMulActionSubsingletonEquivTrivial_symm_apply** 是 Mathlib 中的一个
引理，位于命名空间 `Representation`。
形式化陈述：ofMulActionSubsingletonEquivTrivial_symm_apply (r : k) : (ofMulActionSubsi
ngletonEquivTrivial k G H).symm.toIntertwiningMap.toLinearMap r = .single 1 r
参数：r : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofMulActionSubsingletonEquivTrivial_symm_apply (r : k) :
    (ofMulActionSubsingletonEquivTrivial k G H).symm.toIntertwiningMap.toLinearMap r =
      .single 1 r := rfl

variable (k G) in
/-- The equivalence of representations between `(Fin 1 → G) →₀ k` and `G →₀ k`. -/
/-
**Representation.diagonalOneEquivLeftRegular** 是 Mathlib 中的一个定义，位于命名空间 `Represen
tation`。
形式化陈述：diagonalOneEquivLeftRegular : (diagonal k G 1).Equiv (leftRegular k G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of representations between `(Fin 1 → G) →₀ k` and `G →₀ k`.
-/
def diagonalOneEquivLeftRegular : (diagonal k G 1).Equiv (leftRegular k G) :=
  .mk (MonoidAlgebra.mapDomainLinearEquiv _ _ <| .funUnique _ _) fun g ↦ by ext; simp

@[simp]
/-
**Representation.diagonalOneEquivLeftRegular_apply_single** 是 Mathlib 中的一个引理，位于命
名空间 `Representation`。
形式化陈述：diagonalOneEquivLeftRegular_apply_single (f : Fin 1 -> G) (r : k) : (diago
nalOneEquivLeftRegular k G) (.single f r) = .single (f 0) r
参数：f : Fin 1 -> G；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapDomainLinearEquiv_single`：mapDomainLinearEquiv_single (
e : M ≃ N) (s : S) (m : M) : mapDomainLinearEquiv R S e (single m s) = single (e
 m) s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.funUnique_apply`：∀ (α : Sort u) (β : Sort u_1) [inst : Unique α], 
⇑(Equiv.funUnique α β) = fun f => f default
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma diagonalOneEquivLeftRegular_apply_single (f : Fin 1 → G) (r : k) :
    (diagonalOneEquivLeftRegular k G) (.single f r) = .single (f 0) r := by
  simp [diagonalOneEquivLeftRegular]

@[simp]
/-
**Representation.diagonalOneEquivLeftRegular_symm_apply_single** 是 Mathlib 中的一个引
理，位于命名空间 `Representation`。
形式化陈述：diagonalOneEquivLeftRegular_symm_apply_single (g : G) (r : k) : (diagonalO
neEquivLeftRegular k G).symm (.single g r) = .single (uniqueElim g) r
参数：g : G；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MonoidAlgebra.mapDomainLinearEquiv_single`：mapDomainLinearEquiv_single (
e : M ≃ N) (s : S) (m : M) : mapDomainLinearEquiv R S e (single m s) = single (e
 m) s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.funUnique_symm_apply`：∀ (α : Sort u) (β : Sort u_1) [inst : Unique
 α], ⇑(Equiv.funUnique α β).symm = uniqueElim
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma diagonalOneEquivLeftRegular_symm_apply_single (g : G) (r : k) :
    (diagonalOneEquivLeftRegular k G).symm (.single g r) = .single (uniqueElim g) r := by
  simp [diagonalOneEquivLeftRegular]

section comm

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] (σ : Representation k G V)
  (ρ : Representation k G W)

section finsupp

open Finsupp

/-- Every `f : α → V` can induce an intertwining map between `(α →₀ k[G])` and `V`. -/
@[simps! toLinearMap]
/-
**Representation.freeLift** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：freeLift {α : Type w'} (f : α -> V) : (free k G α).IntertwiningMap σ where
 toLinearMap
参数：f : α -> V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `f : α → V` can induce an intertwining map between `(α →₀ k[G])` and `V`.
-/
def freeLift {α : Type w'} (f : α → V) : (free k G α).IntertwiningMap σ where
  toLinearMap := linearCombination k (fun x => σ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (MonoidAlgebra.coeffLinearEquiv _).toLinearMap
  isIntertwining' g := by ext; simp

@[simp]
/-
**Representation.freeLift_single_single** 是 Mathlib 中的一个引理，位于命名空间 `Representatio
n`。
形式化陈述：freeLift_single_single {α : Type w'} (i : α) (g : G) (r : k) (f : α -> V) 
: freeLift σ f (Finsupp.single i (.single g r)) = r • σ g (f i)
参数：i : α；g : G；r : k；f : α -> V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.curryLinearEquiv_symm_apply`：∀ {α : Type u_9} {β : Type u_10} (R
 : Type u_11) {M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [
inst_2 : _root_.Module R …
· 使用引理 `Finsupp.uncurry_single`：uncurry_single (a : α) (b : β) (m : M) : (single
 a (single b m)).uncurry = single (a, b) m
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma freeLift_single_single {α : Type w'} (i : α) (g : G) (r : k) (f : α → V) :
    freeLift σ f (Finsupp.single i (.single g r)) = r • σ g (f i) := by
  simp [freeLift]

open IntertwiningMap

/-- Equiv between the intertwining map module `(α →₀ G →₀ k) → V` and the function space `α → V`. -/
@[simps]
/-
**Representation.freeLiftLEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：freeLiftLEquiv (α : Type w') : ((free k G α).IntertwiningMap σ) ≃ₗ[k] (α -
> V) where toFun f i
参数：α : Type w'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equiv between the intertwining map module `(α →₀ G →₀ k) → V` and the function s
pace `α → V`.
-/
def freeLiftLEquiv (α : Type w') : ((free k G α).IntertwiningMap σ) ≃ₗ[k] (α → V) where
  toFun f i := f (single i (.single 1 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := freeLift σ
  left_inv f := by ext; simp [← f.isIntertwining]
  right_inv f := by simp [← toLinearMap_apply]

/-- Equiv between representations induced by linear equiv between `(α →₀ V) ⊗[k] W` and
  `α →₀ (V ⊗[k] W)`. -/
/-
**Representation.finsuppTensorLeft** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：finsuppTensorLeft (α : Type w') [DecidableEq α] : ((σ.finsupp α).tprod ρ).
Equiv ((σ.tprod ρ).finsupp α)
参数：α : Type w'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equiv between representations induced by linear equiv between `(α →₀ V) ⊗[k] W` 
and
  `α →₀ (V ⊗[k] W)`.
-/
def finsuppTensorLeft (α : Type w') [DecidableEq α] :
    ((σ.finsupp α).tprod ρ).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppLeft _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppLeft_apply_tmul]
/-
**Representation.finsuppTensorLeft_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation`。
形式化陈述：finsuppTensorLeft_apply_tmul {α : Type w'} [DecidableEq α] (f : α ->₀ V) (
w : W) : finsuppTensorLeft σ ρ α (f otimesₜ w) = f.sum fun i v => Finsupp.single
 i (v otimesₜ w)
参数：f : α ->₀ V；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppLeft_apply_tmul`：finsuppLeft_apply_tmul (p : ι ->₀ 
M) (n : N) : finsuppLeft R S M N ι (p otimesₜ[R] n) = p.sum fun i m => Finsupp.s
ingle i (m otimesₜ[R] n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppTensorLeft_apply_tmul {α : Type w'} [DecidableEq α] (f : α →₀ V) (w : W) :
    finsuppTensorLeft σ ρ α (f ⊗ₜ w) = f.sum fun i v ↦ Finsupp.single i (v ⊗ₜ w) := by
  simp [finsuppTensorLeft, TensorProduct.finsuppLeft_apply_tmul]

@[simp]
/-
**Representation.finsuppTensorLeft_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `R
epresentation`。
形式化陈述：finsuppTensorLeft_apply_tmul_apply {α : Type w'} [DecidableEq α] (f : α ->
₀ V) (w : W) (i : α) : finsuppTensorLeft σ ρ α (f otimesₜ w) i = f i otimesₜ w
参数：f : α ->₀ V；w : W；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.finsuppTensorLeft_apply_tmul`：finsuppTensorLeft_apply_tmu
l {α : Type w'} [DecidableEq α] (f : α ->₀ V) (w : W) : finsuppTensorLeft σ ρ α 
(f otimesₜ w) = f.sum fun i v => …
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finsupp.sum_ite_eq'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) 
(a : α) (…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma finsuppTensorLeft_apply_tmul_apply {α : Type w'} [DecidableEq α] (f : α →₀ V) (w : W)
    (i : α) : finsuppTensorLeft σ ρ α (f ⊗ₜ w) i = f i ⊗ₜ w := by
  simp +contextual [finsuppTensorLeft_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]
/-
**Representation.finsuppTensorLeft_symm_apply_single** 是 Mathlib 中的一个引理，位于命名空间 `
Representation`。
形式化陈述：finsuppTensorLeft_symm_apply_single {α : Type w'} [DecidableEq α] (i : α) 
(v : V) (w : W) : (finsuppTensorLeft σ ρ α).symm (Finsupp.single i (v otimesₜ w)
) = Finsupp.single i v otimesₜ w
参数：i : α；v : V；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppLeft_symm_apply_single`：finsuppLeft_symm_apply_sing
le (i : ι) (m : M) (n : N) : (finsuppLeft R S M N ι).symm (Finsupp.single i (m o
timesₜ[R] n)) = Finsupp.single i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppTensorLeft_symm_apply_single {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W) :
    (finsuppTensorLeft σ ρ α).symm (Finsupp.single i (v ⊗ₜ w)) = Finsupp.single i v ⊗ₜ w := by
  simp [finsuppTensorLeft]

/-- Equiv between representations induced by linear equiv between `V ⊗[k] (α →₀ W)` and
  `α →₀ (V ⊗[k] W)`. -/
/-
**Representation.finsuppTensorRight** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：finsuppTensorRight (α : Type w') [DecidableEq α] : (σ.tprod (ρ.finsupp α))
.Equiv ((σ.tprod ρ).finsupp α)
参数：α : Type w'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equiv between representations induced by linear equiv between `V ⊗[k] (α →₀ W)` 
and
  `α →₀ (V ⊗[k] W)`.
-/
def finsuppTensorRight (α : Type w') [DecidableEq α] :
    (σ.tprod (ρ.finsupp α)).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppRight _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppRight_apply_tmul]
/-
**Representation.finsuppTensorRight_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation`。
形式化陈述：finsuppTensorRight_apply_tmul {α : Type w'} [DecidableEq α] (v : V) (f : α
 ->₀ W) : finsuppTensorRight σ ρ α (v otimesₜ f) = f.sum fun i w => Finsupp.sing
le i (v otimesₜ w)
参数：v : V；f : α ->₀ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppRight_apply_tmul`：finsuppRight_apply_tmul (m : M) (
p : ι ->₀ N) : finsuppRight R S M N ι (m otimesₜ[R] p) = p.sum fun i n => Finsup
p.single i (m otimesₜ[R] n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppTensorRight_apply_tmul {α : Type w'} [DecidableEq α] (v : V) (f : α →₀ W) :
    finsuppTensorRight σ ρ α (v ⊗ₜ f) = f.sum fun i w ↦ Finsupp.single i (v ⊗ₜ w) := by
  simp [finsuppTensorRight, TensorProduct.finsuppRight_apply_tmul]

@[simp]
/-
**Representation.finsuppTensorRight_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `
Representation`。
形式化陈述：finsuppTensorRight_apply_tmul_apply {α : Type w'} [DecidableEq α] (v : V) 
(f : α ->₀ W) (i : α) : finsuppTensorRight σ ρ α (v otimesₜ f) i = v otimesₜ f i
参数：v : V；f : α ->₀ W；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.finsuppTensorRight_apply_tmul`：finsuppTensorRight_apply_t
mul {α : Type w'} [DecidableEq α] (v : V) (f : α ->₀ W) : finsuppTensorRight σ ρ
 α (v otimesₜ f) = f.sum fun i w =…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finsupp.sum_ite_eq'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) 
(a : α) (…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma finsuppTensorRight_apply_tmul_apply {α : Type w'} [DecidableEq α] (v : V) (f : α →₀ W)
    (i : α) : finsuppTensorRight σ ρ α (v ⊗ₜ f) i = v ⊗ₜ f i := by
  simp +contextual [finsuppTensorRight_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]
/-
**Representation.finsuppTensorRight_symm_apply_single** 是 Mathlib 中的一个引理，位于命名空间 
`Representation`。
形式化陈述：finsuppTensorRight_symm_apply_single {α : Type w'} [DecidableEq α] (i : α)
 (v : V) (w : W) : (finsuppTensorRight σ ρ α).symm (Finsupp.single i (v otimesₜ 
w)) = v otimesₜ Finsupp.single i w
参数：i : α；v : V；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppRight_symm_apply_single`：finsuppRight_symm_apply_si
ngle (i : ι) (m : M) (n : N) : (finsuppRight R S M N ι).symm (Finsupp.single i (
m otimesₜ[R] n)) = m otimesₜ[R] Fi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppTensorRight_symm_apply_single {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W) :
    (finsuppTensorRight σ ρ α).symm (Finsupp.single i (v ⊗ₜ w)) = v ⊗ₜ Finsupp.single i w := by
  simp [finsuppTensorRight]

/-- Equiv between representations induced by linear equiv between `(G →₀ k) ⊗[k] (α →₀ k)` and
  `α →₀ G →₀ k`. -/
/-
**Representation.leftRegularTensorTrivialIsoFree** 是 Mathlib 中的一个定义，位于命名空间 `Repr
esentation`。
形式化陈述：leftRegularTensorTrivialIsoFree (α : Type w') : ((leftRegular k G).tprod (
trivial k G k[α])).Equiv (free k G α)
参数：α : Type w'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equiv between representations induced by linear equiv between `(G →₀ k) ⊗[k] (α 
→₀ k)` and
  `α →₀ G →₀ k`.
-/
def leftRegularTensorTrivialIsoFree (α : Type w') :
    ((leftRegular k G).tprod (trivial k G k[α])).Equiv (free k G α) :=
  .mk (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv _) (MonoidAlgebra.coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ curryLinearEquiv k
      ≪≫ₗ Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv _).symm) fun g ↦ by ext; simp

@[simp]
/-
**Representation.leftRegularTensorTrivialIsoFree_apply_single_tmul_single** 是 Ma
thlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：leftRegularTensorTrivialIsoFree_apply_single_tmul_single {α : Type w'} (g 
: G) (i : α) (r s : k) : leftRegularTensorTrivialIsoFree α (.single g r otimesₜ 
.single i s) = .single i (.single g (r * s))
参数：g : G；i : α；r s : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `finsuppTensorFinsupp'_single_tmul_single`：∀ (R : Type u_1) (ι : Type u_5
) (κ : Type u_6) [inst : CommSemiring R] (a : ι) (b : κ) (r₁ r₂ : R),   (finsupp
TensorFinsupp' R ι κ) ((fun₀ |…
· 使用定理 `Finsupp.domCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (e : α ≃ β) (l : α →₀ M),   (Finsupp.domCongr e) l = Fin
supp.equivMa…
· 使用定理 `Finsupp.equivMapDomain_single`：equivMapDomain_single (f : α ≃ β) (a : α)
 (b : M) : equivMapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.curryLinearEquiv_apply`：∀ {α : Type u_9} {β : Type u_10} (R : Ty
pe u_11) {M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R …
· 使用引理 `Finsupp.curry_single`：curry_single (a : α × β) (m : M) : (single a m).cu
rry = single a.1 (single a.2 m)
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftRegularTensorTrivialIsoFree_apply_single_tmul_single {α : Type w'} (g : G) (i : α)
    (r s : k) : leftRegularTensorTrivialIsoFree α (.single g r ⊗ₜ .single i s) =
      .single i (.single g (r * s)) := by
  simp [leftRegularTensorTrivialIsoFree]

@[simp]
/-
**Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single** 是 Ma
thlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：leftRegularTensorTrivialIsoFree_symm_apply_single_single {α : Type w'} (i 
: α) (g : G) (r : k) : (leftRegularTensorTrivialIsoFree α).symm (.single i (.sin
gle g r)) = .single g 1 otimesₜ .single i r
参数：i : α；g : G；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.isIntertwining_symm_isIntertwining`：∀ {A : Type u_1} {G : Ty
pe u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   
[inst_2 : AddCommMonoid V] [inst_3 :…
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.mapRange.linearEquiv_symm`：∀ {α : Type u_1} {M : Type u_2} {N : 
Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring 
R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.domLCongr_symm`：domLCongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) : (
(Finsupp.domLCongr f).symm : (_ ->₀ M) ≃ₗ[R] _) = Finsupp.domLCongr f.symm
· 使用定理 `Representation.Equiv.mk.congr_simp`：∀ {A : Type u_1} {G : Type u_2} {V :
 Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : Ad
dCommMonoid V] [inst_3 :…
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.curryLinearEquiv_symm_apply`：∀ {α : Type u_9} {β : Type u_10} (R
 : Type u_11) {M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [
inst_2 : _root_.Module R …
· 使用引理 `Finsupp.uncurry_single`：uncurry_single (a : α) (b : β) (m : M) : (single
 a (single b m)).uncurry = single (a, b) m
· 使用定理 `Finsupp.domCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (e : α ≃ β) (l : α →₀ M),   (Finsupp.domCongr e) l = Fin
supp.equivMa…
· 使用定理 `Finsupp.equivMapDomain_single`：equivMapDomain_single (f : α ≃ β) (a : α)
 (b : M) : equivMapDomain f (single a b) = single (f a) b
· 使用定理 `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul`：∀ (R : Type u_1) (
ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r : R),   ((fi
nsuppTensorFinsupp' R ι κ).symm fun₀ | i =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftRegularTensorTrivialIsoFree_symm_apply_single_single {α : Type w'} (i : α) (g : G)
    (r : k) :
    (leftRegularTensorTrivialIsoFree α).symm (.single i (.single g r)) =
      .single g 1 ⊗ₜ .single i r := by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

end finsupp

/-- The linear equiv between the hom module `k[G] ⟶ᵍ V` and `V` itself. -/
@[simps!]
/-
**Representation.leftRegularMapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：leftRegularMapEquiv : (leftRegular k G).IntertwiningMap σ ≃ₗ[k] V where to
Fun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equiv between the hom module `k[G] ⟶ᵍ V` and `V` itself.
-/
def leftRegularMapEquiv : (leftRegular k G).IntertwiningMap σ ≃ₗ[k] V where
  toFun f := (Finsupp.llift V k k G).symm
    (f.toLinearMap ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap) (1 : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Finsupp.llift _ _ k _ (fun g ↦ σ g v) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv _).toLinearMap, fun g ↦ by ext g'; simp⟩
  left_inv x := by ext; simp [← x.isIntertwining]
  right_inv v := by simp

set_option backward.isDefEq.respectTransparency false in
/-
**Representation.leftRegularMapEquiv_symm_single** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation`。
形式化陈述：leftRegularMapEquiv_symm_single (g : G) (v : V) : ((leftRegularMapEquiv σ)
.symm v) (.single g 1) = σ g v
参数：g : G；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.leftRegularMapEquiv_symm_apply_toFun`：∀ {G : Type v} [ins
t : Monoid G] {V : Type v'} [inst_1 : AddCommMonoid V] {k : Type u} [inst_2 : Co
mmSemiring k]   [inst_3 : _root_.Module k…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma leftRegularMapEquiv_symm_single (g : G) (v : V) :
    ((leftRegularMapEquiv σ).symm v) (.single g 1) = σ g v := by
  simp

end comm

end

end Representation

